/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharData
import LeanDring.P5.Certificate.Characters.Twin2.CharAssembly
import LeanDring.P5.Certificate.Characters.Twin2.CharExp
import LeanDring.P5.Certificate.SubgroupInventory.Twin2.FratDischarge
import LeanDring.P5.Certificate.Characters.Twin2.CharVecLen
import LeanDring.Theory.DRing.GabCount
import LeanDring.P5.Certificate.Characters.Twin1.CharExtend
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Step 1 — the isolated extension obligation `CharExtendsAt2` (character certification)

This file discharges the single named hypothesis of Linear-character data: a `charOK2`-valid
exponent vector `e` defines an *additive* functional `charForm2 B e` on the
subgroup `H = ⟨B⟩` presented by a well-formed echelon basis `B`, i.e.
`charForm2 B e (x·y) = charForm2 B e x + charForm2 B e y` for `x, y ∈ H`.

The proof is a structural recursion on the echelon basis `B = p :: rest`,
mirroring `card_ofList_cons`: writing `H = ⟨p⟩·N` with `N = ⟨rest⟩`, every
`x ∈ H` factors as `x = x' · pᵃ` with `x' = clearStep 2 p x ∈ N` and
`a = coordAt x (pivotDepth p)`. The lead coordinate is additive
(`coordAt_mul_right`), and the two collection corrections
(a power carry `pⁿ` with `n ∈ {0,5}` and a conjugation tail `pᵃ y' p⁻ᵃ`) are
exactly the terms killed by the `charOK2` power/commutator conditions.
-/

namespace LeanDring.P5Presentation

namespace Q2

open Fin.NatCast
open scoped Pointwise
open scoped commutatorElement

set_option maxRecDepth 100000

/-! ## Recursion for the exponent extraction `expNat2` / `expVec2` -/

/-- The single fold step underlying `expNat2` (record the pivot exponent, then
strip that pivot). -/
private def eStep (acc : Coordinates × List Nat) (p : Coordinates) : Coordinates × List Nat :=
  (clearStep 2 p acc.1, acc.2 ++ [(coordAt acc.1 (pivotDepth p)).val])

private theorem eStep_apply (x : Coordinates) (acc : List Nat) (p : Coordinates) :
    eStep (x, acc) p = (clearStep 2 p x, acc ++ [(coordAt x (pivotDepth p)).val]) := rfl

private theorem expNat2_eq (B : List Coordinates) (x : Coordinates) :
    expNat2 B x = (B.foldl eStep (x, [])).2 := rfl

/-- The accumulator of the fold only ever gets appended to; so the fold from a
non-empty accumulator is the fold from `[]` with the accumulator prefixed. -/
private theorem eStep_foldl_pair (L : List Coordinates) :
    ∀ (x : Coordinates) (acc : List Nat),
      L.foldl eStep (x, acc)
        = ((L.foldl eStep (x, [])).1, acc ++ (L.foldl eStep (x, [])).2) := by
  induction L with
  | nil => intro x acc; simp
  | cons p rest ih =>
      intro x acc
      rw [List.foldl_cons, List.foldl_cons, eStep_apply, eStep_apply,
        ih (clearStep 2 p x) (acc ++ [(coordAt x (pivotDepth p)).val]),
        ih (clearStep 2 p x) ([] ++ [(coordAt x (pivotDepth p)).val])]
      simp [List.append_assoc]

private theorem expNat2_cons (p : Coordinates) (rest : List Coordinates) (x : Coordinates) :
    expNat2 (p :: rest) x
      = (coordAt x (pivotDepth p)).val :: expNat2 rest (clearStep 2 p x) := by
  rw [expNat2_eq, List.foldl_cons, eStep_apply, eStep_foldl_pair]
  simp [expNat2_eq]

private theorem expVec2_cons (p : Coordinates) (rest : List Coordinates) (x : Coordinates) :
    expVec2 (p :: rest) x
      = ((coordAt x (pivotDepth p)).val : ZMod 25) :: expVec2 rest (clearStep 2 p x) := by
  change (expNat2 (p :: rest) x).map (fun n => (n : ZMod 25))
      = _ :: (expNat2 rest (clearStep 2 p x)).map (fun n => (n : ZMod 25))
  rw [expNat2_cons]
  rfl

/-! ## Recursion for `dotZ` / `charForm2` -/

private theorem dotZ_cons (a : ZMod 25) (e : List (ZMod 25)) (b : ZMod 25) (v : List (ZMod 25)) :
    dotZ (a :: e) (b :: v) = a * b + dotZ e v := by
  simp [dotZ]

private theorem dotZ_nil_left (v : List (ZMod 25)) : dotZ [] v = 0 := by
  simp [dotZ]

private theorem charForm2_nil_B (e : List (ZMod 25)) (x : Coordinates) :
    charForm2 [] e x = 0 := by
  simp [charForm2, expVec2, expNat2, dotZ]

private theorem charForm2_nil_e (B : List Coordinates) (x : Coordinates) :
    charForm2 B [] x = 0 := by
  simp [charForm2, dotZ_nil_left]

private theorem charForm2_cons (p : Coordinates) (rest : List Coordinates) (e₀ : ZMod 25)
    (erest : List (ZMod 25)) (x : Coordinates) :
    charForm2 (p :: rest) (e₀ :: erest) x
      = e₀ * ((coordAt x (pivotDepth p)).val : ZMod 25)
        + charForm2 rest erest (clearStep 2 p x) := by
  simp only [charForm2, expVec2_cons, dotZ_cons]

/-- Clearing a pivot from an element whose pivot coordinate already vanishes is
a no-op. -/
private theorem clearStep_id {p w : Coordinates} (h : coordAt w (pivotDepth p) = 0) :
    clearStep 2 p w = w := by
  simp only [clearStep, h, Fin.val_zero, mpow]
  rfl

/-- `charForm2` of the identity vanishes. -/
private theorem charForm2_one (B : List Coordinates) (e : List (ZMod 25)) :
    charForm2 B e ((0, 0, 0, 0, 0) : Coordinates) = 0 := by
  induction B generalizing e with
  | nil => exact charForm2_nil_B e _
  | cons p rest ih =>
      cases e with
      | nil => exact charForm2_nil_e _ _
      | cons e₀ erest =>
          rw [charForm2_cons]
          have h0 : coordAt ((0, 0, 0, 0, 0) : Coordinates) (pivotDepth p) = 0 :=
            coordAt_zero_all _
          rw [clearStep_id h0, h0]
          simp [ih]

/-- If the pivot coordinate of `w` vanishes, the leading `charForm2` term drops
and the head of `e`/`B` can be discarded. -/
private theorem charForm2_lead0 (p : Coordinates) (rest : List Coordinates) (e₀ : ZMod 25)
    (erest : List (ZMod 25)) (w : Coordinates) (h : coordAt w (pivotDepth p) = 0) :
    charForm2 (p :: rest) (e₀ :: erest) w = charForm2 rest erest w := by
  rw [charForm2_cons, clearStep_id h, h]
  simp

/-! ## `Coordinate 2`-typed wrappers (defeq), so `rw`/`simp` match the core terms -/

private theorem charForm2_nil_B' (e : List (ZMod 25)) (x : Coordinate 2) :
    charForm2 ([] : List (Coordinate 2)) e x = 0 := charForm2_nil_B e x

private theorem charForm2_nil_e' (B : List (Coordinate 2)) (x : Coordinate 2) :
    charForm2 B [] x = 0 := charForm2_nil_e B x

private theorem charForm2_one' (B : List (Coordinate 2)) (e : List (ZMod 25)) :
    charForm2 B e ((1 : Coordinate 2)) = 0 := charForm2_one B e

private theorem charForm2_cons' (p : Coordinate 2) (rest : List (Coordinate 2)) (e₀ : ZMod 25)
    (erest : List (ZMod 25)) (x : Coordinate 2) :
    charForm2 ((p :: rest : List (Coordinate 2))) (e₀ :: erest) x
      = e₀ * ((coordAt x (pivotDepth p)).val : ZMod 25)
        + charForm2 rest erest (clearStep 2 p x) :=
  charForm2_cons p rest e₀ erest x

private theorem charForm2_lead0' (p : Coordinate 2) (rest : List (Coordinate 2)) (e₀ : ZMod 25)
    (erest : List (ZMod 25)) (w : Coordinate 2) (h : coordAt w (pivotDepth p) = 0) :
    charForm2 ((p :: rest : List (Coordinate 2))) (e₀ :: erest) w = charForm2 rest erest w :=
  charForm2_lead0 p rest e₀ erest w h

/-- The computable commutator of two members of a subgroup lands in it. -/
private theorem commutatorC_mem {K : Subgroup (Coordinate 2)} {a b : Coordinate 2}
    (ha : a ∈ K) (hb : b ∈ K) : (commutatorC a b : Coordinate 2) ∈ K := by
  have h : (commutatorC a b : Coordinate 2) = (a * b * a⁻¹ * b⁻¹ : Coordinate 2) := by
    rw [commutatorC_eq, commutatorElement_def]
  rw [h]
  exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)

/-! ## Conjugation invariance of `charForm2 rest erest` on `N = ⟨rest⟩`

Given that `charForm2 rest erest` is additive on `N` (`hadd`, the induction
hypothesis) and kills the commutators `⁅p, g⁆` for the generators `g` of `N`
(`hcomm0`, from `charOK2`), it is invariant under conjugation by `p`. -/

/-- On an additive functional, inverses negate. -/
private theorem charForm2_inv
    (rest : List (Coordinate 2)) (erest : List (ZMod 25))
    (hadd : ∀ u v : Coordinate 2, u ∈ ofList 2 hq2 rest → v ∈ ofList 2 hq2 rest →
        charForm2 rest erest ((u * v : Coordinate 2))
          = charForm2 rest erest u + charForm2 rest erest v)
    (w : Coordinate 2) (hw : w ∈ ofList 2 hq2 rest) :
    charForm2 rest erest ((w⁻¹ : Coordinate 2)) = - charForm2 rest erest w := by
  have h1 : charForm2 rest erest ((w * w⁻¹ : Coordinate 2))
      = charForm2 rest erest w + charForm2 rest erest ((w⁻¹ : Coordinate 2)) :=
    hadd w w⁻¹ hw (Subgroup.inv_mem _ hw)
  rw [mul_inv_cancel] at h1
  have h0 : charForm2 rest erest ((1 : Coordinate 2)) = 0 := charForm2_one rest erest
  rw [h0] at h1
  linear_combination -h1

/-- **Conjugation invariance.** `charForm2 rest erest (p·w·p⁻¹) = charForm2 rest erest w`
for every `w ∈ N`. -/
private theorem charForm2_conj
    (p : Coordinate 2) (rest : List (Coordinate 2)) (erest : List (ZMod 25))
    (hnorm : p ∈ Subgroup.normalizer (ofList 2 hq2 rest))
    (hadd : ∀ u v : Coordinate 2, u ∈ ofList 2 hq2 rest → v ∈ ofList 2 hq2 rest →
        charForm2 rest erest ((u * v : Coordinate 2))
          = charForm2 rest erest u + charForm2 rest erest v)
    (hcomm0 : ∀ g ∈ rest, charForm2 rest erest (commutatorC p g) = 0) :
    ∀ w : Coordinate 2, w ∈ ofList 2 hq2 rest →
      charForm2 rest erest ((p * w * p⁻¹ : Coordinate 2)) = charForm2 rest erest w := by
  have hconj : ∀ w : Coordinate 2, w ∈ ofList 2 hq2 rest →
      (p * w * p⁻¹ : Coordinate 2) ∈ ofList 2 hq2 rest :=
    fun w hw => (Subgroup.mem_normalizer_iff.mp hnorm w).mp hw
  intro w hw
  induction hw using Subgroup.closure_induction with
  | mem g hg =>
      have hgN : g ∈ ofList 2 hq2 rest := Subgroup.subset_closure hg
      have hcomm_mem : (⁅p, g⁆ : Coordinate 2) ∈ ofList 2 hq2 rest := by
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (hconj g hgN) (Subgroup.inv_mem _ hgN)
      have hsplit : (p * g * p⁻¹ : Coordinate 2) = (⁅p, g⁆ * g : Coordinate 2) := by
        rw [commutatorElement_def]; group
      have hc0 : charForm2 rest erest (⁅p, g⁆ : Coordinate 2) = 0 := by
        rw [← commutatorC_eq]; exact hcomm0 g hg
      rw [hsplit, hadd _ _ hcomm_mem hgN, hc0, zero_add]
  | one =>
      have h1 : (p * 1 * p⁻¹ : Coordinate 2) = 1 := by group
      rw [h1]
  | mul a b ha hb iha ihb =>
      have haN : a ∈ ofList 2 hq2 rest := ha
      have hbN : b ∈ ofList 2 hq2 rest := hb
      have hsplit : (p * (a * b) * p⁻¹ : Coordinate 2)
          = ((p * a * p⁻¹) * (p * b * p⁻¹) : Coordinate 2) := by group
      rw [hsplit, hadd _ _ (hconj a haN) (hconj b hbN), iha, ihb, hadd _ _ haN hbN]
  | inv a ha iha =>
      have haN : a ∈ ofList 2 hq2 rest := ha
      have hsplit : (p * a⁻¹ * p⁻¹ : Coordinate 2) = ((p * a * p⁻¹)⁻¹ : Coordinate 2) := by group
      rw [hsplit, charForm2_inv rest erest hadd _ (hconj a haN), iha,
        charForm2_inv rest erest hadd a haN]

/-- Conjugation invariance iterated to a natural power of `p`. -/
private theorem charForm2_conj_pow
    (p : Coordinate 2) (rest : List (Coordinate 2)) (erest : List (ZMod 25))
    (hnorm : p ∈ Subgroup.normalizer (ofList 2 hq2 rest))
    (hadd : ∀ u v : Coordinate 2, u ∈ ofList 2 hq2 rest → v ∈ ofList 2 hq2 rest →
        charForm2 rest erest ((u * v : Coordinate 2))
          = charForm2 rest erest u + charForm2 rest erest v)
    (hcomm0 : ∀ g ∈ rest, charForm2 rest erest (commutatorC p g) = 0) :
    ∀ (k : ℕ) (w : Coordinate 2), w ∈ ofList 2 hq2 rest →
      charForm2 rest erest ((p ^ k * w * (p ^ k)⁻¹ : Coordinate 2)) = charForm2 rest erest w := by
  have hconj : ∀ w : Coordinate 2, w ∈ ofList 2 hq2 rest →
      (p * w * p⁻¹ : Coordinate 2) ∈ ofList 2 hq2 rest :=
    fun w hw => (Subgroup.mem_normalizer_iff.mp hnorm w).mp hw
  have hconjK : ∀ (k : ℕ) (w : Coordinate 2), w ∈ ofList 2 hq2 rest →
      (p ^ k * w * (p ^ k)⁻¹ : Coordinate 2) ∈ ofList 2 hq2 rest := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
        intro w hw
        have hstep : (p ^ (k + 1) * w * (p ^ (k + 1))⁻¹ : Coordinate 2)
            = (p * (p ^ k * w * (p ^ k)⁻¹) * p⁻¹ : Coordinate 2) := by
          rw [pow_succ']; group
        rw [hstep]; exact hconj _ (ih w hw)
  intro k
  induction k with
  | zero =>
      intro w hw
      have h0 : (p ^ 0 * w * (p ^ 0)⁻¹ : Coordinate 2) = w := by group
      rw [h0]
  | succ k ih =>
      intro w hw
      have heq : (p ^ (k + 1) * w * (p ^ (k + 1))⁻¹ : Coordinate 2)
          = (p * (p ^ k * w * (p ^ k)⁻¹) * p⁻¹ : Coordinate 2) := by
        rw [pow_succ']; group
      rw [heq, charForm2_conj p rest erest hnorm hadd hcomm0 _ (hconjK k w hw), ih w hw]

/-! ## Unpacking `charOK2` into semantic power/commutator conditions -/

private theorem charOK2_pow (B : List Coordinates) (e : List (ZMod 25)) (h : charOK2 B e = true) :
    ∀ i < B.length, charForm2 B e (mpow 2 (B.getD i zc) 5) = 5 * e.getD i 0 := by
  intro i hi
  have h1 : (List.range B.length).all
      (fun i => decide (dotZ e (expVec2 B (mpow 2 (B.getD i zc) 5)) = 5 * e.getD i 0)) = true := by
    rw [charOK2, Bool.and_eq_true] at h; exact h.1
  have hcell := (List.all_eq_true.mp h1) i (List.mem_range.mpr hi)
  simpa [charForm2] using of_decide_eq_true hcell

private theorem charOK2_comm (B : List Coordinates) (e : List (ZMod 25)) (h : charOK2 B e = true) :
    ∀ i j, i < j → j < B.length →
      charForm2 B e (commutatorC (B.getD i zc) (B.getD j zc)) = 0 := by
  intro i j hij hj
  have h2 : (List.range B.length).all (fun i => (List.range B.length).all (fun j =>
      !(Nat.blt i j) ||
        decide (dotZ e (expVec2 B (commutatorC (B.getD i zc) (B.getD j zc))) = 0))) = true := by
    rw [charOK2, Bool.and_eq_true] at h; exact h.2
  have hi : i < B.length := lt_trans hij hj
  have hrow := (List.all_eq_true.mp h2) i (List.mem_range.mpr hi)
  have hcell := (List.all_eq_true.mp hrow) j (List.mem_range.mpr hj)
  have hlt : Nat.blt i j = true := by simp only [Nat.blt_eq]; omega
  rw [hlt] at hcell
  simp only [Bool.not_true, Bool.false_or] at hcell
  simpa [charForm2] using of_decide_eq_true hcell

/-! ## The additivity core -/

/-- **Step 1 core.** For a well-formed echelon basis `B` and a vector `e`
satisfying the (semantic) `charOK2` power/commutator conditions, `charForm2 B e`
is additive on `⟨B⟩`. Proved by structural recursion on `B`. -/
private theorem charForm2_additive_core :
    ∀ (B : List (Coordinate 2)), WF 2 hq2 B → ∀ (e : List (ZMod 25)),
      (∀ i < B.length, charForm2 B e (mpow 2 (B.getD i zc) 5) = 5 * e.getD i 0) →
      (∀ i j, i < j → j < B.length →
          charForm2 B e (commutatorC (B.getD i zc) (B.getD j zc)) = 0) →
      ∀ (x y : Coordinate 2), x ∈ ofList 2 hq2 B → y ∈ ofList 2 hq2 B →
        charForm2 B e ((x * y : Coordinate 2)) = charForm2 B e x + charForm2 B e y := by
  intro B
  induction B with
  | nil => intro _ e _ _ x y _ _; simp [charForm2_nil_B']
  | cons p rest ih =>
      intro hwf e hPow hComm x y hx hy
      obtain ⟨hp5, hlead, hrest, hpow, hnorm, hwfrest⟩ := hwf
      cases e with
      | nil => simp [charForm2_nil_e']
      | cons e₀ erest =>
          set d := pivotDepth p with hd_def
          set N := ofList 2 hq2 rest with hN_def
          -- an element of `N` has vanishing pivot coordinate
          have hcoord0 : ∀ w : Coordinate 2, w ∈ N → coordAt w d = 0 :=
            fun w hw => (ofList_le_depthGE hq2 p rest hrest) hw d (Nat.lt_succ_self d)
          -- generators of `N` sit in `N`
          have hgetN : ∀ i, i < rest.length → (rest.getD i zc : Coordinate 2) ∈ N := by
            intro i hi
            rw [List.getD_eq_getElem rest zc hi]
            exact Subgroup.subset_closure (List.getElem_mem hi)
          -- `p^5 ∈ N`, and `5 ∣ j ⟹ p^j ∈ N`
          have hpow_dvd : ∀ j : ℤ, (5 : ℤ) ∣ j → (p ^ j : Coordinate 2) ∈ N := by
            intro j hj; obtain ⟨k, rfl⟩ := hj
            rw [zpow_mul, show (5 : ℤ) = ((5 : ℕ) : ℤ) from rfl, zpow_natCast]
            exact Subgroup.zpow_mem N hpow k
          -- conjugation of `N` by `p`, and by a natural power of `p`, stays in `N`
          have hconj : ∀ w : Coordinate 2, w ∈ N → (p * w * p⁻¹ : Coordinate 2) ∈ N :=
            fun w hw => (Subgroup.mem_normalizer_iff.mp hnorm w).mp hw
          have hconjNat : ∀ (k : ℕ) (w : Coordinate 2), w ∈ N →
              (p ^ k * w * (p ^ k)⁻¹ : Coordinate 2) ∈ N := by
            intro k
            induction k with
            | zero => intro w hw; simpa using hw
            | succ k ih2 =>
                intro w hw
                have hstep : (p ^ (k + 1) * w * (p ^ (k + 1))⁻¹ : Coordinate 2)
                    = (p * (p ^ k * w * (p ^ k)⁻¹) * p⁻¹ : Coordinate 2) := by
                  rw [pow_succ']; group
                rw [hstep]; exact hconj _ (ih2 w hw)
          -- inherited semantic conditions for `rest`/`erest`
          have hPow_rest : ∀ i < rest.length,
              charForm2 rest erest (mpow 2 (rest.getD i zc) 5) = 5 * erest.getD i 0 := by
            intro i hi
            have hb := hPow (i + 1) (by simp only [List.length_cons]; omega)
            rw [List.getD_cons_succ, List.getD_cons_succ] at hb
            have hwmem : (mpow 2 (rest.getD i zc) 5 : Coordinate 2) ∈ N := by
              rw [mpow_eq_pow hq2]; exact Subgroup.pow_mem _ (hgetN i hi) 5
            rw [charForm2_lead0' p rest e₀ erest _ (hcoord0 _ hwmem)] at hb
            exact hb
          have hComm_rest : ∀ i j, i < j → j < rest.length →
              charForm2 rest erest (commutatorC (rest.getD i zc) (rest.getD j zc)) = 0 := by
            intro i j hij hj
            have hb := hComm (i + 1) (j + 1) (by omega) (by simp only [List.length_cons]; omega)
            rw [List.getD_cons_succ, List.getD_cons_succ] at hb
            have hwmem : (commutatorC (rest.getD i zc) (rest.getD j zc) : Coordinate 2) ∈ N :=
              commutatorC_mem (hgetN i (lt_trans hij hj)) (hgetN j hj)
            rw [charForm2_lead0' p rest e₀ erest _ (hcoord0 _ hwmem)] at hb
            exact hb
          -- the induction hypothesis, as additivity of `charForm2 rest erest` on `N`
          have hadd : ∀ u v : Coordinate 2, u ∈ N → v ∈ N →
              charForm2 rest erest ((u * v : Coordinate 2))
                = charForm2 rest erest u + charForm2 rest erest v :=
            ih hwfrest erest hPow_rest hComm_rest
          -- commutator condition specialised to conjugation invariance
          have hcomm0 : ∀ g ∈ rest, charForm2 rest erest (commutatorC p g) = 0 := by
            intro g hg
            obtain ⟨idx, hidx, hgv⟩ := List.mem_iff_getElem.mp hg
            have hb := hComm 0 (idx + 1) (by omega) (by simp only [List.length_cons]; omega)
            rw [List.getD_cons_zero, List.getD_cons_succ, List.getD_eq_getElem rest zc hidx,
              hgv] at hb
            have hgN : (g : Coordinate 2) ∈ N := Subgroup.subset_closure hg
            have hwmem : (commutatorC p g : Coordinate 2) ∈ N := by
              have h : (commutatorC p g : Coordinate 2) = (p * g * p⁻¹ : Coordinate 2) * g⁻¹ := by
                rw [commutatorC_eq, commutatorElement_def]
              rw [h]
              exact N.mul_mem (hconj g hgN) (N.inv_mem hgN)
            rw [charForm2_lead0' p rest e₀ erest _ (hcoord0 _ hwmem)] at hb
            exact hb
          -- the induction hypothesis packaged as conjugation invariance
          have hconjval : ∀ (k : ℕ) (w : Coordinate 2), w ∈ N →
              charForm2 rest erest ((p ^ k * w * (p ^ k)⁻¹ : Coordinate 2))
                = charForm2 rest erest w :=
            charForm2_conj_pow p rest erest hnorm hadd hcomm0
          -- lead-term power condition at index 0
          have hpow0 : charForm2 rest erest (mpow 2 p 5) = 5 * e₀ := by
            have hb := hPow 0 (by simp only [List.length_cons]; omega)
            rw [List.getD_cons_zero, List.getD_cons_zero] at hb
            have hwmem : (mpow 2 p 5 : Coordinate 2) ∈ N := by
              rw [mpow_eq_pow hq2]; exact hpow
            rw [charForm2_lead0' p rest e₀ erest _ (hcoord0 _ hwmem)] at hb
            exact hb
          -- abbreviations for the lead coordinates
          set a := coordAt x (pivotDepth p) with ha_def
          set b := coordAt y (pivotDepth p) with hb_def
          -- `x'`, `y'` as genuine `Coordinate 2` values landing in `N`
          set x' : Coordinate 2 := clearStep 2 p x with hx'_def
          set y' : Coordinate 2 := clearStep 2 p y with hy'_def
          have hx'N : x' ∈ N := by
            rw [hx'_def]; exact (mem_head_iff hq2 p rest hp5 hlead hrest hpow hnorm x).mp hx
          have hy'N : y' ∈ N := by
            rw [hy'_def]; exact (mem_head_iff hq2 p rest hp5 hlead hrest hpow hnorm y).mp hy
          -- `H ≤ depthGE (pivotDepth p)`, giving lead-coordinate additivity for the product
          have hHle : ofList 2 hq2 (p :: rest) ≤ depthGE 2 hq2 (pivotDepth p) := by
            refine (Subgroup.closure_le _).mpr ?_
            intro g hg
            simp only [Set.mem_setOf_eq, List.mem_cons] at hg
            rcases hg with rfl | hg
            · exact self_mem_depthGE_pivotDepth hq2 g
            · exact (mem_depthGE hq2 _ g).mpr
                (fun i hi => coordAt_of_lt_pivotDepth g i (lt_trans hi (hrest g hg)))
          have hy_d0 : ∀ i, i < pivotDepth p → coordAt y i = 0 :=
            (mem_depthGE hq2 _ y).mp (hHle hy)
          have hcadd : coordAt ((x * y : Coordinate 2)) (pivotDepth p) = a + b := by
            have := coordAt_mul_right 2 (pivotDepth p) hp5 x y hy_d0
            rw [← ha_def, ← hb_def] at this; exact this
          -- clearStep expansions (as `· * pⁿ`)
          have hxe : x' = x * p ^ (-(a.val : ℤ)) := by
            rw [hx'_def]; have := clearStep_eq hq2 p x; rw [← ha_def] at this; exact this
          have hye : y' = y * p ^ (-(b.val : ℤ)) := by
            rw [hy'_def]; have := clearStep_eq hq2 p y; rw [← hb_def] at this; exact this
          have hxye : (clearStep 2 p ((x * y : Coordinate 2)) : Coordinate 2)
              = ((x * y : Coordinate 2)) * p ^ (-((a + b).val : ℤ)) := by
            have := clearStep_eq hq2 p ((x * y : Coordinate 2)); rw [hcadd] at this; exact this
          -- the collection decomposition of `clearStep(x·y)`
          have hCS : (clearStep 2 p ((x * y : Coordinate 2)) : Coordinate 2)
              = x' * (p ^ (a.val) * y' * (p ^ (a.val))⁻¹)
                * p ^ ((a.val : ℤ) + (b.val : ℤ) - ((a + b).val : ℤ)) := by
            rw [hxye, hxe, hye, ← zpow_natCast p a.val]
            group
          -- the power factor lies in `N` (its exponent is divisible by `5`)
          have hpow_mem :
              (p ^ ((a.val : ℤ) + (b.val : ℤ) - ((a + b).val : ℤ)) : Coordinate 2) ∈ N := by
            apply hpow_dvd
            have hcv : ((a + b).val : ℤ) = (((a.val + b.val) % 5 : ℕ) : ℤ) := by
              rw [Fin.val_add]
            rw [hcv]
            refine ⟨((a.val + b.val) / 5 : ℕ), ?_⟩
            have key := Nat.div_add_mod (a.val + b.val) 5
            push_cast
            omega
          have hconjmem : (p ^ (a.val) * y' * (p ^ (a.val))⁻¹ : Coordinate 2) ∈ N :=
            hconjNat a.val y' hy'N
          -- `charForm2` of `clearStep(x·y)`, additivity applied three times
          have hCF : charForm2 rest erest (clearStep 2 p ((x * y : Coordinate 2)))
              = charForm2 rest erest x' + charForm2 rest erest y'
                + charForm2 rest erest
                    ((p ^ ((a.val : ℤ) + (b.val : ℤ) - ((a + b).val : ℤ)) : Coordinate 2)) := by
            rw [hCS, hadd _ _ (Subgroup.mul_mem _ hx'N hconjmem) hpow_mem,
              hadd _ _ hx'N hconjmem, hconjval a.val y' hy'N]
          -- expand both sides and reduce to the pivot/power arithmetic
          rw [charForm2_cons' p rest e₀ erest ((x * y : Coordinate 2)),
            charForm2_cons' p rest e₀ erest x, charForm2_cons' p rest e₀ erest y,
            hcadd, hCF, ← ha_def, ← hb_def, ← hx'_def, ← hy'_def]
          -- pivot/power correction identity, by cases on the carry
          have hfin : e₀ * ((a + b).val : ZMod 25)
              + charForm2 rest erest
                  ((p ^ ((a.val : ℤ) + (b.val : ℤ) - ((a + b).val : ℤ)) : Coordinate 2))
              = e₀ * (a.val : ZMod 25) + e₀ * (b.val : ZMod 25) := by
            rcases Nat.lt_or_ge (a.val + b.val) 5 with hlt | hge
            · -- no carry: exponent `0`
              have hcval : ((a + b).val : ℕ) = a.val + b.val := by
                rw [Fin.val_add, Nat.mod_eq_of_lt hlt]
              have hexp : (a.val : ℤ) + (b.val : ℤ) - ((a + b).val : ℤ) = 0 := by
                rw [hcval]; push_cast; ring
              rw [hexp, zpow_zero, charForm2_one' rest erest, hcval]
              push_cast; ring
            · -- carry: exponent `5`
              have hcval : ((a + b).val : ℕ) = a.val + b.val - 5 := by
                have h1 := a.isLt; have h2 := b.isLt
                rw [Fin.val_add]; omega
              have hexp : (a.val : ℤ) + (b.val : ℤ) - ((a + b).val : ℤ) = 5 := by
                have h1 := a.isLt; have h2 := b.isLt
                rw [hcval]; omega
              rw [hexp, show (5 : ℤ) = ((5 : ℕ) : ℤ) from rfl, zpow_natCast,
                ← mpow_eq_pow hq2, hpow0, hcval]
              have hcast : ((a.val + b.val - 5 : ℕ) : ZMod 25)
                  = (a.val : ZMod 25) + (b.val : ZMod 25) - 5 := by
                have h5 : 5 ≤ a.val + b.val := hge
                push_cast [Nat.cast_sub h5]; ring
              rw [hcast]; ring
          linear_combination hfin

/-! ## Step 1 headline: `CharExtendsAt2` for every well-formed basis -/

/-- **Step 1 (`CharExtendsAt2`), generic form.** For any well-formed echelon basis
`B`, every `charOK2`-valid vector `e` yields an additive character functional on
`⟨B⟩`. This discharges the sole isolated obligation of the character certification. -/
theorem charExtendsAt2_of_wf (B : List (Coordinate 2)) (hwf : WF 2 hq2 B)
    (e : List (ZMod 25)) : CharExtendsAt2 B e := by
  intro hOK x y hx hy
  have hxm : (x : Coordinate 2) ∈ ofList 2 hq2 B := (sift_mem_iff hq2 B hwf x).mp hx
  have hym : (y : Coordinate 2) ∈ ofList 2 hq2 B := (sift_mem_iff hq2 B hwf y).mp hy
  exact charForm2_additive_core B hwf e (charOK2_pow B e hOK) (charOK2_comm B e hOK) x y hxm hym

/-- **`CharExtendsAt2` for every one of the 148 class representatives.** -/
theorem charExtendsAt2_basisAt (r : Fin 148) (e : List (ZMod 25)) :
    CharExtendsAt2 (basisAt2 r) e := by
  rw [basisAt2_eq]
  have hbnd : (List.range 148).all (fun i => Nat.blt (classRepsData.getD i 0) 676) = true := by
    decide
  have hlt : classRepsData.getD r.val 0 < 676 := by
    have := (List.all_eq_true.mp hbnd) r.val (List.mem_range.mpr r.isLt)
    simpa [Nat.blt_eq] using this
  exact charExtendsAt2_of_wf (getB (classRepsData.getD r.val 0)) (wf_getB hlt) e

/-! # Step 2 — character realization: certified vectors ↔ genuine characters

Each `charOK2`-valid exponent vector `e` of `reps r` is turned into a *genuine*
homomorphism `charOfVec2 r e : ↥(reps r) →* ℂˣ`, `x ↦ ζ₂₅^{charForm2 B e x}`
(multiplicativity is exactly Step 1's `charExtendsAt2_basisAt`). Evaluating at the
`i`-th echelon generator recovers `eᵢ` (`charForm2_getElem`), so distinct certified
vectors give distinct characters (`charOfVec2_inj`); with `charsAt2_nodup`,
`charsAt2_count` and the certified per-vector length `charsAt_vecLen` this yields a
nodup family of `charCounts r` characters, hence the semantic lower bound

  `charCounts r ≤ |Hom(reps r, ℂˣ)| = |(reps r)ᵃᵇ|`  (`charCounts2_le_card_hom`).

The **converse** — that the certified list is *exhaustive* (every character is a
listed vector, equivalently `|Hom| ≤ charCounts r`) — is isolated as the single
named obligation `CharsAtComplete`; from it `charsAt_complete` and the semantic
upgrade `card_abelianization_reps` follow (Step 3 territory). -/

/-! ## `ζ₂₅` and its exponent map — reused verbatim from the q=1 twin
(`zeta25`, `zexp` and their lemmas are group-independent; imported from
`LeanDring/P5/Certificate/Characters/Twin1/CharExtend.lean`). -/

/-! ## Well-formedness and sift plumbing for `basisAt2 r` -/

/-- The echelon basis of `reps r` is well formed. -/
theorem wf_basisAt2 (r : Fin 148) : WF 2 hq2 (basisAt2 r) := by
  rw [basisAt2_eq]
  refine wf_getB ?_
  have hbnd : (List.range 148).all (fun i => Nat.blt (classRepsData.getD i 0) 676) = true := by
    decide
  have := (List.all_eq_true.mp hbnd) r.val (List.mem_range.mpr r.isLt)
  simpa [Nat.blt_eq] using this

/-- Every member of `reps r` sifts to the identity against its echelon basis. -/
theorem siftB_of_mem (r : Fin 148) (x : ↥(reps r)) :
    siftB 2 (basisAt2 r) (x : Coordinate 2) = true := by
  apply (sift_mem_iff hq2 (basisAt2 r) (wf_basisAt2 r) (x : Coordinate 2)).mpr
  rw [← reps_eq_ofList2 r]
  exact x.2

/-- Per-element `charOK2`-validity, extracted from `charsAt2_valid`. -/
theorem validAt (r : Fin 148) {e : List (ZMod 25)} (he : e ∈ charsAt2 r) :
    charOK2 (basisAt2 r) e = true :=
  (List.all_eq_true.mp (charsAt2_valid r)) e he

/-- The whole-range vector-length check (glued from the four chunk `decide`s of
`LeanDring/P5/Certificate/Characters/Twin2/CharVecLen.lean`). -/
theorem checkVecLen2_all : (List.range 148).all checkVecLen2 = true :=
  all148_of_chunks checkVecLen2 vecLenChunk2_0 vecLenChunk2_1 vecLenChunk2_2 vecLenChunk2_3

/-- **Per-vector length.** Every certified exponent vector of `reps r` has length
equal to the number of echelon generators of `reps r`. -/
theorem charsAt_vecLen (r : Fin 148) : ∀ e ∈ charsAt2 r, e.length = (basisAt2 r).length := by
  have h := (List.all_eq_true.mp checkVecLen2_all) r.val (List.mem_range.mpr r.isLt)
  simp only [checkVecLen2] at h
  rw [List.all_eq_true] at h
  intro e he
  exact Nat.eq_of_beq_eq_true (h e he)

/-! ## `charForm2` evaluated at the echelon generators is the standard basis -/

/-- **Evaluation at generators.** For a well-formed echelon basis `B`, the
candidate exponent `charForm2 B e` at the `i`-th generator is exactly `eᵢ`: the
`i`-th generator's pcgs expansion is the `i`-th standard basis vector. -/
private theorem charForm2_getElem :
    ∀ (B : List (Coordinate 2)), WF 2 hq2 B → ∀ (e : List (ZMod 25)) (i : ℕ),
      i < B.length → charForm2 B e (B.getD i zc) = e.getD i 0 := by
  intro B
  induction B with
  | nil => intro _ e i hi; simp only [List.length_nil] at hi; omega
  | cons p rest ih =>
      intro hwf e i hi
      obtain ⟨hp5, hlead, hrest, hpow, hnorm, hwfrest⟩ := hwf
      cases e with
      | nil => rw [charForm2_nil_e', List.getD_nil]
      | cons e₀ erest =>
          cases i with
          | zero =>
              rw [List.getD_cons_zero, List.getD_cons_zero]
              have hcs := clearStep_eq hq2 p p
              rw [hlead] at hcs
              have h0 : clearStep 2 p p = ((0, 0, 0, 0, 0) : Coordinates) := by
                rw [hcs, Fin.val_one, Nat.cast_one, zpow_neg, zpow_one]
                exact mul_inv_cancel p
              have hcz : charForm2 rest erest (clearStep 2 p p) = 0 := by
                rw [h0]; exact charForm2_one rest erest
              rw [charForm2_cons' p rest e₀ erest p, hlead, hcz]
              simp
          | succ j =>
              have hjr : j < rest.length := by
                simp only [List.length_cons] at hi; omega
              have hmem : (rest.getD j zc : Coordinate 2) ∈ rest := by
                rw [List.getD_eq_getElem rest zc hjr]; exact List.getElem_mem hjr
              have hpd : pivotDepth p < pivotDepth (rest.getD j zc) := hrest _ hmem
              have hc0 : coordAt (rest.getD j zc) (pivotDepth p) = 0 :=
                coordAt_of_lt_pivotDepth _ _ hpd
              rw [List.getD_cons_succ, charForm2_lead0' p rest e₀ erest _ hc0,
                List.getD_cons_succ]
              exact ih hwfrest erest j hjr

/-! ## The forward map: a certified vector becomes a genuine character -/

/-- **The character realized by a `charOK2`-valid exponent vector**: the
homomorphism `x ↦ ζ₂₅^{charForm2 B e x}` on `H = reps r`. Multiplicativity is
Step 1's additivity of `charForm2` (`charExtendsAt2_basisAt`). -/
noncomputable def charOfVec2 (r : Fin 148) (e : List (ZMod 25))
    (he : charOK2 (basisAt2 r) e = true) : ↥(reps r) →* ℂˣ where
  toFun x := zexp (charForm2 (basisAt2 r) e (x : Coordinate 2))
  map_one' := by
    change zexp (charForm2 (basisAt2 r) e ((1 : ↥(reps r)) : Coordinate 2)) = 1
    rw [Subgroup.coe_one, charForm2_one' (basisAt2 r) e]
    exact zexp_zero
  map_mul' x y := by
    change zexp (charForm2 (basisAt2 r) e (((x * y : ↥(reps r)) : Coordinate 2)))
       = zexp (charForm2 (basisAt2 r) e (x : Coordinate 2))
         * zexp (charForm2 (basisAt2 r) e (y : Coordinate 2))
    rw [← zexp_add]
    congr 1
    rw [Subgroup.coe_mul]
    exact charExtendsAt2_basisAt r e he (x : Coordinate 2) (y : Coordinate 2)
      (siftB_of_mem r x) (siftB_of_mem r y)

theorem charOfVec2_apply (r : Fin 148) (e : List (ZMod 25)) (he : charOK2 (basisAt2 r) e = true)
    (x : ↥(reps r)) :
    charOfVec2 r e he x = zexp (charForm2 (basisAt2 r) e (x : Coordinate 2)) := rfl

/-- **Value at a generator.** The realized character sends the `i`-th echelon
generator of `reps r` to `ζ₂₅^{eᵢ}`. -/
theorem charOfVec2_gen (r : Fin 148) (e : List (ZMod 25)) (he : charOK2 (basisAt2 r) e = true)
    (i : ℕ) (hi : i < (basisAt2 r).length)
    (hmem : ((basisAt2 r).getD i zc : Coordinate 2) ∈ reps r) :
    charOfVec2 r e he ⟨(basisAt2 r).getD i zc, hmem⟩ = zexp (e.getD i 0) := by
  rw [charOfVec2_apply]
  change zexp (charForm2 (basisAt2 r) e ((basisAt2 r).getD i zc)) = zexp (e.getD i 0)
  congr 1
  exact charForm2_getElem (basisAt2 r) (wf_basisAt2 r) e i hi

/-- **Injectivity on the certified list.** Distinct listed exponent vectors of
`reps r` realize distinct characters. -/
theorem charOfVec2_inj (r : Fin 148) {e e' : List (ZMod 25)}
    (he : e ∈ charsAt2 r) (he' : e' ∈ charsAt2 r)
    (heq : charOfVec2 r e (validAt r he) = charOfVec2 r e' (validAt r he')) : e = e' := by
  have hlen : e.length = (basisAt2 r).length := charsAt_vecLen r e he
  have hlen' : e'.length = (basisAt2 r).length := charsAt_vecLen r e' he'
  apply List.ext_getElem (by rw [hlen, hlen'])
  intro i h1 _
  have hik : i < (basisAt2 r).length := hlen ▸ h1
  have hmem : ((basisAt2 r).getD i zc : Coordinate 2) ∈ reps r := by
    rw [reps_eq_ofList2 r, List.getD_eq_getElem (basisAt2 r) zc hik]
    exact Subgroup.subset_closure (List.getElem_mem hik)
  have hcongr := DFunLike.congr_fun heq (⟨(basisAt2 r).getD i zc, hmem⟩ : ↥(reps r))
  rw [charOfVec2_gen r e _ i hik hmem, charOfVec2_gen r e' _ i hik hmem] at hcongr
  have hval := zexp_inj hcongr
  rwa [List.getD_eq_getElem e 0 (hlen ▸ hik), List.getD_eq_getElem e' 0 (hlen' ▸ hik)] at hval

/-! ## The semantic count bound `charCounts r ≤ |Hom(reps r, ℂˣ)|` -/

/-- **Step 2 lower bound.** The certified character count of `reps r` is at most
the number of genuine linear characters `Hom(reps r, ℂˣ) = |(reps r)ᵃᵇ|`. The
`charCounts r` listed vectors realize that many *distinct* characters. -/
theorem charCounts2_le_card_hom (r : Fin 148) :
    charCounts.getD r.val 0 ≤ Nat.card (↥(reps r) →* ℂˣ) := by
  classical
  haveI : Fintype ↥(reps r) := Fintype.ofFinite _
  haveI : Finite ↥(reps r) := Finite.of_fintype _
  haveI : Finite (Abelianization ↥(reps r)) := Quotient.finite _
  have hcard : Nat.card (↥(reps r) →* ℂˣ) = Nat.card (Abelianization ↥(reps r)) :=
    LeanDring.DRing.card_charHom_eq_card_abelianization
  haveI hfin : Finite (↥(reps r) →* ℂˣ) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  haveI : Fintype (↥(reps r) →* ℂˣ) := Fintype.ofFinite _
  have hLnodup : ((charsAt2 r).attach.map
      (fun p => charOfVec2 r p.1 (validAt r p.2))).Nodup := by
    apply List.Nodup.map_on ?_ (List.nodup_attach.mpr (charsAt2_nodup r))
    rintro ⟨a, ha⟩ _ ⟨b, hb⟩ _ hab
    exact Subtype.ext (charOfVec2_inj r ha hb hab)
  calc charCounts.getD r.val 0
      = ((charsAt2 r).attach.map (fun p => charOfVec2 r p.1 (validAt r p.2))).length := by
        rw [List.length_map, List.length_attach, charsAt2_count r]
    _ ≤ Fintype.card (↥(reps r) →* ℂˣ) := hLnodup.length_le_card
    _ = Nat.card (↥(reps r) →* ℂˣ) := (Nat.card_eq_fintype_card).symm

/-! ## The isolated converse obligation and the conditional headline -/

/-- **The isolated Step-2 converse obligation** (the completeness/exhaustiveness
of the certified enumeration): the number of genuine linear characters of
`reps r` does not exceed the certified count — equivalently every character is
realized by one of the listed exponent vectors. Combined with the unconditional
`charCounts2_le_card_hom`, this pins the count. It is the sole remaining step to
the full Step-2 bijection. -/
def CharsAtComplete (r : Fin 148) : Prop :=
  Nat.card (↥(reps r) →* ℂˣ) ≤ charCounts.getD r.val 0

/-- **Step 2 headline (conditional on completeness).** The number of linear
characters of `reps r` equals its certified count `charCounts r`. -/
theorem charsAt_complete (r : Fin 148) (hc : CharsAtComplete r) :
    Nat.card (↥(reps r) →* ℂˣ) = charCounts.getD r.val 0 :=
  le_antisymm hc (charCounts2_le_card_hom r)

/-- **Semantic upgrade of the character-data aggregate** (conditional on completeness): the
generator-emitted count `charCounts r` is the genuine abelianization order of
`reps r`. -/
theorem card_abelianization_reps (r : Fin 148) (hc : CharsAtComplete r) :
    Nat.card (Abelianization ↥(reps r)) = charCounts.getD r.val 0 := by
  haveI : Fintype ↥(reps r) := Fintype.ofFinite _
  rw [← LeanDring.DRing.card_charHom_eq_card_abelianization]
  exact charsAt_complete r hc

/-! # Step 3 — completeness of the certified enumeration (`CharsAtComplete`)

The converse direction. Every character `χ : ↥(reps r) →* ℂˣ` is *recovered* from
a `charOK2`-valid exponent vector `evalVec … χ`, via the discrete logarithm at the
echelon generators. Three ingredients:

* **(i) exponent 25** — the ambient group `Coordinate 2` has exponent dividing
  `25` (`pow25_eq_one`, a single kernel `decide` over the `mpow` power map), so
  every character value `χ(g)` is a `25`-th root of unity;
* **(ii) discrete log** — the `25`-th roots of unity in `ℂˣ` are exactly the image
  of `zexp : ZMod 25 → ℂˣ`, which is injective; `dlog` inverts it;
* **(iii) reconstruction** — the master evaluation `master_eval` computes `χ` on
  *every* element of `reps r` from its values at the generators, by the same
  echelon recursion as `charForm2`. Consequently `χ ↦ evalVec … χ` is injective,
  its image is `charOK2`-valid, and (given the certified list is *exhaustive*)
  lands in `charsAt2 r` — pinning `|Hom(reps r, ℂˣ)| ≤ charCounts r`. -/

/-! ## (i) The ambient group has exponent dividing `25` -/

/-- **Exponent 25.** Every element of `Coordinate 2` is killed by `25`, bridged
from `mpow25_all` (the chunked `mpow` decide in
`LeanDring/P5/Certificate/Characters/Twin2/CharExp.lean`) to the group power by
`mpow_eq_pow`. -/
theorem pow25_eq_one (x : Coordinate 2) : x ^ (25 : ℕ) = 1 := by
  have hb := mpow_eq_pow hq2 x 25
  rw [mpow25_all x] at hb
  exact hb.symm

/-! ## (ii) The discrete logarithm on the `25`-th roots of unity -/

-- (`exists_dlog`, `dlog`, `zexp_dlog`, `zexp_pow` are group-independent and
-- reused from the q=1 `LeanDring/P5/Certificate/Characters/Twin1/CharExtend.lean`.)

/-! ## Every character value is a `25`-th root of unity -/

/-- Any character of any subgroup sends each element to a `25`-th root of unity
(the ambient exponent is `25`). -/
theorem charVal_pow25 {H : Subgroup (Coordinate 2)} (χ : ↥H →* ℂˣ) (h : ↥H) :
    (χ h) ^ (25 : ℕ) = 1 := by
  rw [← map_pow]
  have hh : h ^ (25 : ℕ) = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, Subgroup.coe_one]
    exact pow25_eq_one (h : Coordinate 2)
  rw [hh, map_one]

/-! ## (iii) The reconstruction vector and the master evaluation -/

/-- Tail inclusion of subgroups presented by a basis: `⟨rest⟩ ≤ ⟨p :: rest⟩`. -/
def inclOfList (p : Coordinate 2) (rest : List (Coordinate 2)) :
    ↥(ofList 2 hq2 rest) →* ↥(ofList 2 hq2 (p :: rest)) :=
  Subgroup.inclusion (by
    apply Subgroup.closure_mono
    intro x hx
    exact List.mem_cons_of_mem p hx)

/-- **The reconstruction vector** of a character `χ` on `⟨B⟩`: its discrete
logarithm at each echelon generator, in basis order. -/
noncomputable def evalVec : (B : List (Coordinate 2)) → (↥(ofList 2 hq2 B) →* ℂˣ) →
    List (ZMod 25)
  | [], _ => []
  | p :: rest, χ =>
      dlog (χ ⟨p, Subgroup.subset_closure (List.mem_cons_self ..)⟩) ::
        evalVec rest (χ.comp (inclOfList p rest))

theorem evalVec_length : ∀ (B : List (Coordinate 2)) (χ : ↥(ofList 2 hq2 B) →* ℂˣ),
    (evalVec B χ).length = B.length := by
  intro B
  induction B with
  | nil => intro _; rfl
  | cons p rest ih =>
      intro χ
      change (evalVec rest (χ.comp (inclOfList p rest))).length + 1 = rest.length + 1
      rw [ih]

/-- **Master evaluation.** A character `χ` on `⟨B⟩` (a well-formed echelon basis)
equals `zexp` of the `charForm2` functional of its reconstruction vector, on
*every* element of `⟨B⟩` — the same echelon recursion that defines `charForm2`. -/
theorem master_eval : ∀ (B : List (Coordinate 2)), WF 2 hq2 B →
    ∀ (χ : ↥(ofList 2 hq2 B) →* ℂˣ) (x : Coordinate 2) (hx : x ∈ ofList 2 hq2 B),
      χ ⟨x, hx⟩ = zexp (charForm2 B (evalVec B χ) x) := by
  intro B
  induction B with
  | nil =>
      intro _ χ x hx
      have hbot : ofList 2 hq2 ([] : List (Coordinate 2)) = ⊥ := by
        have hset : {y : Coordinate 2 | y ∈ ([] : List (Coordinate 2))}
            = (∅ : Set (Coordinate 2)) := by ext y; simp
        rw [ofList, hset, Subgroup.closure_empty]
      have hx1 : x = 1 := by
        have h := hx; rw [hbot, Subgroup.mem_bot] at h; exact h
      have hsub : (⟨x, hx⟩ : ↥(ofList 2 hq2 ([] : List (Coordinate 2)))) = 1 :=
        Subtype.ext (by rw [Subgroup.coe_one]; exact hx1)
      rw [hsub, map_one, charForm2_nil_B', zexp_zero]
  | cons p rest ih =>
      intro hwf χ x hx
      obtain ⟨hp5, hlead, hrest, hpow, hnorm, hwfrest⟩ := hwf
      set a := (coordAt x (pivotDepth p)).val with ha_def
      set x' : Coordinate 2 := clearStep 2 p x with hx'_def
      have hx'N : x' ∈ ofList 2 hq2 rest := by
        rw [hx'_def]
        exact (mem_head_iff hq2 p rest hp5 hlead hrest hpow hnorm x).mp hx
      have hpH : p ∈ ofList 2 hq2 (p :: rest) :=
        Subgroup.subset_closure (List.mem_cons_self ..)
      have hle : ofList 2 hq2 rest ≤ ofList 2 hq2 (p :: rest) := by
        apply Subgroup.closure_mono; intro y hy; exact List.mem_cons_of_mem p hy
      have hx'H : x' ∈ ofList 2 hq2 (p :: rest) := hle hx'N
      have hxe : x = x' * p ^ a := by
        have hcs : x' = x * p ^ (-(a : ℤ)) := clearStep_eq hq2 p x
        have h2 : x' * p ^ (a : ℤ) = x := by rw [hcs]; group
        rw [← h2, zpow_natCast]
      have hcoe : (⟨x, hx⟩ : ↥(ofList 2 hq2 (p :: rest)))
          = ⟨x', hx'H⟩ * ⟨p, hpH⟩ ^ a :=
        Subtype.ext (by rw [Subgroup.coe_mul, SubmonoidClass.coe_pow]; exact hxe)
      have hIH : χ ⟨x', hx'H⟩
          = zexp (charForm2 rest (evalVec rest (χ.comp (inclOfList p rest))) x') := by
        have hkey := ih hwfrest (χ.comp (inclOfList p rest)) x' hx'N
        rw [MonoidHom.comp_apply] at hkey
        exact hkey
      have hpv : zexp (dlog (χ ⟨p, hpH⟩)) = χ ⟨p, hpH⟩ :=
        zexp_dlog (charVal_pow25 χ ⟨p, hpH⟩)
      rw [hcoe, map_mul, map_pow, hIH, ← hpv, zexp_pow, ← zexp_add]
      congr 1
      change charForm2 rest (evalVec rest (χ.comp (inclOfList p rest))) x'
            + dlog (χ ⟨p, hpH⟩) * (a : ZMod 25)
          = charForm2 (p :: rest)
              (dlog (χ ⟨p, hpH⟩) :: evalVec rest (χ.comp (inclOfList p rest))) x
      rw [charForm2_cons p rest (dlog (χ ⟨p, hpH⟩))
            (evalVec rest (χ.comp (inclOfList p rest))) x, ← hx'_def, ← ha_def]
      ring

/-! ## The reconstruction vector is `charOK2`-valid -/

/-- Additivity of the reconstruction functional on `⟨B⟩` (from `master_eval` and
injectivity of `zexp`). -/
theorem charForm2_add_evalVec (B : List (Coordinate 2)) (hwf : WF 2 hq2 B)
    (χ : ↥(ofList 2 hq2 B) →* ℂˣ) (x y : Coordinate 2)
    (hx : x ∈ ofList 2 hq2 B) (hy : y ∈ ofList 2 hq2 B) :
    charForm2 B (evalVec B χ) (x * y)
      = charForm2 B (evalVec B χ) x + charForm2 B (evalVec B χ) y := by
  have hxy : (x * y : Coordinate 2) ∈ ofList 2 hq2 B := mul_mem hx hy
  apply zexp_inj
  rw [zexp_add, ← master_eval B hwf χ x hx, ← master_eval B hwf χ y hy,
    ← master_eval B hwf χ (x * y) hxy, ← map_mul]
  congr 1

/-- The reconstruction functional negates on inverses. -/
theorem charForm2_inv_evalVec (B : List (Coordinate 2)) (hwf : WF 2 hq2 B)
    (χ : ↥(ofList 2 hq2 B) →* ℂˣ) (g : Coordinate 2) (hg : g ∈ ofList 2 hq2 B) :
    charForm2 B (evalVec B χ) ((g⁻¹ : Coordinate 2)) = - charForm2 B (evalVec B χ) g := by
  have h := charForm2_add_evalVec B hwf χ g g⁻¹ hg (inv_mem hg)
  rw [mul_inv_cancel, charForm2_one'] at h
  linear_combination -h

/-- The reconstruction functional scales on powers. -/
theorem charForm2_pow_evalVec (B : List (Coordinate 2)) (hwf : WF 2 hq2 B)
    (χ : ↥(ofList 2 hq2 B) →* ℂˣ) (g : Coordinate 2) (hg : g ∈ ofList 2 hq2 B) :
    ∀ n : ℕ, charForm2 B (evalVec B χ) ((g ^ n : Coordinate 2))
      = (n : ZMod 25) * charForm2 B (evalVec B χ) g := by
  intro n
  induction n with
  | zero => rw [pow_zero, charForm2_one', Nat.cast_zero, zero_mul]
  | succ n ih =>
      rw [pow_succ, charForm2_add_evalVec B hwf χ (g ^ n) g (pow_mem hg n) hg, ih]
      push_cast; ring

/-- Repackaging: the semantic power/commutator conditions imply the Boolean
`charOK2` checker (the converse of `charOK2_pow`/`charOK2_comm`). -/
theorem charOK2_of_conditions (B : List (Coordinate 2)) (e : List (ZMod 25))
    (hp : ∀ i < B.length, charForm2 B e (mpow 2 (B.getD i zc) 5) = 5 * e.getD i 0)
    (hc : ∀ i j, i < j → j < B.length →
        charForm2 B e (commutatorC (B.getD i zc) (B.getD j zc)) = 0) :
    charOK2 B e = true := by
  rw [charOK2, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    rw [decide_eq_true_eq]
    exact hp i hi
  · rw [List.all_eq_true]
    intro i hi
    rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hi hj
    by_cases hij : Nat.blt i j = true
    · simp only [hij, Bool.not_true, Bool.false_or, decide_eq_true_eq]
      have hij' : i < j := by simpa [Nat.blt_eq] using hij
      exact hc i j hij' hj
    · simp only [Bool.not_eq_true] at hij; rw [hij]; rfl

/-- **The reconstruction vector is `charOK2`-valid.** -/
theorem charOK2_evalVec (B : List (Coordinate 2)) (hwf : WF 2 hq2 B)
    (χ : ↥(ofList 2 hq2 B) →* ℂˣ) : charOK2 B (evalVec B χ) = true := by
  apply charOK2_of_conditions
  · intro i hi
    have hgmem : (B.getD i zc : Coordinate 2) ∈ ofList 2 hq2 B := by
      rw [List.getD_eq_getElem B zc hi]; exact Subgroup.subset_closure (List.getElem_mem hi)
    calc charForm2 B (evalVec B χ) (mpow 2 (B.getD i zc) 5)
        = charForm2 B (evalVec B χ) ((B.getD i zc : Coordinate 2) ^ 5) := rfl
      _ = ((5 : ℕ) : ZMod 25) * charForm2 B (evalVec B χ) (B.getD i zc) :=
          charForm2_pow_evalVec B hwf χ (B.getD i zc) hgmem 5
      _ = ((5 : ℕ) : ZMod 25) * (evalVec B χ).getD i 0 := by
          congr 1; exact charForm2_getElem B hwf (evalVec B χ) i hi
      _ = 5 * (evalVec B χ).getD i 0 := by norm_num
  · intro i j hij hj
    have hi := lt_trans hij hj
    have hgi : (B.getD i zc : Coordinate 2) ∈ ofList 2 hq2 B := by
      rw [List.getD_eq_getElem B zc hi]; exact Subgroup.subset_closure (List.getElem_mem hi)
    have hgj : (B.getD j zc : Coordinate 2) ∈ ofList 2 hq2 B := by
      rw [List.getD_eq_getElem B zc hj]; exact Subgroup.subset_closure (List.getElem_mem hj)
    change charForm2 B (evalVec B χ)
        (B.getD i zc * B.getD j zc * (B.getD i zc)⁻¹ * (B.getD j zc)⁻¹ : Coordinate 2) = 0
    rw [charForm2_add_evalVec B hwf χ _ _ (mul_mem (mul_mem hgi hgj) (inv_mem hgi)) (inv_mem hgj),
      charForm2_add_evalVec B hwf χ _ _ (mul_mem hgi hgj) (inv_mem hgi),
      charForm2_add_evalVec B hwf χ _ _ hgi hgj,
      charForm2_inv_evalVec B hwf χ _ hgi, charForm2_inv_evalVec B hwf χ _ hgj]
    ring

/-! ## The injection and the count bound -/

/-- The reconstruction map `χ ↦ evalVec B χ` is injective (from `master_eval`). -/
theorem evalVec_injective (B : List (Coordinate 2)) (hwf : WF 2 hq2 B) :
    Function.Injective
      (evalVec B : (↥(ofList 2 hq2 B) →* ℂˣ) → List (ZMod 25)) := by
  intro χ χ' heq
  refine MonoidHom.ext fun y => ?_
  obtain ⟨x, hx⟩ := y
  rw [master_eval B hwf χ x hx, master_eval B hwf χ' x hx, heq]

/-- **Count bound.** If every reconstruction vector of `⟨B⟩` is listed in `L`,
then `|Hom(⟨B⟩, ℂˣ)| ≤ L.length`. -/
theorem card_hom_le_length (B : List (Coordinate 2)) (hwf : WF 2 hq2 B)
    (L : List (List (ZMod 25)))
    (hmem : ∀ χ : ↥(ofList 2 hq2 B) →* ℂˣ, evalVec B χ ∈ L) :
    Nat.card (↥(ofList 2 hq2 B) →* ℂˣ) ≤ L.length := by
  classical
  haveI : Fintype ↥(ofList 2 hq2 B) := Fintype.ofFinite _
  haveI : Finite (↥(ofList 2 hq2 B) →* ℂˣ) := by
    apply Nat.finite_of_card_ne_zero
    rw [LeanDring.DRing.card_charHom_eq_card_abelianization]
    haveI : Finite (Abelianization ↥(ofList 2 hq2 B)) := Quotient.finite _
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  haveI : Fintype (↥(ofList 2 hq2 B) →* ℂˣ) := Fintype.ofFinite _
  have hinj : Function.Injective (fun χ : ↥(ofList 2 hq2 B) →* ℂˣ =>
      (⟨evalVec B χ, List.mem_toFinset.mpr (hmem χ)⟩ : ↥L.toFinset)) := by
    intro a b hab
    exact evalVec_injective B hwf (Subtype.ext_iff.mp hab)
  calc Nat.card (↥(ofList 2 hq2 B) →* ℂˣ)
      = Fintype.card (↥(ofList 2 hq2 B) →* ℂˣ) := Nat.card_eq_fintype_card
    _ ≤ Fintype.card ↥L.toFinset := Fintype.card_le_of_injective _ hinj
    _ = L.toFinset.card := Fintype.card_coe _
    _ ≤ L.length := List.toFinset_card_le L

/-- **Step 3 reduction.** If the certified list `charsAt2 r` is *exhaustive* — it
contains every `charOK2`-valid vector of the right length — then the completeness
obligation `CharsAtComplete r` holds. Combined with the unconditional
`charCounts2_le_card_hom`, this pins the character count. -/
theorem charsAtComplete_of_exhaustive (r : Fin 148)
    (hex : ∀ e : List (ZMod 25), charOK2 (basisAt2 r) e = true →
        e.length = (basisAt2 r).length → e ∈ charsAt2 r) :
    CharsAtComplete r := by
  change Nat.card (↥(reps r) →* ℂˣ) ≤ charCounts.getD r.val 0
  rw [← charsAt2_count r,
    show Nat.card (↥(reps r) →* ℂˣ)
        = Nat.card (↥(ofList 2 hq2 (basisAt2 r)) →* ℂˣ) from by rw [reps_eq_ofList2 r]]
  apply card_hom_le_length (basisAt2 r) (wf_basisAt2 r) (charsAt2 r)
  intro χ
  exact hex _ (charOK2_evalVec (basisAt2 r) (wf_basisAt2 r) χ)
    (evalVec_length (basisAt2 r) χ)

end Q2

end LeanDring.P5Presentation
