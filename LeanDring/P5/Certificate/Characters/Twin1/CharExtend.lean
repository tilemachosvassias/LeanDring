/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin1.CharData
import LeanDring.P5.Certificate.Characters.Twin1.CharAssembly
import LeanDring.P5.Certificate.Characters.Twin1.CharExp
import LeanDring.P5.Certificate.SubgroupInventory.Twin1.FratDischarge
import LeanDring.P5.Certificate.Characters.Twin1.CharVecLen
import LeanDring.Theory.DRing.GabCount
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The extension obligation `CharExtendsAt`, and the character count it unlocks

This file discharges the extension obligation stated in
`LeanDring.P5.Certificate.Characters.Twin1.CharData`: a `charOK`-valid
exponent vector `e` defines an *additive* functional `charForm B e` on the
subgroup `H = ⟨B⟩` presented by a well-formed echelon basis `B`, i.e.
`charForm B e (x·y) = charForm B e x + charForm B e y` for `x, y ∈ H`.

The proof is a structural recursion on the echelon basis `B = p :: rest`,
mirroring `card_ofList_cons`: writing `H = ⟨p⟩·N` with `N = ⟨rest⟩`, every
`x ∈ H` factors as `x = x' · pᵃ` with `x' = clearStep 1 p x ∈ N` and
`a = coordAt x (pivotDepth p)`. The lead coordinate is additive
(`coordAt_mul_right`), and the two collection corrections
(a power carry `pⁿ` with `n ∈ {0,5}` and a conjugation tail `pᵃ y' p⁻ᵃ`) are
exactly the terms killed by the `charOK` power/commutator conditions.

On that additivity the file then builds the two halves of the character count:
each certified vector realizes a genuine character (`charOfVec`), giving the
lower bound `charCounts r ≤ |Hom(reps r, ℂˣ)|`; and each genuine character is
recovered from a certified vector by discrete logarithm at the echelon
generators (`evalVec`, `master_eval`), reducing the matching upper bound to the
exhaustiveness of the certified list (`CharsAtComplete`).
-/

namespace LeanDring.P5Presentation

open Fin.NatCast
open scoped Pointwise
open scoped commutatorElement

set_option maxRecDepth 100000

/-! ## Recursion for the exponent extraction `expNat` / `expVec` -/

/-- The single fold step underlying `expNat` (record the pivot exponent, then
strip that pivot). -/
private def eStep (acc : Coordinates × List Nat) (p : Coordinates) : Coordinates × List Nat :=
  (clearStep 1 p acc.1, acc.2 ++ [(coordAt acc.1 (pivotDepth p)).val])

private theorem eStep_apply (x : Coordinates) (acc : List Nat) (p : Coordinates) :
    eStep (x, acc) p = (clearStep 1 p x, acc ++ [(coordAt x (pivotDepth p)).val]) := rfl

private theorem expNat_eq (B : List Coordinates) (x : Coordinates) :
    expNat B x = (B.foldl eStep (x, [])).2 := rfl

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
        ih (clearStep 1 p x) (acc ++ [(coordAt x (pivotDepth p)).val]),
        ih (clearStep 1 p x) ([] ++ [(coordAt x (pivotDepth p)).val])]
      simp [List.append_assoc]

private theorem expNat_cons (p : Coordinates) (rest : List Coordinates) (x : Coordinates) :
    expNat (p :: rest) x
      = (coordAt x (pivotDepth p)).val :: expNat rest (clearStep 1 p x) := by
  rw [expNat_eq, List.foldl_cons, eStep_apply, eStep_foldl_pair]
  simp [expNat_eq]

private theorem expVec_cons (p : Coordinates) (rest : List Coordinates) (x : Coordinates) :
    expVec (p :: rest) x
      = ((coordAt x (pivotDepth p)).val : ZMod 25) :: expVec rest (clearStep 1 p x) := by
  change (expNat (p :: rest) x).map (fun n => (n : ZMod 25))
      = _ :: (expNat rest (clearStep 1 p x)).map (fun n => (n : ZMod 25))
  rw [expNat_cons]
  rfl

/-! ## Recursion for `dotZ` / `charForm` -/

private theorem dotZ_cons (a : ZMod 25) (e : List (ZMod 25)) (b : ZMod 25) (v : List (ZMod 25)) :
    dotZ (a :: e) (b :: v) = a * b + dotZ e v := by
  simp [dotZ]

private theorem dotZ_nil_left (v : List (ZMod 25)) : dotZ [] v = 0 := by
  simp [dotZ]

private theorem charForm_nil_B (e : List (ZMod 25)) (x : Coordinates) :
    charForm [] e x = 0 := by
  simp [charForm, expVec, expNat, dotZ]

private theorem charForm_nil_e (B : List Coordinates) (x : Coordinates) :
    charForm B [] x = 0 := by
  simp [charForm, dotZ_nil_left]

private theorem charForm_cons (p : Coordinates) (rest : List Coordinates) (e₀ : ZMod 25)
    (erest : List (ZMod 25)) (x : Coordinates) :
    charForm (p :: rest) (e₀ :: erest) x
      = e₀ * ((coordAt x (pivotDepth p)).val : ZMod 25)
        + charForm rest erest (clearStep 1 p x) := by
  simp only [charForm, expVec_cons, dotZ_cons]

/-- Clearing a pivot from an element whose pivot coordinate already vanishes is
a no-op. -/
private theorem clearStep_id {p w : Coordinates} (h : coordAt w (pivotDepth p) = 0) :
    clearStep 1 p w = w := by
  simp only [clearStep, h, Fin.val_zero, mpow]
  rfl

/-- `charForm` of the identity vanishes. -/
private theorem charForm_one (B : List Coordinates) (e : List (ZMod 25)) :
    charForm B e ((0, 0, 0, 0, 0) : Coordinates) = 0 := by
  induction B generalizing e with
  | nil => exact charForm_nil_B e _
  | cons p rest ih =>
      cases e with
      | nil => exact charForm_nil_e _ _
      | cons e₀ erest =>
          rw [charForm_cons]
          have h0 : coordAt ((0, 0, 0, 0, 0) : Coordinates) (pivotDepth p) = 0 :=
            coordAt_zero_all _
          rw [clearStep_id h0, h0]
          simp [ih]

/-- If the pivot coordinate of `w` vanishes, the leading `charForm` term drops
and the head of `e`/`B` can be discarded. -/
private theorem charForm_lead0 (p : Coordinates) (rest : List Coordinates) (e₀ : ZMod 25)
    (erest : List (ZMod 25)) (w : Coordinates) (h : coordAt w (pivotDepth p) = 0) :
    charForm (p :: rest) (e₀ :: erest) w = charForm rest erest w := by
  rw [charForm_cons, clearStep_id h, h]
  simp

/-! ## `Coordinate 1`-typed wrappers (defeq), so `rw`/`simp` match the core terms -/

private theorem charForm_nil_B' (e : List (ZMod 25)) (x : Coordinate 1) :
    charForm ([] : List (Coordinate 1)) e x = 0 := charForm_nil_B e x

private theorem charForm_nil_e' (B : List (Coordinate 1)) (x : Coordinate 1) :
    charForm B [] x = 0 := charForm_nil_e B x

private theorem charForm_one' (B : List (Coordinate 1)) (e : List (ZMod 25)) :
    charForm B e ((1 : Coordinate 1)) = 0 := charForm_one B e

private theorem charForm_cons' (p : Coordinate 1) (rest : List (Coordinate 1)) (e₀ : ZMod 25)
    (erest : List (ZMod 25)) (x : Coordinate 1) :
    charForm ((p :: rest : List (Coordinate 1))) (e₀ :: erest) x
      = e₀ * ((coordAt x (pivotDepth p)).val : ZMod 25)
        + charForm rest erest (clearStep 1 p x) :=
  charForm_cons p rest e₀ erest x

private theorem charForm_lead0' (p : Coordinate 1) (rest : List (Coordinate 1)) (e₀ : ZMod 25)
    (erest : List (ZMod 25)) (w : Coordinate 1) (h : coordAt w (pivotDepth p) = 0) :
    charForm ((p :: rest : List (Coordinate 1))) (e₀ :: erest) w = charForm rest erest w :=
  charForm_lead0 p rest e₀ erest w h

/-- The computable commutator of two members of a subgroup lands in it. -/
private theorem commutatorC_mem {K : Subgroup (Coordinate 1)} {a b : Coordinate 1}
    (ha : a ∈ K) (hb : b ∈ K) : (commutatorC a b : Coordinate 1) ∈ K := by
  have h : (commutatorC a b : Coordinate 1) = (a * b * a⁻¹ * b⁻¹ : Coordinate 1) := by
    rw [commutatorC_eq, commutatorElement_def]
  rw [h]
  exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)

/-! ## Conjugation invariance of `charForm rest erest` on `N = ⟨rest⟩`

Given that `charForm rest erest` is additive on `N` (`hadd`, the induction
hypothesis) and kills the commutators `⁅p, g⁆` for the generators `g` of `N`
(`hcomm0`, from `charOK`), it is invariant under conjugation by `p`. -/

/-- On an additive functional, inverses negate. -/
private theorem charForm_inv
    (rest : List (Coordinate 1)) (erest : List (ZMod 25))
    (hadd : ∀ u v : Coordinate 1, u ∈ ofList 1 hq1 rest → v ∈ ofList 1 hq1 rest →
        charForm rest erest ((u * v : Coordinate 1))
          = charForm rest erest u + charForm rest erest v)
    (w : Coordinate 1) (hw : w ∈ ofList 1 hq1 rest) :
    charForm rest erest ((w⁻¹ : Coordinate 1)) = - charForm rest erest w := by
  have h1 : charForm rest erest ((w * w⁻¹ : Coordinate 1))
      = charForm rest erest w + charForm rest erest ((w⁻¹ : Coordinate 1)) :=
    hadd w w⁻¹ hw (Subgroup.inv_mem _ hw)
  rw [mul_inv_cancel] at h1
  have h0 : charForm rest erest ((1 : Coordinate 1)) = 0 := charForm_one rest erest
  rw [h0] at h1
  linear_combination -h1

/-- **Conjugation invariance.** `charForm rest erest (p·w·p⁻¹) = charForm rest erest w`
for every `w ∈ N`. -/
private theorem charForm_conj
    (p : Coordinate 1) (rest : List (Coordinate 1)) (erest : List (ZMod 25))
    (hnorm : p ∈ Subgroup.normalizer (ofList 1 hq1 rest))
    (hadd : ∀ u v : Coordinate 1, u ∈ ofList 1 hq1 rest → v ∈ ofList 1 hq1 rest →
        charForm rest erest ((u * v : Coordinate 1))
          = charForm rest erest u + charForm rest erest v)
    (hcomm0 : ∀ g ∈ rest, charForm rest erest (commutatorC p g) = 0) :
    ∀ w : Coordinate 1, w ∈ ofList 1 hq1 rest →
      charForm rest erest ((p * w * p⁻¹ : Coordinate 1)) = charForm rest erest w := by
  have hconj : ∀ w : Coordinate 1, w ∈ ofList 1 hq1 rest →
      (p * w * p⁻¹ : Coordinate 1) ∈ ofList 1 hq1 rest :=
    fun w hw => (Subgroup.mem_normalizer_iff.mp hnorm w).mp hw
  intro w hw
  induction hw using Subgroup.closure_induction with
  | mem g hg =>
      have hgN : g ∈ ofList 1 hq1 rest := Subgroup.subset_closure hg
      have hcomm_mem : (⁅p, g⁆ : Coordinate 1) ∈ ofList 1 hq1 rest := by
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (hconj g hgN) (Subgroup.inv_mem _ hgN)
      have hsplit : (p * g * p⁻¹ : Coordinate 1) = (⁅p, g⁆ * g : Coordinate 1) := by
        rw [commutatorElement_def]; group
      have hc0 : charForm rest erest (⁅p, g⁆ : Coordinate 1) = 0 := by
        rw [← commutatorC_eq]; exact hcomm0 g hg
      rw [hsplit, hadd _ _ hcomm_mem hgN, hc0, zero_add]
  | one =>
      have h1 : (p * 1 * p⁻¹ : Coordinate 1) = 1 := by group
      rw [h1]
  | mul a b ha hb iha ihb =>
      have haN : a ∈ ofList 1 hq1 rest := ha
      have hbN : b ∈ ofList 1 hq1 rest := hb
      have hsplit : (p * (a * b) * p⁻¹ : Coordinate 1)
          = ((p * a * p⁻¹) * (p * b * p⁻¹) : Coordinate 1) := by group
      rw [hsplit, hadd _ _ (hconj a haN) (hconj b hbN), iha, ihb, hadd _ _ haN hbN]
  | inv a ha iha =>
      have haN : a ∈ ofList 1 hq1 rest := ha
      have hsplit : (p * a⁻¹ * p⁻¹ : Coordinate 1) = ((p * a * p⁻¹)⁻¹ : Coordinate 1) := by group
      rw [hsplit, charForm_inv rest erest hadd _ (hconj a haN), iha,
        charForm_inv rest erest hadd a haN]

/-- Conjugation invariance iterated to a natural power of `p`. -/
private theorem charForm_conj_pow
    (p : Coordinate 1) (rest : List (Coordinate 1)) (erest : List (ZMod 25))
    (hnorm : p ∈ Subgroup.normalizer (ofList 1 hq1 rest))
    (hadd : ∀ u v : Coordinate 1, u ∈ ofList 1 hq1 rest → v ∈ ofList 1 hq1 rest →
        charForm rest erest ((u * v : Coordinate 1))
          = charForm rest erest u + charForm rest erest v)
    (hcomm0 : ∀ g ∈ rest, charForm rest erest (commutatorC p g) = 0) :
    ∀ (k : ℕ) (w : Coordinate 1), w ∈ ofList 1 hq1 rest →
      charForm rest erest ((p ^ k * w * (p ^ k)⁻¹ : Coordinate 1)) = charForm rest erest w := by
  have hconj : ∀ w : Coordinate 1, w ∈ ofList 1 hq1 rest →
      (p * w * p⁻¹ : Coordinate 1) ∈ ofList 1 hq1 rest :=
    fun w hw => (Subgroup.mem_normalizer_iff.mp hnorm w).mp hw
  have hconjK : ∀ (k : ℕ) (w : Coordinate 1), w ∈ ofList 1 hq1 rest →
      (p ^ k * w * (p ^ k)⁻¹ : Coordinate 1) ∈ ofList 1 hq1 rest := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
        intro w hw
        have hstep : (p ^ (k + 1) * w * (p ^ (k + 1))⁻¹ : Coordinate 1)
            = (p * (p ^ k * w * (p ^ k)⁻¹) * p⁻¹ : Coordinate 1) := by
          rw [pow_succ']; group
        rw [hstep]; exact hconj _ (ih w hw)
  intro k
  induction k with
  | zero =>
      intro w hw
      have h0 : (p ^ 0 * w * (p ^ 0)⁻¹ : Coordinate 1) = w := by group
      rw [h0]
  | succ k ih =>
      intro w hw
      have heq : (p ^ (k + 1) * w * (p ^ (k + 1))⁻¹ : Coordinate 1)
          = (p * (p ^ k * w * (p ^ k)⁻¹) * p⁻¹ : Coordinate 1) := by
        rw [pow_succ']; group
      rw [heq, charForm_conj p rest erest hnorm hadd hcomm0 _ (hconjK k w hw), ih w hw]

/-! ## Unpacking `charOK` into semantic power/commutator conditions -/

private theorem charOK_pow (B : List Coordinates) (e : List (ZMod 25)) (h : charOK B e = true) :
    ∀ i < B.length, charForm B e (mpow 1 (B.getD i zc) 5) = 5 * e.getD i 0 := by
  intro i hi
  have h1 : (List.range B.length).all
      (fun i => decide (dotZ e (expVec B (mpow 1 (B.getD i zc) 5)) = 5 * e.getD i 0)) = true := by
    rw [charOK, Bool.and_eq_true] at h; exact h.1
  have hcell := (List.all_eq_true.mp h1) i (List.mem_range.mpr hi)
  simpa [charForm] using of_decide_eq_true hcell

private theorem charOK_comm (B : List Coordinates) (e : List (ZMod 25)) (h : charOK B e = true) :
    ∀ i j, i < j → j < B.length →
      charForm B e (commutatorC (B.getD i zc) (B.getD j zc)) = 0 := by
  intro i j hij hj
  have h2 : (List.range B.length).all (fun i => (List.range B.length).all (fun j =>
      !(Nat.blt i j) ||
        decide (dotZ e (expVec B (commutatorC (B.getD i zc) (B.getD j zc))) = 0))) = true := by
    rw [charOK, Bool.and_eq_true] at h; exact h.2
  have hi : i < B.length := lt_trans hij hj
  have hrow := (List.all_eq_true.mp h2) i (List.mem_range.mpr hi)
  have hcell := (List.all_eq_true.mp hrow) j (List.mem_range.mpr hj)
  have hlt : Nat.blt i j = true := by simp only [Nat.blt_eq]; omega
  rw [hlt] at hcell
  simp only [Bool.not_true, Bool.false_or] at hcell
  simpa [charForm] using of_decide_eq_true hcell

/-! ## The additivity core -/

/-- **Additivity core.** For a well-formed echelon basis `B` and a vector `e`
satisfying the (semantic) `charOK` power/commutator conditions, `charForm B e`
is additive on `⟨B⟩`. Proved by structural recursion on `B`. -/
private theorem charForm_additive_core :
    ∀ (B : List (Coordinate 1)), WF 1 hq1 B → ∀ (e : List (ZMod 25)),
      (∀ i < B.length, charForm B e (mpow 1 (B.getD i zc) 5) = 5 * e.getD i 0) →
      (∀ i j, i < j → j < B.length →
          charForm B e (commutatorC (B.getD i zc) (B.getD j zc)) = 0) →
      ∀ (x y : Coordinate 1), x ∈ ofList 1 hq1 B → y ∈ ofList 1 hq1 B →
        charForm B e ((x * y : Coordinate 1)) = charForm B e x + charForm B e y := by
  intro B
  induction B with
  | nil => intro _ e _ _ x y _ _; simp [charForm_nil_B']
  | cons p rest ih =>
      intro hwf e hPow hComm x y hx hy
      obtain ⟨hp5, hlead, hrest, hpow, hnorm, hwfrest⟩ := hwf
      cases e with
      | nil => simp [charForm_nil_e']
      | cons e₀ erest =>
          set d := pivotDepth p with hd_def
          set N := ofList 1 hq1 rest with hN_def
          -- an element of `N` has vanishing pivot coordinate
          have hcoord0 : ∀ w : Coordinate 1, w ∈ N → coordAt w d = 0 :=
            fun w hw => (ofList_le_depthGE hq1 p rest hrest) hw d (Nat.lt_succ_self d)
          -- generators of `N` sit in `N`
          have hgetN : ∀ i, i < rest.length → (rest.getD i zc : Coordinate 1) ∈ N := by
            intro i hi
            rw [List.getD_eq_getElem rest zc hi]
            exact Subgroup.subset_closure (List.getElem_mem hi)
          -- `p^5 ∈ N`, and `5 ∣ j ⟹ p^j ∈ N`
          have hpow_dvd : ∀ j : ℤ, (5 : ℤ) ∣ j → (p ^ j : Coordinate 1) ∈ N := by
            intro j hj; obtain ⟨k, rfl⟩ := hj
            rw [zpow_mul, show (5 : ℤ) = ((5 : ℕ) : ℤ) from rfl, zpow_natCast]
            exact Subgroup.zpow_mem N hpow k
          -- conjugation of `N` by `p`, and by a natural power of `p`, stays in `N`
          have hconj : ∀ w : Coordinate 1, w ∈ N → (p * w * p⁻¹ : Coordinate 1) ∈ N :=
            fun w hw => (Subgroup.mem_normalizer_iff.mp hnorm w).mp hw
          have hconjNat : ∀ (k : ℕ) (w : Coordinate 1), w ∈ N →
              (p ^ k * w * (p ^ k)⁻¹ : Coordinate 1) ∈ N := by
            intro k
            induction k with
            | zero => intro w hw; simpa using hw
            | succ k ih2 =>
                intro w hw
                have hstep : (p ^ (k + 1) * w * (p ^ (k + 1))⁻¹ : Coordinate 1)
                    = (p * (p ^ k * w * (p ^ k)⁻¹) * p⁻¹ : Coordinate 1) := by
                  rw [pow_succ']; group
                rw [hstep]; exact hconj _ (ih2 w hw)
          -- inherited semantic conditions for `rest`/`erest`
          have hPow_rest : ∀ i < rest.length,
              charForm rest erest (mpow 1 (rest.getD i zc) 5) = 5 * erest.getD i 0 := by
            intro i hi
            have hb := hPow (i + 1) (by simp only [List.length_cons]; omega)
            rw [List.getD_cons_succ, List.getD_cons_succ] at hb
            have hwmem : (mpow 1 (rest.getD i zc) 5 : Coordinate 1) ∈ N := by
              rw [mpow_eq_pow hq1]; exact Subgroup.pow_mem _ (hgetN i hi) 5
            rw [charForm_lead0' p rest e₀ erest _ (hcoord0 _ hwmem)] at hb
            exact hb
          have hComm_rest : ∀ i j, i < j → j < rest.length →
              charForm rest erest (commutatorC (rest.getD i zc) (rest.getD j zc)) = 0 := by
            intro i j hij hj
            have hb := hComm (i + 1) (j + 1) (by omega) (by simp only [List.length_cons]; omega)
            rw [List.getD_cons_succ, List.getD_cons_succ] at hb
            have hwmem : (commutatorC (rest.getD i zc) (rest.getD j zc) : Coordinate 1) ∈ N :=
              commutatorC_mem (hgetN i (lt_trans hij hj)) (hgetN j hj)
            rw [charForm_lead0' p rest e₀ erest _ (hcoord0 _ hwmem)] at hb
            exact hb
          -- the induction hypothesis, as additivity of `charForm rest erest` on `N`
          have hadd : ∀ u v : Coordinate 1, u ∈ N → v ∈ N →
              charForm rest erest ((u * v : Coordinate 1))
                = charForm rest erest u + charForm rest erest v :=
            ih hwfrest erest hPow_rest hComm_rest
          -- commutator condition specialised to conjugation invariance
          have hcomm0 : ∀ g ∈ rest, charForm rest erest (commutatorC p g) = 0 := by
            intro g hg
            obtain ⟨idx, hidx, hgv⟩ := List.mem_iff_getElem.mp hg
            have hb := hComm 0 (idx + 1) (by omega) (by simp only [List.length_cons]; omega)
            rw [List.getD_cons_zero, List.getD_cons_succ, List.getD_eq_getElem rest zc hidx,
              hgv] at hb
            have hgN : (g : Coordinate 1) ∈ N := Subgroup.subset_closure hg
            have hwmem : (commutatorC p g : Coordinate 1) ∈ N := by
              have h : (commutatorC p g : Coordinate 1) = (p * g * p⁻¹ : Coordinate 1) * g⁻¹ := by
                rw [commutatorC_eq, commutatorElement_def]
              rw [h]
              exact N.mul_mem (hconj g hgN) (N.inv_mem hgN)
            rw [charForm_lead0' p rest e₀ erest _ (hcoord0 _ hwmem)] at hb
            exact hb
          -- the induction hypothesis packaged as conjugation invariance
          have hconjval : ∀ (k : ℕ) (w : Coordinate 1), w ∈ N →
              charForm rest erest ((p ^ k * w * (p ^ k)⁻¹ : Coordinate 1))
                = charForm rest erest w :=
            charForm_conj_pow p rest erest hnorm hadd hcomm0
          -- lead-term power condition at index 0
          have hpow0 : charForm rest erest (mpow 1 p 5) = 5 * e₀ := by
            have hb := hPow 0 (by simp only [List.length_cons]; omega)
            rw [List.getD_cons_zero, List.getD_cons_zero] at hb
            have hwmem : (mpow 1 p 5 : Coordinate 1) ∈ N := by
              rw [mpow_eq_pow hq1]; exact hpow
            rw [charForm_lead0' p rest e₀ erest _ (hcoord0 _ hwmem)] at hb
            exact hb
          -- abbreviations for the lead coordinates
          set a := coordAt x (pivotDepth p) with ha_def
          set b := coordAt y (pivotDepth p) with hb_def
          -- `x'`, `y'` as genuine `Coordinate 1` values landing in `N`
          set x' : Coordinate 1 := clearStep 1 p x with hx'_def
          set y' : Coordinate 1 := clearStep 1 p y with hy'_def
          have hx'N : x' ∈ N := by
            rw [hx'_def]; exact (mem_head_iff hq1 p rest hp5 hlead hrest hpow hnorm x).mp hx
          have hy'N : y' ∈ N := by
            rw [hy'_def]; exact (mem_head_iff hq1 p rest hp5 hlead hrest hpow hnorm y).mp hy
          -- `H ≤ depthGE (pivotDepth p)`, giving lead-coordinate additivity for the product
          have hHle : ofList 1 hq1 (p :: rest) ≤ depthGE 1 hq1 (pivotDepth p) := by
            refine (Subgroup.closure_le _).mpr ?_
            intro g hg
            simp only [Set.mem_setOf_eq, List.mem_cons] at hg
            rcases hg with rfl | hg
            · exact self_mem_depthGE_pivotDepth hq1 g
            · exact (mem_depthGE hq1 _ g).mpr
                (fun i hi => coordAt_of_lt_pivotDepth g i (lt_trans hi (hrest g hg)))
          have hy_d0 : ∀ i, i < pivotDepth p → coordAt y i = 0 :=
            (mem_depthGE hq1 _ y).mp (hHle hy)
          have hcadd : coordAt ((x * y : Coordinate 1)) (pivotDepth p) = a + b := by
            have := coordAt_mul_right 1 (pivotDepth p) hp5 x y hy_d0
            rw [← ha_def, ← hb_def] at this; exact this
          -- clearStep expansions (as `· * pⁿ`)
          have hxe : x' = x * p ^ (-(a.val : ℤ)) := by
            rw [hx'_def]; have := clearStep_eq hq1 p x; rw [← ha_def] at this; exact this
          have hye : y' = y * p ^ (-(b.val : ℤ)) := by
            rw [hy'_def]; have := clearStep_eq hq1 p y; rw [← hb_def] at this; exact this
          have hxye : (clearStep 1 p ((x * y : Coordinate 1)) : Coordinate 1)
              = ((x * y : Coordinate 1)) * p ^ (-((a + b).val : ℤ)) := by
            have := clearStep_eq hq1 p ((x * y : Coordinate 1)); rw [hcadd] at this; exact this
          -- the collection decomposition of `clearStep(x·y)`
          have hCS : (clearStep 1 p ((x * y : Coordinate 1)) : Coordinate 1)
              = x' * (p ^ (a.val) * y' * (p ^ (a.val))⁻¹)
                * p ^ ((a.val : ℤ) + (b.val : ℤ) - ((a + b).val : ℤ)) := by
            rw [hxye, hxe, hye, ← zpow_natCast p a.val]
            group
          -- the power factor lies in `N` (its exponent is divisible by `5`)
          have hpow_mem :
              (p ^ ((a.val : ℤ) + (b.val : ℤ) - ((a + b).val : ℤ)) : Coordinate 1) ∈ N := by
            apply hpow_dvd
            have hcv : ((a + b).val : ℤ) = (((a.val + b.val) % 5 : ℕ) : ℤ) := by
              rw [Fin.val_add]
            rw [hcv]
            refine ⟨((a.val + b.val) / 5 : ℕ), ?_⟩
            have key := Nat.div_add_mod (a.val + b.val) 5
            push_cast
            omega
          have hconjmem : (p ^ (a.val) * y' * (p ^ (a.val))⁻¹ : Coordinate 1) ∈ N :=
            hconjNat a.val y' hy'N
          -- `charForm` of `clearStep(x·y)`, additivity applied three times
          have hCF : charForm rest erest (clearStep 1 p ((x * y : Coordinate 1)))
              = charForm rest erest x' + charForm rest erest y'
                + charForm rest erest
                    ((p ^ ((a.val : ℤ) + (b.val : ℤ) - ((a + b).val : ℤ)) : Coordinate 1)) := by
            rw [hCS, hadd _ _ (Subgroup.mul_mem _ hx'N hconjmem) hpow_mem,
              hadd _ _ hx'N hconjmem, hconjval a.val y' hy'N]
          -- expand both sides and reduce to the pivot/power arithmetic
          rw [charForm_cons' p rest e₀ erest ((x * y : Coordinate 1)),
            charForm_cons' p rest e₀ erest x, charForm_cons' p rest e₀ erest y,
            hcadd, hCF, ← ha_def, ← hb_def, ← hx'_def, ← hy'_def]
          -- pivot/power correction identity, by cases on the carry
          have hfin : e₀ * ((a + b).val : ZMod 25)
              + charForm rest erest
                  ((p ^ ((a.val : ℤ) + (b.val : ℤ) - ((a + b).val : ℤ)) : Coordinate 1))
              = e₀ * (a.val : ZMod 25) + e₀ * (b.val : ZMod 25) := by
            rcases Nat.lt_or_ge (a.val + b.val) 5 with hlt | hge
            · -- no carry: exponent `0`
              have hcval : ((a + b).val : ℕ) = a.val + b.val := by
                rw [Fin.val_add, Nat.mod_eq_of_lt hlt]
              have hexp : (a.val : ℤ) + (b.val : ℤ) - ((a + b).val : ℤ) = 0 := by
                rw [hcval]; push_cast; ring
              rw [hexp, zpow_zero, charForm_one' rest erest, hcval]
              push_cast; ring
            · -- carry: exponent `5`
              have hcval : ((a + b).val : ℕ) = a.val + b.val - 5 := by
                have h1 := a.isLt; have h2 := b.isLt
                rw [Fin.val_add]; omega
              have hexp : (a.val : ℤ) + (b.val : ℤ) - ((a + b).val : ℤ) = 5 := by
                have h1 := a.isLt; have h2 := b.isLt
                rw [hcval]; omega
              rw [hexp, show (5 : ℤ) = ((5 : ℕ) : ℤ) from rfl, zpow_natCast,
                ← mpow_eq_pow hq1, hpow0, hcval]
              have hcast : ((a.val + b.val - 5 : ℕ) : ZMod 25)
                  = (a.val : ZMod 25) + (b.val : ZMod 25) - 5 := by
                have h5 : 5 ≤ a.val + b.val := hge
                push_cast [Nat.cast_sub h5]; ring
              rw [hcast]; ring
          linear_combination hfin

/-! ## `CharExtendsAt` for every well-formed basis -/

/-- **`CharExtendsAt`, generic form.** For any well-formed echelon basis
`B`, every `charOK`-valid vector `e` yields an additive character functional on
`⟨B⟩`. This discharges the extension obligation. -/
theorem charExtendsAt_of_wf (B : List (Coordinate 1)) (hwf : WF 1 hq1 B)
    (e : List (ZMod 25)) : CharExtendsAt B e := by
  intro hOK x y hx hy
  have hxm : (x : Coordinate 1) ∈ ofList 1 hq1 B := (sift_mem_iff hq1 B hwf x).mp hx
  have hym : (y : Coordinate 1) ∈ ofList 1 hq1 B := (sift_mem_iff hq1 B hwf y).mp hy
  exact charForm_additive_core B hwf e (charOK_pow B e hOK) (charOK_comm B e hOK) x y hxm hym

/-- **`CharExtendsAt` for every one of the 148 class representatives.** -/
theorem charExtendsAt_basisAt (r : Fin 148) (e : List (ZMod 25)) :
    CharExtendsAt (basisAt r) e := by
  rw [basisAt_eq]
  have hbnd : (List.range 148).all (fun i => Nat.blt (classRepsData.getD i 0) 676) = true := by
    decide
  have hlt : classRepsData.getD r.val 0 < 676 := by
    have := (List.all_eq_true.mp hbnd) r.val (List.mem_range.mpr r.isLt)
    simpa [Nat.blt_eq] using this
  exact charExtendsAt_of_wf (getB (classRepsData.getD r.val 0)) (wf_getB hlt) e

/-! # Character realization: certified vectors ↔ genuine characters

Each `charOK`-valid exponent vector `e` of `reps r` is turned into a *genuine*
homomorphism `charOfVec r e : ↥(reps r) →* ℂˣ`, `x ↦ ζ₂₅^{charForm B e x}`
(multiplicativity is exactly `charExtendsAt_basisAt`). Evaluating at the
`i`-th echelon generator recovers `eᵢ` (`charForm_getElem`), so distinct certified
vectors give distinct characters (`charOfVec_inj`); with `charsAt_nodup`,
`charsAt_count` and the certified per-vector length `charsAt_vecLen` this yields a
nodup family of `charCounts r` characters, hence the semantic lower bound

  `charCounts r ≤ |Hom(reps r, ℂˣ)| = |(reps r)ᵃᵇ|`  (`charCounts_le_card_hom`).

The **converse** — that the certified list is *exhaustive* (every character is a
listed vector, equivalently `|Hom| ≤ charCounts r`) — is isolated as the single
named obligation `CharsAtComplete`; from it `charsAt_complete` and the semantic
upgrade `card_abelianization_reps` follow. -/

/-! ## The fixed primitive 25th root of unity `ζ₂₅` and its exponent map -/

private theorem exists_prim_unit25 : ∃ ζ : ℂˣ, IsPrimitiveRoot ((ζ : ℂˣ) : ℂ) 25 := by
  have h : ∃ z : ℂ, IsPrimitiveRoot z 25 := ⟨_, Complex.isPrimitiveRoot_exp 25 (by norm_num)⟩
  obtain ⟨z, hz⟩ := h
  exact ⟨Units.mk0 z (hz.ne_zero (by norm_num)), hz⟩

/-- A fixed primitive complex 25th root of unity, as a unit of `ℂ`. -/
noncomputable def zeta25 : ℂˣ := exists_prim_unit25.choose

theorem zeta25_prim : IsPrimitiveRoot ((zeta25 : ℂˣ) : ℂ) 25 := exists_prim_unit25.choose_spec

theorem zeta25_pow_card : zeta25 ^ 25 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact zeta25_prim.pow_eq_one

theorem zeta25_pow_inj {i j : ℕ} (hi : i < 25) (hj : j < 25) (h : zeta25 ^ i = zeta25 ^ j) :
    i = j := by
  apply zeta25_prim.pow_inj hi hj
  have hc := congrArg (Units.val) h
  rwa [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at hc

/-- The exponent map `ZMod 25 → ℂˣ`, `a ↦ ζ₂₅^{a.val}`. -/
noncomputable def zexp (a : ZMod 25) : ℂˣ := zeta25 ^ a.val

theorem zexp_zero : zexp 0 = 1 := by rw [zexp, ZMod.val_zero, pow_zero]

theorem zexp_add (a b : ZMod 25) : zexp (a + b) = zexp a * zexp b := by
  rw [zexp, zexp, zexp, ZMod.val_add, ← pow_eq_pow_mod (a.val + b.val) zeta25_pow_card, pow_add]

theorem zexp_inj : Function.Injective zexp := by
  intro a b h
  rw [zexp, zexp] at h
  exact ZMod.val_injective 25 (zeta25_pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h)

/-! ## Well-formedness and sift plumbing for `basisAt r` -/

/-- The echelon basis of `reps r` is well formed. -/
theorem wf_basisAt (r : Fin 148) : WF 1 hq1 (basisAt r) := by
  rw [basisAt_eq]
  refine wf_getB ?_
  have hbnd : (List.range 148).all (fun i => Nat.blt (classRepsData.getD i 0) 676) = true := by
    decide
  have := (List.all_eq_true.mp hbnd) r.val (List.mem_range.mpr r.isLt)
  simpa [Nat.blt_eq] using this

/-- Every member of `reps r` sifts to the identity against its echelon basis. -/
theorem siftB_of_mem (r : Fin 148) (x : ↥(reps r)) :
    siftB 1 (basisAt r) (x : Coordinate 1) = true := by
  apply (sift_mem_iff hq1 (basisAt r) (wf_basisAt r) (x : Coordinate 1)).mpr
  rw [← reps_eq_ofList r]
  exact x.2

/-- Per-element `charOK`-validity, extracted from `charsAt_valid`. -/
theorem validAt (r : Fin 148) {e : List (ZMod 25)} (he : e ∈ charsAt r) :
    charOK (basisAt r) e = true :=
  (List.all_eq_true.mp (charsAt_valid r)) e he

/-- The whole-range vector-length check (glued from the four chunk `decide`s of
`LeanDring.P5.Certificate.Characters.Twin1.CharVecLen`). -/
theorem checkVecLen_all : (List.range 148).all checkVecLen = true :=
  all148_of_chunks checkVecLen vecLenChunk0 vecLenChunk1 vecLenChunk2 vecLenChunk3

/-- **Per-vector length.** Every certified exponent vector of `reps r` has length
equal to the number of echelon generators of `reps r`. -/
theorem charsAt_vecLen (r : Fin 148) : ∀ e ∈ charsAt r, e.length = (basisAt r).length := by
  have h := (List.all_eq_true.mp checkVecLen_all) r.val (List.mem_range.mpr r.isLt)
  simp only [checkVecLen] at h
  rw [List.all_eq_true] at h
  intro e he
  exact Nat.eq_of_beq_eq_true (h e he)

/-! ## `charForm` evaluated at the echelon generators is the standard basis -/

/-- **Evaluation at generators.** For a well-formed echelon basis `B`, the
candidate exponent `charForm B e` at the `i`-th generator is exactly `eᵢ`: the
`i`-th generator's pcgs expansion is the `i`-th standard basis vector. -/
private theorem charForm_getElem :
    ∀ (B : List (Coordinate 1)), WF 1 hq1 B → ∀ (e : List (ZMod 25)) (i : ℕ),
      i < B.length → charForm B e (B.getD i zc) = e.getD i 0 := by
  intro B
  induction B with
  | nil => intro _ e i hi; simp only [List.length_nil] at hi; omega
  | cons p rest ih =>
      intro hwf e i hi
      obtain ⟨hp5, hlead, hrest, hpow, hnorm, hwfrest⟩ := hwf
      cases e with
      | nil => rw [charForm_nil_e', List.getD_nil]
      | cons e₀ erest =>
          cases i with
          | zero =>
              rw [List.getD_cons_zero, List.getD_cons_zero]
              have hcs := clearStep_eq hq1 p p
              rw [hlead] at hcs
              have h0 : clearStep 1 p p = ((0, 0, 0, 0, 0) : Coordinates) := by
                rw [hcs, Fin.val_one, Nat.cast_one, zpow_neg, zpow_one]
                exact mul_inv_cancel p
              have hcz : charForm rest erest (clearStep 1 p p) = 0 := by
                rw [h0]; exact charForm_one rest erest
              rw [charForm_cons' p rest e₀ erest p, hlead, hcz]
              simp
          | succ j =>
              have hjr : j < rest.length := by
                simp only [List.length_cons] at hi; omega
              have hmem : (rest.getD j zc : Coordinate 1) ∈ rest := by
                rw [List.getD_eq_getElem rest zc hjr]; exact List.getElem_mem hjr
              have hpd : pivotDepth p < pivotDepth (rest.getD j zc) := hrest _ hmem
              have hc0 : coordAt (rest.getD j zc) (pivotDepth p) = 0 :=
                coordAt_of_lt_pivotDepth _ _ hpd
              rw [List.getD_cons_succ, charForm_lead0' p rest e₀ erest _ hc0,
                List.getD_cons_succ]
              exact ih hwfrest erest j hjr

/-! ## The forward map: a certified vector becomes a genuine character -/

/-- **The character realized by a `charOK`-valid exponent vector**: the
homomorphism `x ↦ ζ₂₅^{charForm B e x}` on `H = reps r`. Multiplicativity is
the additivity of `charForm` (`charExtendsAt_basisAt`). -/
noncomputable def charOfVec (r : Fin 148) (e : List (ZMod 25))
    (he : charOK (basisAt r) e = true) : ↥(reps r) →* ℂˣ where
  toFun x := zexp (charForm (basisAt r) e (x : Coordinate 1))
  map_one' := by
    change zexp (charForm (basisAt r) e ((1 : ↥(reps r)) : Coordinate 1)) = 1
    rw [Subgroup.coe_one, charForm_one' (basisAt r) e]
    exact zexp_zero
  map_mul' x y := by
    change zexp (charForm (basisAt r) e (((x * y : ↥(reps r)) : Coordinate 1)))
       = zexp (charForm (basisAt r) e (x : Coordinate 1))
         * zexp (charForm (basisAt r) e (y : Coordinate 1))
    rw [← zexp_add]
    congr 1
    rw [Subgroup.coe_mul]
    exact charExtendsAt_basisAt r e he (x : Coordinate 1) (y : Coordinate 1)
      (siftB_of_mem r x) (siftB_of_mem r y)

theorem charOfVec_apply (r : Fin 148) (e : List (ZMod 25)) (he : charOK (basisAt r) e = true)
    (x : ↥(reps r)) : charOfVec r e he x = zexp (charForm (basisAt r) e (x : Coordinate 1)) := rfl

/-- **Value at a generator.** The realized character sends the `i`-th echelon
generator of `reps r` to `ζ₂₅^{eᵢ}`. -/
theorem charOfVec_gen (r : Fin 148) (e : List (ZMod 25)) (he : charOK (basisAt r) e = true)
    (i : ℕ) (hi : i < (basisAt r).length)
    (hmem : ((basisAt r).getD i zc : Coordinate 1) ∈ reps r) :
    charOfVec r e he ⟨(basisAt r).getD i zc, hmem⟩ = zexp (e.getD i 0) := by
  rw [charOfVec_apply]
  change zexp (charForm (basisAt r) e ((basisAt r).getD i zc)) = zexp (e.getD i 0)
  congr 1
  exact charForm_getElem (basisAt r) (wf_basisAt r) e i hi

/-- **Injectivity on the certified list.** Distinct listed exponent vectors of
`reps r` realize distinct characters. -/
theorem charOfVec_inj (r : Fin 148) {e e' : List (ZMod 25)}
    (he : e ∈ charsAt r) (he' : e' ∈ charsAt r)
    (heq : charOfVec r e (validAt r he) = charOfVec r e' (validAt r he')) : e = e' := by
  have hlen : e.length = (basisAt r).length := charsAt_vecLen r e he
  have hlen' : e'.length = (basisAt r).length := charsAt_vecLen r e' he'
  apply List.ext_getElem (by rw [hlen, hlen'])
  intro i h1 _
  have hik : i < (basisAt r).length := hlen ▸ h1
  have hmem : ((basisAt r).getD i zc : Coordinate 1) ∈ reps r := by
    rw [reps_eq_ofList r, List.getD_eq_getElem (basisAt r) zc hik]
    exact Subgroup.subset_closure (List.getElem_mem hik)
  have hcongr := DFunLike.congr_fun heq (⟨(basisAt r).getD i zc, hmem⟩ : ↥(reps r))
  rw [charOfVec_gen r e _ i hik hmem, charOfVec_gen r e' _ i hik hmem] at hcongr
  have hval := zexp_inj hcongr
  rwa [List.getD_eq_getElem e 0 (hlen ▸ hik), List.getD_eq_getElem e' 0 (hlen' ▸ hik)] at hval

/-! ## The semantic count bound `charCounts r ≤ |Hom(reps r, ℂˣ)|` -/

/-- **Lower bound.** The certified character count of `reps r` is at most
the number of genuine linear characters `Hom(reps r, ℂˣ) = |(reps r)ᵃᵇ|`. The
`charCounts r` listed vectors realize that many *distinct* characters. -/
theorem charCounts_le_card_hom (r : Fin 148) :
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
  have hLnodup : ((charsAt r).attach.map
      (fun p => charOfVec r p.1 (validAt r p.2))).Nodup := by
    apply List.Nodup.map_on ?_ (List.nodup_attach.mpr (charsAt_nodup r))
    rintro ⟨a, ha⟩ _ ⟨b, hb⟩ _ hab
    exact Subtype.ext (charOfVec_inj r ha hb hab)
  calc charCounts.getD r.val 0
      = ((charsAt r).attach.map (fun p => charOfVec r p.1 (validAt r p.2))).length := by
        rw [List.length_map, List.length_attach, charsAt_count r]
    _ ≤ Fintype.card (↥(reps r) →* ℂˣ) := hLnodup.length_le_card
    _ = Nat.card (↥(reps r) →* ℂˣ) := (Nat.card_eq_fintype_card).symm

/-! ## The isolated converse obligation and the conditional headline -/

/-- **The converse obligation** (the completeness/exhaustiveness of the certified
enumeration): the number of genuine linear characters of `reps r` does not exceed
the certified count — equivalently every character is realized by one of the
listed exponent vectors. Combined with the unconditional
`charCounts_le_card_hom`, this pins the count, making the certified vectors a
complete enumeration of the characters. -/
def CharsAtComplete (r : Fin 148) : Prop :=
  Nat.card (↥(reps r) →* ℂˣ) ≤ charCounts.getD r.val 0

/-- **The character count (conditional on completeness).** The number of linear
characters of `reps r` equals its certified count `charCounts r`. -/
theorem charsAt_complete (r : Fin 148) (hc : CharsAtComplete r) :
    Nat.card (↥(reps r) →* ℂˣ) = charCounts.getD r.val 0 :=
  le_antisymm hc (charCounts_le_card_hom r)

/-- **Semantic upgrade of the aggregate count** (conditional on completeness): the
generator-emitted count `charCounts r` is the genuine abelianization order of
`reps r`. -/
theorem card_abelianization_reps (r : Fin 148) (hc : CharsAtComplete r) :
    Nat.card (Abelianization ↥(reps r)) = charCounts.getD r.val 0 := by
  haveI : Fintype ↥(reps r) := Fintype.ofFinite _
  rw [← LeanDring.DRing.card_charHom_eq_card_abelianization]
  exact charsAt_complete r hc

/-! # Completeness of the certified enumeration (`CharsAtComplete`)

The converse direction. Every character `χ : ↥(reps r) →* ℂˣ` is *recovered* from
a `charOK`-valid exponent vector `evalVec … χ`, via the discrete logarithm at the
echelon generators. Three ingredients:

* **(i) exponent 25** — the ambient group `Coordinate 1` has exponent dividing
  `25` (`pow25_eq_one`, a single kernel `decide` over the `mpow` power map), so
  every character value `χ(g)` is a `25`-th root of unity;
* **(ii) discrete log** — the `25`-th roots of unity in `ℂˣ` are exactly the image
  of `zexp : ZMod 25 → ℂˣ`, which is injective; `dlog` inverts it;
* **(iii) reconstruction** — the master evaluation `master_eval` computes `χ` on
  *every* element of `reps r` from its values at the generators, by the same
  echelon recursion as `charForm`. Consequently `χ ↦ evalVec … χ` is injective,
  its image is `charOK`-valid, and (given the certified list is *exhaustive*)
  lands in `charsAt r` — pinning `|Hom(reps r, ℂˣ)| ≤ charCounts r`. -/

/-! ## (i) The ambient group has exponent dividing `25` -/

/-- **Exponent 25.** Every element of `Coordinate 1` is killed by `25`, bridged
from `mpow25_all` (the chunked `mpow` decide in
`LeanDring.P5.Certificate.Characters.Twin1.CharExp`) to the group power by
`mpow_eq_pow`. -/
theorem pow25_eq_one (x : Coordinate 1) : x ^ (25 : ℕ) = 1 := by
  have hb := mpow_eq_pow hq1 x 25
  rw [mpow25_all x] at hb
  exact hb.symm

/-! ## (ii) The discrete logarithm on the `25`-th roots of unity -/

/-- Every `25`-th root of unity in `ℂˣ` is `ζ₂₅` to some `ZMod 25` power. -/
theorem exists_dlog (u : ℂˣ) (hu : u ^ (25 : ℕ) = 1) : ∃ c : ZMod 25, zexp c = u := by
  have hval : ((u : ℂ)) ^ (25 : ℕ) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  obtain ⟨i, hi, hpow⟩ := zeta25_prim.eq_pow_of_pow_eq_one hval
  refine ⟨(i : ZMod 25), ?_⟩
  apply Units.ext
  rw [zexp, Units.val_pow_eq_pow_val, ZMod.val_natCast_of_lt hi, hpow]

/-- The discrete logarithm: a chosen `ZMod 25` exponent of a unit (junk `0` off
the `25`-th roots of unity). On a `25`-th root of unity it inverts `zexp`. -/
noncomputable def dlog (u : ℂˣ) : ZMod 25 :=
  if h : ∃ c : ZMod 25, zexp c = u then h.choose else 0

theorem zexp_dlog {u : ℂˣ} (hu : u ^ (25 : ℕ) = 1) : zexp (dlog u) = u := by
  rw [dlog, dif_pos (exists_dlog u hu)]
  exact (exists_dlog u hu).choose_spec

/-- `zexp` respects natural powers: `(zexp c) ^ n = zexp (c * n)`. -/
theorem zexp_pow (c : ZMod 25) (n : ℕ) : zexp c ^ n = zexp (c * (n : ZMod 25)) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, mul_zero, zexp_zero]
  | succ n ih =>
      rw [pow_succ, ih, ← zexp_add, Nat.cast_succ, mul_add, mul_one]

/-! ## Every character value is a `25`-th root of unity -/

/-- Any character of any subgroup sends each element to a `25`-th root of unity
(the ambient exponent is `25`). -/
theorem charVal_pow25 {H : Subgroup (Coordinate 1)} (χ : ↥H →* ℂˣ) (h : ↥H) :
    (χ h) ^ (25 : ℕ) = 1 := by
  rw [← map_pow]
  have hh : h ^ (25 : ℕ) = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, Subgroup.coe_one]
    exact pow25_eq_one (h : Coordinate 1)
  rw [hh, map_one]

/-! ## (iii) The reconstruction vector and the master evaluation -/

/-- Tail inclusion of subgroups presented by a basis: `⟨rest⟩ ≤ ⟨p :: rest⟩`. -/
def inclOfList (p : Coordinate 1) (rest : List (Coordinate 1)) :
    ↥(ofList 1 hq1 rest) →* ↥(ofList 1 hq1 (p :: rest)) :=
  Subgroup.inclusion (by
    apply Subgroup.closure_mono
    intro x hx
    exact List.mem_cons_of_mem p hx)

/-- **The reconstruction vector** of a character `χ` on `⟨B⟩`: its discrete
logarithm at each echelon generator, in basis order. -/
noncomputable def evalVec : (B : List (Coordinate 1)) → (↥(ofList 1 hq1 B) →* ℂˣ) →
    List (ZMod 25)
  | [], _ => []
  | p :: rest, χ =>
      dlog (χ ⟨p, Subgroup.subset_closure (List.mem_cons_self ..)⟩) ::
        evalVec rest (χ.comp (inclOfList p rest))

theorem evalVec_length : ∀ (B : List (Coordinate 1)) (χ : ↥(ofList 1 hq1 B) →* ℂˣ),
    (evalVec B χ).length = B.length := by
  intro B
  induction B with
  | nil => intro _; rfl
  | cons p rest ih =>
      intro χ
      change (evalVec rest (χ.comp (inclOfList p rest))).length + 1 = rest.length + 1
      rw [ih]

/-- **Master evaluation.** A character `χ` on `⟨B⟩` (a well-formed echelon basis)
equals `zexp` of the `charForm` functional of its reconstruction vector, on
*every* element of `⟨B⟩` — the same echelon recursion that defines `charForm`. -/
theorem master_eval : ∀ (B : List (Coordinate 1)), WF 1 hq1 B →
    ∀ (χ : ↥(ofList 1 hq1 B) →* ℂˣ) (x : Coordinate 1) (hx : x ∈ ofList 1 hq1 B),
      χ ⟨x, hx⟩ = zexp (charForm B (evalVec B χ) x) := by
  intro B
  induction B with
  | nil =>
      intro _ χ x hx
      have hbot : ofList 1 hq1 ([] : List (Coordinate 1)) = ⊥ := by
        have hset : {y : Coordinate 1 | y ∈ ([] : List (Coordinate 1))}
            = (∅ : Set (Coordinate 1)) := by ext y; simp
        rw [ofList, hset, Subgroup.closure_empty]
      have hx1 : x = 1 := by
        have h := hx; rw [hbot, Subgroup.mem_bot] at h; exact h
      have hsub : (⟨x, hx⟩ : ↥(ofList 1 hq1 ([] : List (Coordinate 1)))) = 1 :=
        Subtype.ext (by rw [Subgroup.coe_one]; exact hx1)
      rw [hsub, map_one, charForm_nil_B', zexp_zero]
  | cons p rest ih =>
      intro hwf χ x hx
      obtain ⟨hp5, hlead, hrest, hpow, hnorm, hwfrest⟩ := hwf
      set a := (coordAt x (pivotDepth p)).val with ha_def
      set x' : Coordinate 1 := clearStep 1 p x with hx'_def
      have hx'N : x' ∈ ofList 1 hq1 rest := by
        rw [hx'_def]
        exact (mem_head_iff hq1 p rest hp5 hlead hrest hpow hnorm x).mp hx
      have hpH : p ∈ ofList 1 hq1 (p :: rest) :=
        Subgroup.subset_closure (List.mem_cons_self ..)
      have hle : ofList 1 hq1 rest ≤ ofList 1 hq1 (p :: rest) := by
        apply Subgroup.closure_mono; intro y hy; exact List.mem_cons_of_mem p hy
      have hx'H : x' ∈ ofList 1 hq1 (p :: rest) := hle hx'N
      have hxe : x = x' * p ^ a := by
        have hcs : x' = x * p ^ (-(a : ℤ)) := clearStep_eq hq1 p x
        have h2 : x' * p ^ (a : ℤ) = x := by rw [hcs]; group
        rw [← h2, zpow_natCast]
      have hcoe : (⟨x, hx⟩ : ↥(ofList 1 hq1 (p :: rest)))
          = ⟨x', hx'H⟩ * ⟨p, hpH⟩ ^ a :=
        Subtype.ext (by rw [Subgroup.coe_mul, SubmonoidClass.coe_pow]; exact hxe)
      have hIH : χ ⟨x', hx'H⟩
          = zexp (charForm rest (evalVec rest (χ.comp (inclOfList p rest))) x') := by
        have hkey := ih hwfrest (χ.comp (inclOfList p rest)) x' hx'N
        rw [MonoidHom.comp_apply] at hkey
        exact hkey
      have hpv : zexp (dlog (χ ⟨p, hpH⟩)) = χ ⟨p, hpH⟩ :=
        zexp_dlog (charVal_pow25 χ ⟨p, hpH⟩)
      rw [hcoe, map_mul, map_pow, hIH, ← hpv, zexp_pow, ← zexp_add]
      congr 1
      change charForm rest (evalVec rest (χ.comp (inclOfList p rest))) x'
            + dlog (χ ⟨p, hpH⟩) * (a : ZMod 25)
          = charForm (p :: rest)
              (dlog (χ ⟨p, hpH⟩) :: evalVec rest (χ.comp (inclOfList p rest))) x
      rw [charForm_cons p rest (dlog (χ ⟨p, hpH⟩))
            (evalVec rest (χ.comp (inclOfList p rest))) x, ← hx'_def, ← ha_def]
      ring

/-! ## The reconstruction vector is `charOK`-valid -/

/-- Additivity of the reconstruction functional on `⟨B⟩` (from `master_eval` and
injectivity of `zexp`). -/
theorem charForm_add_evalVec (B : List (Coordinate 1)) (hwf : WF 1 hq1 B)
    (χ : ↥(ofList 1 hq1 B) →* ℂˣ) (x y : Coordinate 1)
    (hx : x ∈ ofList 1 hq1 B) (hy : y ∈ ofList 1 hq1 B) :
    charForm B (evalVec B χ) (x * y)
      = charForm B (evalVec B χ) x + charForm B (evalVec B χ) y := by
  have hxy : (x * y : Coordinate 1) ∈ ofList 1 hq1 B := mul_mem hx hy
  apply zexp_inj
  rw [zexp_add, ← master_eval B hwf χ x hx, ← master_eval B hwf χ y hy,
    ← master_eval B hwf χ (x * y) hxy, ← map_mul]
  congr 1

/-- The reconstruction functional negates on inverses. -/
theorem charForm_inv_evalVec (B : List (Coordinate 1)) (hwf : WF 1 hq1 B)
    (χ : ↥(ofList 1 hq1 B) →* ℂˣ) (g : Coordinate 1) (hg : g ∈ ofList 1 hq1 B) :
    charForm B (evalVec B χ) ((g⁻¹ : Coordinate 1)) = - charForm B (evalVec B χ) g := by
  have h := charForm_add_evalVec B hwf χ g g⁻¹ hg (inv_mem hg)
  rw [mul_inv_cancel, charForm_one'] at h
  linear_combination -h

/-- The reconstruction functional scales on powers. -/
theorem charForm_pow_evalVec (B : List (Coordinate 1)) (hwf : WF 1 hq1 B)
    (χ : ↥(ofList 1 hq1 B) →* ℂˣ) (g : Coordinate 1) (hg : g ∈ ofList 1 hq1 B) :
    ∀ n : ℕ, charForm B (evalVec B χ) ((g ^ n : Coordinate 1))
      = (n : ZMod 25) * charForm B (evalVec B χ) g := by
  intro n
  induction n with
  | zero => rw [pow_zero, charForm_one', Nat.cast_zero, zero_mul]
  | succ n ih =>
      rw [pow_succ, charForm_add_evalVec B hwf χ (g ^ n) g (pow_mem hg n) hg, ih]
      push_cast; ring

/-- Repackaging: the semantic power/commutator conditions imply the Boolean
`charOK` checker (the converse of `charOK_pow`/`charOK_comm`). -/
theorem charOK_of_conditions (B : List (Coordinate 1)) (e : List (ZMod 25))
    (hp : ∀ i < B.length, charForm B e (mpow 1 (B.getD i zc) 5) = 5 * e.getD i 0)
    (hc : ∀ i j, i < j → j < B.length →
        charForm B e (commutatorC (B.getD i zc) (B.getD j zc)) = 0) :
    charOK B e = true := by
  rw [charOK, Bool.and_eq_true]
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

/-- **The reconstruction vector is `charOK`-valid.** -/
theorem charOK_evalVec (B : List (Coordinate 1)) (hwf : WF 1 hq1 B)
    (χ : ↥(ofList 1 hq1 B) →* ℂˣ) : charOK B (evalVec B χ) = true := by
  apply charOK_of_conditions
  · intro i hi
    have hgmem : (B.getD i zc : Coordinate 1) ∈ ofList 1 hq1 B := by
      rw [List.getD_eq_getElem B zc hi]; exact Subgroup.subset_closure (List.getElem_mem hi)
    calc charForm B (evalVec B χ) (mpow 1 (B.getD i zc) 5)
        = charForm B (evalVec B χ) ((B.getD i zc : Coordinate 1) ^ 5) := rfl
      _ = ((5 : ℕ) : ZMod 25) * charForm B (evalVec B χ) (B.getD i zc) :=
          charForm_pow_evalVec B hwf χ (B.getD i zc) hgmem 5
      _ = ((5 : ℕ) : ZMod 25) * (evalVec B χ).getD i 0 := by
          congr 1; exact charForm_getElem B hwf (evalVec B χ) i hi
      _ = 5 * (evalVec B χ).getD i 0 := by norm_num
  · intro i j hij hj
    have hi := lt_trans hij hj
    have hgi : (B.getD i zc : Coordinate 1) ∈ ofList 1 hq1 B := by
      rw [List.getD_eq_getElem B zc hi]; exact Subgroup.subset_closure (List.getElem_mem hi)
    have hgj : (B.getD j zc : Coordinate 1) ∈ ofList 1 hq1 B := by
      rw [List.getD_eq_getElem B zc hj]; exact Subgroup.subset_closure (List.getElem_mem hj)
    change charForm B (evalVec B χ)
        (B.getD i zc * B.getD j zc * (B.getD i zc)⁻¹ * (B.getD j zc)⁻¹ : Coordinate 1) = 0
    rw [charForm_add_evalVec B hwf χ _ _ (mul_mem (mul_mem hgi hgj) (inv_mem hgi)) (inv_mem hgj),
      charForm_add_evalVec B hwf χ _ _ (mul_mem hgi hgj) (inv_mem hgi),
      charForm_add_evalVec B hwf χ _ _ hgi hgj,
      charForm_inv_evalVec B hwf χ _ hgi, charForm_inv_evalVec B hwf χ _ hgj]
    ring

/-! ## The injection and the count bound -/

/-- The reconstruction map `χ ↦ evalVec B χ` is injective (from `master_eval`). -/
theorem evalVec_injective (B : List (Coordinate 1)) (hwf : WF 1 hq1 B) :
    Function.Injective
      (evalVec B : (↥(ofList 1 hq1 B) →* ℂˣ) → List (ZMod 25)) := by
  intro χ χ' heq
  refine MonoidHom.ext fun y => ?_
  obtain ⟨x, hx⟩ := y
  rw [master_eval B hwf χ x hx, master_eval B hwf χ' x hx, heq]

/-- **Count bound.** If every reconstruction vector of `⟨B⟩` is listed in `L`,
then `|Hom(⟨B⟩, ℂˣ)| ≤ L.length`. -/
theorem card_hom_le_length (B : List (Coordinate 1)) (hwf : WF 1 hq1 B)
    (L : List (List (ZMod 25)))
    (hmem : ∀ χ : ↥(ofList 1 hq1 B) →* ℂˣ, evalVec B χ ∈ L) :
    Nat.card (↥(ofList 1 hq1 B) →* ℂˣ) ≤ L.length := by
  classical
  haveI : Fintype ↥(ofList 1 hq1 B) := Fintype.ofFinite _
  haveI : Finite (↥(ofList 1 hq1 B) →* ℂˣ) := by
    apply Nat.finite_of_card_ne_zero
    rw [LeanDring.DRing.card_charHom_eq_card_abelianization]
    haveI : Finite (Abelianization ↥(ofList 1 hq1 B)) := Quotient.finite _
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  haveI : Fintype (↥(ofList 1 hq1 B) →* ℂˣ) := Fintype.ofFinite _
  have hinj : Function.Injective (fun χ : ↥(ofList 1 hq1 B) →* ℂˣ =>
      (⟨evalVec B χ, List.mem_toFinset.mpr (hmem χ)⟩ : ↥L.toFinset)) := by
    intro a b hab
    exact evalVec_injective B hwf (Subtype.ext_iff.mp hab)
  calc Nat.card (↥(ofList 1 hq1 B) →* ℂˣ)
      = Fintype.card (↥(ofList 1 hq1 B) →* ℂˣ) := Nat.card_eq_fintype_card
    _ ≤ Fintype.card ↥L.toFinset := Fintype.card_le_of_injective _ hinj
    _ = L.toFinset.card := Fintype.card_coe _
    _ ≤ L.length := List.toFinset_card_le L

/-- **Completeness reduction.** If the certified list `charsAt r` is *exhaustive* — it
contains every `charOK`-valid vector of the right length — then the completeness
obligation `CharsAtComplete r` holds. Combined with the unconditional
`charCounts_le_card_hom`, this pins the character count. -/
theorem charsAtComplete_of_exhaustive (r : Fin 148)
    (hex : ∀ e : List (ZMod 25), charOK (basisAt r) e = true →
        e.length = (basisAt r).length → e ∈ charsAt r) :
    CharsAtComplete r := by
  change Nat.card (↥(reps r) →* ℂˣ) ≤ charCounts.getD r.val 0
  rw [← charsAt_count r,
    show Nat.card (↥(reps r) →* ℂˣ)
        = Nat.card (↥(ofList 1 hq1 (basisAt r)) →* ℂˣ) from by rw [reps_eq_ofList r]]
  apply card_hom_le_length (basisAt r) (wf_basisAt r) (charsAt r)
  intro χ
  exact hex _ (charOK_evalVec (basisAt r) (wf_basisAt r) χ)
    (evalVec_length (basisAt r) χ)

end LeanDring.P5Presentation
