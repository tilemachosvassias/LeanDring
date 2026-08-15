/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin1.CharExhaust

/-!
# Completeness of the certified enumeration by a row-combination certificate (`k ≥ 4`)

The `k ≤ 3` classes are discharged by brute `decide` over `25^k` exponent vectors
(`LeanDring.P5.Certificate.Characters.Twin1.CharComplete` and its `Chunk01`–
`Chunk08` submodules). For `k ≥ 4` that enumeration is infeasible in the kernel, so
we instead bound the *solution count* directly by linear algebra over `ZMod 25`.

The `charOK`-valid vectors of `reps r` are the solutions of the homogeneous
`ZMod 25` linear system `charOKrows` (power rows `PR i · e = 5 eᵢ`, commutator rows
`CR · e = 0`). Rewriting each power relation as `(PR i − 5 δᵢ) · e = 0`, the whole
system is `row · e = 0` for `row` ranging over `constraintRows`. For every
coordinate `j` we supply (compiled-emitted, untrusted) integer coefficients
`coeffs` with `Σ coeffsₜ · rowₜ = m · δⱼ` — a small kernel `decide` — whence
`m · eⱼ = 0`. The resulting per-coordinate annihilator constraints confine every
solution to an explicit product "box" of size `∏ |annVals mⱼ| = charCounts r`, and
`card_hom_le_length` turns that into `|Hom(reps r, ℂˣ)| ≤ charCounts r`, i.e.
`CharsAtComplete r`. No `25^k` enumeration, no `native_decide`.
-/

namespace LeanDring.P5Presentation

open Fin.NatCast

set_option maxRecDepth 100000

private theorem dotZ_cons (a : ZMod 25) (e : List (ZMod 25)) (b : ZMod 25) (v : List (ZMod 25)) :
    dotZ (a :: e) (b :: v) = a * b + dotZ e v := by simp [dotZ]

/-! ## `dotZ` is linear in its second argument -/

/-- Add two `ZMod 25` vectors coordinatewise. -/
def vAdd (u v : List (ZMod 25)) : List (ZMod 25) := List.zipWith (· + ·) u v

/-- Scale a `ZMod 25` vector. -/
def vScale (a : ZMod 25) (v : List (ZMod 25)) : List (ZMod 25) := v.map (a * ·)

/-- Subtract two `ZMod 25` vectors coordinatewise. -/
def vSub (u v : List (ZMod 25)) : List (ZMod 25) := List.zipWith (· - ·) u v

private theorem dotZ_vAdd (e : List (ZMod 25)) :
    ∀ u v : List (ZMod 25), u.length = v.length →
      dotZ e (vAdd u v) = dotZ e u + dotZ e v := by
  induction e with
  | nil => intro u v _; simp [dotZ, vAdd]
  | cons a e ih =>
      intro u v huv
      match u, v, huv with
      | [], [], _ => simp [dotZ, vAdd]
      | b :: u, c :: v, huv =>
          have huv' : u.length = v.length := by simpa using huv
          simp only [vAdd, List.zipWith_cons_cons, dotZ_cons] at *
          rw [ih u v huv']
          ring

private theorem dotZ_vScale (e : List (ZMod 25)) :
    ∀ v : List (ZMod 25), dotZ e (vScale a v) = a * dotZ e v := by
  induction e with
  | nil => intro v; simp [dotZ, vScale]
  | cons x e ih =>
      intro v
      match v with
      | [] => simp [dotZ, vScale]
      | b :: v =>
          simp only [vScale, List.map_cons, dotZ_cons]
          have hih := ih v
          simp only [vScale] at hih
          rw [hih]; ring

private theorem dotZ_vSub (e : List (ZMod 25)) :
    ∀ u v : List (ZMod 25), u.length = v.length →
      dotZ e (vSub u v) = dotZ e u - dotZ e v := by
  induction e with
  | nil => intro u v _; simp [dotZ, vSub]
  | cons a e ih =>
      intro u v huv
      match u, v, huv with
      | [], [], _ => simp [dotZ, vSub]
      | b :: u, c :: v, huv =>
          have huv' : u.length = v.length := by simpa using huv
          simp only [vSub, List.zipWith_cons_cons, dotZ_cons] at *
          rw [ih u v huv']
          ring

/-! ## Standard scaled basis covectors -/

/-- `stdRow k j m = m · δⱼ` as a length-`k` vector (`m` at position `j`, else `0`). -/
def stdRow : ℕ → ℕ → ZMod 25 → List (ZMod 25)
  | 0, _, _ => []
  | k + 1, 0, m => m :: List.replicate k 0
  | k + 1, j + 1, m => 0 :: stdRow k j m

theorem stdRow_length (k j : ℕ) (m : ZMod 25) : (stdRow k j m).length = k := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
      cases j with
      | zero => simp [stdRow]
      | succ j => simp only [stdRow, List.length_cons, ih j]

private theorem dotZ_replicate_zero (e : List (ZMod 25)) (n : ℕ) :
    dotZ e (List.replicate n 0) = 0 := by
  induction e generalizing n with
  | nil => simp [dotZ]
  | cons a e ih =>
      cases n with
      | zero => simp [dotZ]
      | succ n => simp only [List.replicate_succ, dotZ_cons, mul_zero, zero_add]; exact ih n

/-- `dotZ e (m · δⱼ) = m · eⱼ`. -/
theorem dotZ_stdRow : ∀ (k j : ℕ) (e : List (ZMod 25)) (m : ZMod 25),
    e.length = k → j < k → dotZ e (stdRow k j m) = m * e.getD j 0 := by
  intro k
  induction k with
  | zero => intro j e m _ hj; omega
  | succ k ih =>
      intro j e m hlen hj
      match e, hlen with
      | a :: e, hlen =>
          cases j with
          | zero =>
              simp only [stdRow, dotZ_cons, dotZ_replicate_zero, add_zero, List.getD_cons_zero]
              ring
          | succ j =>
              simp only [stdRow, dotZ_cons, mul_zero, zero_add, List.getD_cons_succ]
              exact ih j e m (by simpa using hlen) (by omega)

/-! ## Linear combinations of the constraint rows vanish on solutions -/

private theorem vScale_length (a : ZMod 25) (v : List (ZMod 25)) :
    (vScale a v).length = v.length := by simp [vScale]

/-- `Σ coeffsₜ · rowₜ` (coordinatewise), as a length-`k` vector. -/
def linComb (k : ℕ) : List (ZMod 25) → List (List (ZMod 25)) → List (ZMod 25)
  | [], _ => List.replicate k 0
  | _, [] => List.replicate k 0
  | c :: cs, row :: rs => vAdd (vScale c row) (linComb k cs rs)

private theorem linComb_length (k : ℕ) :
    ∀ (coeffs : List (ZMod 25)) (rows : List (List (ZMod 25))),
      (∀ w ∈ rows, w.length = k) → (linComb k coeffs rows).length = k := by
  intro coeffs
  induction coeffs with
  | nil => intro rows _; simp [linComb]
  | cons c cs ih =>
      intro rows hrows
      match rows with
      | [] => simp [linComb]
      | row :: rs =>
          have hrow : row.length = k := hrows row (List.mem_cons_self ..)
          have hrest : (linComb k cs rs).length = k :=
            ih rs (fun w hw => hrows w (List.mem_cons_of_mem _ hw))
          simp only [linComb, vAdd, List.length_zipWith, vScale_length, hrow, hrest, Nat.min_self]

/-- If `e` annihilates every constraint row, it annihilates every combination. -/
theorem dotZ_linComb_zero (e : List (ZMod 25)) (k : ℕ) :
    ∀ (coeffs : List (ZMod 25)) (rows : List (List (ZMod 25))),
      (∀ w ∈ rows, w.length = k) → (∀ w ∈ rows, dotZ e w = 0) →
        dotZ e (linComb k coeffs rows) = 0 := by
  intro coeffs
  induction coeffs with
  | nil => intro rows _ _; simp [linComb, dotZ_replicate_zero]
  | cons c cs ih =>
      intro rows hrows hz
      match rows with
      | [] => simp [linComb, dotZ_replicate_zero]
      | row :: rs =>
          have hrow : row.length = k := hrows row (List.mem_cons_self ..)
          have hrestlen : (linComb k cs rs).length = k :=
            linComb_length k cs rs (fun w hw => hrows w (List.mem_cons_of_mem _ hw))
          simp only [linComb]
          rw [dotZ_vAdd e _ _ (by rw [vScale_length, hrow, hrestlen]),
            dotZ_vScale, hz row (List.mem_cons_self ..), mul_zero, zero_add,
            ih rs (fun w hw => hrows w (List.mem_cons_of_mem _ hw))
               (fun w hw => hz w (List.mem_cons_of_mem _ hw))]

/-! ## The constraint rows of a representative -/

/-- Homogeneous constraint rows of the `charOKrows` system: the power rows shifted
by `−5 δᵢ`, followed by the commutator rows. A solution `e` of `charOKrows PR CR`
annihilates every one of them. -/
def constraintRows (PR CR : List (List (ZMod 25))) (k : ℕ) : List (List (ZMod 25)) :=
  (List.range PR.length).map (fun i => vSub (PR.getD i []) (stdRow k i 5)) ++ CR

/-- Every constraint row is annihilated by a `charOKrows`-solution `e`. -/
theorem constraints_zero (PR CR : List (List (ZMod 25))) (e : List (ZMod 25))
    (k : ℕ) (hk : k = PR.length) (hlen : e.length = k)
    (hpr : ∀ i < PR.length, (PR.getD i []).length = k)
    (hOK : charOKrows PR CR e = true) :
    ∀ w ∈ constraintRows PR CR k, dotZ e w = 0 := by
  rw [charOKrows, Bool.and_eq_true] at hOK
  obtain ⟨hpow, hcom⟩ := hOK
  rw [List.all_eq_true] at hpow hcom
  intro w hw
  rw [constraintRows, List.mem_append] at hw
  rcases hw with hw | hw
  · rw [List.mem_map] at hw
    obtain ⟨i, hi, rfl⟩ := hw
    rw [List.mem_range] at hi
    have hpi := hpow i (List.mem_range.mpr hi)
    rw [decide_eq_true_eq] at hpi
    rw [dotZ_vSub e _ _ (by rw [hpr i hi, stdRow_length]),
      hpi, dotZ_stdRow k i e 5 hlen (by omega)]
    ring
  · have := hcom w hw
    rwa [decide_eq_true_eq] at this

/-! ## The solution "box" and its enumeration -/

/-- The `ZMod 25` values annihilated by `m` (`{0}` if `m` is a unit, `5·ℤ/25` if
`m = 5`, all of `ZMod 25` if `m = 0`). -/
def annVals (m : ZMod 25) : List (ZMod 25) := zmodAll.filter (fun x => decide (m * x = 0))

theorem mem_annVals {m x : ZMod 25} (h : m * x = 0) : x ∈ annVals m := by
  rw [annVals, List.mem_filter]
  exact ⟨mem_zmodAll x, by simp [h]⟩

/-- Enumerate the product box `∏ⱼ annVals multsⱼ` of exponent vectors. -/
def boxVecs : List (ZMod 25) → List (List (ZMod 25))
  | [] => [[]]
  | m :: ms => (annVals m).flatMap (fun a => (boxVecs ms).map (fun v => a :: v))

/-- Every vector whose `j`-th entry is annihilated by `multsⱼ` lies in the box. -/
theorem mem_boxVecs : ∀ (mults e : List (ZMod 25)), e.length = mults.length →
    (∀ j, j < mults.length → mults.getD j 0 * e.getD j 0 = 0) → e ∈ boxVecs mults := by
  intro mults
  induction mults with
  | nil =>
      intro e hlen _
      have he0 : e = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst he0; simp [boxVecs]
  | cons m ms ih =>
      intro e hlen hcoord
      match e, hlen with
      | a :: e, hlen =>
          have hlen' : e.length = ms.length := by simpa using hlen
          have ha : m * a = 0 := by have := hcoord 0 (by simp); simpa using this
          have hrest : ∀ j, j < ms.length → ms.getD j 0 * e.getD j 0 = 0 := by
            intro j hj; have := hcoord (j + 1) (by simpa using hj); simpa using this
          rw [boxVecs, List.mem_flatMap]
          exact ⟨a, mem_annVals ha, List.mem_map.mpr ⟨e, ih e hlen' hrest, rfl⟩⟩

/-! ## The reusable per-representative discharge -/

/-- **Row-combination completeness engine.** Given per-coordinate annihilator
multipliers `mults` and integer row-combination coefficients `coeffs`, all
kernel-checked to be consistent with the embedded `charOKrows` system, the
completeness obligation `CharsAtComplete r` holds. Every hypothesis below is a
small `decide` (no `25^k` enumeration). -/
theorem charsAtComplete_of_cert (r : Fin 148) (mults : List (ZMod 25))
    (coeffs : List (List (ZMod 25)))
    (hml : mults.length = (repPR.getD r.val []).length)
    (hbl : (basisAt r).length = (repPR.getD r.val []).length)
    (hcount : (boxVecs mults).length = charCounts.getD r.val 0)
    (hrowlen : (constraintRows (repPR.getD r.val []) (repCR.getD r.val []) mults.length).all
        (fun w => decide (w.length = mults.length)) = true)
    (hpr : (List.range (repPR.getD r.val []).length).all
        (fun i => decide (((repPR.getD r.val []).getD i []).length = mults.length)) = true)
    (hcert : (List.range mults.length).all (fun j =>
        decide (linComb mults.length (coeffs.getD j [])
          (constraintRows (repPR.getD r.val []) (repCR.getD r.val []) mults.length)
          = stdRow mults.length j (mults.getD j 0))) = true) :
    CharsAtComplete r := by
  change Nat.card (↥(reps r) →* ℂˣ) ≤ charCounts.getD r.val 0
  rw [← hcount,
    show Nat.card (↥(reps r) →* ℂˣ)
        = Nat.card (↥(ofList 1 hq1 (basisAt r)) →* ℂˣ) from by rw [reps_eq_ofList r]]
  apply card_hom_le_length (basisAt r) (wf_basisAt r) (boxVecs mults)
  intro χ
  set e := evalVec (basisAt r) χ with he
  -- bridge `charOK` to the embedded `charOKrows` system
  have hrows := checker_at checkRows_all r
  simp only [checkRows, Bool.and_eq_true, decide_eq_true_eq] at hrows
  obtain ⟨hPR, hCR⟩ := hrows
  have hOKrows : charOKrows (repPR.getD r.val []) (repCR.getD r.val []) e = true := by
    rw [hPR, hCR]
    exact (charOKrows_iff (basisAt r) e).mpr (charOK_evalVec (basisAt r) (wf_basisAt r) χ)
  have helen : e.length = mults.length := by
    rw [he, evalVec_length]; exact hbl.trans hml.symm
  -- unpack the small decides
  have hpr' : ∀ i < (repPR.getD r.val []).length,
      ((repPR.getD r.val []).getD i []).length = mults.length := by
    intro i hi
    have := (List.all_eq_true.mp hpr) i (List.mem_range.mpr hi)
    rwa [decide_eq_true_eq] at this
  have hrowlen' : ∀ w ∈ constraintRows (repPR.getD r.val []) (repCR.getD r.val []) mults.length,
      w.length = mults.length := by
    intro w hw
    have := (List.all_eq_true.mp hrowlen) w hw
    rwa [decide_eq_true_eq] at this
  have hzero := constraints_zero (repPR.getD r.val []) (repCR.getD r.val []) e mults.length
    hml (helen) hpr' hOKrows
  -- confine `e` to the box
  apply mem_boxVecs mults e helen
  intro j hj
  have hcertj : linComb mults.length (coeffs.getD j [])
      (constraintRows (repPR.getD r.val []) (repCR.getD r.val []) mults.length)
      = stdRow mults.length j (mults.getD j 0) := by
    have := (List.all_eq_true.mp hcert) j (List.mem_range.mpr hj)
    rwa [decide_eq_true_eq] at this
  have hcomb := dotZ_linComb_zero e mults.length (coeffs.getD j [])
    (constraintRows (repPR.getD r.val []) (repCR.getD r.val []) mults.length) hrowlen' hzero
  rw [hcertj, dotZ_stdRow mults.length j e (mults.getD j 0) helen hj] at hcomb
  exact hcomb

end LeanDring.P5Presentation
