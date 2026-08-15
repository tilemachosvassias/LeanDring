/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.ConjugacyClasses.Twin1.NormLink2Data
import LeanDring.P5.Certificate.ConjugacyClasses.Twin1.NormOrbits

/-!
# The orbit matrices realize genuine normalizer conjugation

The emitted conjugation matrices `normMats r` were built from the coordinate
generators of `normBasis B` — an echelon base of `N_G(reps r)` — which are not
literally the canonical inventory base `getB (normIdxData r)` that
`NormCard.lean` identifies as the normalizer. Here the matrices are certified
against **their own** generating set `normGens r`, and that set is shown to
generate `N_G(reps r)`.

## The four kernel certificates (whole-range, one `decide` each)

* `normGenMemCheck_all` — every `n ∈ normGens r` lies in `N_G(reps r)`;
* `normGenWfCheck_all`  — `normGens r` is a well-formed echelon base;
* `normGenLenCheck_all` — its length equals that of the certified normalizer base;
* `normRealizeCheck_all` — `normMats r = (normGens r).map (conjMatrixL2 B)`.

The bases are small and the matrices are `ZMod 25` micro-matrices, so all four
whole-range `decide`s fit comfortably in this one file.

## Semantic layer

* `normGens_generate` — `⟨normGens r⟩ = N_G(reps r)`. (a) membership gives
  `⟨normGens r⟩ ≤ N`; (b)+(c) give `|⟨normGens r⟩| = 5^len = |N|`; equal order +
  `≤` ⟹ equality (`Subgroup.eq_of_le_of_card_ge`), then `normAt_eq_final`. So
  `normGens r` genuinely generates the normalizer.
* `normMats_realize` — the per-entry realization
  `(normMats r)[j][i] = expVec_B (nⱼ⁻¹ · gᵢ · nⱼ)` with `nⱼ = (normGens r)[j]`,
  `gᵢ = (basisAt r)[i]`, `B = basisAt r`. Orientation: `n⁻¹ g n`.
* `orbit_semantically_closed` — every `MatReach`-connected pair `e, e'` (a word
  `w` of matrix steps carrying `e` to `e'`) is realized by a genuine normalizer
  element: the product `n = ∏ₖ (normGens r)[k]` lies in `N_G(reps r)` and the
  matrix-step transport takes `e` to `e'`. Purely vector-level (no
  `CharPairClass`, no `CharExtendsAt`).
-/

namespace LeanDring.P5Presentation

open Fin.NatCast

set_option maxRecDepth 100000
-- file-level maxHeartbeats: dozens of decide-heavy declarations below need it
set_option linter.style.setOption false
set_option maxHeartbeats 4000000

/-! ## The four whole-range kernel certificates -/

/-- **(a)** Every `normGens r` element sifts into the certified normalizer base. -/
theorem normGenMemCheck_all : (List.range 148).all normGenMemCheck = true := by decide

/-- **(b)** Every `normGens r` is a well-formed echelon base. -/
theorem normGenWfCheck_all : (List.range 148).all normGenWfCheck = true := by decide

/-- **(c)** `normGens r` and the certified normalizer base have equal length. -/
theorem normGenLenCheck_all : (List.range 148).all normGenLenCheck = true := by decide

/-- **(d)** The emitted matrices are the conjugation matrices of `normGens r`. -/
theorem normRealizeCheck_all : (List.range 148).all normRealizeCheck = true := by decide

/-! ## Per-representative fact extraction -/

/-- Membership: each `n ∈ normGens r` sifts into `getB (normIdxData r)`. -/
theorem normGenMem_at (r : Fin 148) {g : Coordinate 1} (hg : g ∈ normGens.getD r.val []) :
    siftB 1 (getB (normIdxData.getD r.val 0)) g = true := by
  have h := (List.all_eq_true.mp normGenMemCheck_all) r.val (List.mem_range.mpr r.isLt)
  simp only [normGenMemCheck, List.all_eq_true] at h
  exact h g hg

/-- Well-formedness of `normGens r` as a semantic `WF` predicate. -/
theorem normGenWf_at (r : Fin 148) : WF 1 hq1 (normGens.getD r.val []) := by
  have h := (List.all_eq_true.mp normGenWfCheck_all) r.val (List.mem_range.mpr r.isLt)
  simp only [normGenWfCheck] at h
  exact wf_of_wfB' hq1 _ h

/-- Order match: `normGens r` and the certified normalizer base have equal length. -/
theorem normGenLen_at (r : Fin 148) :
    (normGens.getD r.val []).length = (getB (normIdxData.getD r.val 0)).length := by
  have h := (List.all_eq_true.mp normGenLenCheck_all) r.val (List.mem_range.mpr r.isLt)
  simp only [normGenLenCheck] at h
  exact Nat.eq_of_beq_eq_true h

/-- Realization (matrix form): the emitted matrices are exactly the conjugation
matrices of `normGens r`'s elements on `B = getB (classRepsData r)`. -/
theorem normRealize_at (r : Fin 148) :
    normMats.getD r.val [] =
      (normGens.getD r.val []).map (conjMatrixL2 (getB (classRepsData.getD r.val 0))) := by
  have h := (List.all_eq_true.mp normRealizeCheck_all) r.val (List.mem_range.mpr r.isLt)
  simp only [normRealizeCheck, decide_eq_true_eq] at h
  exact h

/-! ## Generation certificate: `normGens r` presents `N_G(reps r)` -/

/-- **Generation.** The emitted coordinate generators `normGens r` genuinely
generate the normalizer `N_G(reps r)`. Any generating set of `N` defines the
same conjugation orbits, so certifying the matrices against `normGens r`
(rather than the canonical inventory base) is enough. -/
theorem normGens_generate (r : Fin 148) :
    ofList 1 hq1 (normGens.getD r.val []) =
      Subgroup.normalizer ((reps r : Subgroup (Coordinate 1)) : Set (Coordinate 1)) := by
  have hlt : normIdxData.getD r.val 0 < 676 := normIdxData_lt r
  have hle : ofList 1 hq1 (normGens.getD r.val []) ≤ subAt (normIdxData.getD r.val 0) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    exact (siftB_getB_iff hlt g).mp (normGenMem_at r hg)
  have hcardG : Nat.card (ofList 1 hq1 (normGens.getD r.val []))
      = 5 ^ (normGens.getD r.val []).length := card_ofList hq1 _ (normGenWf_at r)
  have hcardN : Nat.card (subAt (normIdxData.getD r.val 0))
      = 5 ^ (getB (normIdxData.getD r.val 0)).length := card_subAt hlt
  have heq : ofList 1 hq1 (normGens.getD r.val []) = subAt (normIdxData.getD r.val 0) := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcardG, hcardN, normGenLen_at r]
  rw [heq]
  exact normAt_eq_final r

/-! ## The per-entry realization on the character basis -/

/-- **Realization (per entry).** With `B = basisAt r`, `nⱼ = (normGens r)[j]`,
`gᵢ = B[i]`, the `(j,i)` entry of the emitted matrices is the `B`-exponent vector
of `nⱼ⁻¹ · gᵢ · nⱼ`. This is the sift/`expVec` step that pins the matrices to
genuine conjugation by the (now certified, `normGens_generate`) normalizer
generators. Orientation: `n⁻¹ g n`. -/
theorem normMats_realize (r : Fin 148) {j i : Nat}
    (hj : j < (normGens.getD r.val []).length) (hi : i < (basisAt r).length) :
    ((normMats.getD r.val []).getD j []).getD i [] =
      expVec (basisAt r)
        (conjC 1 (invC 1 ((normGens.getD r.val []).getD j zc)) ((basisAt r).getD i zc)) := by
  set B := getB (classRepsData.getD r.val 0) with hB
  have hbas : basisAt r = B := basisAt_eq r
  set n := (normGens.getD r.val []).getD j zc with hn
  -- outer index j: pull the j-th matrix out of the map
  have hjlen : j < (List.map (conjMatrixL2 B) (normGens.getD r.val [])).length := by
    rwa [List.length_map]
  have step1 : (normMats.getD r.val []).getD j [] = conjMatrixL2 B n := by
    rw [normRealize_at r,
      List.getD_eq_getElem _ [] hjlen,
      ← List.getD_eq_getElem _ (conjMatrixL2 B zc) hjlen,
      List.getD_map]
  -- inner index i: pull the i-th row out of `conjMatrixL2 B n = B.map (…)`
  have hiB : i < B.length := by rwa [hbas] at hi
  have hilen : i < (List.map (fun gi => expVec B (conjC 1 (invC 1 n) gi)) B).length := by
    rwa [List.length_map]
  rw [step1]
  change (List.map (fun gi => expVec B (conjC 1 (invC 1 n) gi)) B).getD i [] = _
  rw [List.getD_eq_getElem _ [] hilen,
    ← List.getD_eq_getElem _ (expVec B (conjC 1 (invC 1 n) zc)) hilen,
    List.getD_map, hbas]

/-! ## Semantic closure of the matrix orbits under genuine normalizer elements -/

/-- The `k`-th generator of `normGens r`, typed in the group `Coordinate 1`
(out-of-range index defaults to the identity). -/
def normGenAt (r k : Nat) : Coordinate 1 := (normGens.getD r []).getD k (0, 0, 0, 0, 0)

/-- Any `normGenAt r k` (default the identity) lands in `N_G(reps r)`. -/
theorem normGen_getD_mem (r : Fin 148) (k : Nat) :
    (normGenAt r.val k) ∈
      Subgroup.normalizer ((reps r : Subgroup (Coordinate 1)) : Set (Coordinate 1)) := by
  rw [← normGens_generate r, normGenAt]
  by_cases hk : k < (normGens.getD r.val []).length
  · rw [List.getD_eq_getElem _ _ hk]
    exact Subgroup.subset_closure (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ (Nat.not_lt.mp hk)]
    exact Subgroup.one_mem _

/-- The `normGens r`-product of any index word lands in `N_G(reps r)`. -/
theorem foldl_normGen_mem (r : Fin 148) (w : List Nat) :
    w.foldl (fun acc k => acc * normGenAt r.val k) (1 : Coordinate 1) ∈
      Subgroup.normalizer ((reps r : Subgroup (Coordinate 1)) : Set (Coordinate 1)) := by
  set N := Subgroup.normalizer ((reps r : Subgroup (Coordinate 1)) : Set (Coordinate 1)) with hN
  suffices H : ∀ acc : Coordinate 1, acc ∈ N →
      w.foldl (fun acc k => acc * normGenAt r.val k) acc ∈ N by
    exact H 1 (Subgroup.one_mem N)
  induction w with
  | nil => intro acc hacc; exact hacc
  | cons k rest ih =>
      intro acc hacc
      simp only [List.foldl_cons]
      exact ih _ (N.mul_mem hacc (normGen_getD_mem r k))

/-- **Orbit closure, semantically.** Whenever the emitted matrix action carries a
character-exponent vector `e` of rep `r` to `e'` (`MatReach` — a word `w` of
per-generator matrix steps), the transport is realized by a genuine element of
`N_G(reps r)`: the ordered product `n = ∏ₖ (normGens r)[k]` over `w`. This
grounds the whole `N`-orbit partition of `NormOrbits.lean` in honest normalizer
conjugation, at the vector level. -/
theorem orbit_semantically_closed (r : Fin 148) {e e' : List (ZMod 25)}
    (h : MatReach r.val e e') :
    ∃ (w : List Nat) (n : Coordinate 1),
      n ∈ Subgroup.normalizer ((reps r : Subgroup (Coordinate 1)) : Set (Coordinate 1)) ∧
      n = w.foldl (fun acc k => acc * normGenAt r.val k) (1 : Coordinate 1) ∧
      w.foldl (fun x k => genAct r.val k x) e = e' := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, _, foldl_normGen_mem r w, rfl, hw⟩

end LeanDring.P5Presentation
