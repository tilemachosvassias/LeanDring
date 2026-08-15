/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.ConjugacyClasses.Twin1.ConjClasses
import LeanDring.Theory.DRing.BridgeCounts
import LeanDring.P5.Certificate.ConjugacyClasses.Twin1.NormOrbitData

/-!
# The normalizer-card bridge: the emitted normalizer index is `N_G(reps r)`

The emitted index `normIdxData r` is untrusted data. This file proves that the
subgroup it names really is the normalizer `N_G(reps r)` of the `r`-th
subgroup-class representative.

## The per-class squeeze (the reusable normalizer-card lemma)

* `card_subtype_fin_eq` / `finRange_map_classOfData` / `conjIdxCount` /
  `card_classIdx` — bridge the abstract `Nat.card` of a `Fin 676` class-index
  subtype to the certified data count `classSizeNat`.
* `conjSub_iff_markClass` — subgroup conjugacy (`conjSub`) is exactly mark-class
  equality (`⟦⟨·,1⟩⟧`), tying the certified index action to the abstract
  `card_conjClass_mul`.
* `conj_iff_classOf` / `markClass_reps_iff` — conjugacy of inventory subgroups is
  detected by the certified class label.
* `card_conjClass_reps` — **the squeeze, proven once**: the `G`-conjugacy class of
  `reps r` has exactly `classSizeNat r` members.
* `normalizer_card_pin` — hence `classSizeNat r · |N_G(reps r)| = 3125`
  (`card_conjClass_mul` specialised, with `|G| = 3125`).

## Identifying the emitted index

* `normSiftCheck` / `Ncand_le_norm` — the generators of `subAt (normIdxData r)`
  normalize `reps r` (`normalizes_closure` idiom), so the candidate lies inside
  `N_G(reps r)`.
* `normCardCheck` / `normIdxCheck` — the cheap kernel checks pinning
  `5 ^ |N_cand base| · classSizeNat r = 3125` and the index range.
* `normAt_eq` / `normAt_eq_of_all` — equal order + `≤` gives equality:
  `subAt (normIdxData r) = N_G(reps r)`. The heavy whole-range sift check
  `normSiftCheck_all` is discharged in the sibling `NormLink1.lean`.

**Scope.** The emitted matrices `normMats` are *not* certified here: they were
built from the generators of `normBasis B`, which need not be the canonical
inventory base `getB (normIdxData r)` identified above, so the direct kernel
check against that base fails. They are certified against their own generating
set in `NormLink2Data.lean` / `NormLink.lean`.
-/

namespace LeanDring.P5Presentation

open Fin.NatCast
open LeanDring LeanDring.DRing LeanDring.MonGSet

set_option maxRecDepth 100000

/-- Generic: card of a `Fin n` subtype = list filter length over `finRange`. -/
theorem card_subtype_fin_eq {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    Nat.card {i : Fin n // p i} = ((List.finRange n).filter (fun i => decide (p i))).length := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter (fun i => decide (p i))),
    List.toFinset_filter, List.toFinset_finRange]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]

/-- `classOfData` reconstructed as a map over `finRange 676`. -/
theorem finRange_map_classOfData :
    (List.finRange 676).map (fun i => classOfData.getD i.val 0) = classOfData := by
  apply List.ext_getElem
  · rw [List.length_map, List.length_finRange, classOfData_length]
  · intro k h1 h2
    rw [List.getElem_map, List.getElem_finRange]
    simp only [Fin.val_cast]
    exact List.getD_eq_getElem classOfData 0 h2

/-- The filter-count of class-`c` indices equals `classOfData.count c`. -/
theorem conjIdxCount (c : ℕ) :
    ((List.finRange 676).filter (fun i => decide (classOfD i.val = c))).length
      = classOfData.count c := by
  rw [← List.countP_eq_length_filter]
  have hcomp : (fun i : Fin 676 => decide (classOfD i.val = c))
      = (fun v : ℕ => decide (v = c)) ∘ (fun i : Fin 676 => classOfData.getD i.val 0) := rfl
  rw [hcomp, ← List.countP_map, finRange_map_classOfData, List.count_eq_countP]
  apply List.countP_congr
  intro x _
  by_cases hx : x = c <;> simp [hx]

/-- **The per-class squeeze**, proven once: the number of `Fin 676` indices in
class `c` equals the data count `classSizeNat c`. -/
theorem card_classIdx (c : ℕ) :
    Nat.card {i : Fin 676 // classOfD i.val = c} = classSizeNat c := by
  rw [card_subtype_fin_eq, conjIdxCount]; rfl

/-! ## Subgroup conjugacy ↔ mark-class equality ↔ class label -/

/-- `∃ g, conjSub g A = B` iff the mark classes of `B` and `A` coincide. -/
theorem conjSub_iff_markClass (A B : Subgroup (Coordinate 1)) :
    (∃ g : Coordinate 1, conjSub g A = B) ↔
      ((⟦⟨B, 1⟩⟧ : CharPairClass (Coordinate 1) ℂˣ) = ⟦⟨A, 1⟩⟧) := by
  constructor
  · rintro ⟨g, rfl⟩
    refine markClass_eq_iff.mpr ⟨g⁻¹, fun k => ?_⟩
    simp only [conjSub, mem_map_conj_iff, inv_inv]
  · intro h
    obtain ⟨a, ha⟩ := markClass_eq_iff.mp h
    refine ⟨a⁻¹, ?_⟩
    ext k
    simp only [conjSub, mem_map_conj_iff, inv_inv]
    exact (ha k).symm

/-- Conjugacy of two inventory subgroups is detected by the class label. -/
theorem conj_iff_classOf (i j : Nat) (hi : i < 676) (hj : j < 676) :
    (∃ g : Coordinate 1, conjSub g (subAt i) = subAt j) ↔ classOfD i = classOfD j := by
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨i', hi', heq, hcls⟩ := orbit_inv g i hi
    have : i' = j := subAt_inj i' j hi' hj (heq.symm.trans hg)
    rw [this] at hcls; exact hcls.symm
  · intro hcls
    obtain ⟨g1, hg1⟩ := reach (depthData.getD i 0) i hi rfl
    obtain ⟨g2, hg2⟩ := reach (depthData.getD j 0) j hj rfl
    have hrep : repIdx i = repIdx j := by unfold repIdx; rw [hcls]
    refine ⟨g2 * g1⁻¹, ?_⟩
    have hi_eq : subAt i = conjSub g1 (subAt (repIdx i)) := hg1.symm
    rw [hi_eq, conjSub_conjSub, mul_assoc, inv_mul_cancel, mul_one, hrep, hg2]

/-- Mark class of `subAt i` matches that of `reps r` iff `i` sits in class `r`. -/
theorem markClass_reps_iff (r : Fin 148) (i : Nat) (hi : i < 676) :
    ((⟦⟨subAt i, 1⟩⟧ : CharPairClass (Coordinate 1) ℂˣ) = ⟦⟨reps r, 1⟩⟧) ↔
      classOfD i = r.val := by
  have hreprlt : classRepsData.getD r.val 0 < 676 := classReps_lt r.val r.isLt
  have hclsrepr : classOfD (classRepsData.getD r.val 0) = r.val := classOf_rep r.val r.isLt
  have hreps : reps r = subAt (classRepsData.getD r.val 0) := rfl
  rw [hreps, ← conjSub_iff_markClass (subAt (classRepsData.getD r.val 0)) (subAt i),
    conj_iff_classOf (classRepsData.getD r.val 0) i hreprlt hi, hclsrepr]
  exact eq_comm

/-! ## The conjugacy class size = certified class size, and the normalizer-card pin -/

/-- The `G`-conjugacy class of `reps r` (as mark classes) has `classSizeNat r`
members — the abstract class count equals the certified data count. -/
theorem card_conjClass_reps (r : Fin 148) :
    Nat.card {L₂ : Subgroup (Coordinate 1) //
        (⟦⟨L₂, 1⟩⟧ : CharPairClass (Coordinate 1) ℂˣ) = ⟦⟨reps r, 1⟩⟧} = classSizeNat r.val := by
  rw [← card_classIdx r.val]
  refine (Nat.card_eq_of_bijective
    (fun x : {i : Fin 676 // classOfD i.val = r.val} =>
      (⟨subAt x.1.val, (markClass_reps_iff r x.1.val x.1.isLt).mpr x.2⟩ :
        {L₂ : Subgroup (Coordinate 1) //
          (⟦⟨L₂, 1⟩⟧ : CharPairClass (Coordinate 1) ℂˣ) = ⟦⟨reps r, 1⟩⟧})) ?_).symm
  constructor
  · rintro ⟨⟨i, hi⟩, hpi⟩ ⟨⟨j, hj⟩, hpj⟩ he
    have hsub : subAt i = subAt j := congrArg Subtype.val he
    exact Subtype.ext (Fin.ext (subAt_inj i j hi hj hsub))
  · rintro ⟨L₂, hcls⟩
    obtain ⟨j, hj, hsub⟩ := exists_index_of_inInv L₂ (allSubs_complete L₂)
    have hclsj : classOfD j = r.val :=
      (markClass_reps_iff r j hj).mp (by rw [hsub]; exact hcls)
    exact ⟨⟨⟨j, hj⟩, hclsj⟩, Subtype.ext hsub⟩

theorem card_coordinate1 : Nat.card (Coordinate 1) = 3125 := by
  rw [Nat.card_eq_fintype_card]; rfl

/-- **The normalizer-card pin.** `|class| · |N_G(reps r)| = 3125`, with the class
size given by the certified data count `classSizeNat r`. -/
theorem normalizer_card_pin (r : Fin 148) :
    classSizeNat r.val *
      Nat.card (Subgroup.normalizer ((reps r : Subgroup (Coordinate 1)) : Set (Coordinate 1)))
      = 3125 := by
  have h := card_conjClass_mul (reps r)
  rw [card_conjClass_reps r, card_coordinate1] at h
  exact h

/-! ## The emitted normalizer index is genuinely `N_G(reps r)` -/

/-- Sift checker: every generator `n` of the candidate normalizer base
(and its inverse) conjugates every generator `g` of `reps r`'s base back into
`reps r`. -/
def normSiftCheck (r : Nat) : Bool :=
  let B := getB (classRepsData.getD r 0)
  let Nb := getB (normIdxData.getD r 0)
  Nb.all (fun n => B.all (fun g =>
    siftB 1 B (conjC 1 n g) && siftB 1 B (conjC 1 (invC 1 n) g)))

/-- Extract the two sift facts for a `(n, g)` pair. -/
theorem normSift_at (r : Fin 148) (hsift : normSiftCheck r.val = true)
    {n : Coordinate 1} (hn : n ∈ getB (normIdxData.getD r.val 0))
    {g : Coordinate 1} (hg : g ∈ getB (classRepsData.getD r.val 0)) :
    siftB 1 (getB (classRepsData.getD r.val 0)) (conjC 1 n g) = true ∧
      siftB 1 (getB (classRepsData.getD r.val 0)) (conjC 1 (invC 1 n) g) = true := by
  simp only [normSiftCheck] at hsift
  have h2 := (List.all_eq_true.mp ((List.all_eq_true.mp hsift) n hn)) g hg
  rwa [Bool.and_eq_true] at h2

/-- **The `≤` direction.** The candidate normalizer base sits inside the true
normalizer of `reps r`. -/
theorem Ncand_le_norm (r : Fin 148) (hsift : normSiftCheck r.val = true) :
    subAt (normIdxData.getD r.val 0) ≤
      Subgroup.normalizer ((reps r : Subgroup (Coordinate 1)) : Set (Coordinate 1)) := by
  have hreplt : classRepsData.getD r.val 0 < 676 := classReps_lt r.val r.isLt
  rw [subAt_eq_closure]
  refine (Subgroup.closure_le _).mpr ?_
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  have hrepclo : (reps r : Subgroup (Coordinate 1))
      = Subgroup.closure {x : Coordinate 1 | x ∈ getB (classRepsData.getD r.val 0)} := by
    rw [show (reps r : Subgroup (Coordinate 1)) = subAt (classRepsData.getD r.val 0) from rfl,
      subAt_eq_closure]
  rw [SetLike.mem_coe, hrepclo]
  apply normalizes_closure hq1 n {x : Coordinate 1 | x ∈ getB (classRepsData.getD r.val 0)}
  · intro g hg
    have hs := (normSift_at r hsift hn hg).1
    have hmem := (siftB_getB_iff hreplt (conjC 1 n g)).mp hs
    rwa [conjC_eq hq1 n g] at hmem
  · intro g hg
    have hs := (normSift_at r hsift hn hg).2
    have hmem := (siftB_getB_iff hreplt (conjC 1 (invC 1 n) g)).mp hs
    rw [conjC_eq hq1 (invC 1 n) g, show invC 1 n = n⁻¹ from rfl, inv_inv] at hmem
    exact hmem

/-- **Identification.** The emitted normalizer index `normIdxData r` presents
exactly `N_G(reps r)`. -/
theorem normAt_eq (r : Fin 148) (hsift : normSiftCheck r.val = true)
    (hlt : normIdxData.getD r.val 0 < 676)
    (hcard : 5 ^ (getB (normIdxData.getD r.val 0)).length * classSizeNat r.val = 3125) :
    subAt (normIdxData.getD r.val 0) =
      Subgroup.normalizer ((reps r : Subgroup (Coordinate 1)) : Set (Coordinate 1)) := by
  have hle := Ncand_le_norm r hsift
  have hcs : 0 < classSizeNat r.val := by
    rcases Nat.eq_zero_or_pos (classSizeNat r.val) with h | h
    · rw [h, Nat.mul_zero] at hcard; exact absurd hcard (by norm_num)
    · exact h
  have hpin := normalizer_card_pin r
  have hNcard : Nat.card
      (Subgroup.normalizer ((reps r : Subgroup (Coordinate 1)) : Set (Coordinate 1)))
      = 5 ^ (getB (normIdxData.getD r.val 0)).length := by
    have : classSizeNat r.val *
        Nat.card (Subgroup.normalizer ((reps r : Subgroup (Coordinate 1)) : Set (Coordinate 1)))
        = classSizeNat r.val * 5 ^ (getB (normIdxData.getD r.val 0)).length := by
      rw [hpin, mul_comm (classSizeNat r.val), hcard]
    exact (Nat.eq_of_mul_eq_mul_left hcs this)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hNcard, card_subAt hlt]

/-! ## Cheap kernel checks: normalizer index range and the card identity -/

/-- `normIdxData r` is an in-range inventory index. -/
def normIdxCheck (r : Nat) : Bool := Nat.blt (normIdxData.getD r 0) 676

/-- The card identity `5 ^ |N_cand base| · |class r| = 3125`. -/
def normCardCheck (r : Nat) : Bool :=
  Nat.beq (5 ^ (getB (normIdxData.getD r 0)).length * classSizeNat r) 3125

theorem normIdxCheck_all : (List.range 148).all normIdxCheck = true := by decide
theorem normCardCheck_all : (List.range 148).all normCardCheck = true := by decide

theorem normIdxData_lt (r : Fin 148) : normIdxData.getD r.val 0 < 676 := by
  have := (List.all_eq_true.mp normIdxCheck_all) r.val (List.mem_range.mpr r.isLt)
  simpa only [normIdxCheck, Nat.blt_eq] using this

theorem normCard_id (r : Fin 148) :
    5 ^ (getB (normIdxData.getD r.val 0)).length * classSizeNat r.val = 3125 := by
  have := (List.all_eq_true.mp normCardCheck_all) r.val (List.mem_range.mpr r.isLt)
  simpa only [normCardCheck, Nat.beq_eq] using this

/-- **Identification, unconditional (relative to the sift certificate).** Given the
whole-range sift check, the emitted index presents exactly `N_G(reps r)`. -/
theorem normAt_eq_of_all (hsiftAll : (List.range 148).all normSiftCheck = true) (r : Fin 148) :
    subAt (normIdxData.getD r.val 0) =
      Subgroup.normalizer ((reps r : Subgroup (Coordinate 1)) : Set (Coordinate 1)) :=
  normAt_eq r ((List.all_eq_true.mp hsiftAll) r.val (List.mem_range.mpr r.isLt))
    (normIdxData_lt r) (normCard_id r)

end LeanDring.P5Presentation
