/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.ConjData
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.ConjR.Chunk01
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.ConjR.Chunk02
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.ConjR.Chunk03
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.ConjR.Chunk04
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.ConjR.Chunk05
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.ConjAux
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.ConjTree
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.ConjBound
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.ConjCount

/-!
# The 148 subgroup conjugacy classes of `Coordinate 2` (conjugacy classes, twin q=2)

Building on the completed subgroup inventory (`allSubs_complete` — the 676-subgroup inventory is
complete), this file certifies the **conjugation action** on that inventory as a
kernel-checked index action, and derives the classification of subgroups up to
conjugacy:

* `conjSub g H = H.map (MulAut.conj g)` — conjugation of a subgroup;
* `move_correct` — for each standard generator `g_k` and index `i`,
  `conjSub g_k (subAt i) = subAt (conjMove k i)`, in range and class-preserving
  (kernel-checked in `Conj2R/Chunk01.lean`–`Conj2R/Chunk05.lean` and `ConjAux.lean`);
* `orbit_inv` — conjugation by **any** group element preserves the class label
  `classOf` (word-induction over the five generators, closed under inverse via
  completeness);
* `reps : Fin 148 → Subgroup (Coordinate 2)` and:
  * `reps_complete` — every subgroup is conjugate to some `reps r`;
  * `reps_pairwise_nonconj` — distinct `reps` are non-conjugate;
  * `classSize_sum` — the class sizes sum to `676`;
  * `reps_normal_iff` / `normal_count` — a class is a singleton iff its
    representative is normal, and there are exactly `71` normal subgroups.

All data is untrusted output of the compiled generator, re-checked by kernel
`decide` (split across sibling files to keep each process' memory bounded) — no
`native_decide`, no `sorry`, no new axioms. GAP reference: 148 classes, 71
normal — identical twin statistics to q=1.
-/

namespace LeanDring.P5Presentation

namespace Q2

open Fin.NatCast

set_option maxRecDepth 100000
-- file-level maxHeartbeats: dozens of decide-heavy declarations below need it
set_option linter.style.setOption false
set_option maxHeartbeats 4000000

/-! ## Conjugation of subgroups -/

/-- Conjugation of a subgroup by `g`, as `H ↦ g H g⁻¹`. -/
def conjSub (g : Coordinate 2) (H : Subgroup (Coordinate 2)) : Subgroup (Coordinate 2) :=
  H.map (MulAut.conj g).toMonoidHom

theorem conjSub_one (H : Subgroup (Coordinate 2)) : conjSub 1 H = H := by
  unfold conjSub
  rw [show ((MulAut.conj (1 : Coordinate 2)).toMonoidHom) = MonoidHom.id (Coordinate 2) by
        ext x; simp, Subgroup.map_id]

theorem conjSub_conjSub (a b : Coordinate 2) (H : Subgroup (Coordinate 2)) :
    conjSub a (conjSub b H) = conjSub (a * b) H := by
  unfold conjSub
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_assoc,
    mul_inv_rev]

theorem card_conjSub (g : Coordinate 2) (H : Subgroup (Coordinate 2)) :
    Nat.card (conjSub g H) = Nat.card H := by
  unfold conjSub
  exact (Nat.card_congr
    (Subgroup.equivMapOfInjective H (MulAut.conj g).toMonoidHom
      (EquivLike.injective (MulAut.conj g))).toEquiv).symm

/-- Conjugation of an element, spelled to match the computable `conjC`. -/
theorem conjSub_hom_apply (g x : Coordinate 2) :
    (MulAut.conj g).toMonoidHom x = conjC 2 g x := by
  rw [conjC_eq hq2 g x, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem conjSub_eq_map_conj (g : Coordinate 2) (H : Subgroup (Coordinate 2)) :
    conjSub g H = H.map (MulAut.conj g) := rfl

/-! ## The five standard generators generate `⊤` -/

/-- The five standard generators as a list. -/
def gksList : List (Coordinate 2) :=
  [(1,0,0,0,0), (0,1,0,0,0), (0,0,1,0,0), (0,0,0,1,0), (0,0,0,0,1)]

/-- The generating set of `⊤`. -/
def S5 : Set (Coordinate 2) := {x | x ∈ gksList}

theorem closure_S5_eq_top : Subgroup.closure S5 = ⊤ := by
  have hclo : Subgroup.closure S5 = ofList 2 hq2 gksList := rfl
  have hwf : wfB 2 gksList = true := by decide
  have hcard : Nat.card (Subgroup.closure S5) = 3125 := by
    rw [hclo, card_ofList hq2 gksList (wf_of_wfB hq2 gksList hwf)]; rfl
  have htop : Nat.card (Coordinate 2) = 3125 := by rw [Nat.card_eq_fintype_card]; rfl
  exact Subgroup.eq_top_of_card_eq _ (hcard.trans htop.symm)

/-! ## `subAt` injectivity -/

theorem subAt_inj (i j : Nat) (hi : i < 676) (hj : j < 676)
    (h : subAt i = subAt j) : i = j := by
  have hpw := Hbases
  rw [List.pairwise_iff_getElem] at hpw
  have key : ∀ a b : Nat, (ha : a < allBases.length) → (hb : b < allBases.length) →
      a < b → subAt a ≠ subAt b := by
    intro a b ha hb hab
    have hd : ofList 2 hq2 allBases[a] ≠ ofList 2 hq2 allBases[b] := hpw a b ha hb hab
    rw [subAt_eq_ofList, subAt_eq_ofList]
    change ofList 2 hq2 (allBases.getD a []) ≠ ofList 2 hq2 (allBases.getD b [])
    rw [List.getD_eq_getElem allBases [] ha, List.getD_eq_getElem allBases [] hb]
    exact hd
  have hlti : i < allBases.length := by rw [allBases_card]; exact hi
  have hltj : j < allBases.length := by rw [allBases_card]; exact hj
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · exact absurd h (key i j hlti hltj hlt)
  · exact heq
  · exact absurd h.symm (key j i hltj hlti hgt)

/-! ## Semantic correctness of one conjugation move -/

/-- If every generator of `subAt i`, conjugated by `g_k`, sifts into `subAt j`
and `subAt j` has the same order, then `conjSub g_k (subAt i) = subAt j`. -/
theorem conjSub_subAt_eq (k i j : Nat) (hi : i < 676) (hj : j < 676)
    (hlen : (getB i).length = (getB j).length)
    (hsift : ∀ gen ∈ getB i, siftB 2 (getB j) (conjC 2 (gElt k) gen) = true) :
    conjSub (gElt k) (subAt i) = subAt j := by
  have hle : conjSub (gElt k) (subAt i) ≤ subAt j := by
    rw [conjSub, subAt_eq_ofList, ofList, MonoidHom.map_closure, Subgroup.closure_le]
    rintro y ⟨x, hx, rfl⟩
    have hsval : siftB 2 (getB j) (conjC 2 (gElt k) x) = true := hsift x hx
    rw [conjSub_hom_apply]
    have := (LeanDring.P5Presentation.sift_mem_iff hq2 (getB j) (wf_getB hj)
      (conjC 2 (gElt k) x)).mp hsval
    rw [subAt_eq_ofList]; exact this
  have hcard : Nat.card (subAt j) ≤ Nat.card (conjSub (gElt k) (subAt i)) := by
    rw [card_conjSub, card_subAt hi, card_subAt hj, hlen]
  exact Subgroup.eq_of_le_of_card_ge hle hcard

/-! ## Extracting per-`(k,i)` facts from the split kernel checks -/

theorem conjTab_row_length (k : Nat) (hk : k < 5) : (conjTab.getD k []).length = 676 := by
  interval_cases k
  exacts [conjTab_row_length_0, conjTab_row_length_1, conjTab_row_length_2,
    conjTab_row_length_3, conjTab_row_length_4]

theorem conjRowCheck_true (k : Nat) (hk : k < 5) : conjRowCheck k = true := by
  interval_cases k
  exacts [conjRowCheck_0, conjRowCheck_1, conjRowCheck_2, conjRowCheck_3, conjRowCheck_4]

theorem classInvRowCheck_true (k : Nat) (hk : k < 5) : classInvRowCheck k = true := by
  interval_cases k
  exacts [classInvRowCheck_0, classInvRowCheck_1, classInvRowCheck_2, classInvRowCheck_3,
    classInvRowCheck_4]

theorem classOfData_length : classOfData.length = 676 := by decide

/-- The `(k, i)` conjugation-check fact, extracted from the row-`k` check. -/
theorem conjEntry_at (k i : Nat) (hk : k < 5) (hi : i < 676) :
    conjEntryOK2 (gElt k) (getB i, conjMove k i) = true := by
  have hbl : allBasesRaw.length = 676 := allBases_card
  have hrl : (conjTab.getD k []).length = 676 := conjTab_row_length k hk
  have hi1 : i < allBasesRaw.length := by rw [hbl]; exact hi
  have hi2 : i < (conjTab.getD k []).length := by rw [hrl]; exact hi
  have hi' : i < (conjPairs k).length := by
    change i < (allBasesRaw.zip (conjTab.getD k [])).length
    rw [List.length_zip]; omega
  have e1 : getB i = allBasesRaw[i]'hi1 := List.getD_eq_getElem allBasesRaw [] hi1
  have e2 : conjMove k i = (conjTab.getD k [])[i]'hi2 :=
    List.getD_eq_getElem (conjTab.getD k []) 0 hi2
  have hz : (conjPairs k)[i]'hi' = (allBasesRaw[i]'hi1, (conjTab.getD k [])[i]'hi2) := by
    change (allBasesRaw.zip (conjTab.getD k []))[i]'hi' = _
    exact List.getElem_zip
  have hget : (conjPairs k)[i]'hi' = (getB i, conjMove k i) := by rw [hz, e1, e2]
  have hmem : (getB i, conjMove k i) ∈ conjPairs k := hget ▸ List.getElem_mem hi'
  exact List.all_eq_true.mp (conjRowCheck_true k hk) _ hmem

/-- The `(k, i)` class-invariance fact, extracted from the row-`k` check. -/
theorem classInv_at (k i : Nat) (hk : k < 5) (hi : i < 676) :
    classOfD (conjMove k i) = classOfD i := by
  have hcl : classOfData.length = 676 := classOfData_length
  have hrl : (conjTab.getD k []).length = 676 := conjTab_row_length k hk
  have hi1 : i < classOfData.length := by rw [hcl]; exact hi
  have hi2 : i < (conjTab.getD k []).length := by rw [hrl]; exact hi
  have hi' : i < (classInvPairs k).length := by
    change i < (classOfData.zip (conjTab.getD k [])).length
    rw [List.length_zip]; omega
  have e1 : classOfD i = classOfData[i]'hi1 := List.getD_eq_getElem classOfData 0 hi1
  have e2 : conjMove k i = (conjTab.getD k [])[i]'hi2 :=
    List.getD_eq_getElem (conjTab.getD k []) 0 hi2
  have hz : (classInvPairs k)[i]'hi' = (classOfData[i]'hi1, (conjTab.getD k [])[i]'hi2) := by
    change (classOfData.zip (conjTab.getD k []))[i]'hi' = _
    exact List.getElem_zip
  have hget : (classInvPairs k)[i]'hi' = (classOfD i, conjMove k i) := by rw [hz, e1, e2]
  have hmem : (classOfD i, conjMove k i) ∈ classInvPairs k := hget ▸ List.getElem_mem hi'
  have := List.all_eq_true.mp (classInvRowCheck_true k hk) _ hmem
  simp only [classInvEntryOK2, Nat.beq_eq] at this
  exact this

/-- The main per-move fact: conjugating `subAt i` by `g_k` lands on
`subAt (conjMove k i)`, which is in range and in the same class. -/
theorem move_correct (k i : Nat) (hk : k < 5) (hi : i < 676) :
    conjSub (gElt k) (subAt i) = subAt (conjMove k i) ∧
      conjMove k i < 676 ∧ classOfD (conjMove k i) = classOfD i := by
  have hentry := conjEntry_at k i hk hi
  simp only [conjEntryOK2, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, List.all_eq_true] at hentry
  obtain ⟨⟨hjlt, hlen⟩, hsift⟩ := hentry
  exact ⟨conjSub_subAt_eq k i (conjMove k i) hi hjlt hlen hsift, hjlt, classInv_at k i hk hi⟩

/-! ### Extraction of the partition/tree data facts -/

theorem classOfD_lt (i : Nat) (hi : i < 676) : classOfD i < 148 := by
  have := List.all_eq_true.mp classOfBound_true i (List.mem_range.mpr hi)
  simpa [Nat.blt_eq] using this

theorem classReps_lt (c : Nat) (hc : c < 148) : classRepsData.getD c 0 < 676 := by
  have := List.all_eq_true.mp repRange_true c (List.mem_range.mpr hc)
  simp only [Bool.and_eq_true, Nat.blt_eq] at this
  exact this.1

theorem classOf_rep (c : Nat) (hc : c < 148) : classOfD (classRepsData.getD c 0) = c := by
  have := List.all_eq_true.mp repRange_true c (List.mem_range.mpr hc)
  simp only [Bool.and_eq_true, Nat.beq_eq] at this
  exact this.2

theorem repIdx_of_rep (i : Nat) (hi : i < 676) (hr : isRepData.getD i false = true) :
    repIdx i = i := by
  have := List.all_eq_true.mp repIdx_true i (List.mem_range.mpr hi)
  simp only [hr, Bool.not_true, Bool.false_or, Nat.beq_eq] at this
  exact this

/-! ## Reachability: every subgroup is conjugate to its class representative -/

theorem reach : ∀ n i, i < 676 → depthData.getD i 0 = n →
    ∃ g : Coordinate 2, conjSub g (subAt (repIdx i)) = subAt i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro i hi hn
    have hti := List.all_eq_true.mp treeCheckAll_true i (List.mem_range.mpr hi)
    by_cases hr : isRepData.getD i false = true
    · exact ⟨1, by rw [repIdx_of_rep i hi hr, conjSub_one]⟩
    · have hrf : isRepData.getD i false = false := by
        cases h : isRepData.getD i false with
        | false => rfl
        | true => exact absurd h hr
      simp only [treeEntryOK, hrf, Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_or,
        Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hti
      obtain ⟨⟨⟨⟨hk5, hj676⟩, hdlt⟩, hcls⟩, hmv⟩ := hti
      set k := parentKData.getD i 0 with hk_def
      set j := parentJData.getD i 0 with hj_def
      have hjdepth : depthData.getD j 0 < n := hn ▸ hdlt
      obtain ⟨g0, hg0⟩ := IH (depthData.getD j 0) hjdepth j hj676 rfl
      have hmc := (move_correct k j hk5 hj676).1
      rw [hmv] at hmc
      have hrep_eq : repIdx j = repIdx i := by unfold repIdx; rw [hcls]
      exact ⟨(gElt k : Coordinate 2) * g0, by rw [← conjSub_conjSub, ← hrep_eq, hg0, hmc]⟩

/-! ## Conjugation by any element preserves the class label -/

theorem orbit_inv (g : Coordinate 2) :
    ∀ i, i < 676 → ∃ i', i' < 676 ∧ conjSub g (subAt i) = subAt i' ∧ classOfD i' = classOfD i := by
  have hg : g ∈ Subgroup.closure S5 := closure_S5_eq_top ▸ Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      intro i hi
      simp only [S5, Set.mem_setOf_eq, gksList, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · obtain ⟨he, hb, hc⟩ := move_correct 0 i (by norm_num) hi; exact ⟨conjMove 0 i, hb, he, hc⟩
      · obtain ⟨he, hb, hc⟩ := move_correct 1 i (by norm_num) hi; exact ⟨conjMove 1 i, hb, he, hc⟩
      · obtain ⟨he, hb, hc⟩ := move_correct 2 i (by norm_num) hi; exact ⟨conjMove 2 i, hb, he, hc⟩
      · obtain ⟨he, hb, hc⟩ := move_correct 3 i (by norm_num) hi; exact ⟨conjMove 3 i, hb, he, hc⟩
      · obtain ⟨he, hb, hc⟩ := move_correct 4 i (by norm_num) hi; exact ⟨conjMove 4 i, hb, he, hc⟩
  | one => intro i hi; exact ⟨i, hi, conjSub_one _, rfl⟩
  | mul x y hx hy Px Py =>
      intro i hi
      obtain ⟨i'', hi'', hxy, hcls''⟩ := Py i hi
      obtain ⟨i', hi', hxy', hcls'⟩ := Px i'' hi''
      exact ⟨i', hi', by rw [← conjSub_conjSub, hxy, hxy'], by rw [hcls', hcls'']⟩
  | inv x hx Px =>
      intro i hi
      obtain ⟨i0, hi0, hsub⟩ := exists_index_of_inInv (conjSub x⁻¹ (subAt i)) (allSubs_complete _)
      obtain ⟨i', hi', hxeq, hcls⟩ := Px i0 hi0
      have hxi : conjSub x (subAt i0) = subAt i := by
        rw [hsub, conjSub_conjSub, mul_inv_cancel, conjSub_one]
      have hii : i' = i := subAt_inj i' i hi' hi (hxeq.symm.trans hxi)
      refine ⟨i0, hi0, hsub.symm, ?_⟩
      rw [hii] at hcls
      exact hcls.symm

/-! ## The 148 representatives and the classification theorems -/

/-- The `148` conjugacy-class representatives. -/
def reps (r : Fin 148) : Subgroup (Coordinate 2) := subAt (classRepsData.getD r.val 0)

/-- **Completeness up to conjugacy.** Every subgroup of `Coordinate 2` is conjugate
to some representative `reps r`. -/
theorem reps_complete (K : Subgroup (Coordinate 2)) :
    ∃ r : Fin 148, ∃ g : Coordinate 2, conjSub g (reps r) = K := by
  obtain ⟨i, hi, rfl⟩ := exists_index_of_inInv K (allSubs_complete K)
  refine ⟨⟨classOfD i, classOfD_lt i hi⟩, ?_⟩
  obtain ⟨g, hg⟩ := reach (depthData.getD i 0) i hi rfl
  exact ⟨g, by simpa only [reps, repIdx, classOfD] using hg⟩

/-- **Pairwise non-conjugacy.** Distinct representatives are non-conjugate. -/
theorem reps_pairwise_nonconj (r r' : Fin 148) (hne : r ≠ r') :
    ¬ ∃ g : Coordinate 2, conjSub g (reps r) = reps r' := by
  rintro ⟨g, hg⟩
  have hrlt : classRepsData.getD r.val 0 < 676 := classReps_lt r.val r.isLt
  obtain ⟨i', hi', heq, hcls⟩ := orbit_inv g (classRepsData.getD r.val 0) hrlt
  have hi'eq : i' = classRepsData.getD r'.val 0 := by
    apply subAt_inj i' _ hi' (classReps_lt r'.val r'.isLt)
    rw [← heq]; exact hg
  have h1 : classOfD i' = r.val := by rw [hcls]; exact classOf_rep r.val r.isLt
  have h2 : classOfD i' = r'.val := by rw [hi'eq]; exact classOf_rep r'.val r'.isLt
  exact hne (Fin.ext (h1 ▸ h2))

/-! ## Normal subgroups: singleton classes -/

/-- A subgroup fixed by every generator-conjugation is normal (word induction over
the five generators, closed under inverse and product). -/
theorem normal_of_gens_fix (H : Subgroup (Coordinate 2))
    (hfix : ∀ k, k < 5 → conjSub (gElt k) H = H) : H.Normal := by
  rw [Subgroup.normal_iff_map_conj_eq]
  intro g
  rw [← conjSub_eq_map_conj]
  have hg : g ∈ Subgroup.closure S5 := closure_S5_eq_top ▸ Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      simp only [S5, Set.mem_setOf_eq, gksList, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact hfix 0 (by norm_num)
      · exact hfix 1 (by norm_num)
      · exact hfix 2 (by norm_num)
      · exact hfix 3 (by norm_num)
      · exact hfix 4 (by norm_num)
  | one => exact conjSub_one H
  | mul x y hx hy Px Py => rw [← conjSub_conjSub, Py, Px]
  | inv x hx Px =>
      have hxx : conjSub x⁻¹ (conjSub x H) = H := by
        rw [conjSub_conjSub, inv_mul_cancel, conjSub_one]
      rwa [Px] at hxx

/-- **Normality is a singleton class**, and the data flag `isNormalIdx` detects
it: `reps r` is normal iff it is fixed by all five generator-conjugations. -/
theorem reps_normal_iff (r : Fin 148) :
    (reps r).Normal ↔ isNormalIdx (classRepsData.getD r.val 0) = true := by
  set rep := classRepsData.getD r.val 0 with hrep
  have hreplt : rep < 676 := classReps_lt r.val r.isLt
  constructor
  · intro hnorm
    rw [isNormalIdx, List.all_eq_true]
    intro k hk
    simp only [List.mem_range] at hk
    have hmap := (Subgroup.normal_iff_map_conj_eq.mp hnorm) (gElt k)
    rw [← conjSub_eq_map_conj] at hmap
    have hmc := (move_correct k rep hk hreplt).1
    have hmclt := (move_correct k rep hk hreplt).2.1
    have hmap' : conjSub (gElt k) (subAt rep) = subAt rep := hmap
    have hss : subAt (conjMove k rep) = subAt rep := hmc.symm.trans hmap'
    simp only [Nat.beq_eq]
    exact subAt_inj (conjMove k rep) rep hmclt hreplt hss
  · intro hflag
    rw [isNormalIdx, List.all_eq_true] at hflag
    apply normal_of_gens_fix
    intro k hk
    have hmc := (move_correct k rep hk hreplt).1
    have hbeq := hflag k (List.mem_range.mpr hk)
    simp only [Nat.beq_eq] at hbeq
    rw [reps, ← hrep]
    calc conjSub (gElt k) (subAt rep) = subAt (conjMove k rep) := hmc
      _ = subAt rep := by rw [hbeq]

end Q2

end LeanDring.P5Presentation
