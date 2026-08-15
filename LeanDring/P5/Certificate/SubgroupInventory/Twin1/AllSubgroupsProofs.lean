/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SubgroupInventory.Twin1.AllSubgroups

/-!
# Distinctness of the 676-subgroup inventory

`LeanDring.P5.Certificate.SubgroupInventory.Twin1.AllSubgroups` certifies all 676
bases as well-formed `Cgs` (`allSubs`). This file certifies that **no two of them
present the same subgroup**:

* `allSubs_pairwise_distinct` — `List.Pairwise (·.toSubgroup ≠ ·.toSubgroup) allSubs`.

The proof splits the pairs in two:

* **cross-stratum** pairs (different generator-list length) are distinct *for free*
  via `card_ofList` (orders `5^i ≠ 5^j`) — no kernel group arithmetic;
* **within-stratum** pairs are decided by the mutual-sift `cgsEquivRaw` returning
  `false` (which `cgsEquiv_iff` certifies as subgroup inequality), chunked so each
  kernel `decide` stays small (the two large strata `sub2`/`sub3` are split into
  blocks and reassembled by the `Bool`-level append/split lemmas).

Also recorded here are the two **completeness anchors** `bot_mem_allSubs`,
`top_mem_allSubs` (`⊥` and `⊤` are in the inventory), the starting points of the
downward induction. Completeness itself — *every* subgroup of `Coordinate 1` is
presented by some member of `allSubs` — is reduced to a Frattini-quotient
obligation in `LeanDring.P5.Certificate.SubgroupInventory.Twin1.Complete` and
proved in `LeanDring.P5.Certificate.SubgroupInventory.Twin1.FratDischarge`.
-/

namespace LeanDring.P5Presentation

open Cgs

-- file-level maxHeartbeats: dozens of decide-heavy declarations below need it
set_option linter.style.setOption false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

/-! ## The raw mutual-sift equality and its `Bool` pairwise/cross combinators -/

/-- Mutual-sift equality on raw bases; agrees with `Cgs.cgsEquiv`. -/
def cgsEquivRaw (a b : List (Coordinate 1)) : Bool :=
  b.all (fun g => siftB 1 a g) && a.all (fun g => siftB 1 b g)

theorem cgsEquivRaw_eq (c c' : Cgs 1 hq1) : cgsEquivRaw c.gens c'.gens = c.cgsEquiv c' := rfl

/-- All unordered pairs of a base list are `cgsEquivRaw`-distinct. -/
def pairwiseDistinctB : List (List (Coordinate 1)) → Bool
  | [] => true
  | a :: rest => rest.all (fun b => !cgsEquivRaw a b) && pairwiseDistinctB rest

/-- Every base in `l1` is `cgsEquivRaw`-distinct from every base in `l2`. -/
def crossDistinctB (l1 l2 : List (List (Coordinate 1))) : Bool :=
  l1.all (fun a => l2.all (fun b => !cgsEquivRaw a b))

theorem pairwiseDistinctB_iff (l : List (List (Coordinate 1))) :
    pairwiseDistinctB l = true ↔ List.Pairwise (fun a b => cgsEquivRaw a b = false) l := by
  induction l with
  | nil => simp [pairwiseDistinctB]
  | cons a t ih =>
      simp only [pairwiseDistinctB, Bool.and_eq_true, List.all_eq_true, List.pairwise_cons, ih,
        Bool.not_eq_true']

theorem all_and' {α} (l : List α) (f g : α → Bool) :
    l.all (fun a => f a && g a) = (l.all f && l.all g) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.all_cons, ih]; simp only [Bool.and_assoc, Bool.and_left_comm]

theorem pairwiseDistinctB_append (l1 l2 : List (List (Coordinate 1))) :
    pairwiseDistinctB (l1 ++ l2)
      = (pairwiseDistinctB l1 && crossDistinctB l1 l2 && pairwiseDistinctB l2) := by
  induction l1 with
  | nil => simp [pairwiseDistinctB, crossDistinctB]
  | cons a t ih =>
      simp only [List.cons_append, pairwiseDistinctB, crossDistinctB, List.all_cons,
        List.all_append, ih]
      simp only [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

theorem crossDistinctB_append_right (l1 l2 l3 : List (List (Coordinate 1))) :
    crossDistinctB l1 (l2 ++ l3) = (crossDistinctB l1 l2 && crossDistinctB l1 l3) := by
  simp only [crossDistinctB, List.all_append, all_and']

theorem pairwiseDistinctB_split (n : ℕ) (l : List (List (Coordinate 1))) :
    pairwiseDistinctB l =
      (pairwiseDistinctB (l.take n) && crossDistinctB (l.take n) (l.drop n)
        && pairwiseDistinctB (l.drop n)) := by
  conv_lhs => rw [← List.take_append_drop n l]
  rw [pairwiseDistinctB_append]

theorem crossDistinctB_split (n : ℕ) (l1 l2 : List (List (Coordinate 1))) :
    crossDistinctB l1 l2 =
      (crossDistinctB l1 (l2.take n) && crossDistinctB l1 (l2.drop n)) := by
  conv_lhs => rw [← List.take_append_drop n l2, crossDistinctB_append_right]

/-! ## From `Bool` distinctness to subgroup inequality -/

/-- Distinct raw bases (`cgsEquivRaw = false`, both well-formed) present distinct
subgroups. -/
theorem ofList_ne_of_cgsEquivRaw_false (a b : List (Coordinate 1))
    (ha : wfB 1 a = true) (hb : wfB 1 b = true) (h : cgsEquivRaw a b = false) :
    ofList 1 hq1 a ≠ ofList 1 hq1 b := by
  intro hEq
  have hc : (⟨a, ha⟩ : Cgs 1 hq1).cgsEquiv ⟨b, hb⟩ = true :=
    (Cgs.cgsEquiv_iff ⟨a, ha⟩ ⟨b, hb⟩).mpr hEq
  rw [← cgsEquivRaw_eq ⟨a, ha⟩ ⟨b, hb⟩, h] at hc
  exact Bool.noConfusion hc

/-- Bases of different length present subgroups of different order, hence distinct
(the free cross-stratum discriminator). -/
theorem ofList_ne_of_length_ne (a b : List (Coordinate 1))
    (ha : wfB 1 a = true) (hb : wfB 1 b = true) (hlen : a.length ≠ b.length) :
    ofList 1 hq1 a ≠ ofList 1 hq1 b := by
  intro h
  have ca : Nat.card (ofList 1 hq1 a) = 5 ^ a.length := card_ofList hq1 a (wf_of_wfB hq1 a ha)
  have cb : Nat.card (ofList 1 hq1 b) = 5 ^ b.length := card_ofList hq1 b (wf_of_wfB hq1 b hb)
  rw [h, cb] at ca
  exact hlen (Nat.pow_right_injective (by norm_num) ca.symm)

/-- The distinctness relation on raw bases. -/
def RDistinct (a b : List (Coordinate 1)) : Prop := ofList 1 hq1 a ≠ ofList 1 hq1 b

theorem within_stratum (s : List (List (Coordinate 1)))
    (hwf : ∀ a ∈ s, wfB 1 a = true) (hpd : pairwiseDistinctB s = true) :
    List.Pairwise RDistinct s :=
  ((pairwiseDistinctB_iff s).mp hpd).imp_of_mem fun ha hb h =>
    ofList_ne_of_cgsEquivRaw_false _ _ (hwf _ ha) (hwf _ hb) h

theorem cross_stratum (s t : List (List (Coordinate 1))) (i j : ℕ) (hij : i ≠ j)
    (hwfs : ∀ a ∈ s, wfB 1 a = true) (hwft : ∀ b ∈ t, wfB 1 b = true)
    (hlens : ∀ a ∈ s, a.length = i) (hlent : ∀ b ∈ t, b.length = j) :
    ∀ a ∈ s, ∀ b ∈ t, RDistinct a b := fun a ha b hb =>
  ofList_ne_of_length_ne a b (hwfs a ha) (hwft b hb) (by rw [hlens a ha, hlent b hb]; exact hij)

/-! ## Per-stratum well-formedness and length facts -/

theorem hwf0 : ∀ a ∈ sub0, wfB 1 a = true := by
  intro a ha; rw [← wfB'_eq_wfB]; exact (List.all_eq_true.mp wf0) a ha
theorem hwf1 : ∀ a ∈ sub1, wfB 1 a = true := by
  intro a ha; rw [← wfB'_eq_wfB]
  have h1 : sub1.all (fun b => wfB' 1 b) = true := by
    simp only [sub1, List.all_append, wf1_0, wf1_1, wf1_2, wf1_3, wf1_4, wf1_5, Bool.and_self]
  exact (List.all_eq_true.mp h1) a ha
theorem hwf2 : ∀ a ∈ sub2, wfB 1 a = true := by
  intro a ha; rw [← wfB'_eq_wfB]; exact (List.all_eq_true.mp wf2) a ha
theorem hwf3 : ∀ a ∈ sub3, wfB 1 a = true := by
  intro a ha; rw [← wfB'_eq_wfB]; exact (List.all_eq_true.mp wf3) a ha
theorem hwf4 : ∀ a ∈ sub4, wfB 1 a = true := by
  intro a ha; rw [← wfB'_eq_wfB]; exact (List.all_eq_true.mp wf4) a ha
theorem hwf5 : ∀ a ∈ sub5, wfB 1 a = true := by
  intro a ha; rw [← wfB'_eq_wfB]; exact (List.all_eq_true.mp wf5) a ha

theorem hlen0 : ∀ a ∈ sub0, a.length = 0 := by decide
theorem hlen1 : ∀ a ∈ sub1, a.length = 1 := by decide
theorem hlen2 : ∀ a ∈ sub2, a.length = 2 := by decide
theorem hlen3 : ∀ a ∈ sub3, a.length = 3 := by decide
theorem hlen4 : ∀ a ∈ sub4, a.length = 4 := by decide
theorem hlen5 : ∀ a ∈ sub5, a.length = 5 := by decide

/-! ## Within-stratum distinctness (chunked kernel `decide`s) -/

theorem pdb0 : pairwiseDistinctB sub0 = true := by decide
theorem pdb1 : pairwiseDistinctB sub1 = true := by decide
theorem pdb4 : pairwiseDistinctB sub4 = true := by decide
theorem pdb5 : pairwiseDistinctB sub5 = true := by decide

-- `sub2` (306 bases): 3 blocks of 102, reassembled below.
theorem pdb2_A : pairwiseDistinctB (sub2.take 102) = true := by decide
theorem pdb2_B : pairwiseDistinctB ((sub2.drop 102).take 102) = true := by decide
theorem pdb2_C : pairwiseDistinctB ((sub2.drop 102).drop 102) = true := by decide
theorem cr2_AB : crossDistinctB (sub2.take 102) ((sub2.drop 102).take 102) = true := by decide
theorem cr2_AC : crossDistinctB (sub2.take 102) ((sub2.drop 102).drop 102) = true := by decide
theorem cr2_BC : crossDistinctB ((sub2.drop 102).take 102) ((sub2.drop 102).drop 102) = true := by
  decide

theorem pdb2 : pairwiseDistinctB sub2 = true := by
  rw [pairwiseDistinctB_split 102, pairwiseDistinctB_split 102 (sub2.drop 102),
    crossDistinctB_split 102 (sub2.take 102) (sub2.drop 102)]
  simp only [pdb2_A, pdb2_B, pdb2_C, cr2_AB, cr2_AC, cr2_BC, Bool.and_self]

-- `sub3` (181 bases): 2 blocks of 91.
theorem pdb3_A : pairwiseDistinctB (sub3.take 91) = true := by decide
theorem pdb3_B : pairwiseDistinctB (sub3.drop 91) = true := by decide
theorem cr3_AB : crossDistinctB (sub3.take 91) (sub3.drop 91) = true := by decide

theorem pdb3 : pairwiseDistinctB sub3 = true := by
  rw [pairwiseDistinctB_split 91]
  simp only [pdb3_A, pdb3_B, cr3_AB, Bool.and_self]

/-! ## Assembly: the full inventory is pairwise-distinct -/

theorem allBases_flatten : allBases = [sub0, sub1, sub2, sub3, sub4, sub5].flatten := by
  simp only [allBases, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

/-- Every two distinct bases in the inventory present distinct subgroups. -/
theorem Hbases : List.Pairwise RDistinct allBases := by
  rw [allBases_flatten, List.pairwise_flatten]
  refine ⟨?_, ?_⟩
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl
    · exact within_stratum _ hwf0 pdb0
    · exact within_stratum _ hwf1 pdb1
    · exact within_stratum _ hwf2 pdb2
    · exact within_stratum _ hwf3 pdb3
    · exact within_stratum _ hwf4 pdb4
    · exact within_stratum _ hwf5 pdb5
  · refine List.Pairwise.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))))
    all_goals intro l' hl'
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
    · rcases hl' with rfl | rfl | rfl | rfl | rfl
      · exact cross_stratum _ _ 0 1 (by decide) hwf0 hwf1 hlen0 hlen1
      · exact cross_stratum _ _ 0 2 (by decide) hwf0 hwf2 hlen0 hlen2
      · exact cross_stratum _ _ 0 3 (by decide) hwf0 hwf3 hlen0 hlen3
      · exact cross_stratum _ _ 0 4 (by decide) hwf0 hwf4 hlen0 hlen4
      · exact cross_stratum _ _ 0 5 (by decide) hwf0 hwf5 hlen0 hlen5
    · rcases hl' with rfl | rfl | rfl | rfl
      · exact cross_stratum _ _ 1 2 (by decide) hwf1 hwf2 hlen1 hlen2
      · exact cross_stratum _ _ 1 3 (by decide) hwf1 hwf3 hlen1 hlen3
      · exact cross_stratum _ _ 1 4 (by decide) hwf1 hwf4 hlen1 hlen4
      · exact cross_stratum _ _ 1 5 (by decide) hwf1 hwf5 hlen1 hlen5
    · rcases hl' with rfl | rfl | rfl
      · exact cross_stratum _ _ 2 3 (by decide) hwf2 hwf3 hlen2 hlen3
      · exact cross_stratum _ _ 2 4 (by decide) hwf2 hwf4 hlen2 hlen4
      · exact cross_stratum _ _ 2 5 (by decide) hwf2 hwf5 hlen2 hlen5
    · rcases hl' with rfl | rfl
      · exact cross_stratum _ _ 3 4 (by decide) hwf3 hwf4 hlen3 hlen4
      · exact cross_stratum _ _ 3 5 (by decide) hwf3 hwf5 hlen3 hlen5
    · rcases hl' with rfl
      · exact cross_stratum _ _ 4 5 (by decide) hwf4 hwf5 hlen4 hlen5

/-- **Distinctness of the inventory.** No two of the 676 certified `Cgs` present
the same subgroup. -/
theorem allSubs_pairwise_distinct :
    List.Pairwise (fun c c' => c.toSubgroup ≠ c'.toSubgroup) allSubs := by
  have h : List.Pairwise RDistinct (allSubs.map Cgs.gens) := by rw [allSubs_gens]; exact Hbases
  rwa [List.pairwise_map] at h

/-! ## Completeness anchors (top and bottom of the lattice)

The two endpoints of the downward-saturation completeness argument: the trivial
and the full subgroup are both present in the certified inventory. -/

/-- Any inventory base yields a certified member of `allSubs` with those generators. -/
theorem mem_allSubs_of_mem_allBases (b : List (Coordinate 1)) (hb : b ∈ allBases) :
    ∃ c ∈ allSubs, c.gens = b := by
  refine ⟨⟨b, allBases_wfB b hb⟩, ?_, rfl⟩
  simp only [allSubs, List.mem_map]
  exact ⟨⟨b, hb⟩, List.mem_attach _ _, rfl⟩

/-- **The trivial subgroup is in the inventory.** -/
theorem bot_mem_allSubs : ∃ c ∈ allSubs, c.toSubgroup = ⊥ := by
  obtain ⟨c, hc, hg⟩ := mem_allSubs_of_mem_allBases [] (by decide)
  refine ⟨c, hc, ?_⟩
  rw [Cgs.toSubgroup, hg, ofList,
    show {x : Coordinate 1 | x ∈ ([] : List (Coordinate 1))} = ∅ by ext y; simp,
    Subgroup.closure_empty]

/-- **The full group is in the inventory.** -/
theorem top_mem_allSubs : ∃ c ∈ allSubs, c.toSubgroup = ⊤ := by
  obtain ⟨c, hc, hg⟩ := mem_allSubs_of_mem_allBases
    [(1,0,0,0,0),(0,1,0,0,0),(0,0,1,0,0),(0,0,0,1,0),(0,0,0,0,1)] (by decide)
  refine ⟨c, hc, ?_⟩
  have h1 : Nat.card c.toSubgroup = 3125 := by rw [c.card_toSubgroup, hg]; rfl
  have h2 : Nat.card (Coordinate 1) = 3125 := by rw [Nat.card_eq_fintype_card]; rfl
  exact Subgroup.eq_top_of_card_eq _ (h1.trans h2.symm)

end LeanDring.P5Presentation
