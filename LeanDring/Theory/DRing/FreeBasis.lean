/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.Census
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

-- The `[Fintype _]` binders below are unused in several *statements* but are
-- load-bearing in their *proofs* (instance synthesis for cardinality and basis
-- constructions), so they cannot be `omit`ted.  The linter's suggested rewrite
-- to `[Finite _]` + `Fintype.ofFinite` is a genuine refactor, not a cleanup.
set_option linter.unusedFintypeInType false

/-!
# The `ℤ`-basis of `D(G)` and the rank formula

Packaging of the completed Satz 2.1.1: choosing a representative in each
conjugacy class of character pairs gives a `ℤ`-basis of the D-ring
(`DRing.basisOfCharPairClass : Basis (CharPairClass G ℂˣ) ℤ (DRing G)`),
hence **`rank D(G) = #{(K, λ)}/G-conjugacy`** (`DRing.rank_dring`) — the
D-rank invariant used throughout the strata separations.

Linear independence over `ℤ` reduces to the census: a vanishing integer
combination splits into two `ℕ`-combinations with equal sums, whose class
multisets must agree (`basisElt_sum_unique`); counting the classes kills
every coefficient.
-/

namespace LeanDring

namespace DRing

open MonGSet Finset

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- A chosen representative basis vector for each conjugacy class. -/
noncomputable def classElt (c : CharPairClass G ℂˣ) : DRing G :=
  basisElt c.out.1 c.out.2

theorem classElt_mk (p : CharPair G ℂˣ) :
    classElt (⟦p⟧ : CharPairClass G ℂˣ) = basisElt p.1 p.2 :=
  (basisElt_eq_iff _ _ _ _).mpr (Quotient.mk_out p)

/-- Push a `Finset`-sum of multisets through `map` and `sum`. -/
private theorem sum_map_finsetSum {ι β γ : Type*} [AddCommMonoid γ]
    (s : Finset ι) (f : ι → Multiset β) (h : β → γ) :
    ((∑ i ∈ s, f i).map h).sum = ∑ i ∈ s, ((f i).map h).sum := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, Multiset.map_add, Multiset.sum_add, ih]

/-- Push a `Finset`-sum of multisets through `map`. -/
private theorem map_finsetSum {ι β γ : Type*} (s : Finset ι) (f : ι → Multiset β)
    (h : β → γ) : (∑ i ∈ s, f i).map h = ∑ i ∈ s, (f i).map h := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, Multiset.map_add, ih]

/-- The positive-part multiset of an integer combination. -/
private noncomputable def posMultiset (S : Finset (CharPairClass G ℂˣ))
    (n : CharPairClass G ℂˣ → ℕ) : Multiset (CharPair G ℂˣ) :=
  ∑ c ∈ S, Multiset.replicate (n c) c.out

private theorem posMultiset_sum (S : Finset (CharPairClass G ℂˣ))
    (n : CharPairClass G ℂˣ → ℕ) :
    ((posMultiset S n).map fun p => basisElt p.1 p.2).sum =
      ∑ c ∈ S, n c • classElt c := by
  rw [posMultiset, sum_map_finsetSum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Multiset.map_replicate, Multiset.sum_replicate]
  rfl

omit [Fintype G] in
private theorem posMultiset_classes [DecidableEq (CharPairClass G ℂˣ)]
    (S : Finset (CharPairClass G ℂˣ))
    (n : CharPairClass G ℂˣ → ℕ) (c₀ : CharPairClass G ℂˣ) :
    Multiset.count c₀ ((posMultiset S n).map fun p => (⟦p⟧ : CharPairClass G ℂˣ)) =
      if c₀ ∈ S then n c₀ else 0 := by
  have hmap : ((posMultiset S n).map fun p => (⟦p⟧ : CharPairClass G ℂˣ)) =
      ∑ c ∈ S, Multiset.replicate (n c) c := by
    rw [posMultiset, map_finsetSum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Multiset.map_replicate, Quotient.out_eq]
    rfl
  refine (congrArg (Multiset.count c₀) hmap).trans ?_
  rw [Multiset.count_sum']
  have hterm : ∀ c ∈ S, Multiset.count c₀ (Multiset.replicate (n c) c) =
      if c = c₀ then n c else 0 := fun c _ => Multiset.count_replicate _ _ _
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' S c₀ n]

/-- **Linear independence of the class representatives over `ℤ`** — the
census kills every vanishing integer combination. -/
theorem linearIndependent_classElt :
    LinearIndependent ℤ (classElt (G := G)) := by
  classical
  rw [linearIndependent_iff']
  intro S g hsum
  -- split into positive and negative parts
  set Sp := S.filter (fun c => 0 < g c) with hSp
  set Sn := S.filter (fun c => g c < 0) with hSn
  have h2 : ∑ c ∈ S.filter (fun c => ¬ 0 < g c), g c • classElt c =
      ∑ c ∈ Sn, g c • classElt c := by
    rw [← Finset.sum_filter_add_sum_filter_not (S.filter fun c => ¬ 0 < g c)
      (fun c => g c < 0) (fun c => g c • classElt c)]
    have hz : ∑ c ∈ (S.filter fun c => ¬ 0 < g c).filter (fun c => ¬ g c < 0),
        g c • classElt c = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      obtain ⟨hc1, hc2⟩ := Finset.mem_filter.mp hc
      obtain ⟨-, hc3⟩ := Finset.mem_filter.mp hc1
      rw [le_antisymm (not_lt.mp hc3) (not_lt.mp hc2), zero_smul]
    have hff : (S.filter fun c => ¬ 0 < g c).filter (fun c => g c < 0) = Sn := by
      rw [Finset.filter_filter]
      exact Finset.filter_congr fun c _ => by
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨not_lt.mpr h.le, h⟩
    rw [hz, add_zero, hff]
  have hsplit : ∑ c ∈ Sp, g c • classElt c + ∑ c ∈ Sn, g c • classElt c = 0 := by
    have h1 := Finset.sum_filter_add_sum_filter_not S (fun c => 0 < g c)
      (fun c => g c • classElt c)
    rw [hsum, h2] at h1
    exact h1
  -- express the two sides as multiset sums of basis elements
  have hpos : ((posMultiset Sp fun c => (g c).toNat).map fun p => basisElt p.1 p.2).sum =
      ∑ c ∈ Sp, g c • classElt c := by
    rw [posMultiset_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    have h0 : (0 : ℤ) ≤ g c := (Finset.mem_filter.mp hc).2.le
    rw [← natCast_zsmul, Int.toNat_of_nonneg h0]
  have hneg : ((posMultiset Sn fun c => (-g c).toNat).map fun p => basisElt p.1 p.2).sum =
      ∑ c ∈ Sn, -(g c • classElt c) := by
    rw [posMultiset_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    have h0 : (0 : ℤ) ≤ -g c := neg_nonneg.mpr (Finset.mem_filter.mp hc).2.le
    rw [← neg_smul, ← natCast_zsmul, Int.toNat_of_nonneg h0]
  have hsums : ((posMultiset Sp fun c => (g c).toNat).map fun p => basisElt p.1 p.2).sum =
      ((posMultiset Sn fun c => (-g c).toNat).map fun p => basisElt p.1 p.2).sum := by
    rw [hpos, hneg, Finset.sum_neg_distrib]
    exact eq_neg_of_add_eq_zero_left hsplit
  -- census: the class multisets agree, so all counts vanish
  have hclasses := basisElt_sum_unique _ _ hsums
  have hcount : ∀ c₀ : CharPairClass G ℂˣ,
      (if c₀ ∈ Sp then (g c₀).toNat else 0) =
        (if c₀ ∈ Sn then (-g c₀).toNat else 0) := by
    intro c₀
    exact (posMultiset_classes Sp _ c₀).symm.trans
      ((congrArg (Multiset.count c₀) hclasses).trans (posMultiset_classes Sn _ c₀))
  -- conclude coefficientwise
  intro c₀ hc₀
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `g c₀ < 0`: the negative side has positive count, the positive side zero
    have hmemn : c₀ ∈ Sn := Finset.mem_filter.mpr ⟨hc₀, hlt⟩
    have hmemp : c₀ ∉ Sp := fun h =>
      absurd (Finset.mem_filter.mp h).2 (not_lt.mpr hlt.le)
    have := hcount c₀
    rw [if_pos hmemn, if_neg hmemp] at this
    have hz : (-g c₀).toNat = 0 := this.symm
    rw [Int.toNat_eq_zero] at hz
    omega
  · have hmemp : c₀ ∈ Sp := Finset.mem_filter.mpr ⟨hc₀, hgt⟩
    have hmemn : c₀ ∉ Sn := fun h =>
      absurd (Finset.mem_filter.mp h).2 (not_lt.mpr hgt.le)
    have := hcount c₀
    rw [if_pos hmemp, if_neg hmemn] at this
    rw [Int.toNat_eq_zero] at this
    omega

/-- **The class representatives span `D(G)`.** -/
theorem span_classElt :
    ⊤ ≤ Submodule.span ℤ (Set.range (classElt (G := G))) := by
  intro x _
  obtain ⟨s, t, rfl⟩ := exists_basisElt_decomposition x
  refine sub_mem ?_ ?_ <;>
  · refine multiset_sum_mem _ fun a ha => ?_
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp ha
    rw [← classElt_mk p]
    exact Submodule.subset_span ⟨⟦p⟧, rfl⟩

/-- **The `ℤ`-basis of `D(G)`** indexed by conjugacy classes of character
pairs — Satz 2.1.1, packaged. -/
noncomputable def basisOfCharPairClass :
    Module.Basis (CharPairClass G ℂˣ) ℤ (DRing G) :=
  Module.Basis.mk linearIndependent_classElt span_classElt

-- The `Fintype G` binder is kept rather than `omit`ted: this signature is the
-- paper-facing statement re-exported as `rank_dring` in
-- `LeanDring/MainResults.lean` and audited in `LeanDring/AxiomAudit.lean`.
/-- **The rank formula**: `rank D(G) = #{(K, λ)}/G-conjugacy` — the D-rank
invariant of the strata separations, as a theorem about the ring. -/
theorem rank_dring :
    Cardinal.lift.{u + 1} (Cardinal.mk (CharPairClass G ℂˣ)) =
      Cardinal.lift.{u} (Module.rank ℤ (DRing G)) :=
  basisOfCharPairClass.mk_eq_rank

-- `[Fintype G]`/`[Fintype G']` are unused in the type but load-bearing in
-- the proof (basis construction on both sides); keep them.
/-- **The D-rank is a ring invariant**: isomorphic D-rings have equally
many conjugacy classes of character pairs. Contrapositive: distinct pair
counts separate D-rings — the criterion behind every rank separation. -/
theorem card_charPairClass_eq_of_dringEquiv {G' : Type u} [Group G']
    [Fintype G'] (Φ : DRing G ≃+* DRing G') :
    Cardinal.mk (CharPairClass G ℂˣ) = Cardinal.mk (CharPairClass G' ℂˣ) := by
  have h1 := rank_dring (G := G)
  have h2 := rank_dring (G := G')
  have h3 : Module.rank ℤ (DRing G) = Module.rank ℤ (DRing G') :=
    Φ.toAddEquiv.toIntLinearEquiv.rank_eq
  rw [h3] at h1
  exact Cardinal.lift_injective (h1.trans h2.symm)

end DRing

end LeanDring
