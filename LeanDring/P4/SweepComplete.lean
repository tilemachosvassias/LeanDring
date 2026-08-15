/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import Mathlib.GroupTheory.Commutator.Basic
import LeanDring.P4.Abelian
import LeanDring.P4.ModularModels
import LeanDring.P4.LastModels
import LeanDring.P4.ExpModels
import LeanDring.P4.ColTwo
import LeanDring.P4.NpTwoCounts
import LeanDring.P4.ModelPow
import LeanDring.P4.Model
import LeanDring.P4.NoTableIso
import LeanDring.P4.SweepSeparations
import LeanDring.P4.TwinFinal
import LeanDring.P4.AbelianizationSep
import LeanDring.P4.OrderP3

/-!
# The complete order-`p⁴` pairwise separation (105/105)

Two reusable separators reduce every non-isomorphic pair of the fifteen
order-`p⁴` groups to a one-liner:
* `isEmpty_of_card_sub_ne` — different subgroup count at some order;
* `isEmpty_of_abelian_nonabelian` — an abelian model vs a nonabelian one
  (distinct abelianization orders).
The residual within-class pairs use twenty-one bespoke separations: sixteen
imported from `Abelian`, `AbelianizationSep`, `NoTableIso`, `OrderP3`,
`SweepSeparations` and `TwinFinal`, and five proved privately here
(`isEmpty_a211_ch7` and its four siblings).
-/

namespace LeanDring.P4

open DRing

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

/-- **Count separator.** Two groups whose subgroup counts differ at some order
`n` have no species-table isomorphism. -/
theorem isEmpty_of_card_sub_ne {G H : Type u} [Group G] [Fintype G] [Group H]
    [Fintype H] {n a b : ℕ}
    (hG : Nat.card {K : Subgroup G // Nat.card K = n} = a)
    (hH : Nat.card {K : Subgroup H // Nat.card K = n} = b) (hab : a ≠ b) :
    IsEmpty (SpeciesTableIso G H) := by
  constructor
  intro T
  have h := T.card_subgroups_eq n
  rw [hG, hH] at h
  exact hab h

/-- **Abelian-vs-nonabelian separator.** An abelian order-`p⁴` model and a
nonabelian one have distinct abelianization orders (`p⁴` vs `< p⁴`). -/
theorem isEmpty_of_abelian_nonabelian {A N : Type u} [CommGroup A] [Fintype A]
    [Group N] [Fintype N] (hA : Nat.card A = p ^ 4) (hN : Nat.card N = p ^ 4)
    (hNnc : ∃ a b : N, a * b ≠ b * a) :
    IsEmpty (SpeciesTableIso A N) := by
  constructor
  intro T
  have hEq := card_abelianization_eq_of_speciesTableIso_of_pgroup three_le_p_of_odd hA hN T
  rw [card_abelianization_of_comm] at hEq
  have hlt := card_abelianization_lt_of_not_comm hNnc
  rw [hA] at hEq
  rw [hN] at hlt
  omega

omit [Fact (Odd p)] in
/-- `p ≥ 2` helper for the count inequalities. -/
theorem two_le_p : 2 ≤ p := (Fact.out : p.Prime).two_le

/-- **Subgroup-inclusion transports non-commutativity.** If two elements of a
subgroup `S ≤ G` fail to commute, so do their images in `G`. -/
private theorem noncomm_of_subgroup {G : Type u} [Group G] {S : Subgroup G}
    (h : ∃ a b : S, a * b ≠ b * a) : ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨(a : G), (b : G), ?_⟩
  intro heq
  apply hab
  apply SetLike.coe_eq_coe.mp
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact heq

omit [Fact (Odd p)] in
/-- `|A211| = p⁴`. -/
private theorem card_a211_eq : Nat.card (A211 p) = p ^ 4 := by
  rw [Nat.card_eq_fintype_card]
  change Fintype.card (Multiplicative (ZMod (p ^ 2) × ZMod p × ZMod p)) = p ^ 4
  rw [Fintype.card_multiplicative, Fintype.card_prod, Fintype.card_prod]
  simp only [ZMod.card]
  ring

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
/-- `|Model p d| = p⁴`. -/
private theorem card_model_eq (d : ZMod p) : Nat.card (Model p d) = p ^ 4 := by
  rw [Nat.card_congr (Model.toProd (p := p) (d := d)), Nat.card_prod, Nat.card_prod]
  simp only [Nat.card_zmod]
  ring

omit [Fact (Odd p)] in
/-- `Gid3` is nonabelian: `⟨0,0,1⟩` and `⟨1,0,0⟩` fail to commute (their product
differs in the central `y`-coordinate by `redp p 1 = 1 ≠ 0`). -/
private theorem gid3_noncomm : ∃ a b : Gid3 p, a * b ≠ b * a := by
  refine ⟨⟨0, 0, 1⟩, ⟨1, 0, 0⟩, ?_⟩
  intro heq
  have hy : (0 + 0 + 1 * redp p 1 : ZMod p) = 0 + 0 + 0 * redp p 0 := congrArg Gid3.y heq
  simp only [map_one, mul_one, zero_mul, add_zero, zero_add] at hy
  exact one_ne_zero hy

/-- `Gid8` is nonabelian: the outer generator `s = ⟨(0,0,0),1⟩` and `⟨(1,0,0),0⟩`
fail to commute, with commutator `⟨(0,1,0),0⟩ ≠ 1`. -/
private theorem gid8_noncomm : ∃ a b : Gid8 p, a * b ≠ b * a := by
  refine ⟨⟨(0, 0, 0), 1⟩, ⟨(1, 0, 0), 0⟩, ?_⟩
  intro heq
  have key := gid8_comm (p := p) 1 0
  have hzero : (1 : Gid8 p) = ⟨(0, 1, 0), 0⟩ :=
    (commutatorElement_eq_one_iff_mul_comm.mpr heq).symm.trans key
  have hv : (0 : ZMod p) = 1 := congrArg (fun g : Gid8 p => g.vec.2.1) hzero
  exact one_ne_zero hv.symm

/-- `A211` (abelian) vs `CH7` (nonabelian). -/
private theorem isEmpty_a211_ch7 : IsEmpty (SpeciesTableIso (A211 p) (CH7 p)) :=
  isEmpty_of_abelian_nonabelian card_a211_eq (CH7.card_ch7 p)
    (noncomm_of_subgroup (socleCH7_nonabelian (p := p)))

/-- `A211` (abelian) vs `Gid3` (nonabelian). -/
private theorem isEmpty_a211_gid3 : IsEmpty (SpeciesTableIso (A211 p) (Gid3 p)) :=
  isEmpty_of_abelian_nonabelian card_a211_eq (Gid3.card_gid3 p) gid3_noncomm

/-- `A211` (abelian) vs `Gid8` (nonabelian). -/
private theorem isEmpty_a211_gid8 : IsEmpty (SpeciesTableIso (A211 p) (Gid8 p)) :=
  isEmpty_of_abelian_nonabelian card_a211_eq (Gid8.card_gid8 p) gid8_noncomm

/-- `A211` (abelian) vs `Model p 1` (nonabelian). -/
private theorem isEmpty_a211_model1 :
    IsEmpty (SpeciesTableIso (A211 p) (Model p 1)) :=
  isEmpty_of_abelian_nonabelian card_a211_eq (card_model_eq 1)
    (noncomm_of_subgroup (socleModel_nonabelian (p := p) one_ne_zero))

/-- `A211` (abelian) vs `Model p d` (nonabelian, `d ≠ 0`). -/
private theorem isEmpty_a211_modelD {d : ZMod p} (hd : d ≠ 0) :
    IsEmpty (SpeciesTableIso (A211 p) (Model p d)) :=
  isEmpty_of_abelian_nonabelian card_a211_eq (card_model_eq d)
    (noncomm_of_subgroup (socleModel_nonabelian (p := p) hd))

/-- **The complete order-`p⁴` pairwise separation.** All `105 = C(15,2)` pairs of
the fifteen order-`p⁴` groups are species-table-distinct. -/
theorem p4_pairwise_species_distinct (hp5 : 5 ≤ p) {d : ZMod p} (hd : d ≠ 0)
    (hd_qnr : quadraticChar (ZMod p) d = -1) :
    IsEmpty (SpeciesTableIso (A4 p) (A31 p)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (A22 p)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (A211 p)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (A1111 p)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (M6 p)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (M8 p)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (G9 p)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (CH7 p)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (Gid3 p)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (G14 p)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (Gid8 p)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (MaxClass p)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (A22 p)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (A211 p)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (A1111 p)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (M6 p)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (M8 p)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (G9 p)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (CH7 p)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (Gid3 p)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (G14 p)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (Gid8 p)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (MaxClass p)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (A22 p) (A211 p)) ∧
      IsEmpty (SpeciesTableIso (A22 p) (A1111 p)) ∧
      IsEmpty (SpeciesTableIso (A22 p) (M6 p)) ∧
      IsEmpty (SpeciesTableIso (A22 p) (M8 p)) ∧
      IsEmpty (SpeciesTableIso (A22 p) (G9 p)) ∧
      IsEmpty (SpeciesTableIso (A22 p) (CH7 p)) ∧
      IsEmpty (SpeciesTableIso (A22 p) (Gid3 p)) ∧
      IsEmpty (SpeciesTableIso (A22 p) (G14 p)) ∧
      IsEmpty (SpeciesTableIso (A22 p) (Gid8 p)) ∧
      IsEmpty (SpeciesTableIso (A22 p) (MaxClass p)) ∧
      IsEmpty (SpeciesTableIso (A22 p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (A22 p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (A211 p) (A1111 p)) ∧
      IsEmpty (SpeciesTableIso (A211 p) (M6 p)) ∧
      IsEmpty (SpeciesTableIso (A211 p) (M8 p)) ∧
      IsEmpty (SpeciesTableIso (A211 p) (G9 p)) ∧
      IsEmpty (SpeciesTableIso (A211 p) (CH7 p)) ∧
      IsEmpty (SpeciesTableIso (A211 p) (Gid3 p)) ∧
      IsEmpty (SpeciesTableIso (A211 p) (G14 p)) ∧
      IsEmpty (SpeciesTableIso (A211 p) (Gid8 p)) ∧
      IsEmpty (SpeciesTableIso (A211 p) (MaxClass p)) ∧
      IsEmpty (SpeciesTableIso (A211 p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (A211 p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (A1111 p) (M6 p)) ∧
      IsEmpty (SpeciesTableIso (A1111 p) (M8 p)) ∧
      IsEmpty (SpeciesTableIso (A1111 p) (G9 p)) ∧
      IsEmpty (SpeciesTableIso (A1111 p) (CH7 p)) ∧
      IsEmpty (SpeciesTableIso (A1111 p) (Gid3 p)) ∧
      IsEmpty (SpeciesTableIso (A1111 p) (G14 p)) ∧
      IsEmpty (SpeciesTableIso (A1111 p) (Gid8 p)) ∧
      IsEmpty (SpeciesTableIso (A1111 p) (MaxClass p)) ∧
      IsEmpty (SpeciesTableIso (A1111 p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (A1111 p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (M6 p) (M8 p)) ∧
      IsEmpty (SpeciesTableIso (M6 p) (G9 p)) ∧
      IsEmpty (SpeciesTableIso (M6 p) (CH7 p)) ∧
      IsEmpty (SpeciesTableIso (M6 p) (Gid3 p)) ∧
      IsEmpty (SpeciesTableIso (M6 p) (G14 p)) ∧
      IsEmpty (SpeciesTableIso (M6 p) (Gid8 p)) ∧
      IsEmpty (SpeciesTableIso (M6 p) (MaxClass p)) ∧
      IsEmpty (SpeciesTableIso (M6 p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (M6 p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (M8 p) (G9 p)) ∧
      IsEmpty (SpeciesTableIso (M8 p) (CH7 p)) ∧
      IsEmpty (SpeciesTableIso (M8 p) (Gid3 p)) ∧
      IsEmpty (SpeciesTableIso (M8 p) (G14 p)) ∧
      IsEmpty (SpeciesTableIso (M8 p) (Gid8 p)) ∧
      IsEmpty (SpeciesTableIso (M8 p) (MaxClass p)) ∧
      IsEmpty (SpeciesTableIso (M8 p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (M8 p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (G9 p) (CH7 p)) ∧
      IsEmpty (SpeciesTableIso (G9 p) (Gid3 p)) ∧
      IsEmpty (SpeciesTableIso (G9 p) (G14 p)) ∧
      IsEmpty (SpeciesTableIso (G9 p) (Gid8 p)) ∧
      IsEmpty (SpeciesTableIso (G9 p) (MaxClass p)) ∧
      IsEmpty (SpeciesTableIso (G9 p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (G9 p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (CH7 p) (Gid3 p)) ∧
      IsEmpty (SpeciesTableIso (CH7 p) (G14 p)) ∧
      IsEmpty (SpeciesTableIso (CH7 p) (Gid8 p)) ∧
      IsEmpty (SpeciesTableIso (CH7 p) (MaxClass p)) ∧
      IsEmpty (SpeciesTableIso (CH7 p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (CH7 p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (Gid3 p) (G14 p)) ∧
      IsEmpty (SpeciesTableIso (Gid3 p) (Gid8 p)) ∧
      IsEmpty (SpeciesTableIso (Gid3 p) (MaxClass p)) ∧
      IsEmpty (SpeciesTableIso (Gid3 p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (Gid3 p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (G14 p) (Gid8 p)) ∧
      IsEmpty (SpeciesTableIso (G14 p) (MaxClass p)) ∧
      IsEmpty (SpeciesTableIso (G14 p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (G14 p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (Gid8 p) (MaxClass p)) ∧
      IsEmpty (SpeciesTableIso (Gid8 p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (Gid8 p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (MaxClass p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (MaxClass p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (Model p 1) (Model p d)) := by
  refine ⟨isEmpty_of_card_sub_ne (card_order_p_subgroups_a4 (p := p))
    (card_order_p_subgroups_a31 (p := p))
    (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a4 (p := p))
      (card_order_p_subgroups_a22 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a4 (p := p))
      (card_order_p_subgroups_a211 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a4 (p := p))
      (card_order_p_subgroups_a1111 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a4 (p := p))
      (M6.card_order_p_subgroups_m6 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a4 (p := p))
      (M8.card_order_p_subgroups_m8 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a4 (p := p))
      (card_order_p_subgroups_g9 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a4 (p := p))
      (CH7.card_order_p_subgroups_ch7 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a4 (p := p))
      (Gid3.card_order_p_subgroups_gid3 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a4 (p := p))
      (card_order_p_subgroups_g14 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a4 (p := p))
      (Gid8.card_order_p_subgroups_gid8 (p := p) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a4 (p := p))
      (MaxClass.card_order_p_subgroups_maxClass (p := p) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a4 (p := p))
      (Model.card_order_p_subgroups (p := p) (d := 1) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a4 (p := p))
      (Model.card_order_p_subgroups (p := p) (d := d) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_tableIso_a31_a22 (p := p),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a31 (p := p))
      (card_order_p_subgroups_a211 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a31 (p := p))
      (card_order_p_subgroups_a1111 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_tableIso_a31_m6,
    isEmpty_of_card_sub_ne (card_order_p2_subgroups_a31 (p := p))
      (M8.card_order_p2_subgroups_m8 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a31 (p := p))
      (card_order_p_subgroups_g9 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a31 (p := p))
      (CH7.card_order_p_subgroups_ch7 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a31 (p := p))
      (Gid3.card_order_p_subgroups_gid3 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a31 (p := p))
      (card_order_p_subgroups_g14 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a31 (p := p))
      (Gid8.card_order_p_subgroups_gid8 (p := p) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a31 (p := p))
      (MaxClass.card_order_p_subgroups_maxClass (p := p) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a31 (p := p))
      (Model.card_order_p_subgroups (p := p) (d := 1) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a31 (p := p))
      (Model.card_order_p_subgroups (p := p) (d := d) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a22 (p := p))
      (card_order_p_subgroups_a211 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a22 (p := p))
      (card_order_p_subgroups_a1111 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p2_subgroups_a22 (p := p))
      (M6.card_order_p2_subgroups_m6 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_tableIso_a22_m8,
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a22 (p := p))
      (card_order_p_subgroups_g9 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a22 (p := p))
      (CH7.card_order_p_subgroups_ch7 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a22 (p := p))
      (Gid3.card_order_p_subgroups_gid3 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a22 (p := p))
      (card_order_p_subgroups_g14 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a22 (p := p))
      (Gid8.card_order_p_subgroups_gid8 (p := p) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a22 (p := p))
      (MaxClass.card_order_p_subgroups_maxClass (p := p) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a22 (p := p))
      (Model.card_order_p_subgroups (p := p) (d := 1) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a22 (p := p))
      (Model.card_order_p_subgroups (p := p) (d := d) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a211 (p := p))
      (card_order_p_subgroups_a1111 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a211 (p := p))
      (M6.card_order_p_subgroups_m6 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a211 (p := p))
      (M8.card_order_p_subgroups_m8 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_tableIso_a211_g9,
    isEmpty_a211_ch7,
    isEmpty_a211_gid3,
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a211 (p := p))
      (card_order_p_subgroups_g14 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_a211_gid8,
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a211 (p := p))
      (MaxClass.card_order_p_subgroups_maxClass (p := p) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_a211_model1,
    isEmpty_a211_modelD hd,
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a1111 (p := p))
      (M6.card_order_p_subgroups_m6 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a1111 (p := p))
      (M8.card_order_p_subgroups_m8 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a1111 (p := p))
      (card_order_p_subgroups_g9 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a1111 (p := p))
      (CH7.card_order_p_subgroups_ch7 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a1111 (p := p))
      (Gid3.card_order_p_subgroups_gid3 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_tableIso_a1111_g14 hp5,
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a1111 (p := p))
      (Gid8.card_order_p_subgroups_gid8 (p := p) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_tableIso_a1111_maxClass hp5,
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a1111 (p := p))
      (Model.card_order_p_subgroups (p := p) (d := 1) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_a1111 (p := p))
      (Model.card_order_p_subgroups (p := p) (d := d) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_tableIso_m6_m8,
    isEmpty_of_card_sub_ne (M6.card_order_p_subgroups_m6 (p := p))
      (card_order_p_subgroups_g9 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (M6.card_order_p_subgroups_m6 (p := p))
      (CH7.card_order_p_subgroups_ch7 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (M6.card_order_p_subgroups_m6 (p := p))
      (Gid3.card_order_p_subgroups_gid3 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (M6.card_order_p_subgroups_m6 (p := p))
      (card_order_p_subgroups_g14 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (M6.card_order_p_subgroups_m6 (p := p))
      (Gid8.card_order_p_subgroups_gid8 (p := p) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (M6.card_order_p_subgroups_m6 (p := p))
      (MaxClass.card_order_p_subgroups_maxClass (p := p) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (M6.card_order_p_subgroups_m6 (p := p))
      (Model.card_order_p_subgroups (p := p) (d := 1) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (M6.card_order_p_subgroups_m6 (p := p))
      (Model.card_order_p_subgroups (p := p) (d := d) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (M8.card_order_p_subgroups_m8 (p := p))
      (card_order_p_subgroups_g9 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (M8.card_order_p_subgroups_m8 (p := p))
      (CH7.card_order_p_subgroups_ch7 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (M8.card_order_p_subgroups_m8 (p := p))
      (Gid3.card_order_p_subgroups_gid3 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (M8.card_order_p_subgroups_m8 (p := p))
      (card_order_p_subgroups_g14 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (M8.card_order_p_subgroups_m8 (p := p))
      (Gid8.card_order_p_subgroups_gid8 (p := p) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (M8.card_order_p_subgroups_m8 (p := p))
      (MaxClass.card_order_p_subgroups_maxClass (p := p) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (M8.card_order_p_subgroups_m8 (p := p))
      (Model.card_order_p_subgroups (p := p) (d := 1) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (M8.card_order_p_subgroups_m8 (p := p))
      (Model.card_order_p_subgroups (p := p) (d := d) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_tableIso_g9_ch7,
    isEmpty_tableIso_g9_gid3,
    isEmpty_of_card_sub_ne (card_order_p_subgroups_g9 (p := p))
      (card_order_p_subgroups_g14 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_tableIso_g9_gid8,
    isEmpty_of_card_sub_ne (card_order_p_subgroups_g9 (p := p))
      (MaxClass.card_order_p_subgroups_maxClass (p := p) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p2_subgroups_g9 (p := p))
      (card_order_p2_subgroups_model (p := p) hp5 one_ne_zero)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p2_subgroups_g9 (p := p))
      (card_order_p2_subgroups_model (p := p) hp5 hd)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_tableIso_ch7_gid3,
    isEmpty_of_card_sub_ne (CH7.card_order_p_subgroups_ch7 (p := p))
      (card_order_p_subgroups_g14 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p2_subgroups_ch7 (p := p))
      (card_order_p2_subgroups_gid8 (p := p) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (CH7.card_order_p_subgroups_ch7 (p := p))
      (MaxClass.card_order_p_subgroups_maxClass (p := p) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_tableIso_ch7_model hp5 one_ne_zero,
    isEmpty_tableIso_ch7_model hp5 hd,
    isEmpty_of_card_sub_ne (Gid3.card_order_p_subgroups_gid3 (p := p))
      (card_order_p_subgroups_g14 (p := p))
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_tableIso_gid3_gid8,
    isEmpty_of_card_sub_ne (Gid3.card_order_p_subgroups_gid3 (p := p))
      (MaxClass.card_order_p_subgroups_maxClass (p := p) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p2_subgroups_gid3 (p := p))
      (card_order_p2_subgroups_model (p := p) hp5 one_ne_zero)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p2_subgroups_gid3 (p := p))
      (card_order_p2_subgroups_model (p := p) hp5 hd)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_g14 (p := p))
      (Gid8.card_order_p_subgroups_gid8 (p := p) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_tableIso_g14_maxClass hp5,
    isEmpty_of_card_sub_ne (card_order_p_subgroups_g14 (p := p))
      (Model.card_order_p_subgroups (p := p) (d := 1) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (card_order_p_subgroups_g14 (p := p))
      (Model.card_order_p_subgroups (p := p) (d := d) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (Gid8.card_order_p_subgroups_gid8 (p := p) hp5)
      (MaxClass.card_order_p_subgroups_maxClass (p := p) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_tableIso_gid8_model hp5 one_ne_zero,
    isEmpty_tableIso_gid8_model hp5 hd,
    isEmpty_of_card_sub_ne (MaxClass.card_order_p_subgroups_maxClass (p := p) hp5)
      (Model.card_order_p_subgroups (p := p) (d := 1) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_of_card_sub_ne (MaxClass.card_order_p_subgroups_maxClass (p := p) hp5)
      (Model.card_order_p_subgroups (p := p) (d := d) hp5)
      (by have := two_le_p (p := p); nlinarith),
    isEmpty_tableIso_model_model hp5 hd hd_qnr⟩

end LeanDring.P4
