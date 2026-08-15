/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import Mathlib.GroupTheory.Frattini
import LeanDring.Even.Functorial

-- Several statements below do not mention the section's `[Fintype _]` /
-- group binders, but their proofs need them for instance synthesis, so the
-- binders cannot be `omit`ted.  The linters' suggested rewrite to `[Finite _]`
-- plus `Fintype.ofFinite` is a genuine refactor, not a cleanup.
set_option linter.unusedFintypeInType false

/-!
# The separation frame: dropping "both extraspecial"

**EVEN-ORDER LAYER.** No `sorry`, three standard axioms.

The class theorem for extraspecial `2`-groups is stated with *both*
groups assumed extraspecial.  This file removes that assumption, by
recognition: the ring `D(G)` must betray that its group is extraspecial,
and within-stratum rigidity then finishes.  The three open ingredients
are typed as `Prop`s and the two assembly theorems are proved from them:

* `IsExtraspecial` — center = commutator = Frattini, of order `p`;
* `OrderTransfer` — **[OPEN]** `D(G) ≅ D(H) ⟹ |G| = |H|`;
* `RankSeparation` — **[OPEN]** at equal (extraspecial) order, equality
  of fused-pair counts forces extraspecialness;
* `ExtraspecialRigidity` — **[OPEN formally]** within-stratum
  D-rigidity: two extraspecial groups with isomorphic D-rings are
  isomorphic;
* `extraspecialRecognition_of_rankSeparation` — **[PROVEN]**
  `OrderTransfer → RankSeparation → ExtraspecialRecognition`, via the
  kernel-checked rank transfer
  `DRing.natCard_charPairClass_eq_of_dringEquiv`;
* `dtoB_extraspecial_of_recognition` — **[PROVEN]** recognition +
  rigidity give the class theorem with "both extraspecial" dropped:
  for `G` extraspecial and `H` an arbitrary finite group,
  `D(G) ≅ D(H) ⟹ B(G) ≅ B(H)`.
-/


namespace LeanDring

open MonGSet DRing

universe u

/-- An extraspecial `p`-group: the center, commutator subgroup and
Frattini subgroup coincide and have order `p`. -/
structure IsExtraspecial (p : ℕ) (G : Type u) [Group G] : Prop where
  pgroup : IsPGroup p G
  center_eq_commutator : Subgroup.center G = commutator G
  center_eq_frattini : Subgroup.center G = frattini G
  card_center : Nat.card (Subgroup.center G) = p

namespace Even

/-- **[OPEN] Order transfer**: isomorphic D-rings force equal group
orders.  (The fused-pair count transfers by the kernel-checked rank
theorem `DRing.natCard_charPairClass_eq_of_dringEquiv`; recovering `|G|`
itself is `LeanDring/Even/OrderTransfer.lean`.) -/
def OrderTransfer : Prop :=
  ∀ (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H],
    Nonempty (DRing G ≃+* DRing H) → Nat.card G = Nat.card H

/-- **[OPEN] Rank separation**: among groups of the order of an
extraspecial group `G`, only extraspecial groups attain the fused-pair
count of `G`. -/
def RankSeparation : Prop :=
  ∀ (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H],
    IsExtraspecial 2 G → Nat.card G = Nat.card H →
      Nat.card (CharPairClass G ℂˣ) = Nat.card (CharPairClass H ℂˣ) →
        IsExtraspecial 2 H

/-- **Extraspecial recognition**: the D-ring of an extraspecial group
is realized only by extraspecial groups. -/
def ExtraspecialRecognition : Prop :=
  ∀ (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H],
    IsExtraspecial 2 G → Nonempty (DRing G ≃+* DRing H) →
      IsExtraspecial 2 H

/-- **[OPEN formally] Within-stratum extraspecial D-rigidity**: two
extraspecial groups with isomorphic D-rings are isomorphic. -/
def ExtraspecialRigidity : Prop :=
  ∀ (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H],
    IsExtraspecial 2 G → IsExtraspecial 2 H →
      Nonempty (DRing G ≃+* DRing H) → Nonempty (G ≃* H)

/-- **The recognition assembly**: order transfer and rank separation
yield extraspecial recognition, via the kernel-checked transfer of the
fused-pair count along a D-ring isomorphism. -/
theorem extraspecialRecognition_of_rankSeparation
    (htr : OrderTransfer.{u}) (hsep : RankSeparation.{u}) :
    ExtraspecialRecognition.{u} := by
  intro G H _ _ _ _ hG hD
  obtain ⟨Φ⟩ := hD
  exact hsep G H hG (htr G H ⟨Φ⟩)
    (natCard_charPairClass_eq_of_dringEquiv Φ)

/-- **The endgame**: recognition plus within-stratum rigidity drop
"both extraspecial" from the class theorem — for `G` extraspecial and
`H` an arbitrary finite group, `D(G) ≅ D(H)` implies
`B(G) ≅ B(H)`. -/
theorem dtoB_extraspecial_of_recognition
    (hrec : ExtraspecialRecognition.{u}) (hrig : ExtraspecialRigidity.{u})
    (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H]
    (hG : IsExtraspecial 2 G) (hD : Nonempty (DRing G ≃+* DRing H)) :
    Nonempty (BurnsideRing G ≃+* BurnsideRing H) := by
  obtain ⟨θ⟩ := hrig G H hG (hrec G H hG hD) hD
  exact ⟨burnsideRingCongr θ⟩

end Even

end LeanDring
