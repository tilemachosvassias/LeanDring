/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import Mathlib.GroupTheory.PGroup
import LeanDring.Theory.DRing.DtoB
import LeanDring.Theory.DRing.AbelianTwo
import LeanDring.Theory.OddOrder.OddOrder

/-!
# The even-order `D ⇒ B` target, as typed statements

**EVEN-ORDER LAYER.** No `sorry`, three standard axioms.

Müller's theorem (`OddOrder.burnsideEquivOfOddOrder`, [PROVEN]) settles
`D(G) ≅ D(H) ⟹ B(G) ≅ B(H)` for odd order. This file states the remaining
even-order problem *as mathematics*, in the exact form the hand notes
converged on, and proves the
assemblies that are free given the existing formal corpus:

* `DtoBConjecture` — **[OPEN]** the original target, all finite groups;
* `TwoGroupDtoB` — **[OPEN]** the 2-group core (N1: for nilpotent groups
 the obstruction is 2-local);
* `dtoB_of_odd` — **[PROVEN]** the odd instance of the target (Müller);
* `dtoB_of_rigidity` — **[PROVEN]** rigidity ⟹ `D ⇒ B`, the per-stratum
 assembly (abelian, metacyclic, … strata enter through their hand-proven
 rigidity statements);
* `burnsideEquivOfPsiTwoConjugate` — **[PROVEN]** the transport engine in
 *gauge form*: it suffices that `Φ` carries `ψ²` to an `Aut(D(G'))`-
 conjugate of `ψ²`. The strict-equivariance hypothesis of
 `burnsideEquivOfPsiTwoEquivariant` is genuinely too strong: by the
 central-gauge dichotomy (Theorem G1,
 hand-proven, not yet formal) cyclic and generalized-quaternion 2-groups
 admit ring automorphisms of `D` moving `η(B)`, so no theorem of the form
 "every iso is strictly ψ²-equivariant" can hold;
* `twoGroupDtoB_of_psiTwoRecognition` — **[PROVEN reduction, ⟸ direction]**
 ψ²-recognition up to gauge implies `TwoGroupDtoB`. This is the formal
 interface of the consolidated wall: the entire open content of the
 2-group case is the recognition hypothesis `hrec`.

## Negative finding

The nilpotent assembly (`D ⇒ B` for nilpotent groups with, say, abelian
Sylow-2 — hand-proven via tensor-factor recovery) is **not** free in the
current formal corpus:
`LeanDring/Theory/DRing/SplitDG.lean` is Müller's Lemma 2.6.1 unit split
`D(G) = ℤĜ ⊕ I`, *not* the coprime factorization
`D(G × H) ≅ D(G) ⊗ D(H)`. Neither the tensor splitting nor tensor-factor
recovery exists in Lean yet; formalizing the splitting is the missing
prerequisite for any formal statement beyond 2-groups.
-/

namespace LeanDring

namespace Even

open MonRing DRing

universe u v

/-- Two finite 2-groups admit a common exponent bound `2 ^ m`, as required
by the `FIX-ψ²` interface. -/
theorem exists_common_two_exponent (G : Type u) (G' : Type v)
    [Group G] [Group G'] [Finite G] [Finite G']
    (hG : IsPGroup 2 G) (hG' : IsPGroup 2 G') :
    ∃ m : ℕ, (∀ g : G, g ^ 2 ^ m = 1) ∧ ∀ g : G', g ^ 2 ^ m = 1 := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hG
  obtain ⟨n', hn'⟩ := IsPGroup.iff_card.mp hG'
  refine ⟨n + n', fun g => ?_, fun g => ?_⟩
  · have h1 : g ^ 2 ^ n = 1 := by rw [← hn]; exact pow_card_eq_one'
    calc g ^ 2 ^ (n + n') = (g ^ 2 ^ n) ^ 2 ^ n' := by rw [← pow_mul, ← pow_add]
      _ = 1 := by rw [h1, one_pow]
  · have h1 : g ^ 2 ^ n' = 1 := by rw [← hn']; exact pow_card_eq_one'
    calc g ^ 2 ^ (n + n') = (g ^ 2 ^ n') ^ 2 ^ n := by
          rw [← pow_mul, ← pow_add, Nat.add_comm]
      _ = 1 := by rw [h1, one_pow]

/-- **[OPEN] The original target**: `D(G) ≅ D(H) ⟹ B(G) ≅ B(H)` for all
finite groups.  The odd-order instance is `dtoB_of_odd` below; the
even-order instances are the subject of this file. -/
def DtoBConjecture : Prop :=
  ∀ (G G' : Type u) [Group G] [Group G'] [Fintype G] [Fintype G'],
    Nonempty (DRing G ≃+* DRing G') →
      Nonempty (BurnsideRing G ≃+* BurnsideRing G')

/-- **[OPEN] The 2-group core** of the even-order target. By the hand
reduction (N1) the nilpotent
even-order obstruction is 2-local, so this is the statement the whole
program aims at. It is *not* known whether it is true; a counterexample
would be a pair satisfying N1–N7 of the consolidation note. -/
def TwoGroupDtoB : Prop :=
  ∀ (G G' : Type u) [Group G] [Group G'] [Fintype G] [Fintype G'],
    IsPGroup 2 G → IsPGroup 2 G' →
      Nonempty (DRing G ≃+* DRing G') →
        Nonempty (BurnsideRing G ≃+* BurnsideRing G')

/-- **[PROVEN] The odd-order instance of the target** (Müller Satz 2.5.4).
Recorded here as the anchor showing the target's odd half is closed. -/
theorem dtoB_of_odd {G : Type u} {G' : Type v}
    [Group G] [Fintype G] [Group G'] [Fintype G']
    (hG : Odd (Fintype.card G)) (hG' : Odd (Fintype.card G'))
    (hD : Nonempty (DRing G ≃+* DRing G')) :
    Nonempty (BurnsideRing G ≃+* BurnsideRing G') :=
  hD.elim fun Φ => ⟨OddOrder.burnsideEquivOfOddOrder Φ hG hG'⟩

/-- **[PROVEN] Rigidity ⟹ `D ⇒ B`**, the per-stratum assembly: on any
class of groups where `D`-rigidity (`D ≅ D ⟹ G ≅ G`) is a theorem, the
target follows by functoriality of the Burnside ring.  This is how the
hand-proven rigid strata (abelian 2-groups, metacyclic, cyclic-index-2,
within-stratum extraspecial) will enter once their rigidity statements are
formalized. -/
theorem dtoB_of_rigidity {G G' : Type u} [Group G] [Group G']
    (hrig : Nonempty (DRing G ≃+* DRing G') → Nonempty (G ≃* G'))
    (hD : Nonempty (DRing G ≃+* DRing G')) :
    Nonempty (BurnsideRing G ≃+* BurnsideRing G') :=
  (hrig hD).elim fun e => ⟨burnsideRingCongr e⟩

/-- **[PROVEN] The transport engine, gauge form.**  If `Φ: D(G) ≅ D(G')`
carries `ψ²` to an `Aut(D(G'))`-conjugate of `ψ²` — i.e.
`Φ ∘ ψ² ∘ Φ⁻¹ = α ∘ ψ² ∘ α⁻¹` for some ring automorphism `α` — then
`B(G) ≅ B(G')`.  This, not strict equivariance, is the correct hypothesis:
the central gauge (Theorem G1, hand-proven) shows strict ψ²-equivariance
fails for cyclic and generalized-quaternion 2-groups while `D ⇒ B` still
holds there via the gauge `α`. -/
noncomputable def burnsideEquivOfPsiTwoConjugate
    {G : Type u} {G' : Type v} [Group G] [Group G']
    (Φ : DRing G ≃+* DRing G') {m : ℕ}
    (hG : ∀ g : G, g ^ 2 ^ m = 1) (hG' : ∀ g : G', g ^ 2 ^ m = 1)
    (α : DRing G' ≃+* DRing G')
    (hconj : ∀ y : DRing G', Φ (psi 2 (Φ.symm y)) = α (psi 2 (α.symm y))) :
    BurnsideRing G ≃+* BurnsideRing G' :=
  burnsideEquivOfPsiTwoEquivariant (Φ.trans α.symm) hG hG'
    (fun x => by
      have h := hconj (Φ x)
      rw [Φ.symm_apply_apply] at h
      simp only [RingEquiv.trans_apply]
      rw [h, α.symm_apply_apply])

/-- **[PROVEN reduction, ⟸ direction] ψ²-recognition up to gauge implies
the 2-group target.**  The hypothesis `hrec` is the precise formal
statement of the consolidated open wall: *every* ring isomorphism of
D-rings of finite 2-groups carries `ψ²` to a gauge conjugate of `ψ²`.
Everything else is banked; the entire open content of `TwoGroupDtoB` is
`hrec`. -/
theorem twoGroupDtoB_of_psiTwoRecognition
    (hrec : ∀ (G G' : Type u) [Group G] [Group G'] [Fintype G] [Fintype G'],
      IsPGroup 2 G → IsPGroup 2 G' →
        ∀ Φ : DRing G ≃+* DRing G', ∃ α : DRing G' ≃+* DRing G',
          ∀ y : DRing G', Φ (psi 2 (Φ.symm y)) = α (psi 2 (α.symm y))) :
    TwoGroupDtoB.{u} := by
  intro G G' _ _ _ _ h2 h2' hD
  obtain ⟨Φ⟩ := hD
  obtain ⟨m, hm, hm'⟩ := exists_common_two_exponent G G' h2 h2'
  obtain ⟨α, hα⟩ := hrec G G' h2 h2' Φ
  exact ⟨burnsideEquivOfPsiTwoConjugate Φ hm hm' α hα⟩

end Even

end LeanDring
