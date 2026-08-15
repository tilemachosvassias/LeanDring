/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.Adams

/-!
# The `D ⇒ B` transport engine

**If a ring isomorphism `D(G) ≅ D(G')` commutes with the collapsing Adams
operation, it restricts to the Burnside copies**: `B(G) ≅ B(G')`
(`DRing.burnsideEquivOfPsiEquivariant`). For 2-groups, commuting with `ψ²`
alone suffices (`DRing.burnsideEquivOfPsiTwoEquivariant`), because there the
Burnside copy is `Fix(ψ²)` (`DRing.range_eta_eq_fix_psi_two`).

This is the formal reduction behind the `D ⇒ B` theorems:

* **Müller's odd-order theorem** reduces to: every ring isomorphism between
  odd-order D-rings is `ψ`-equivariant (via Galois-intrinsicness of coprime
  Adams operations, Müller §2.5). That step needs the ghost-ring/Galois layer
  and is not formalized here.
* **2-groups** (in particular abelian 2-groups, and hence nilpotent groups
  with abelian 2-Sylow subgroup by the coprime factorization) reduce to
  `ψ²`-equivariance, which is open.

The engine itself is unconditional and sorry-free: the mathematical content
of each target theorem is exactly the ψ-equivariance hypothesis.
-/

namespace LeanDring

namespace DRing

open MonRing

universe u v

variable {G : Type u} [Group G] {G' : Type v} [Group G']

/-- On the Burnside copy, `η ∘ forget` is the identity. -/
theorem eta_forget_of_mem_range {x : DRing G}
    (hx : x ∈ Set.range (eta : BurnsideRing G →+* DRing G)) :
    eta (forget x) = x := by
  obtain ⟨b, rfl⟩ := hx
  rw [forget_eta]

/-- `ψ`-equivariance passes to the inverse isomorphism. -/
theorem symm_psi_comm (Φ : DRing G ≃+* DRing G') {N : ℕ}
    (hcomm : ∀ x, Φ (psi N x) = psi N (Φ x)) (y : DRing G') :
    Φ.symm (psi N y) = psi N (Φ.symm y) := by
  apply Φ.injective
  rw [Φ.apply_symm_apply, hcomm, Φ.apply_symm_apply]

/-- **The `D ⇒ B` transport engine.** A ring isomorphism `D(G) ≅ D(G')`
commuting with the collapsing Adams operation `ψᴺ` (any `N` annihilating
both groups) maps the Burnside copy to the Burnside copy, hence induces a
ring isomorphism `B(G) ≅ B(G')`. -/
noncomputable def burnsideEquivOfPsiEquivariant (Φ : DRing G ≃+* DRing G')
    {N : ℕ} (hNG : ∀ g : G, g ^ N = 1) (hNG' : ∀ g : G', g ^ N = 1)
    (hcomm : ∀ x, Φ (psi N x) = psi N (Φ x)) :
    BurnsideRing G ≃+* BurnsideRing G' := by
  -- `Φ` preserves the Burnside copies, since `η(B) = Fix(ψᴺ)`
  have hfwd : ∀ x ∈ Set.range (eta : BurnsideRing G →+* DRing G),
      Φ x ∈ Set.range (eta : BurnsideRing G' →+* DRing G') := by
    intro x hx
    rw [range_eta_eq_fix_psi hNG] at hx
    rw [range_eta_eq_fix_psi hNG']
    change psi N (Φ x) = Φ x
    rw [← hcomm, hx]
  have hbwd : ∀ y ∈ Set.range (eta : BurnsideRing G' →+* DRing G'),
      Φ.symm y ∈ Set.range (eta : BurnsideRing G →+* DRing G) := by
    intro y hy
    rw [range_eta_eq_fix_psi hNG'] at hy
    rw [range_eta_eq_fix_psi hNG]
    change psi N (Φ.symm y) = Φ.symm y
    rw [← symm_psi_comm Φ hcomm, hy]
  -- the induced maps: conjugate by `η` using the `forget` retraction
  refine RingEquiv.ofRingHom
    ((forget.comp (Φ : DRing G →+* DRing G')).comp eta)
    ((forget.comp (Φ.symm : DRing G' →+* DRing G)).comp eta) ?_ ?_
  · refine RingHom.ext fun c => ?_
    have h1 : eta (forget (Φ.symm (eta c))) = Φ.symm (eta c) :=
      eta_forget_of_mem_range (hbwd _ ⟨c, rfl⟩)
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, RingHom.id_apply]
    rw [h1, Φ.apply_symm_apply, forget_eta]
  · refine RingHom.ext fun b => ?_
    have h1 : eta (forget (Φ (eta b))) = Φ (eta b) :=
      eta_forget_of_mem_range (hfwd _ ⟨b, rfl⟩)
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, RingHom.id_apply]
    rw [h1, Φ.symm_apply_apply, forget_eta]

/-- `ψ²`-equivariance bootstraps to `ψ^(2^m)`-equivariance. -/
theorem psi_two_pow_comm (Φ : DRing G ≃+* DRing G')
    (hcomm : ∀ x, Φ (psi 2 x) = psi 2 (Φ x)) :
    ∀ (i : ℕ) (x : DRing G), Φ (psi (2 ^ i) x) = psi (2 ^ i) (Φ x) := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    intro x
    have h1 : psi (2 ^ (i + 1)) x = psi 2 (psi (2 ^ i) x) := by
      rw [psi_psi, ← pow_succ]
    have h2 : psi (2 ^ (i + 1)) (Φ x) = psi 2 (psi (2 ^ i) (Φ x)) := by
      rw [psi_psi, ← pow_succ]
    rw [h1, h2, hcomm, ih]

/-- **The 2-group `D ⇒ B` reduction, packaged**: for 2-groups, a ring
isomorphism `D(G) ≅ D(G')` commuting with `ψ²` alone already induces
`B(G) ≅ B(G')`. By `range_eta_eq_fix_psi_two`, `ψ²`-equivariance is exactly
what a `D ⇒ B` proof for 2-groups must supply. -/
noncomputable def burnsideEquivOfPsiTwoEquivariant (Φ : DRing G ≃+* DRing G')
    {m : ℕ} (hG : ∀ g : G, g ^ (2 ^ m) = 1) (hG' : ∀ g : G', g ^ (2 ^ m) = 1)
    (hcomm : ∀ x, Φ (psi 2 x) = psi 2 (Φ x)) :
    BurnsideRing G ≃+* BurnsideRing G' :=
  burnsideEquivOfPsiEquivariant Φ hG hG' (psi_two_pow_comm Φ hcomm m)

end DRing

end LeanDring
