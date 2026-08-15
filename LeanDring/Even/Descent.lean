/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Even.Functorial
import LeanDring.Theory.OddOrder.OddOrder

/-!
# Descent is class combinatorics; at odd order the shadow is the identity

**EVEN-ORDER LAYER.** No `sorry`, three standard axioms.

Two results that pin down the *nature* of the open recognition question.

* `shadowDescends_iff_congr` — **descent is well-definedness on shadow
  classes**: a map of point spaces satisfies the descent condition iff
  it is constant-on-classes up to classes, i.e. iff it induces a map of
  shadow partitions.  Recognition is therefore pure finite partition
  combinatorics — no lattice arithmetic appears in the condition
  itself; the lattice enters only through which bijections are
  available (`Γ`).

  Context (hand-derived, C₂): in `D(C₂)` the within-fibre transposition
  `(C₂,1) ↔ (C₂,sgn)` preserves the ghost lattice — the ghost basis is
  `(1,1,1), (1,1,−1), (2,0,0)` and the swap of the last two coordinates
  sends `(1,1,−1) ↦ (1,−1,1) = −(1,1,−1) + (2,0,0)` — so gauges can
  move mark points to decorated points (this is Theorem G2's
  `(z,z)`-edge).  Such gauges still descend, because they preserve the
  fibre setwise.  Descent is strictly weaker than pointwise shadow
  intertwining, and the mark-point *set* is not `Γ`-stable: only the
  class partition matters.

* `burnsideShadow_eq_id_of_odd` — **at odd order the shadow is the
  identity**: every integer point of an odd-order D-ring is already a
  mark point (`AllIntegerPointsAreMarks`, Müller's spectrum theorem),
  so `P = id`, every descent condition is vacuous, and
  `shadowDescends_of_odd` records that *any* identification between
  odd-order D-rings descends.  This localizes the entire even-order
  difficulty formally: the open question exists exactly because at
  `p = 2` the shadow is a non-identity idempotent — there are integer
  points with genuinely nontrivial fused decorations.
-/

namespace LeanDring

namespace Even

open MonRing

universe u v

variable {G : Type u} [Group G] {G' : Type v} [Group G']

/-- **Descent is well-definedness on shadow classes**: a map of point
spaces satisfies the descent condition iff equal-shadow points are sent
to equal-shadow points.  The recognition question is pure partition
combinatorics. -/
theorem shadowDescends_iff_congr
    (f : IntPoint (DRing G') → IntPoint (DRing G)) :
    (∀ φ' : IntPoint (DRing G'),
        burnsideShadow (f (burnsideShadow φ')) = burnsideShadow (f φ')) ↔
      ∀ φ' ψ' : IntPoint (DRing G'), burnsideShadow φ' = burnsideShadow ψ' →
        burnsideShadow (f φ') = burnsideShadow (f ψ') := by
  constructor
  · intro hdesc φ' ψ' h
    calc burnsideShadow (f φ') = burnsideShadow (f (burnsideShadow φ')) :=
          (hdesc φ').symm
      _ = burnsideShadow (f (burnsideShadow ψ')) := by rw [h]
      _ = burnsideShadow (f ψ') := hdesc ψ'
  · intro hcongr φ'
    exact hcongr _ _ (burnsideShadow_idempotent φ')

/-- **At odd order the Burnside shadow is the identity**: every integer
point is a mark point (Müller's spectrum theorem,
`AllIntegerPointsAreMarks`), so the projection has nothing to
collapse. -/
theorem burnsideShadow_eq_id_of_odd {G : Type u} [Group G] [Fintype G]
    (hG : Odd (Fintype.card G)) (φ : IntPoint (DRing G)) :
    burnsideShadow φ = φ := by
  have hmarks := OddOrder.allIntegerPointsAreMarks_of_odd (G := G) hG
  obtain ⟨H, hs⟩ := hmarks ((Int.castRingHom ℂ).comp φ)
    (fun x => ⟨φ x, rfl⟩)
  -- `φ = mark_H ∘ forget`, hence shadow-fixed
  have hφ : ∀ x : DRing G,
      φ x = BurnsideRing.mark H (MonRing.forget x) := by
    intro x
    have h1 := DFunLike.congr_fun hs x
    have h2 := DFunLike.congr_fun (DRing.species_one_eq_mark_forget H) x
    simp only [RingHom.coe_comp, Function.comp_apply] at h1 h2
    have h3 : (Int.castRingHom ℂ) (φ x) =
        (Int.castRingHom ℂ) (BurnsideRing.mark H (MonRing.forget x)) := by
      rw [h1, h2]
    exact Int.cast_injective (α := ℂ) h3
  ext x
  change φ (eta (MonRing.forget x)) = φ x
  rw [hφ, hφ x, forget_eta]

/-- **Odd-order descent is vacuous**: any map between the point spaces
of odd-order D-rings satisfies the descent condition.  The even-order
recognition question exists exactly because the `p = 2` shadow is a
non-identity idempotent. -/
theorem shadowDescends_of_odd {G : Type u} [Group G] [Fintype G]
    {G' : Type v} [Group G'] [Fintype G']
    (hG : Odd (Fintype.card G)) (hG' : Odd (Fintype.card G'))
    (f : IntPoint (DRing G') → IntPoint (DRing G)) (φ' : IntPoint (DRing G')) :
    burnsideShadow (f (burnsideShadow φ')) = burnsideShadow (f φ') := by
  rw [burnsideShadow_eq_id_of_odd hG', burnsideShadow_eq_id_of_odd hG]

end Even

end LeanDring
