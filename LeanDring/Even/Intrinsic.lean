/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Even.Functorial

/-!
# η-recognition: the subring form of the recognition wall

**EVEN-ORDER LAYER.** No `sorry`, three standard axioms.

`Shadow.lean`/`TIR.lean` reduced the 2-group target `TwoGroupDtoB` to
*shadow recognition* (property (S)), phrased through integer points, ghost
lattices and the ψ²-shadow partition. This file records the same wall in
its most economical form — pure subring language, no points, no lattices,
no Adams operations:

* `MonRing.burnsideEquivOfMapsEta` — **[PROVEN] aligned transport**: if a
 single ring isomorphism `Φ: B^A(G) ≅ B^A(H)` carries the Burnside
 subring `η(B(G))` into `η(B(H))` and its inverse does likewise, then
 `B(G) ≅ B(H)`. No finiteness, p-group, fibre, or lattice hypotheses:
 the equivalence is `forget ∘ Φ ∘ η`, and alignment makes it invertible.
* `EtaRecognition` — **[OPEN]** for finite 2-groups, every D-ring
 isomorphism can be replaced by an *aligned* one. By the central-gauge
 dichotomy (Theorem G1) the strict
 statement "every isomorphism is aligned" is **false** — cyclic and
 generalized-quaternion 2-groups admit ring automorphisms of `D` moving
 `η(B)` — so the existential ("up to gauge") form recorded here is the
 weakest subring-level hypothesis that still closes the target.
* `twoGroupDtoB_of_etaRecognition` — **[PROVEN]** η-recognition implies
 `TwoGroupDtoB`.
* `etaRecognition_of_rigidity` — **[PROVEN]** 2-group D-rigidity implies
 η-recognition: rigidity supplies `θ: G ≃* H`, and `D(θ)` is aligned by
 the η/forget commutation squares.

Together with `Functorial.lean` this yields a second, lattice-free
sandwich

 `TwoGroupRigidity ⟹ EtaRecognition ⟹ TwoGroupDtoB`,

parallel to `TwoGroupRigidity ⟹ ShadowRecognition ⟹ TwoGroupDtoB`. For
finite 2-groups `η(B) = Fix ψ²` (`MarksSlice.lean`), so η-recognition is
the subring shadow of ψ²-recognition-up-to-gauge
(`burnsideEquivOfPsiTwoConjugate`); no formal comparison between the two
recognition properties is attempted here.
-/

namespace LeanDring

namespace MonRing

universe u v

variable {G : Type u} [Group G] {H : Type u} [Group H]
variable {A : Type v} [CommGroup A]

/-- **Aligned transport.**  A ring isomorphism `Φ: B^A(G) ≅ B^A(H)`
mapping `η(B(G))` into `η(B(H))`, with inverse mapping `η(B(H))` into
`η(B(G))`, induces `B(G) ≅ B(H)` via `forget ∘ Φ ∘ η`. -/
noncomputable def burnsideEquivOfMapsEta (Φ : MonRing G A ≃+* MonRing H A)
    (h : ∀ b : BurnsideRing G,
      Φ (eta b) ∈ Set.range (eta (G := H) (A := A)))
    (h' : ∀ b : BurnsideRing H,
      Φ.symm (eta b) ∈ Set.range (eta (G := G) (A := A))) :
    BurnsideRing G ≃+* BurnsideRing H := by
  refine RingEquiv.ofRingHom
    ((MonRing.forget).comp ((Φ : MonRing G A →+* MonRing H A).comp eta))
    ((MonRing.forget).comp
      ((Φ.symm : MonRing H A →+* MonRing G A).comp eta)) ?_ ?_
  · refine RingHom.ext fun b => ?_
    obtain ⟨c, hc⟩ := h' b
    have h1 : MonRing.forget (Φ.symm (eta b)) = c := by
      rw [← hc, forget_eta]
    have h2 : Φ (eta c) = eta b := by
      rw [hc, RingEquiv.apply_symm_apply]
    simp only [RingHom.comp_apply, RingHom.coe_coe, RingHom.id_apply]
    rw [h1, h2, forget_eta]
  · refine RingHom.ext fun b => ?_
    obtain ⟨c, hc⟩ := h b
    have h1 : MonRing.forget (Φ (eta b)) = c := by
      rw [← hc, forget_eta]
    have h2 : Φ.symm (eta c) = eta b := by
      rw [hc, RingEquiv.symm_apply_apply]
    simp only [RingHom.comp_apply, RingHom.coe_coe, RingHom.id_apply]
    rw [h1, h2, forget_eta]

end MonRing

namespace Even

open MonRing

universe u

/-- **[OPEN] η-recognition for finite 2-groups**: whenever the D-rings of
two finite 2-groups are isomorphic, *some* isomorphism between them is
aligned (carries `η(B(G))` into `η(B(H))` and conversely).  Equivalently:
every isomorphism becomes aligned after composition with a gauge
automorphism of `D(H)`.  The strict form (every isomorphism aligned) is
false by Theorem G1. -/
def EtaRecognition : Prop :=
  ∀ (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H],
    IsPGroup 2 G → IsPGroup 2 H →
      Nonempty (DRing G ≃+* DRing H) →
        ∃ Ψ : DRing G ≃+* DRing H,
          (∀ b : BurnsideRing G,
            Ψ (eta b) ∈ Set.range (eta (G := H) (A := ℂˣ))) ∧
          ∀ b : BurnsideRing H,
            Ψ.symm (eta b) ∈ Set.range (eta (G := G) (A := ℂˣ))

/-- **The lattice-free sandwich, right half**: η-recognition closes the
2-group target. -/
theorem twoGroupDtoB_of_etaRecognition (hrec : EtaRecognition.{u}) :
    TwoGroupDtoB.{u} := by
  intro G H _ _ _ _ hG hH hD
  obtain ⟨Ψ, h, h'⟩ := hrec G H hG hH hD
  exact ⟨MonRing.burnsideEquivOfMapsEta Ψ h h'⟩

/-- **The lattice-free sandwich, left half**: 2-group D-rigidity implies
η-recognition — rigidity supplies `θ: G ≃* H`, and the functorial
isomorphism `D(θ)` is aligned by the η/forget commutation squares. -/
theorem etaRecognition_of_rigidity (hrig : TwoGroupRigidity.{u}) :
    EtaRecognition.{u} := by
  intro G H _ _ _ _ hG hH hD
  obtain ⟨θ⟩ := hrig G H hG hH hD
  refine ⟨MonRing.congr θ,
    fun b => ⟨burnsideRingCongr θ b, (MonRing.congr_eta θ b).symm⟩,
    fun b => ⟨(burnsideRingCongr θ).symm b, ?_⟩⟩
  rw [RingEquiv.eq_symm_apply, MonRing.congr_eta,
    RingEquiv.apply_symm_apply]

end Even

end LeanDring
