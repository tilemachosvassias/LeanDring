/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Even.MarksSlice
import LeanDring.Even.Target

/-!
# The Burnside shadow, point-level FIX-ψ², and the final reduction

**EVEN-ORDER LAYER.** No `sorry`, three standard axioms.

The slice condition of the capstone talks about ghost *vectors*; this
file exposes the underlying *point dynamics* and then closes the loop
back to the typed open target of `Target.lean`.

* `forget_psi` — **new identity**: `forget ∘ ψᵏ = forget` for every `k`
  (Adams operations are invisible to the underlying Burnside class).
* `burnsideShadow` — the idempotent projection `φ ↦ φ ∘ η ∘ forget` on
  integer points; for 2-power exponent it *is* the collapsing pushforward
  (`pointPush_psi_eq_burnsideShadow`), so every point flows to its
  shadow under iterated ψ²-pushforward.
* `pointPush_psi_two_fixed_iff` — **point-level FIX-ψ²**: the
  ψ²-pushforward-fixed integer points of `D(G)` (`G` a 2-group) are
  exactly the pullbacks of integer points of `B(G)` along `forget`.
  This is the species-free face of "fixed decorations are trivial".
* `sliceFix_iff_comp_shadow` — the slice condition is shadow-determinacy:
  a ghost vector is ψ²-symmetric iff it factors through its shadow.
* `burnsideNonempty_of_exists_sliceIdentification` — the reduction in
  its cleanest form: for finite 2-groups, `B(G) ≅ B(H)` follows from the
  *existence* of a slice-respecting lattice identification.  The D-ring
  isomorphism enters only as a source of identifications (N2), and by
  the gauge torsor all identifications are gauge translates of it.
* `SliceRecognition` / `twoGroupDtoB_of_sliceRecognition` — **the final
  reduction**: the residual open question, packaged as one Prop, provably
  implies `TwoGroupDtoB`.  Everything else in the even-order program is
  now a theorem.
-/

namespace LeanDring

namespace Even

open MonRing

universe u v

variable {G : Type u} [Group G]

/-- **Adams operations are invisible to the underlying Burnside class**:
`forget (ψᵏ x) = forget x`.  (Marks separate `B(G)`, and the `(H,1)`
species sees `ψᵏ` as `1 ↦ 1ᵏ`.) -/
theorem forget_psi (k : ℕ) (x : DRing G) :
    MonRing.forget (psi k x) = MonRing.forget x := by
  apply BurnsideRing.mark_injective
  funext H
  have h1 := DFunLike.congr_fun (DRing.species_one_eq_mark_forget H) (psi k x)
  have h2 := DFunLike.congr_fun (DRing.species_one_eq_mark_forget H) x
  simp only [RingHom.coe_comp, Function.comp_apply] at h1 h2
  have h3 : DRing.species H (1 : H) (psi k x) = DRing.species H (1 : H) x := by
    rw [DRing.species_psi, one_pow]
  have h4 : (Int.castRingHom ℂ) (BurnsideRing.mark H (MonRing.forget (psi k x))) =
      (Int.castRingHom ℂ) (BurnsideRing.mark H (MonRing.forget x)) := by
    rw [← h1, ← h2, h3]
  simpa using Int.cast_injective (α := ℂ) h4

/-- The **Burnside shadow** of an integer point: pull back along `η`,
push forward along `forget`.  The canonical projection of a point onto
its underlying mark behaviour. -/
def burnsideShadow : IntPoint (DRing G) → IntPoint (DRing G) := fun φ =>
  (φ.comp (eta : BurnsideRing G →+* DRing G)).comp MonRing.forget

theorem burnsideShadow_idempotent (φ : IntPoint (DRing G)) :
    burnsideShadow (burnsideShadow φ) = burnsideShadow φ := by
  ext x
  change φ (eta (MonRing.forget (eta (MonRing.forget x)))) =
    φ (eta (MonRing.forget x))
  rw [forget_eta]

/-- For 2-power exponent, the collapsing pushforward **is** the shadow
projection: every integer point flows to its Burnside shadow. -/
theorem pointPush_psi_eq_burnsideShadow {N : ℕ} (hN : ∀ g : G, g ^ N = 1) :
    pointPush (psi N : DRing G →+* DRing G) = burnsideShadow := by
  funext φ
  ext x
  change φ (psi N x) = φ (eta (MonRing.forget x))
  rw [psi_eq_eta_forget hN]

/-- The shadow absorbs pushforwards: `P ∘ ψᵏ⁎ = P` on points. -/
theorem burnsideShadow_pointPush_psi (k : ℕ) (φ : IntPoint (DRing G)) :
    burnsideShadow (pointPush (psi k : DRing G →+* DRing G) φ) =
      burnsideShadow φ := by
  ext x
  change φ (psi k (eta (MonRing.forget x))) = φ (eta (MonRing.forget x))
  rw [psi_eta]

/-- Shadow points are pushforward-fixed: `ψᵏ⁎ ∘ P = P` on points. -/
theorem pointPush_psi_burnsideShadow (k : ℕ) (φ : IntPoint (DRing G)) :
    pointPush (psi k : DRing G →+* DRing G) (burnsideShadow φ) =
      burnsideShadow φ := by
  ext x
  change φ (eta (MonRing.forget (psi k x))) = φ (eta (MonRing.forget x))
  rw [forget_psi]

/-- ψ²-pushforward-fixity iterates to ψ^(2^k)-fixity on points. -/
theorem pointPush_psi_pow_fixed {φ : IntPoint (DRing G)}
    (hfix : pointPush (psi 2 : DRing G →+* DRing G) φ = φ) (k : ℕ) :
    pointPush (psi (2 ^ k) : DRing G →+* DRing G) φ = φ := by
  induction k with
  | zero =>
    ext y
    change φ (psi (2 ^ 0) y) = φ y
    rw [pow_zero, psi_one]
  | succ k ih =>
    have hcomp : pointPush (psi (2 ^ (k + 1)) : DRing G →+* DRing G) φ =
        pointPush (psi (2 ^ k) : DRing G →+* DRing G)
          (pointPush (psi 2 : DRing G →+* DRing G) φ) := by
      ext y
      change φ (psi (2 ^ (k + 1)) y) = φ (psi 2 (psi (2 ^ k) y))
      rw [psi_psi, show (2 : ℕ) ^ k * 2 = 2 ^ (k + 1) from (pow_succ 2 k).symm]
    rw [hcomp, hfix, ih]

/-- **Point-level FIX-ψ²**: for a 2-group, the ψ²-pushforward-fixed
integer points of `D(G)` are exactly the pullbacks along `forget` of
integer points of the Burnside ring.  The species-free face of "a fused
decoration with `h² ∼ h` is trivial". -/
theorem pointPush_psi_two_fixed_iff {m : ℕ} (hG : ∀ g : G, g ^ 2 ^ m = 1)
    (φ : IntPoint (DRing G)) :
    pointPush (psi 2 : DRing G →+* DRing G) φ = φ ↔
      ∃ ψb : BurnsideRing G →+* ℤ, φ = ψb.comp MonRing.forget := by
  constructor
  · intro hfix
    refine ⟨φ.comp (eta : BurnsideRing G →+* DRing G), ?_⟩
    have h1 := pointPush_psi_pow_fixed hfix m
    rw [pointPush_psi_eq_burnsideShadow hG] at h1
    exact h1.symm
  · rintro ⟨ψb, rfl⟩
    ext x
    change ψb (MonRing.forget (psi 2 x)) = ψb (MonRing.forget x)
    rw [forget_psi]

/-- **The slice is shadow-determinacy**: a ghost vector is ψ²-symmetric
iff it factors through the Burnside shadow of its argument. -/
theorem sliceFix_iff_comp_shadow {m : ℕ} (hG : ∀ g : G, g ^ 2 ^ m = 1)
    (v : IntPoint (DRing G) → ℤ) :
    v ∘ pointPush (psi 2 : DRing G →+* DRing G) = v ↔
      v ∘ burnsideShadow = v := by
  constructor
  · intro hsym
    rw [← pointPush_psi_eq_burnsideShadow hG]
    exact symm_pointPush_psi_pow hsym m
  · intro hsh
    funext φ
    change v (pointPush (psi 2 : DRing G →+* DRing G) φ) = v φ
    calc v (pointPush (psi 2 : DRing G →+* DRing G) φ)
        = v (burnsideShadow (pointPush (psi 2 : DRing G →+* DRing G) φ)) :=
          (congrFun hsh _).symm
      _ = v (burnsideShadow φ) := by rw [burnsideShadow_pointPush_psi]
      _ = v φ := congrFun hsh φ

/-- **The reduction, cleanest form**: for finite 2-groups, `B(G) ≅ B(H)`
follows from the existence of a slice-respecting lattice identification.
A D-ring isomorphism supplies identifications (N2); by the gauge torsor
every identification is a gauge translate of it. -/
theorem burnsideNonempty_of_exists_sliceIdentification
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (hG : IsPGroup 2 G) (hH : IsPGroup 2 H)
    (e : IntPoint (DRing H) ≃ IntPoint (DRing G))
    (he : IdentifiesLattices e)
    (hslice : ∀ v : IntPoint (DRing G) → ℤ, v ∈ (ghost (DRing G)).range →
      (v ∘ pointPush (psi 2 : DRing G →+* DRing G) = v ↔
        (v ∘ ⇑e) ∘ pointPush (psi 2 : DRing H →+* DRing H) = v ∘ ⇑e)) :
    Nonempty (BurnsideRing G ≃+* BurnsideRing H) := by
  obtain ⟨eG⟩ := marksOntoSlice_of_isPGroup hG
  obtain ⟨eH⟩ := marksOntoSlice_of_isPGroup hH
  exact ⟨(eG.trans (fixedSubringEquivOfIdentifies e he _ _ hslice)).trans
    eH.symm⟩

/-- **The residual open question, packaged**: every D-ring isomorphism
of finite 2-groups admits a slice-respecting lattice identification.
By the gauge torsor this is equivalent to: some gauge adjustment of the
isomorphism's point bijection respects the ψ²-symmetric slice — the
An5″/TIR orbit question in its final form. -/
def SliceRecognition : Prop :=
  ∀ (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H],
    IsPGroup 2 G → IsPGroup 2 H →
    ∀ _Φ : DRing G ≃+* DRing H,
      ∃ e : IntPoint (DRing H) ≃ IntPoint (DRing G),
        IdentifiesLattices e ∧
        ∀ v : IntPoint (DRing G) → ℤ, v ∈ (ghost (DRing G)).range →
          (v ∘ pointPush (psi 2 : DRing G →+* DRing G) = v ↔
            (v ∘ ⇑e) ∘ pointPush (psi 2 : DRing H →+* DRing H) = v ∘ ⇑e)

/-- **The final reduction**: slice recognition implies the open 2-group
target.  Every other ingredient of the even-order program is a theorem;
this is the one implication left to feed. -/
theorem twoGroupDtoB_of_sliceRecognition (hrec : SliceRecognition.{u}) :
    TwoGroupDtoB.{u} := by
  intro G H _ _ _ _ hG hH hD
  obtain ⟨Φ⟩ := hD
  obtain ⟨e, he, hslice⟩ := hrec G H hG hH Φ
  exact burnsideNonempty_of_exists_sliceIdentification hG hH e he hslice

end Even

end LeanDring
