/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import Mathlib.GroupTheory.PGroup
import LeanDring.Even.Assembly
import LeanDring.Theory.DRing.MarkInjectivity

/-!
# `MarksOntoSlice` is a theorem for finite 2-groups

**EVEN-ORDER LAYER.** No `sorry`, three standard axioms.

This file discharges the `MarksOntoSlice` hypothesis of
`LeanDring.Even.burnsideNonempty_of_sliceRecognition`: for a finite
2-group `G`, the Burnside ring is isomorphic to the ψ²-fixed slice of
the ghost lattice of `D(G)`.

* `psi_eq_eta_forget` — **the collapse identity** `ψᴺ = η ∘ forget` for
  any exponent `N` annihilating `G`: the collapsing Adams operation *is*
  the Burnside retraction.  (New to the formal corpus; follows from the
  species–Adams relation, `φ_{H,1} = mark ∘ forget`, and joint species
  injectivity — all banked.)
* `symm_pointPush_psi_pow` — ψ²-symmetry of a ghost vector iterates to
  ψ^(2^k)-symmetry.
* `burnsideToSlice` — the map `b ↦ ghost (η b)` into the fixed slice;
  injective by mark separation (`BurnsideRing.mark_injective`, with the
  mark species entering as genuine integer points `mark_H ∘ forget`),
  surjective by the collapse identity plus iterated symmetry.
* `marksOntoSlice_of_isPGroup` — `MarksOntoSlice G` for finite 2-groups.
* `burnsideNonempty_of_sliceRecognition_of_isPGroup` — **the capstone**:
  for finite 2-groups, `B(G) ≅ B(H)` follows from a `D`-ring
  isomorphism whose induced point bijection respects the ψ²-symmetric
  slice — no residual hypotheses on the Burnside side.  Combined with
  `identifiesLattices_trans` (gauges compose), the 2-group `D ⇒ B`
  target is now formally reduced to the `Γ`-orbit recognition question
  and nothing else.
-/

namespace LeanDring

namespace Even

open MonRing

universe u v

variable {G : Type u} [Group G]

/-- **The collapse identity**: for any exponent `N` annihilating `G`,
the collapsing Adams operation is the Burnside retraction,
`ψᴺ = η ∘ forget`. -/
theorem psi_eq_eta_forget {N : ℕ} (hN : ∀ g : G, g ^ N = 1) (x : DRing G) :
    psi N x = eta (MonRing.forget x) := by
  refine DRing.species_injective (funext fun H => funext fun h => ?_)
  change DRing.species H h (psi N x) =
    DRing.species H h (eta (MonRing.forget x))
  have hpow : h ^ N = (1 : H) := by
    ext
    push_cast
    exact hN h
  have h1 : DRing.species H h (psi N x) = DRing.species H (1 : H) x := by
    rw [DRing.species_psi, hpow]
  have h2 := DFunLike.congr_fun (DRing.species_comp_eta H h) (MonRing.forget x)
  simp only [RingHom.coe_comp, Function.comp_apply] at h2
  have h3 := DFunLike.congr_fun (DRing.species_one_eq_mark_forget H) x
  simp only [RingHom.coe_comp, Function.comp_apply] at h3
  rw [h1, h3, h2]

/-- ψ²-symmetry of a ghost vector iterates to ψ^(2^k)-symmetry. -/
theorem symm_pointPush_psi_pow {v : IntPoint (DRing G) → ℤ}
    (hv : v ∘ pointPush (psi 2 : DRing G →+* DRing G) = v) (k : ℕ) :
    v ∘ pointPush (psi (2 ^ k) : DRing G →+* DRing G) = v := by
  induction k with
  | zero =>
    funext φ
    simp only [Function.comp_apply]
    congr 1
    ext y
    change φ (psi (2 ^ 0) y) = φ y
    rw [pow_zero, psi_one]
  | succ k ih =>
    funext φ
    have hcomp : pointPush (psi (2 ^ (k + 1)) : DRing G →+* DRing G) φ =
        pointPush (psi 2 : DRing G →+* DRing G)
          (pointPush (psi (2 ^ k) : DRing G →+* DRing G) φ) := by
      ext y
      change φ (psi (2 ^ (k + 1)) y) = φ (psi (2 ^ k) (psi 2 y))
      rw [psi_psi, show (2 : ℕ) * 2 ^ k = 2 ^ (k + 1) from (pow_succ' 2 k).symm]
    calc (v ∘ pointPush (psi (2 ^ (k + 1)) : DRing G →+* DRing G)) φ
        = v (pointPush (psi 2 : DRing G →+* DRing G)
            (pointPush (psi (2 ^ k) : DRing G →+* DRing G) φ)) := by
          rw [Function.comp_apply, hcomp]
      _ = v (pointPush (psi (2 ^ k) : DRing G →+* DRing G) φ) := congrFun hv _
      _ = v φ := congrFun ih φ

/-- The mark-ghost map `b ↦ ghost (η b)`, corestricted to the ψ²-fixed
slice of the ghost lattice. -/
noncomputable def burnsideToSlice (G : Type u) [Group G] :
    BurnsideRing G →+* fixedSubring (psi 2 : DRing G →+* DRing G) :=
  RingHom.codRestrict
    ((ghost (DRing G)).comp (eta : BurnsideRing G →+* DRing G)) _
    fun b => ghost_mem_fixedSubring (psi_eta 2 b)

@[simp] theorem coe_burnsideToSlice_apply (b : BurnsideRing G) :
    ((burnsideToSlice G b :
        fixedSubring (psi 2 : DRing G →+* DRing G)) : IntPoint (DRing G) → ℤ)
      = ghost (DRing G) (eta b) := rfl

/-- Injectivity: marks separate `B(G)`, and the mark species enter as
genuine integer points `mark_H ∘ forget` of `D(G)`. -/
theorem burnsideToSlice_injective (G : Type u) [Group G] :
    Function.Injective (burnsideToSlice G) := by
  intro a b hab
  apply BurnsideRing.mark_injective
  funext H
  have h2 := congrFun (congrArg Subtype.val hab)
    ((BurnsideRing.mark H).comp MonRing.forget)
  simpa using h2

/-- Surjectivity: a ψ²-symmetric ghost vector is ψ^(2^m)-symmetric, and
the collapse identity turns the ψ^(2^m)-image into a Burnside element. -/
theorem burnsideToSlice_surjective {m : ℕ} (hG : ∀ g : G, g ^ 2 ^ m = 1) :
    Function.Surjective (burnsideToSlice G) := by
  rintro ⟨v, hv⟩
  obtain ⟨hvrange, hvsym⟩ := mem_fixedSubring.mp hv
  obtain ⟨x, rfl⟩ := RingHom.mem_range.mp hvrange
  refine ⟨MonRing.forget x, Subtype.ext ?_⟩
  change ghost (DRing G) (eta (MonRing.forget x)) = ghost (DRing G) x
  rw [← psi_eq_eta_forget hG x, ← ghost_comp_pointPush]
  exact symm_pointPush_psi_pow hvsym m

/-- `MarksOntoSlice` holds for any group of 2-power exponent. -/
theorem marksOntoSlice_of_exponent {m : ℕ} (hG : ∀ g : G, g ^ 2 ^ m = 1) :
    MarksOntoSlice G :=
  ⟨RingEquiv.ofBijective (burnsideToSlice G)
    ⟨burnsideToSlice_injective G, burnsideToSlice_surjective hG⟩⟩

/-- **`MarksOntoSlice` is a theorem for finite 2-groups**: `B(G)` is the
ψ²-fixed slice of the ghost lattice of `D(G)`. -/
theorem marksOntoSlice_of_isPGroup [Finite G] (hG : IsPGroup 2 G) :
    MarksOntoSlice G := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hG
  exact marksOntoSlice_of_exponent (m := n) fun g => by
    rw [← hn]
    exact pow_card_eq_one'

/-- **The capstone — the 2-group wall is exactly the orbit question**:
for finite 2-groups, a `D`-ring isomorphism whose induced point
bijection respects the ψ²-symmetric slice yields `B(G) ≅ B(H)`, with no
residual hypotheses.  By `identifiesLattices_trans` the slice condition
may be arranged after any gauge `σ ∈ Γ`, so the `Γ`-orbit recognition
question of `Transport.lean` is now formally *equivalent in force* to
everything the 2-group `D ⇒ B` target still needs. -/
theorem burnsideNonempty_of_sliceRecognition_of_isPGroup
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (hG : IsPGroup 2 G) (hH : IsPGroup 2 H)
    (Φ : DRing G ≃+* DRing H)
    (hslice : ∀ v : IntPoint (DRing G) → ℤ, v ∈ (ghost (DRing G)).range →
      (v ∘ pointPush (MonRing.psi 2) = v ↔
        (v ∘ ⇑(intPointEquiv Φ)) ∘ pointPush (MonRing.psi 2) =
          v ∘ ⇑(intPointEquiv Φ))) :
    Nonempty (BurnsideRing G ≃+* BurnsideRing H) :=
  burnsideNonempty_of_sliceRecognition (marksOntoSlice_of_isPGroup hG)
    (marksOntoSlice_of_isPGroup hH) Φ hslice

end Even

end LeanDring
