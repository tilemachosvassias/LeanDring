/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.Gauss.GaussSign
import LeanDring.P4.QuadSum

/-!
# The `G₁`/`G₂` A-block specializations

This file specializes `P4.Model.species_A_block_gauss` at the
element `ca^d`, represented in `Model p d` by the normal form `s = a⁰s¹b⁰`.
It deliberately stops at the quadratic Gauss sum, so that the two entry
formulas share one algebraic core.  Evaluating the remaining canonical Gauss
sum (`gauss_eq_sqrt_mul`) and folding the quadratic phase
into a `ζ₈ₚ` exponent (`g1_exponent_identity`, `g2_exponent_identity`) are done
separately, in `TwinSeparation`.
-/

namespace LeanDring.P4

open AddChar Complex ZMod

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

namespace Model

open DRing

variable {d : ZMod p}

/-- The generator `ca^d` of the cyclic `C_{p²}` factor of `A`.
In the model's normal forms this is the distinguished coordinate `s`. -/
noncomputable def sElt (p : ℕ) [Fact p.Prime] [Fact (Odd p)] (d : ZMod p) :
    subA p d :=
  ⟨⟨0, 1, 0⟩, by rw [mem_subA_iff]; exact map_zero _⟩

@[simp] theorem sElt_coe :
    ((sElt p d : subA p d) : Model p d) = ⟨0, 1, 0⟩ := rfl

/-- The A-block formula specialized at `ca^d`.  This is the common algebraic
core of the `G₁` and `G₂` entry formulas, before evaluating the remaining
quadratic Gauss sum. -/
theorem species_sElt_gauss (χ : subA p d →* ℂˣ)
    (hψ : zChar χ ≠ 1) (κ : ZMod p)
    (hκ : bChar χ = (zChar χ).mulShift κ) :
    species (subA p d) (sElt p d) (DRing.basisElt (subA p d) χ) =
      ((χ (sElt p d) : ℂˣ) : ℂ) *
        (zChar χ (- (d - (2 : ZMod p)⁻¹ + κ) ^ 2 *
            (4 * (2 : ZMod p)⁻¹)⁻¹) *
          (χq p ((2 : ZMod p)⁻¹) * gaussSum (χq p) (zChar χ))) := by
  simpa only [sElt_coe, mul_one, one_mul, add_zero] using
    species_A_block_gauss (p := p) (d := d) χ (sElt p d) hψ one_ne_zero κ hκ

/-- **The `G₁` entry, Gauss-sum specialization.**  For `d = 1`, normalize the
central restriction of `χ` to Mathlib's standard additive character and its
restriction to `b` to the shift indexed by `β`.  The resulting formula has
the exact `β`-dependent quadratic phase; the closed `√p·ζ₈ₚ^…` value follows
from it in `g1_entry_form`, once the Gauss sum is evaluated. -/
theorem g1_entry_gauss_form (χ : subA p (1 : ZMod p) →* ℂˣ) (β : ZMod p)
    (hz : zChar χ = (stdAddChar : AddChar (ZMod p) ℂ))
    (hb : bChar χ = (stdAddChar : AddChar (ZMod p) ℂ).mulShift β) :
    species (subA p (1 : ZMod p)) (sElt p 1)
        (DRing.basisElt (subA p (1 : ZMod p)) χ) =
      ((χ (sElt p 1) : ℂˣ) : ℂ) *
        (stdAddChar (- ((1 : ZMod p) - (2 : ZMod p)⁻¹ + β) ^ 2 *
            (4 * (2 : ZMod p)⁻¹)⁻¹) *
          (χq p ((2 : ZMod p)⁻¹) * LeanDring.GaussSign.gauss p)) := by
  have hstd : (stdAddChar : AddChar (ZMod p) ℂ) ≠ 1 := by
    simpa using (isPrimitive_stdAddChar p)
      (one_ne_zero : (1 : ZMod p) ≠ 0)
  have hψ : zChar χ ≠ 1 := by rwa [hz]
  have hκ : bChar χ = (zChar χ).mulShift β := by rwa [hz]
  rw [species_sElt_gauss χ hψ β hκ, hz]
  rfl

/-- **The `G₂` entry, Gauss-sum specialization.**  For nonzero `d`, normalize
the central character by the shift `d⁻¹` and the `b`-character by `-1`, as
here.  The relative `b`-coordinate is then `κ = -d`.  This theorem
records the exact shifted Gauss sum to which Gauss's sign theorem is applied
in `g2_entry_form`; it does not itself use that theorem. -/
theorem g2_entry_gauss_form (χ : subA p d →* ℂˣ) (hd : d ≠ 0)
    (hz : zChar χ = (stdAddChar : AddChar (ZMod p) ℂ).mulShift d⁻¹)
    (hb : bChar χ = (stdAddChar : AddChar (ZMod p) ℂ).mulShift (-1)) :
    species (subA p d) (sElt p d) (DRing.basisElt (subA p d) χ) =
      ((χ (sElt p d) : ℂˣ) : ℂ) *
        (((stdAddChar : AddChar (ZMod p) ℂ).mulShift d⁻¹)
            (- (d - (2 : ZMod p)⁻¹ - d) ^ 2 *
              (4 * (2 : ZMod p)⁻¹)⁻¹) *
          (χq p ((2 : ZMod p)⁻¹) *
            gaussSum (χq p)
              ((stdAddChar : AddChar (ZMod p) ℂ).mulShift d⁻¹))) := by
  have hstd : (stdAddChar : AddChar (ZMod p) ℂ) ≠ 1 := by
    simpa using (isPrimitive_stdAddChar p)
      (one_ne_zero : (1 : ZMod p) ≠ 0)
  have hshift :
      (stdAddChar : AddChar (ZMod p) ℂ).mulShift d⁻¹ ≠ 1 :=
    (IsPrimitive.of_ne_one hstd) (inv_ne_zero hd)
  have hψ : zChar χ ≠ 1 := by rwa [hz]
  have hκ : bChar χ = (zChar χ).mulShift (-d) := by
    rw [hz, hb, mulShift_mulShift]
    congr 1
    field_simp
  rw [species_sElt_gauss χ hψ (-d) hκ, hz]
  simp only [sub_eq_add_neg]

end Model

end LeanDring.P4
