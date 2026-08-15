/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.DecideIso
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-!
# Exact cyclotomic codes and the computability boundary

An element of `ℚ(ζₙ)` is represented by a rational polynomial, normalized by
remainder modulo the cyclotomic polynomial `Φₙ`.

The main theorem `reduce_eq_iff_eval_eq` proves reflection: normalized codes
are equal exactly when their complex evaluations at a primitive `n`th root
are equal. This is the proof layer needed by `SpeciesTableEncoding`.

Important computability boundary: Mathlib's `cyclotomic` and `modByMonic` are
currently noncomputable definitions, even over `ℚ`. Consequently `reduce` is
deliberately marked `noncomputable`. An executable instantiation still needs
a computable cyclotomic-polynomial generator and monic-remainder algorithm,
plus proofs that they agree with these Mathlib definitions.
-/

namespace LeanDring.CyclotomicCode

open Polynomial

/-- Normalize a rational polynomial modulo `Φₙ`. -/
noncomputable def reduce (n : ℕ) (f : ℚ[X]) : ℚ[X] :=
  f %ₘ cyclotomic n ℚ

/-- Evaluate a rational polynomial at a complex number. -/
noncomputable def eval (ζ : ℂ) (f : ℚ[X]) : ℂ :=
  f.eval₂ (algebraMap ℚ ℂ) ζ

variable {n : ℕ} [NeZero n] {ζ : ℂ}

theorem eval_cyclotomic_eq_zero (hζ : IsPrimitiveRoot ζ n) :
    eval ζ (cyclotomic n ℚ) = 0 := by
  rw [eval, eval₂_eq_eval_map, map_cyclotomic]
  exact isRoot_cyclotomic_iff.mpr hζ

/-- Reduction does not change evaluation at a primitive root. -/
theorem eval_reduce (hζ : IsPrimitiveRoot ζ n) (f : ℚ[X]) :
    eval ζ (reduce n f) = eval ζ f := by
  exact eval₂_modByMonic_eq_self_of_root
    (eval_cyclotomic_eq_zero hζ)

/-- **Cyclotomic reflection.** Equality of normalized rational-polynomial
codes is exactly equality of their values at a primitive complex root. -/
theorem reduce_eq_iff_eval_eq (hζ : IsPrimitiveRoot ζ n) (f g : ℚ[X]) :
    reduce n f = reduce n g ↔ eval ζ f = eval ζ g := by
  constructor
  · intro h
    rw [← eval_reduce hζ f, ← eval_reduce hζ g, h]
  · intro h
    unfold eval at h
    have hroot : Polynomial.aeval ζ (f - g) = 0 := by
      rw [aeval_def, eval₂_sub, h, sub_self]
    have hirr : Irreducible (cyclotomic n ℚ) :=
      cyclotomic.irreducible_rat (NeZero.pos n)
    have hmin : minpoly ℚ ζ = cyclotomic n ℚ :=
      (hζ.minpoly_eq_cyclotomic_of_irreducible hirr).symm
    have hdvd : cyclotomic n ℚ ∣ f - g := by
      rw [← hmin]
      exact minpoly.dvd ℚ ζ hroot
    exact modByMonic_eq_of_dvd_sub (cyclotomic.monic n ℚ) hdvd

/-- A monomial code evaluates to the corresponding power of `ζ`. -/
theorem eval_monomial_one (ζ : ℂ) (k : ℕ) :
    eval ζ (monomial k 1 : ℚ[X]) = ζ ^ k := by
  simp [eval]

/-- A finite sum of monomial codes evaluates to the sum of powers. -/
theorem eval_sum_monomial_one {ι : Type*} [Fintype ι] (ζ : ℂ) (e : ι → ℕ) :
    eval ζ (∑ i, (monomial (e i) 1 : ℚ[X])) = ∑ i, ζ ^ e i := by
  rw [eval, show (∑ i, (monomial (e i) 1 : ℚ[X])) =
      ∑ i ∈ Finset.univ, (monomial (e i) 1 : ℚ[X]) from rfl,
    eval₂_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval₂_monomial, map_one, one_mul]

end LeanDring.CyclotomicCode
