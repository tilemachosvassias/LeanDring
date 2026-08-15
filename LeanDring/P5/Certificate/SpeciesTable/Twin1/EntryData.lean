/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryFix

/-!
# The concrete `Coordinate q` bridge for the fixed-coset predicate

Specialising the generic pieces of `Twin1/EntryFix.lean` to the computable group
`Coordinate q`: whether the coset `⟦t⟧` is fixed by the subgroup `⟨gH⟩` is
decided by sifting the per-generator **return elements** `t⁻¹·g·t` (a
`mulC`/`invC` product) against the well-formed echelon list `gK` of `K = ⟨gK⟩`.

This `siftB`-`Bool` characterization (`coset_fixed_iff_siftB`) is what makes the
`hfix` hypothesis of `transversalEquiv` and the `card_fixedPoints_eq_filter`
predicate discharge by kernel `decide`, at pure coordinate / `F₅` level (no
`3125`-carrier scan when `[G:K]` is small).
-/

namespace LeanDring.P5Presentation

open MulAction

/-- The return element `t⁻¹·g·t` in the `Coordinate q` group, as a pure
`mulC`/`invC` product (definitionally the group conjugate). -/
def retConj (q : ℕ) (t g : Coordinates) : Coordinates :=
  mulC q (mulC q (invC q t) g) t

/-- **The fixed-coset predicate is a `siftB` Bool.** For a well-formed echelon
list `gK` presenting `K = ⟨gK⟩`, the coset `⟦t⟧` is fixed by `H = ⟨gH⟩` iff every
generator's return element `t⁻¹·g·t` sifts into `K`.  Forward uses
`LeanDring.conj_mem_of_fixedPoints`; backward uses
`LeanDring.mem_fixedPoints_of_gens`. -/
theorem coset_fixed_iff_siftB {q : ℕ} (hq : q = 1 ∨ q = 2)
    (gK gH : List (Coordinate q)) (hwfK : WF q hq gK) (t : Coordinate q) :
    letI := coordinateGroup q hq
    ((QuotientGroup.mk t : Coordinate q ⧸ ofList q hq gK)
        ∈ fixedPoints (ofList q hq gH) (Coordinate q ⧸ ofList q hq gK))
      ↔ gH.all (fun g => siftB q gK (retConj q t g)) = true := by
  letI := coordinateGroup q hq
  have hret : ∀ g : Coordinate q, (retConj q t g : Coordinate q) = t⁻¹ * g * t :=
    fun _ => rfl
  constructor
  · intro hfix
    rw [List.all_eq_true]
    intro g hg
    have hgH : g ∈ ofList q hq gH :=
      Subgroup.subset_closure (by simpa using hg)
    have hmem : t⁻¹ * g * t ∈ ofList q hq gK :=
      LeanDring.conj_mem_of_fixedPoints (ofList q hq gH) (ofList q hq gK) t hfix ⟨g, hgH⟩
    exact (sift_mem_iff hq gK hwfK (retConj q t g)).mpr (by rw [hret g]; exact hmem)
  · intro hall
    rw [List.all_eq_true] at hall
    refine LeanDring.mem_fixedPoints_of_gens (ofList q hq gH) (ofList q hq gK)
      {x : Coordinate q | x ∈ gH} rfl t (fun g hg => ?_)
    have hg' : g ∈ gH := hg
    have := (sift_mem_iff hq gK hwfK (retConj q t g)).mp (hall g hg')
    rw [hret g] at this
    exact this

/-! ## Coset equality as a `decide` — the `hinj` input via canonical `reduceAux` -/

/-- **`reduceAux` output lies in the same left coset.** `reduceAux gs x = x · m`
for some `m ∈ ⟨gs⟩`: each `clearStep` right-multiplies by a power of a generator,
so the reduced normal form differs from `x` by an element of the generated
subgroup. -/
theorem reduceAux_right_coset {q : ℕ} (hq : q = 1 ∨ q = 2) :
    ∀ (gs : List (Coordinate q)), letI := coordinateGroup q hq;
      ∀ x : Coordinate q, ∃ m : Coordinate q, m ∈ ofList q hq gs ∧
        reduceAux q gs x = x * m := by
  letI := coordinateGroup q hq
  intro gs
  induction gs with
  | nil =>
      intro x
      exact ⟨1, Subgroup.one_mem _, by simp only [reduceAux, mul_one]⟩
  | cons p rest ih =>
      intro x
      have hle : ofList q hq rest ≤ ofList q hq (p :: rest) := by
        apply Subgroup.closure_mono
        intro y hy; exact List.mem_cons_of_mem _ hy
      have hpmem : p ∈ ofList q hq (p :: rest) :=
        Subgroup.subset_closure (by simp [List.mem_cons])
      obtain ⟨m', hm'mem, hm'eq⟩ := ih (clearStep q p x)
      refine ⟨p ^ (-(coordAt x (pivotDepth p)).val : ℤ) * m',
        Subgroup.mul_mem _ (Subgroup.zpow_mem _ hpmem _) (hle hm'mem), ?_⟩
      -- reduceAux (p::rest) x = reduceAux rest (clearStep p x) = clearStep p x * m'
      have hcs : (clearStep q p x : Coordinate q)
          = x * p ^ (-(coordAt x (pivotDepth p)).val : ℤ) := clearStep_eq hq p x
      change reduceAux q rest (clearStep q p x)
        = x * (p ^ (-(coordAt x (pivotDepth p)).val : ℤ) * m')
      rw [hm'eq, hcs, mul_assoc]

/-- **Coset equality is decided by canonical `reduceAux` forms.** `⟦x⟧ = ⟦y⟧`
iff the two reduced normal forms coincide — a `DecidableEq Coordinates` test,
hence injectivity of a transversal `fun i ↦ ⟦R i⟧` is `decide`-able through the
computable proxy `fun i ↦ reduceAux gs (R i)`. -/
theorem coset_eq_iff_reduceAux {q : ℕ} (hq : q = 1 ∨ q = 2)
    (gs : List (Coordinate q)) (hwf : WF q hq gs) (x y : Coordinate q) :
    letI := coordinateGroup q hq
    ((QuotientGroup.mk x : Coordinate q ⧸ ofList q hq gs) = QuotientGroup.mk y)
      ↔ reduceAux q gs x = reduceAux q gs y := by
  letI := coordinateGroup q hq
  constructor
  · intro hxy
    have hmem : x⁻¹ * y ∈ ofList q hq gs := QuotientGroup.eq.mp hxy
    have hstep : reduceAux q gs ((x * (x⁻¹ * y) : Coordinate q)) = reduceAux q gs x :=
      reduceAux_mul_mem hq gs hwf x (x⁻¹ * y) hmem
    rw [show (x * (x⁻¹ * y) : Coordinate q) = y by group] at hstep
    exact hstep.symm
  · intro hxy
    obtain ⟨mx, hmxmem, hmxeq⟩ := reduceAux_right_coset hq gs x
    obtain ⟨my, hmymem, hmyeq⟩ := reduceAux_right_coset hq gs y
    -- x * mx = reduceAux x = reduceAux y = y * my  ⟹  x⁻¹ y = mx my⁻¹ ∈ K
    have hxy' : (x * mx : Coordinate q) = y * my := by rw [← hmxeq, ← hmyeq, hxy]
    refine QuotientGroup.eq.mpr ?_
    have key : (x⁻¹ * y : Coordinate q) = mx * my⁻¹ := by
      apply mul_left_cancel (a := x)
      rw [← mul_assoc, mul_inv_cancel, one_mul, ← mul_assoc, hxy', mul_assoc,
        mul_inv_cancel, mul_one]
    rw [key]
    exact Subgroup.mul_mem _ hmxmem (Subgroup.inv_mem _ hmymem)

end LeanDring.P5Presentation
