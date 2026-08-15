/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.SpeciesColumn
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.ConjClasses

/-!
# The `SpeciesColumn` bridge, q=2 twin: concrete step 1 for `Coordinate 2`

The generic column-reduction machinery (`species_eq_of_abelianization_eq`,
`species_of_conjSub`, `SpeciesColsComplete`, `hasSpeciesMatch_of_reduced`,
`nonempty_dringEquiv_of_reduced`) lives in
`LeanDring/P5/Certificate/SpeciesTable/Twin1/SpeciesColumn.lean` and is stated for an
arbitrary group `G` — it is **reused verbatim**, not duplicated.

This file supplies only the `q = 2`-specific concrete first step: every species
column of `SmallGroup(3125,69) = Coordinate 2` conjugates onto one of the `148`
subgroup-class representatives `Q2.reps r`, via `Q2.reps_complete` and the generic
conjugation move `species_of_conjSub`.
-/

namespace LeanDring.DRing

open MulAction SpeciesTableEncoding

namespace Q2

open P5Presentation.Q2 (reps reps_complete conjSub)

/-- **Concrete step 1 (q=2).** Every species column `(H, h)` of `Coordinate 2` has
the same species as a column `(reps r, h')` on one of the `148` subgroup-class
representatives. -/
theorem species_col_conj_to_reps (H : Subgroup (P5Presentation.Coordinate 2))
    (h : H) :
    ∃ (r : Fin 148) (h' : reps r), species H h = species (reps r) h' := by
  obtain ⟨r, g, hg⟩ := reps_complete H
  have hmem : g⁻¹ * (h : P5Presentation.Coordinate 2) * g ∈ reps r := by
    have hh : (h : P5Presentation.Coordinate 2) ∈ conjSub g (reps r) := by
      rw [hg]; exact h.2
    rw [conjSub, Subgroup.mem_map] at hh
    obtain ⟨y, hy, hyeq⟩ := hh
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyeq
    have hyv : g⁻¹ * (h : P5Presentation.Coordinate 2) * g = y := by rw [← hyeq]; group
    rw [hyv]; exact hy
  refine ⟨r, ⟨g⁻¹ * (h : P5Presentation.Coordinate 2) * g, hmem⟩, ?_⟩
  refine species_of_conjSub (reps r) ⟨g⁻¹ * (h : P5Presentation.Coordinate 2) * g, hmem⟩
    g hg h ?_
  change (h : P5Presentation.Coordinate 2)
    = g * (g⁻¹ * (h : P5Presentation.Coordinate 2) * g) * g⁻¹
  group

end Q2

end LeanDring.DRing
