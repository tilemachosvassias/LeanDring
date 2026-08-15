/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.RingIsomorphism.MatchAll

/-!
# Stage 5 — the assembly: `D(SmallGroup(3125,68)) ≃+* D(SmallGroup(3125,69))`

The final assembly step.  `LeanDring.DRing.Q2.dringEquiv_of_rowMatch_coordinate2` already
carries the column-completeness half (`speciesColsComplete_coordinate2`)
internally; its three explicit inputs are supplied here:

* the source column family `colsG1` — the `Coordinate 1` columns indexed by the
  *same* orbit-representative index as the `Coordinate 2` columns (the twins'
  transversals have equal length, `transLenTr`), i.e. the column matching is the
  IDENTITY;
* the row equivalence `sigmaEquiv`
  (`LeanDring/P5/Certificate/RingIsomorphism/Twin2/Sigma.lean`);
* the match `hmatch`, which is the master cell theorem
  (`LeanDring/P5/Certificate/RingIsomorphism/MatchAll.lean`) after rewriting
  `classElt` on both sides into the two row basis elements (`classElt_mk`,
  `classElt_sigmaEquiv_orbRepClass`).

`master` covers every one of the `2724 × 2724` cells: the `⊥` column abstractly,
the off-support blocks by the order bound resp. the certified empty fixed-point
sets, and the `683,027` on-support cells by the per-column certificates
(`ColCert.hD` / `species_eq_of_fastcode_eq` fed by the stage-3/4 and α-aligned
all-decides).
-/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

set_option maxRecDepth 100000
set_option linter.style.setOption false

/-- The `Coordinate 1` species columns, indexed by the `Coordinate 2`
orbit-representative column index (identity column matching). -/
noncomputable def colsG1 :
    (Σ r : Fin 148, {p : Nat // p < (Q2.transData.getD r.val []).length ∧
        (Q2.cosetIsRep.getD r.val []).getD p false = true})
      → SpeciesColumn (Coordinate 1) :=
  fun x => ⟨reps x.1, colE1 x.1 x.2.val (transLenTr x.1 x.2.val x.2.2.1)⟩

set_option maxHeartbeats 4000000 in
-- kernel decide over large certified lists needs extra heartbeats
/-- **The row match.** Every orbit-representative column of `Coordinate 2` is
reproduced — row by row, under `σ` — by the `Coordinate 1` column of the same
index. -/
theorem hmatch : ∀ i' : (Σ r : Fin 148, {p : Nat //
      p < (Q2.transData.getD r.val []).length ∧
        (Q2.cosetIsRep.getD r.val []).getD p false = true}),
    ∃ i : (Σ r : Fin 148, {p : Nat // p < (Q2.transData.getD r.val []).length ∧
        (Q2.cosetIsRep.getD r.val []).getD p false = true}),
      ∀ c : CharPairClass (Coordinate 1) ℂˣ,
        species (LeanDring.DRing.Q2.orbitRepColumns i').1
            (LeanDring.DRing.Q2.orbitRepColumns i').2 (classElt (sigmaEquiv c))
          = species (colsG1 i).1 (colsG1 i).2 (classElt c) := by
  rintro ⟨rH, ⟨p, hp, hrep⟩⟩
  refine ⟨⟨rH, ⟨p, hp, hrep⟩⟩, fun c => ?_⟩
  obtain ⟨⟨rK, ⟨q, hq⟩⟩, rfl⟩ := orbRepClass_surjective c
  have h1 : classElt (orbRepClass ⟨rK, ⟨q, hq⟩⟩) = rowE1 rK q.val q.isLt := by
    rw [rowE1]; exact classElt_mk _
  have h2 : classElt (sigmaEquiv (orbRepClass ⟨rK, ⟨q, hq⟩⟩))
      = rowE2 rK q.val q.isLt hq := by
    rw [rowE2]
    exact classElt_sigmaEquiv_orbRepClass rK q hq (alnCheck_rep rK q.isLt hq).1
  rw [h1, h2]
  exact master rH p hp hrep rK q.val q.isLt hq

set_option maxHeartbeats 4000000 in
-- kernel decide over large certified lists needs extra heartbeats
/-- **The main theorem, formalised.** The `D`-rings of the two presented groups
`Coordinate 1` and `Coordinate 2` are isomorphic.

The identification of `Coordinate 1`/`Coordinate 2` with GAP's
`SmallGroup(3125,68)`/`SmallGroup(3125,69)` labels, and the fact that those two
groups are themselves non-isomorphic, are external computational provenance
([COMPUTED] — established by GAP, not formalised here); this theorem's
formalised content is exactly the ring isomorphism
`Nonempty (DRing (Coordinate 1) ≃+* DRing (Coordinate 2))`. -/
theorem dring_equiv_coordinate12 :
    Nonempty (DRing (Coordinate 1) ≃+* DRing (Coordinate 2)) :=
  LeanDring.DRing.Q2.dringEquiv_of_rowMatch_coordinate2 colsG1 sigmaEquiv hmatch

end LeanDring.P5Presentation
