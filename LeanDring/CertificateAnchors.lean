/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory
import LeanDring.P5

/-!
# Certificate anchors

The verification-facing companion of `LeanDring/MainResults.lean` — read that
file first.  This one restates, in the same full-signature style, the technical
certificate propositions that tie the paper's computational claims to
kernel-checked statements: the certificate landmarks behind the main theorem,
the completeness capstones, the row equivalence, the two cell-discharge lemmas,
and the census of the two `5⁵` groups.

These are audit anchors, not headline mathematics: their value is that a reader
can go from a computational claim in the paper to a kernel-checked Lean
statement in one step.  Nothing new is proved in this file; every declaration is
a type-ascribed alias of an internal result, whose name is given in each
doc-string.

## Verification

```bash
lake env lean LeanDring/CertificateAnchors.lean
```

Every `#print axioms` line at the end of this file must report a subset of
`[propext, Classical.choice, Quot.sound]`.
-/

namespace LeanDring.Paper

open LeanDring LeanDring.DRing LeanDring.MonGSet LeanDring.P5Presentation
open MulAction

/-! ## 1. The two certificate landmarks behind the main theorem

These two results carry the computational content of the main theorem.  Their
internal names (`master`, `hmatch`) are artefacts of the emit-and-discharge
pipeline and are unsuitable for citation; the English names below are the
citeable ones. -/

/-- **Species-table entry match (the master cell theorem).**  For every column of
the species table — indexed by a subgroup-class representative `rH` together with
a transversal position `p` marked as a coset representative — and every row —
indexed by a subgroup-class representative `rK` together with an
orbit-representative character position `j` — the two twins' species-table
entries agree.

This is the cell-level statement covering all `2724 × 2724` entries.

Internal name: `LeanDring.P5Presentation.master`
(`LeanDring/P5/Certificate/RingIsomorphism/MatchAll.lean`, auto-emitted by
`python/p5_match_emit.py`). -/
theorem species_table_entry_match_coordinate12
    (rH : Fin 148) (p : Nat) (hp : p < (Q2.transData.getD rH.val []).length)
    (hrep : (Q2.cosetIsRep.getD rH.val []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps rH) (colE2 rH p hp) (rowE2 rK j hj hq)
      = species (reps rH) (colE1 rH p (transLenTr rH p hp)) (rowE1 rK j hj) :=
  LeanDring.P5Presentation.master rH p hp hrep rK j hj hq

/-- **Row-by-row column match.**  Every one of the `2724` orbit-representative
species columns of `Coordinate 2` is reproduced — row by row, under the row
equivalence `σ` (`charPairClassEquiv_coordinate12`) — by the `Coordinate 1`
column of the same index.  This is the hypothesis that
`dringEquiv_of_rowMatch_coordinate2` needs, and the last input the main theorem
was missing.

Internal name: `LeanDring.P5Presentation.hmatch`
(`LeanDring/P5/Certificate/RingIsomorphism/Twin1/Assembly.lean`). -/
theorem row_column_match_coordinate12 : ∀ i' : (Σ r : Fin 148, {p : Nat //
      p < (Q2.transData.getD r.val []).length ∧
        (Q2.cosetIsRep.getD r.val []).getD p false = true}),
    ∃ i : (Σ r : Fin 148, {p : Nat // p < (Q2.transData.getD r.val []).length ∧
        (Q2.cosetIsRep.getD r.val []).getD p false = true}),
      ∀ c : CharPairClass (Coordinate 1) ℂˣ,
        species (LeanDring.DRing.Q2.orbitRepColumns i').1
            (LeanDring.DRing.Q2.orbitRepColumns i').2 (classElt (sigmaEquiv c))
          = species (colsG1 i).1 (colsG1 i).2 (classElt c) :=
  LeanDring.P5Presentation.hmatch

/-! ## 2. The completeness capstones

The abstract glue: a *complete* family of species columns plus a checked
entrywise match upgrades to a genuine ring isomorphism. -/

/-- **Completeness capstone, `Coordinate 1`.**  The `2724` orbit-representative columns form
a complete family of species columns: every species column `(H, h)` induces the
same species ring homomorphism as one of them.

Internal name: `LeanDring.DRing.speciesColsComplete_coordinate1`
(`LeanDring/P5/Certificate/SpeciesTable/Twin1/SpeciesComplete.lean`). -/
theorem speciesColsComplete_coordinate1 :
    SpeciesColsComplete LeanDring.DRing.orbitRepColumns :=
  LeanDring.DRing.speciesColsComplete_coordinate1

/-- **Completeness capstone, `Coordinate 2`.**  The twin statement.

Internal name: `LeanDring.DRing.Q2.speciesColsComplete_coordinate2`
(`LeanDring/P5/Certificate/SpeciesTable/Twin2/SpeciesComplete.lean`). -/
theorem speciesColsComplete_coordinate2 :
    SpeciesColsComplete LeanDring.DRing.Q2.orbitRepColumns :=
  LeanDring.DRing.Q2.speciesColsComplete_coordinate2

/-- **Completeness glue, `Coordinate 1`.**  Given any finite group `G`, a family of species
columns of `G`, a bijection `σ` of character-pair classes and an entrywise match
against the complete `Coordinate 1` family, one gets `D(G) ≃+* D(Coordinate 1)`.

Internal name: `LeanDring.DRing.dringEquiv_of_rowMatch_coordinate1`. -/
theorem dringEquiv_of_rowMatch_coordinate1 {G : Type} [Group G] [Fintype G]
    {ι : Type*} (colsG : ι → SpeciesColumn G)
    (σ : CharPairClass G ℂˣ ≃ CharPairClass (Coordinate 1) ℂˣ)
    (hmatch : ∀ i' : (Σ r : Fin 148, {p : Nat //
          p < (transData.getD r.val []).length ∧
            (cosetIsRep.getD r.val []).getD p false = true}),
        ∃ i : ι, ∀ c : CharPairClass G ℂˣ,
          species (LeanDring.DRing.orbitRepColumns i').1
              (LeanDring.DRing.orbitRepColumns i').2 (classElt (σ c)) =
            species (colsG i).1 (colsG i).2 (classElt c)) :
    Nonempty (DRing G ≃+* DRing (Coordinate 1)) :=
  LeanDring.DRing.dringEquiv_of_rowMatch_coordinate1 colsG σ hmatch

/-- **Completeness glue, `Coordinate 2`.**  The twin statement — this is the theorem the
main result is an instance of.

Internal name: `LeanDring.DRing.Q2.dringEquiv_of_rowMatch_coordinate2`. -/
theorem dringEquiv_of_rowMatch_coordinate2 {G : Type} [Group G] [Fintype G]
    {ι : Type*} (colsG : ι → SpeciesColumn G)
    (σ : CharPairClass G ℂˣ ≃ CharPairClass (Coordinate 2) ℂˣ)
    (hmatch : ∀ i' : (Σ r : Fin 148, {p : Nat //
          p < (Q2.transData.getD r.val []).length ∧
            (Q2.cosetIsRep.getD r.val []).getD p false = true}),
        ∃ i : ι, ∀ c : CharPairClass G ℂˣ,
          species (LeanDring.DRing.Q2.orbitRepColumns i').1
              (LeanDring.DRing.Q2.orbitRepColumns i').2 (classElt (σ c)) =
            species (colsG i).1 (colsG i).2 (classElt c)) :
    Nonempty (DRing G ≃+* DRing (Coordinate 2)) :=
  LeanDring.DRing.Q2.dringEquiv_of_rowMatch_coordinate2 colsG σ hmatch

/-! ## 3. The row equivalence σ -/

/-- **The row equivalence σ.**  A bijection between the `2724` character-pair
classes of `Coordinate 1` and those of `Coordinate 2`, obtained by transporting
the combinatorial index map ψ along the two proven index bijections
`orbRepClass`.

Internal name: `LeanDring.P5Presentation.sigmaEquiv`
(`LeanDring/P5/Certificate/RingIsomorphism/Twin2/Sigma.lean`). -/
noncomputable def charPairClassEquiv_coordinate12 :
    CharPairClass (Coordinate 1) ℂˣ ≃ CharPairClass (Coordinate 2) ℂˣ :=
  LeanDring.P5Presentation.sigmaEquiv

/-- **The row that σ selects.**  For the pair class sitting at the `Coordinate 1`
orbit-representative character position `q` of subgroup class `r`,
`classElt (σ c)` is the basis element of the *aligned* `Coordinate 2` character —
exactly the row the per-column certificates compare against.

Internal name: `LeanDring.P5Presentation.classElt_sigmaEquiv_orbRepClass`
(`LeanDring/P5/Certificate/RingIsomorphism/Twin2/Sigma.lean`). -/
theorem classElt_charPairClassEquiv_orbitRep (r : Fin 148)
    (q : Fin (repChars.getD r.val []).length)
    (hq : (normIsRep.getD r.val []).getD q.val false = true)
    (hlt : (alnPos.getD r.val []).getD q.val 0 < (Q2.repChars2.getD r.val []).length) :
    classElt (charPairClassEquiv_coordinate12 (orbRepClass ⟨r, ⟨q, hq⟩⟩))
      = basisElt (Q2.reps r) (Q2.charOfVec2 r
          ((Q2.repChars2.getD r.val []).getD ((alnPos.getD r.val []).getD q.val 0) [])
          (Q2.validAt r (Q2.listedAt r hlt))) :=
  LeanDring.P5Presentation.classElt_sigmaEquiv_orbRepClass r q hq hlt

/-! ## 4. The two cell-discharge lemmas

The on-support species-table cells outside the `⊥` column are discharged
through one of these two
lemmas; the `⊥` column and the off-support cells go through the three
dispatchers `species_bot_column` / `species_zero_of_fixCard_zero` /
`species_zero_of_len_lt` (audited separately in `LeanDring/AxiomAudit.lean`).  The second
lemma is the paper's *trusted-computation interface*:
all 173 006 residual cells that require a real kernel `decide` pass through it. -/

/-- **Cell discharge, coincident columns.**  When the two twins' column data and
row exponent vectors are literally equal, the two species entries are equal —
by `rfl` on the fast code, at zero kernel cost.

Internal name: `LeanDring.P5Presentation.species_eq_of_data_eq`
(`LeanDring/P5/Certificate/SpeciesTable/EntrySupport.lean`). -/
theorem species_eq_of_data_eq
    (rK rH : Fin 148) (e : List (ZMod 25)) (heK : charOK (basisAt rK) e = true)
    (h : ↥(reps rH)) {T : Type*} [Fintype T] (t : T → Coordinate 1)
    (hfix : ∀ i, ((t i : Coordinate 1) : Coordinate 1 ⧸ reps rK)
      ∈ fixedPoints (reps rH) (Coordinate 1 ⧸ reps rK))
    (hinj : Function.Injective
      (fun i => ((t i : Coordinate 1) : Coordinate 1 ⧸ reps rK)))
    (hcard : Fintype.card T
      = Fintype.card (fixedPoints (reps rH) (Coordinate 1 ⧸ reps rK)))
    (hb : ∀ i, (t i)⁻¹ * (h : Coordinate 1) * (t i) ∈ reps rK)
    (rK' rH' : Fin 148) (e' : List (ZMod 25))
    (heK' : Q2.charOK2 (Q2.basisAt2 rK') e' = true)
    (h' : ↥(Q2.reps rH')) (t' : T → Coordinate 2)
    (hfix' : ∀ i, ((t' i : Coordinate 2) : Coordinate 2 ⧸ Q2.reps rK')
      ∈ fixedPoints (Q2.reps rH') (Coordinate 2 ⧸ Q2.reps rK'))
    (hinj' : Function.Injective
      (fun i => ((t' i : Coordinate 2) : Coordinate 2 ⧸ Q2.reps rK')))
    (hcard' : Fintype.card T
      = Fintype.card (fixedPoints (Q2.reps rH') (Coordinate 2 ⧸ Q2.reps rK')))
    (hb' : ∀ i, (t' i)⁻¹ * (h' : Coordinate 2) * (t' i) ∈ Q2.reps rK')
    (hD : colData1 rK h t = colData2 rK' h' t')
    (he : List.map ZMod.val e = List.map ZMod.val e') :
    species (reps rH) h (basisElt (reps rK) (charOfVec rK e heK))
      = species (Q2.reps rH') h' (basisElt (Q2.reps rK') (Q2.charOfVec2 rK' e' heK')) :=
  LeanDring.P5Presentation.species_eq_of_data_eq rK rH e heK h t hfix hinj hcard hb
    rK' rH' e' heK' h' t' hfix' hinj' hcard' hb' hD he

/-- **Cell discharge, divergent columns — the trusted-computation interface.**
When the two twins' column data differ, a single kernel `decide` on the embedded
*fast codes* reflects, through the proven cross-coordinate cyclotomic bridge
(`LeanDring.P5CyclotomicCode.sumPowers_eq_iff_value_eq`), to equality of the two
species entries in `ℂ`.

Every residual real-`decide` cell of the `5⁵` certificate is discharged by this
one lemma; the paper should cite it as the point where exact computation enters
the proof.

Internal name: `LeanDring.P5Presentation.species_eq_of_fastcode_eq`
(`LeanDring/P5/Certificate/SpeciesTable/EntrySupport.lean`). -/
theorem species_eq_of_fastcode_eq
    (rK rH : Fin 148) (e : List (ZMod 25)) (heK : charOK (basisAt rK) e = true)
    (h : ↥(reps rH)) {T : Type*} [Fintype T] (t : T → Coordinate 1)
    (hfix : ∀ i, ((t i : Coordinate 1) : Coordinate 1 ⧸ reps rK)
      ∈ fixedPoints (reps rH) (Coordinate 1 ⧸ reps rK))
    (hinj : Function.Injective
      (fun i => ((t i : Coordinate 1) : Coordinate 1 ⧸ reps rK)))
    (hcard : Fintype.card T
      = Fintype.card (fixedPoints (reps rH) (Coordinate 1 ⧸ reps rK)))
    (hb : ∀ i, (t i)⁻¹ * (h : Coordinate 1) * (t i) ∈ reps rK)
    (rK' rH' : Fin 148) (e' : List (ZMod 25))
    (heK' : Q2.charOK2 (Q2.basisAt2 rK') e' = true)
    (h' : ↥(Q2.reps rH')) {T' : Type*} [Fintype T'] (t' : T' → Coordinate 2)
    (hfix' : ∀ i, ((t' i : Coordinate 2) : Coordinate 2 ⧸ Q2.reps rK')
      ∈ fixedPoints (Q2.reps rH') (Coordinate 2 ⧸ Q2.reps rK'))
    (hinj' : Function.Injective
      (fun i => ((t' i : Coordinate 2) : Coordinate 2 ⧸ Q2.reps rK')))
    (hcard' : Fintype.card T'
      = Fintype.card (fixedPoints (Q2.reps rH') (Coordinate 2 ⧸ Q2.reps rK')))
    (hb' : ∀ i, (t' i)⁻¹ * (h' : Coordinate 2) * (t' i) ∈ Q2.reps rK')
    (hcode : LeanDring.P5CyclotomicCode.sumPowers
          (fastCode (colData1 rK (h : Coordinate 1) t) (List.map ZMod.val e))
        = LeanDring.P5CyclotomicCode.sumPowers
          (fastCode (colData2 rK' (h' : Coordinate 2) t') (List.map ZMod.val e'))) :
    species (reps rH) h (basisElt (reps rK) (charOfVec rK e heK))
      = species (Q2.reps rH') h' (basisElt (Q2.reps rK') (Q2.charOfVec2 rK' e' heK')) :=
  LeanDring.P5Presentation.species_eq_of_fastcode_eq rK rH e heK h t hfix hinj hcard hb
    rK' rH' e' heK' h' t' hfix' hinj' hcard' hb' hcode

/-! ## 5. The census of the two groups (the census layers)

The certified inventory underlying the species tables: the groups themselves,
their `676` subgroups, `148` subgroup conjugacy classes, `5236` linear characters
of the class representatives, `2724` character-pair classes, and hence the
`ℤ`-rank `2724` of each `D`-ring. -/

/-- **Coordinate model.**  The coordinate space of the pc-presentation has `5⁵ = 3125` elements.

Internal name: `LeanDring.P5Presentation.card_coordinates`. -/
theorem card_coordinates : Fintype.card Coordinates = 3125 :=
  LeanDring.P5Presentation.card_coordinates

/-- **Coordinate model.**  The kernel-computable coordinate model *is* the presented group:
`Coordinate q ≃* Group q` for `q ∈ {1, 2}`.

Internal name: `LeanDring.P5Presentation.normalFormMulEquiv`
(`LeanDring/P5/Certificate/ComputableModel/Twin1/ComputableGroup.lean`). -/
noncomputable def normalFormMulEquiv (q : ℕ) (hq : q = 1 ∨ q = 2) :
    Coordinate q ≃* LeanDring.P5Presentation.Group q :=
  LeanDring.P5Presentation.normalFormMulEquiv q hq

/-- **Subgroup inventory, `Coordinate 1`.**  The certified inventory of `676` subgroups is
**complete**: every subgroup of `Coordinate 1` occurs in it.

Internal name: `LeanDring.P5Presentation.allSubs_complete`
(`LeanDring/P5/Certificate/SubgroupInventory/Twin1/FratDischarge.lean`). -/
theorem subgroupInventory_complete_coordinate1 :
    ∀ K : Subgroup (Coordinate 1), ∃ c ∈ allSubs, c.toSubgroup = K :=
  LeanDring.P5Presentation.allSubs_complete

/-- **Subgroup inventory, `Coordinate 2`.**  The twin statement.

Internal name: `LeanDring.P5Presentation.Q2.allSubs_complete`
(`LeanDring/P5/Certificate/SubgroupInventory/Twin2/FratDischarge.lean`; also exported as
`allSubs2_complete`). -/
theorem subgroupInventory_complete_coordinate2 :
    ∀ K : Subgroup (Coordinate 2), ∃ c ∈ Q2.allSubs, c.toSubgroup = K :=
  LeanDring.P5Presentation.Q2.allSubs_complete

/-- **Subgroup inventory.**  The `676` subgroups of `Coordinate 1`, counted by the rank of their
canonical generating base: `[1, 156, 306, 181, 31, 1]`, total `676`.

Internal names: `LeanDring.P5Presentation.allBases_card`, `…allBases_strata`. -/
theorem subgroupCount_coordinate1 :
    allBases.length = 676 ∧
      (List.range 6).map (fun k => (allBases.filter (fun b => decide (b.length = k))).length)
        = [1, 156, 306, 181, 31, 1] :=
  ⟨LeanDring.P5Presentation.allBases_card, LeanDring.P5Presentation.allBases_strata⟩

/-- **Conjugacy-class representatives, `Coordinate 1`.**  The `148` representatives
exhaust the subgroup
conjugacy classes: every subgroup is conjugate to one of them.

Internal name: `LeanDring.P5Presentation.reps_complete`. -/
theorem subgroupClasses_complete_coordinate1 (K : Subgroup (Coordinate 1)) :
    ∃ r : Fin 148, ∃ g : Coordinate 1, conjSub g (reps r) = K :=
  LeanDring.P5Presentation.reps_complete K

/-- **Conjugacy-class representatives, `Coordinate 1`.**  The `148` representatives are pairwise
non-conjugate — so there are exactly `148` classes.

Internal name: `LeanDring.P5Presentation.reps_pairwise_nonconj`. -/
theorem subgroupClasses_distinct_coordinate1 (r r' : Fin 148) (hne : r ≠ r') :
    ¬ ∃ g : Coordinate 1, conjSub g (reps r) = reps r' :=
  LeanDring.P5Presentation.reps_pairwise_nonconj r r' hne

/-- **Conjugacy-class representatives, `Coordinate 2`.**  The twin statement.

Internal name: `LeanDring.P5Presentation.Q2.reps_complete`. -/
theorem subgroupClasses_complete_coordinate2 (K : Subgroup (Coordinate 2)) :
    ∃ r : Fin 148, ∃ g : Coordinate 2, Q2.conjSub g (Q2.reps r) = K :=
  LeanDring.P5Presentation.Q2.reps_complete K

/-- **Conjugacy-class representatives, `Coordinate 2`.**  The twin statement.

Internal name: `LeanDring.P5Presentation.Q2.reps_pairwise_nonconj`. -/
theorem subgroupClasses_distinct_coordinate2 (r r' : Fin 148) (hne : r ≠ r') :
    ¬ ∃ g : Coordinate 2, Q2.conjSub g (Q2.reps r) = Q2.reps r' :=
  LeanDring.P5Presentation.Q2.reps_pairwise_nonconj r r' hne

/-- **Character certification, `Coordinate 1`.**  The certified character lists
are **complete**: for
each of the `148` class representatives, the number of linear characters equals
the certified count.  Summed, this is the `5236` characters of the census.

Internal name: `LeanDring.P5Presentation.charsAt_complete_all`
(`LeanDring/P5/Certificate/Characters/Twin1/CharCompleteFinal.lean`). -/
theorem characterCount_complete_coordinate1 (r : Fin 148) :
    Nat.card (↥(reps r) →* ℂˣ) = charCounts.getD r.val 0 :=
  LeanDring.P5Presentation.charsAt_complete_all r

/-- **Character certification, `Coordinate 2`.**  The twin statement.

Internal name: `LeanDring.P5Presentation.Q2.charsAt_complete_all2`
(`LeanDring/P5/Certificate/Characters/Twin2/CharCompleteFull.lean`). -/
theorem characterCount_complete_coordinate2 (r : Fin 148) :
    Nat.card (↥(Q2.reps r) →* ℂˣ) = charCounts.getD r.val 0 :=
  LeanDring.P5Presentation.Q2.charsAt_complete_all2 r

/-- **Character-pair class count.**  The total number of character-pair classes computed on the
orbit side: `Σ_r orbitCountR r = 2724`.

Internal name: `LeanDring.P5Presentation.pairClassTotal`. -/
theorem pairClassTotal_coordinate1 : ((List.range 148).map orbitCountR).sum = 2724 :=
  LeanDring.P5Presentation.pairClassTotal

/-- **Pair-class census, `Coordinate 1`.**  The orbit-representative index map onto the abstract
character-pair classes is a bijection — the semantic content behind the count
`2724`.

Internal name: `LeanDring.P5Presentation.orbRepClass_bijective`. -/
theorem pairClassIndex_bijective_coordinate1 :
    Function.Bijective (LeanDring.P5Presentation.orbRepClass) :=
  LeanDring.P5Presentation.orbRepClass_bijective

/-- **Pair-class census, `Coordinate 2`.**  The twin statement.

Internal name: `LeanDring.P5Presentation.Q2.orbRepClass_bijective`. -/
theorem pairClassIndex_bijective_coordinate2 :
    Function.Bijective (LeanDring.P5Presentation.Q2.orbRepClass) :=
  LeanDring.P5Presentation.Q2.orbRepClass_bijective

/-- **Pair-class census, `Coordinate 1`.**  `#{(K, λ)} / conjugacy = 2724`.

Internal name: `LeanDring.P5Presentation.card_charPairClass_coordinate1`. -/
theorem card_charPairClass_coordinate1 :
    Nat.card (CharPairClass (Coordinate 1) ℂˣ) = 2724 :=
  LeanDring.P5Presentation.card_charPairClass_coordinate1

/-- **Pair-class census, `Coordinate 2`.**  `#{(K, λ)} / conjugacy = 2724`.

Internal name: `LeanDring.P5Presentation.Q2.card_charPairClass_coordinate2`. -/
theorem card_charPairClass_coordinate2 :
    Nat.card (CharPairClass (Coordinate 2) ℂˣ) = 2724 :=
  LeanDring.P5Presentation.Q2.card_charPairClass_coordinate2

end LeanDring.Paper

/-! ## 6. Axiom audit for this file -/

#print axioms LeanDring.Paper.species_table_entry_match_coordinate12
#print axioms LeanDring.Paper.row_column_match_coordinate12
#print axioms LeanDring.Paper.speciesColsComplete_coordinate1
#print axioms LeanDring.Paper.speciesColsComplete_coordinate2
#print axioms LeanDring.Paper.dringEquiv_of_rowMatch_coordinate1
#print axioms LeanDring.Paper.dringEquiv_of_rowMatch_coordinate2
#print axioms LeanDring.Paper.charPairClassEquiv_coordinate12
#print axioms LeanDring.Paper.classElt_charPairClassEquiv_orbitRep
#print axioms LeanDring.Paper.species_eq_of_data_eq
#print axioms LeanDring.Paper.species_eq_of_fastcode_eq
#print axioms LeanDring.Paper.card_coordinates
#print axioms LeanDring.Paper.normalFormMulEquiv
#print axioms LeanDring.Paper.subgroupInventory_complete_coordinate1
#print axioms LeanDring.Paper.subgroupInventory_complete_coordinate2
#print axioms LeanDring.Paper.subgroupCount_coordinate1
#print axioms LeanDring.Paper.subgroupClasses_complete_coordinate1
#print axioms LeanDring.Paper.subgroupClasses_distinct_coordinate1
#print axioms LeanDring.Paper.subgroupClasses_complete_coordinate2
#print axioms LeanDring.Paper.subgroupClasses_distinct_coordinate2
#print axioms LeanDring.Paper.characterCount_complete_coordinate1
#print axioms LeanDring.Paper.characterCount_complete_coordinate2
#print axioms LeanDring.Paper.pairClassTotal_coordinate1
#print axioms LeanDring.Paper.pairClassIndex_bijective_coordinate1
#print axioms LeanDring.Paper.pairClassIndex_bijective_coordinate2
#print axioms LeanDring.Paper.card_charPairClass_coordinate1
#print axioms LeanDring.Paper.card_charPairClass_coordinate2
