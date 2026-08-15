/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.Bridge

/-!
# A verified finite decision procedure for species-table matching

Raw species values lie in `ℂ`, so they cannot be compared by computation.
Moreover, the current enumeration of complex linear characters is
noncomputable.  This module therefore separates reflection from search:
`SpeciesTableEncoding` supplies finite executable row, column, and value-code
types, together with a theorem saying that equality of codes is exactly
equality of the corresponding complex species entries.

`decideSpeciesMatch` exhaustively searches the finite encoded tables.  Its
correctness is proved in both directions for `HasSpeciesMatch`, and a positive
answer yields a ring equivalence by `equivOfSpeciesMatch`.

This does **not** decide arbitrary abstract D-ring isomorphism: the converse
that every ring equivalence preserves the distinguished character-pair basis
and permutes species is the separate, currently open basis-rigidity problem.
-/

namespace LeanDring.DRing

universe u v

open MonGSet

variable {G G' : Type u} [Group G] [Group G'] [Fintype G] [Fintype G']

/-- A column label for the unreduced species table: a subgroup and one of its
elements.  Using all such labels agrees with the input expected by
`equivOfSpeciesMatch`; duplicate conjugate columns are harmless. -/
abbrev SpeciesColumn (G : Type u) [Group G] := (H : Subgroup G) × H

/-- Finite executable presentations of two species tables over a shared
decidable code type.  `entry_eq_iff` is the trusted reflection theorem: it is
the only place where an eventual cyclotomic implementation must connect its
exact codes to the existing complex-valued species. -/
structure SpeciesTableEncoding (G G' : Type u) [Group G] [Group G']
    [Fintype G] [Fintype G'] where
  Row : Type v
  Row' : Type v
  Col : Type v
  Col' : Type v
  Code : Type v
  rowFintype : Fintype Row
  rowFintype' : Fintype Row'
  colFintype : Fintype Col
  colFintype' : Fintype Col'
  rowDecidableEq : DecidableEq Row
  rowDecidableEq' : DecidableEq Row'
  colDecidableEq : DecidableEq Col
  colDecidableEq' : DecidableEq Col'
  codeDecidableEq : DecidableEq Code
  rows : Row ≃ CharPairClass G ℂˣ
  rows' : Row' ≃ CharPairClass G' ℂˣ
  cols : Col ≃ SpeciesColumn G
  cols' : Col' ≃ SpeciesColumn G'
  entry : Col → Row → Code
  entry' : Col' → Row' → Code
  entry_eq_iff : ∀ (j : Col) (j' : Col') (r : Row) (r' : Row'),
    entry j r = entry' j' r' ↔
      species (cols j).1 (cols j).2 (classElt (rows r)) =
        species (cols' j').1 (cols' j').2 (classElt (rows' r'))

namespace SpeciesTableEncoding

variable (E : SpeciesTableEncoding G G')

/-- The finite certificate searched by `decideSpeciesMatch`: a row
permutation such that every target column occurs as a source column after
that permutation. -/
def EncodedMatch : Prop :=
  ∃ σ : E.Row → E.Row', Function.Bijective σ ∧
    ∀ j' : E.Col', ∃ j : E.Col,
      ∀ r : E.Row, E.entry j r = E.entry' j' (σ r)

private def encodedMatchDecidable : Decidable E.EncodedMatch := by
  letI := E.rowFintype
  letI := E.rowFintype'
  letI := E.colFintype
  letI := E.colFintype'
  letI := E.rowDecidableEq
  letI := E.rowDecidableEq'
  letI := E.colDecidableEq
  letI := E.colDecidableEq'
  letI := E.codeDecidableEq
  unfold EncodedMatch
  infer_instance

/-- Exhaustive Boolean search for an encoded species-table matching. -/
def decideSpeciesMatch : Bool := @decide E.EncodedMatch E.encodedMatchDecidable

/-- Validity of a supplied table-matching certificate.  Unlike
`EncodedMatch`, this does not search for either map: `σ` and `τ` are the row
and column maps emitted by the external producer, and Lean checks them. -/
def CertificateValid (σ : E.Row → E.Row') (τ : E.Col' → E.Col) : Prop :=
  Function.Bijective σ ∧
    ∀ j' : E.Col', ∀ r : E.Row,
      E.entry (τ j') r = E.entry' j' (σ r)

private def certificateValidDecidable (σ : E.Row → E.Row')
    (τ : E.Col' → E.Col) : Decidable (E.CertificateValid σ τ) := by
  letI := E.rowFintype
  letI := E.rowFintype'
  letI := E.colFintype
  letI := E.colFintype'
  letI := E.rowDecidableEq
  letI := E.rowDecidableEq'
  letI := E.colDecidableEq
  letI := E.colDecidableEq'
  letI := E.codeDecidableEq
  unfold CertificateValid
  infer_instance

/-- Kernel-executable checker for a supplied row/column matching
certificate.  Its work is linear in the matrix size, rather than a search
through row permutations. -/
def checkCertificate (σ : E.Row → E.Row') (τ : E.Col' → E.Col) : Bool :=
  @decide (E.CertificateValid σ τ) (E.certificateValidDecidable σ τ)

/-- The certificate checker accepts exactly valid supplied maps. -/
theorem checkCertificate_eq_true_iff (σ : E.Row → E.Row')
    (τ : E.Col' → E.Col) :
    E.checkCertificate σ τ = true ↔ E.CertificateValid σ τ := by
  change (@decide (E.CertificateValid σ τ)
    (E.certificateValidDecidable σ τ) = true) ↔ _
  rw [@decide_eq_true_eq _ (E.certificateValidDecidable σ τ)]

/-- The mathematical species-matching condition consumed by
`equivOfSpeciesMatch`. -/
def HasSpeciesMatch (G G' : Type u) [Group G] [Group G']
    [Fintype G] [Fintype G'] : Prop :=
  ∃ σ : CharPairClass G ℂˣ ≃ CharPairClass G' ℂˣ,
    ∀ (H' : Subgroup G') (h' : H'), ∃ (H : Subgroup G) (h : H),
      ∀ c : CharPairClass G ℂˣ,
        species H' h' (classElt (σ c)) = species H h (classElt c)

theorem encodedMatch_iff_hasSpeciesMatch :
    E.EncodedMatch ↔ HasSpeciesMatch G G' := by
  constructor
  · rintro ⟨σ, hσbij, hσ⟩
    let σe : E.Row ≃ E.Row' := Equiv.ofBijective σ hσbij
    let σ' : CharPairClass G ℂˣ ≃ CharPairClass G' ℂˣ :=
      E.rows.symm.trans (σe.trans E.rows')
    refine ⟨σ', fun H' h' => ?_⟩
    let j' : E.Col' := E.cols'.symm ⟨H', h'⟩
    obtain ⟨j, hj⟩ := hσ j'
    refine ⟨(E.cols j).1, (E.cols j).2, fun c => ?_⟩
    let r : E.Row := E.rows.symm c
    have hc : E.rows r = c := E.rows.apply_symm_apply c
    have hj' : E.cols' j' = ⟨H', h'⟩ := E.cols'.apply_symm_apply ⟨H', h'⟩
    have he := (E.entry_eq_iff j j' r (σe r)).mp (hj r)
    rw [hc, hj'] at he
    exact he.symm
  · rintro ⟨σ, hσ⟩
    let σe : E.Row ≃ E.Row' := E.rows.trans (σ.trans E.rows'.symm)
    refine ⟨σe, σe.bijective, fun j' => ?_⟩
    obtain ⟨H, h, hh⟩ := hσ (E.cols' j').1 (E.cols' j').2
    let j : E.Col := E.cols.symm ⟨H, h⟩
    refine ⟨j, fun r => ?_⟩
    apply (E.entry_eq_iff j j' r (σe r)).mpr
    have hj : E.cols j = ⟨H, h⟩ := E.cols.apply_symm_apply ⟨H, h⟩
    rw [hj]
    simpa [σe] using (hh (E.rows r)).symm

/-- A checked supplied certificate gives the mathematical species match. -/
theorem hasSpeciesMatch_of_checkCertificate {σ : E.Row → E.Row'}
    {τ : E.Col' → E.Col} (h : E.checkCertificate σ τ = true) :
    HasSpeciesMatch G G' := by
  have hv := (E.checkCertificate_eq_true_iff σ τ).mp h
  apply E.encodedMatch_iff_hasSpeciesMatch.mp
  exact ⟨σ, hv.1, fun j' => ⟨τ j', hv.2 j'⟩⟩

/-- The Boolean search is sound and complete for species matching. -/
theorem decideSpeciesMatch_eq_true_iff :
    E.decideSpeciesMatch = true ↔ HasSpeciesMatch G G' := by
  change (@decide E.EncodedMatch E.encodedMatchDecidable = true) ↔ _
  rw [@decide_eq_true_eq E.EncodedMatch E.encodedMatchDecidable,
    E.encodedMatch_iff_hasSpeciesMatch]

/-- A positive verified table search produces an abstract D-ring
isomorphism.  This is the sound direction needed for checked collision
certificates. -/
theorem nonempty_dringEquiv_of_decideSpeciesMatch
    (h : E.decideSpeciesMatch = true) :
    Nonempty (DRing G ≃+* DRing G') := by
  obtain ⟨σ, hσ⟩ := E.decideSpeciesMatch_eq_true_iff.mp h
  exact nonempty_dringEquiv_of_speciesMatch σ hσ

/-- A positive kernel check of supplied maps produces an abstract D-ring
isomorphism without running the exhaustive permutation search. -/
theorem nonempty_dringEquiv_of_checkCertificate {σ : E.Row → E.Row'}
    {τ : E.Col' → E.Col} (h : E.checkCertificate σ τ = true) :
    Nonempty (DRing G ≃+* DRing G') := by
  obtain ⟨σ', hσ'⟩ := E.hasSpeciesMatch_of_checkCertificate h
  exact nonempty_dringEquiv_of_speciesMatch σ' hσ'

end SpeciesTableEncoding

end LeanDring.DRing
