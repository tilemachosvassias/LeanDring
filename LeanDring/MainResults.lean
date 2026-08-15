/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory
import LeanDring.Even
import LeanDring.P4
import LeanDring.P5

/-!
# Main results

**Start here.**  This file states the mathematical results of the development —
the theorems the accompanying paper is about — each restated with its **full
signature** (never inferred with a bare `:=`), so that every hypothesis a claim
depends on is visible without opening the ~950 000-line development behind it.

Nothing new is proved in this file.  Every declaration is a type-ascribed alias
of an internal result; the internal name is given in each doc-string so that a
reader can go from a paper citation to the proof in one step.

The *verification-facing* companion is `LeanDring/CertificateAnchors.lean`: it
restates, in the same style, the technical certificate propositions (census
counts, table-cell matches, completeness capstones) that tie the paper's
computational claims to kernel-checked statements.

## Vocabulary

The two groups of order `5⁵` at the heart of the main theorem are called
`Coordinate 1` and `Coordinate 2` throughout the Lean development.  They are the
kernel-computable models of two explicit pc-presentations; the SmallGroups
library (Besche–Eick–O'Brien, distributed with GAP) catalogues the presented
groups as `SmallGroup(3125, 68)` and `SmallGroup(3125, 69)` — a catalogue
identifier, not a mathematical name.  The identification with those
library labels, and the fact that the two groups are themselves non-isomorphic, are
external computational provenance (`[COMPUTED]`, established by GAP) and are
**not** formalised here.

`Coordinate q` is the *computable model*: the pc normal-form coordinate space
with a kernel-reducible multiplication.  The abstractly presented group of the
same pc presentation is `Group q = PresentedGroup (relations q)`; the two are
identified by `normalFormMulEquiv`, and
`dring_isomorphism_of_presented_5_5_twins` below restates the main theorem for
the presented groups.

## Verification

```bash
lake env lean LeanDring/MainResults.lean
```

Every `#print axioms` line at the end of this file must report a subset of
`[propext, Classical.choice, Quot.sound]` — the three standard axioms of Lean's
classical foundation.  There is no `sorry`, no custom axiom, and no
`native_decide` anywhere in the development.

`LeanDring/AxiomAudit.lean` remains the larger internal audit (1300 declarations).
-/

namespace LeanDring.Paper

open LeanDring LeanDring.DRing LeanDring.MonGSet LeanDring.P5Presentation
open MulAction

/-! ## 1. The main theorem — failure of D-ring rigidity at order `p⁵` -/

/-- **Main theorem.**  The monomial representation rings of the two
groups of order `5⁵` are isomorphic as rings:
`D(SmallGroup(3125,68)) ≅ D(SmallGroup(3125,69))`.

Together with the (external, `[COMPUTED]`) fact that those two groups are not
isomorphic, this is the counterexample to `D`-ring rigidity at order `p⁵`.

Internal name: `LeanDring.P5Presentation.dring_equiv_coordinate12`
(`LeanDring/P5/Certificate/RingIsomorphism/Twin1/Assembly.lean`). -/
theorem dring_isomorphism_of_5_5_twins :
    Nonempty (DRing (Coordinate 1) ≃+* DRing (Coordinate 2)) :=
  LeanDring.P5Presentation.dring_equiv_coordinate12

/-- **Pair-class census, `Coordinate 1`.**  `rank_ℤ D(Coordinate 1) = 2724`.

Internal name: `LeanDring.P5Presentation.rank_dring_coordinate1`. -/
theorem rank_dring_coordinate1 :
    Module.rank ℤ (DRing (Coordinate 1)) = 2724 :=
  LeanDring.P5Presentation.rank_dring_coordinate1

/-- **Pair-class census, `Coordinate 2`.**  `rank_ℤ D(Coordinate 2) = 2724`.  The two
`D`-rings have equal rank — a necessary condition for the main theorem, and the
first place where the twins agree while the groups differ.

Internal name: `LeanDring.P5Presentation.Q2.rank_dring_coordinate2`. -/
theorem rank_dring_coordinate2 :
    Module.rank ℤ (DRing (Coordinate 2)) = 2724 :=
  LeanDring.P5Presentation.Q2.rank_dring_coordinate2

/-- **Burnside-ring corollary of the main theorem.**  The two groups of order
`5⁵` have isomorphic Burnside rings: `B(G⁽¹⁾) ≅ B(G⁽²⁾)`.

This is Müller's odd-order theorem (Diss. Jena 2008, Satz 2.5.3--2.5.4) —
restated in this file as `burnsideEquivOfOddOrder` — applied to the `D`-ring
isomorphism of `dring_isomorphism_of_5_5_twins` at the odd order
`|Coordinate q| = 3125`.  It is the passage the paper's section on the
counterexample cites: the `D`-ring coincidence is not an accident of the
monomial layer, it already forces a coincidence of ordinary Burnside rings.

Internal name: `LeanDring.OddOrder.burnsideEquivOfOddOrder`
(`LeanDring/Theory/OddOrder/OddOrder.lean`), applied to
`LeanDring.P5Presentation.dring_equiv_coordinate12`. -/
noncomputable def burnside_isomorphism_of_5_5_twins :
    BurnsideRing (Coordinate 1) ≃+* BurnsideRing (Coordinate 2) :=
  LeanDring.OddOrder.burnsideEquivOfOddOrder dring_isomorphism_of_5_5_twins.some
    (by rw [show Fintype.card (Coordinate 1) = 3125 from card_coordinates]; decide)
    (by rw [show Fintype.card (Coordinate 2) = 3125 from card_coordinates]; decide)

/-- **The main theorem for the presented groups.**  The `D`-rings of the two
*abstractly presented* groups `Group q = PresentedGroup (relations q)` — the
groups given by the pc presentation itself, with no computable model
interposed — are isomorphic.

This closes the gap between the computable models and the presented groups that
caveat (ii) of the paper speaks about: `dring_isomorphism_of_5_5_twins` is a
statement about the coordinate models `Coordinate q`, and this transports it
along the normal-form isomorphisms `normalFormMulEquiv q : Coordinate q ≃* Group q`
using functoriality of the `D`-ring in group isomorphisms.

Internal names: `LeanDring.P5Presentation.normalFormMulEquiv`
(`LeanDring/P5/Certificate/ComputableModel/Twin1/ComputableGroup.lean`) and
`LeanDring.MonRing.congr` (`LeanDring/Even/Functorial.lean`). -/
theorem dring_isomorphism_of_presented_5_5_twins :
    Nonempty (DRing (P5Presentation.Group 1) ≃+* DRing (P5Presentation.Group 2)) :=
  dring_isomorphism_of_5_5_twins.map fun Φ =>
    ((MonRing.congr (normalFormMulEquiv 1 (Or.inl rfl)) :
        DRing (Coordinate 1) ≃+* DRing (P5Presentation.Group 1)).symm.trans
      (Φ.trans (MonRing.congr (normalFormMulEquiv 2 (Or.inr rfl)) :
        DRing (Coordinate 2) ≃+* DRing (P5Presentation.Group 2))))

end LeanDring.Paper

/-! ## 2. The order-`p⁴` arc -/

namespace LeanDring.Paper

open LeanDring.DRing LeanDring.P4

/-- **The exceptional-pair separation.**  For `p ≥ 5` and `d` a quadratic
non-residue mod `p`, the two
exceptional groups of order `p⁴` — models (xii) and (xiii) — have non-isomorphic
species tables.  This is the rigidity result the `5⁵` counterexample is the
boundary of.

Internal name: `LeanDring.P4.isEmpty_tableIso_model_model`
(`LeanDring/P4/TwinFinal.lean`). -/
theorem exceptional_p4_twins_separated {p : ℕ} [Fact p.Prime] [Fact (Odd p)]
    (hp5 : 5 ≤ p) {d : ZMod p} (hd : d ≠ 0)
    (hd_qnr : quadraticChar (ZMod p) d = -1) :
    IsEmpty (SpeciesTableIso (Model p 1) (Model p d)) :=
  LeanDring.P4.isEmpty_tableIso_model_model hp5 hd hd_qnr

/-- **The complete order-`p⁴` model sweep.**  All `105 = C(15,2)` pairs among the
fifteen formalized models of order `p⁴` are separated by their species tables.

Note: this is a statement about the *fifteen Lean models*.  Passing from it to a
statement about an arbitrary group of order `p⁴` uses the classical
classification of groups of order `p⁴`, which is an external input (see
`p4_species_classifies` below).

The fifteen models have fifteen distinct types, so the statement is necessarily
a `105`-fold conjunction; see `LeanDring/P4/SweepComplete.lean` for its
proof-side organisation.

Internal name: `LeanDring.P4.p4_pairwise_species_distinct`
(`LeanDring/P4/SweepComplete.lean`). -/
theorem p4_pairwise_species_distinct {p : ℕ} [Fact p.Prime] [Fact (Odd p)]
    (hp5 : 5 ≤ p) {d : ZMod p} (hd : d ≠ 0)
    (hd_qnr : quadraticChar (ZMod p) d = -1) :
    IsEmpty (SpeciesTableIso (A4 p) (A31 p)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (A22 p)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (A211 p)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (A1111 p)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (M6 p)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (M8 p)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (G9 p)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (CH7 p)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (Gid3 p)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (G14 p)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (Gid8 p)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (MaxClass p)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (A4 p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (A22 p)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (A211 p)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (A1111 p)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (M6 p)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (M8 p)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (G9 p)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (CH7 p)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (Gid3 p)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (G14 p)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (Gid8 p)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (MaxClass p)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (A31 p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (A22 p) (A211 p)) ∧
      IsEmpty (SpeciesTableIso (A22 p) (A1111 p)) ∧
      IsEmpty (SpeciesTableIso (A22 p) (M6 p)) ∧
      IsEmpty (SpeciesTableIso (A22 p) (M8 p)) ∧
      IsEmpty (SpeciesTableIso (A22 p) (G9 p)) ∧
      IsEmpty (SpeciesTableIso (A22 p) (CH7 p)) ∧
      IsEmpty (SpeciesTableIso (A22 p) (Gid3 p)) ∧
      IsEmpty (SpeciesTableIso (A22 p) (G14 p)) ∧
      IsEmpty (SpeciesTableIso (A22 p) (Gid8 p)) ∧
      IsEmpty (SpeciesTableIso (A22 p) (MaxClass p)) ∧
      IsEmpty (SpeciesTableIso (A22 p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (A22 p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (A211 p) (A1111 p)) ∧
      IsEmpty (SpeciesTableIso (A211 p) (M6 p)) ∧
      IsEmpty (SpeciesTableIso (A211 p) (M8 p)) ∧
      IsEmpty (SpeciesTableIso (A211 p) (G9 p)) ∧
      IsEmpty (SpeciesTableIso (A211 p) (CH7 p)) ∧
      IsEmpty (SpeciesTableIso (A211 p) (Gid3 p)) ∧
      IsEmpty (SpeciesTableIso (A211 p) (G14 p)) ∧
      IsEmpty (SpeciesTableIso (A211 p) (Gid8 p)) ∧
      IsEmpty (SpeciesTableIso (A211 p) (MaxClass p)) ∧
      IsEmpty (SpeciesTableIso (A211 p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (A211 p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (A1111 p) (M6 p)) ∧
      IsEmpty (SpeciesTableIso (A1111 p) (M8 p)) ∧
      IsEmpty (SpeciesTableIso (A1111 p) (G9 p)) ∧
      IsEmpty (SpeciesTableIso (A1111 p) (CH7 p)) ∧
      IsEmpty (SpeciesTableIso (A1111 p) (Gid3 p)) ∧
      IsEmpty (SpeciesTableIso (A1111 p) (G14 p)) ∧
      IsEmpty (SpeciesTableIso (A1111 p) (Gid8 p)) ∧
      IsEmpty (SpeciesTableIso (A1111 p) (MaxClass p)) ∧
      IsEmpty (SpeciesTableIso (A1111 p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (A1111 p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (M6 p) (M8 p)) ∧
      IsEmpty (SpeciesTableIso (M6 p) (G9 p)) ∧
      IsEmpty (SpeciesTableIso (M6 p) (CH7 p)) ∧
      IsEmpty (SpeciesTableIso (M6 p) (Gid3 p)) ∧
      IsEmpty (SpeciesTableIso (M6 p) (G14 p)) ∧
      IsEmpty (SpeciesTableIso (M6 p) (Gid8 p)) ∧
      IsEmpty (SpeciesTableIso (M6 p) (MaxClass p)) ∧
      IsEmpty (SpeciesTableIso (M6 p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (M6 p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (M8 p) (G9 p)) ∧
      IsEmpty (SpeciesTableIso (M8 p) (CH7 p)) ∧
      IsEmpty (SpeciesTableIso (M8 p) (Gid3 p)) ∧
      IsEmpty (SpeciesTableIso (M8 p) (G14 p)) ∧
      IsEmpty (SpeciesTableIso (M8 p) (Gid8 p)) ∧
      IsEmpty (SpeciesTableIso (M8 p) (MaxClass p)) ∧
      IsEmpty (SpeciesTableIso (M8 p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (M8 p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (G9 p) (CH7 p)) ∧
      IsEmpty (SpeciesTableIso (G9 p) (Gid3 p)) ∧
      IsEmpty (SpeciesTableIso (G9 p) (G14 p)) ∧
      IsEmpty (SpeciesTableIso (G9 p) (Gid8 p)) ∧
      IsEmpty (SpeciesTableIso (G9 p) (MaxClass p)) ∧
      IsEmpty (SpeciesTableIso (G9 p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (G9 p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (CH7 p) (Gid3 p)) ∧
      IsEmpty (SpeciesTableIso (CH7 p) (G14 p)) ∧
      IsEmpty (SpeciesTableIso (CH7 p) (Gid8 p)) ∧
      IsEmpty (SpeciesTableIso (CH7 p) (MaxClass p)) ∧
      IsEmpty (SpeciesTableIso (CH7 p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (CH7 p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (Gid3 p) (G14 p)) ∧
      IsEmpty (SpeciesTableIso (Gid3 p) (Gid8 p)) ∧
      IsEmpty (SpeciesTableIso (Gid3 p) (MaxClass p)) ∧
      IsEmpty (SpeciesTableIso (Gid3 p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (Gid3 p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (G14 p) (Gid8 p)) ∧
      IsEmpty (SpeciesTableIso (G14 p) (MaxClass p)) ∧
      IsEmpty (SpeciesTableIso (G14 p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (G14 p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (Gid8 p) (MaxClass p)) ∧
      IsEmpty (SpeciesTableIso (Gid8 p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (Gid8 p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (MaxClass p) (Model p 1)) ∧
      IsEmpty (SpeciesTableIso (MaxClass p) (Model p d)) ∧
      IsEmpty (SpeciesTableIso (Model p 1) (Model p d)) :=
  LeanDring.P4.p4_pairwise_species_distinct hp5 hd hd_qnr

/-- **The abstract order-`p⁴` classification statement.**  Species tables
classify groups of order `p⁴`, **conditional** on `P4Classification p d` — the
hypothesis that every group of order `p⁴` is isomorphic to one of the fifteen
formalized models.  That hypothesis is the classical classification of groups of
order `p⁴` ([AGW16]); it is *not* proved in this development and is the sole
external mathematical input at this layer.

Internal name: `LeanDring.P4.p4_species_classifies`
(`LeanDring/P4/Capstone.lean`). -/
theorem p4_species_classifies {p : ℕ} [Fact p.Prime] [Fact (Odd p)]
    (hp5 : 5 ≤ p) {d : ZMod p} (hd : d ≠ 0)
    (hd_qnr : quadraticChar (ZMod p) d = -1) (hclass : P4Classification p d)
    {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H]
    (hG : Nat.card G = p ^ 4) (hH : Nat.card H = p ^ 4)
    (hiso : Nonempty (SpeciesTableIso G H)) : Nonempty (G ≃* H) :=
  LeanDring.P4.p4_species_classifies hp5 hd hd_qnr hclass hG hH hiso

/-- **The exceptional order-`p⁴` case is impossible.**  The root-of-unity
equation that a species-table isomorphism between the two exceptional models
would force has no solution: a `ζ_{8p}` exponent comparison mod `8` is
contradictory.  This is the arithmetic heart of `exceptional_p4_twins_separated`.

Internal name: `LeanDring.P4.value_equation_impossible`
(`LeanDring/P4/Endgame.lean`). -/
theorem order_p4_exceptional_case_impossible (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (m β : ℕ) (d' : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I / ((8 * p : ℕ) : ℂ)) ^
        ((p : ℤ) - (1 + 2 * (β : ℤ)) ^ 2 + 8 * (m : ℤ)) ≠
      (-1 : ℂ) ^ ((p ^ 2 + 7) / 8) * (if p % 4 = 1 then (1 : ℂ) else Complex.I) *
        Complex.exp (2 * Real.pi * Complex.I / ((8 * p : ℕ) : ℂ)) ^
          (-(d' * ((p : ℤ) + 1) ^ 3)) :=
  LeanDring.P4.value_equation_impossible p hp hp2 m β d'

end LeanDring.Paper

/-! ## 3. Odd order, Gauss sign, abelian 2-groups, and the foundations -/

namespace LeanDring.Paper

open LeanDring LeanDring.DRing LeanDring.MonGSet

/-- **Müller's odd-order theorem** ([Mueller2012] Thm. 2.4; dissertation
Satz 2.5.3--2.5.4).
A ring isomorphism of the
monomial representation rings of two finite groups of **odd** order induces a
ring isomorphism of their Burnside rings.

Internal name: `LeanDring.OddOrder.burnsideEquivOfOddOrder`
(`LeanDring/Theory/OddOrder/OddOrder.lean`). -/
noncomputable def burnsideEquivOfOddOrder
    {G : Type u} {G' : Type v} [Group G] [Fintype G]
    [Group G'] [Fintype G'] (Phi : DRing G ≃+* DRing G')
    (hG : Odd (Fintype.card G)) (hG' : Odd (Fintype.card G')) :
    BurnsideRing G ≃+* BurnsideRing G' :=
  LeanDring.OddOrder.burnsideEquivOfOddOrder Phi hG hG'

/-- **Gauss's sign theorem** ([BEW98] Thm 1.5.2).  The quadratic Gauss sum
modulo an odd prime `p`
equals `√p` when `p ≡ 1 (mod 4)` and `i√p` when `p ≡ 3 (mod 4)`.

Internal name: `LeanDring.GaussSign.gauss_eq`
(`LeanDring/Theory/Gauss/GaussSignTheorem.lean`).  This result and
`LeanDring.GaussSign.rootNumber_χℂ_eq_one` are the two Mathlib-upstreamable
components of the development. -/
theorem gauss_eq (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    LeanDring.GaussSign.gauss p
      = if p % 4 = 1 then ((Real.sqrt p : ℝ) : ℂ)
        else Complex.I * ((Real.sqrt p : ℝ) : ℂ) :=
  LeanDring.GaussSign.gauss_eq hp2

/-- **The cyclic 2-group slice of `D ⇒ B`.**  For cyclic 2-groups, a `D`-ring
isomorphism induces a Burnside-ring isomorphism.

Internal name: `LeanDring.AbelianTwo.burnsideEquivOfCyclicTwoGroup`
(`LeanDring/Theory/DRing/AbelianTwo.lean`). -/
noncomputable def burnsideEquivOfCyclicTwoGroup
    {G : Type u} [Group G] [Fintype G] {G' : Type u} [Group G'] [Fintype G']
    (hGc : IsCyclic G) (hG'c : IsCyclic G') {r s : ℕ}
    (hG : Fintype.card G = 2 ^ r) (hG' : Fintype.card G' = 2 ^ s)
    (Φ : DRing G ≃+* DRing G') : BurnsideRing G ≃+* BurnsideRing G' :=
  LeanDring.AbelianTwo.burnsideEquivOfCyclicTwoGroup hGc hG'c hG hG' Φ

/-- **The species table is a complete invariant.**  An element of `D(G)` is
determined by its species values — the map `D(G) → ∏_{(H,h)} ℂ` is injective.
This is what makes "species table" a meaningful object.

Internal name: `LeanDring.DRing.species_injective`
(`LeanDring/Theory/DRing/SpeciesInjectivity.lean`). -/
theorem species_injective {G : Type u} [Group G] :
    Function.Injective (fun x : DRing G => fun (H : Subgroup G) (m : H) =>
      species H m x) :=
  LeanDring.DRing.species_injective

/-- **Marks determine elements of the Burnside ring.**  The fundamental theorem
of the Burnside ring: the mark homomorphism is injective.

Internal name: `LeanDring.BurnsideRing.mark_injective`
(`LeanDring/Theory/DRing/MarkInjectivity.lean`). -/
theorem mark_injective {G : Type u} [Group G] :
    Function.Injective
      (fun a : BurnsideRing G => fun H : Subgroup G => LeanDring.BurnsideRing.mark H a) :=
  LeanDring.BurnsideRing.mark_injective

set_option linter.unusedFintypeInType false in
-- hypothesis kept: mirrors the internal `LeanDring.DRing.rank_dring` signature,
-- which needs `[Fintype G]` for `basisOfCharPairClass`.
/-- **The rank formula.**  The `ℤ`-rank of `D(G)` equals the number of
character-pair classes `(K, λ)` up to conjugacy.  Freeness itself — the
explicit `ℤ`-basis — is `LeanDring.DRing.basisOfCharPairClass` in the same
file, and is not restated by this alias.

Internal name: `LeanDring.DRing.rank_dring` (`LeanDring/Theory/DRing/FreeBasis.lean`). -/
theorem rank_dring {G : Type u} [Group G] [Fintype G] :
    Cardinal.lift.{u + 1} (Cardinal.mk (CharPairClass G ℂˣ)) =
      Cardinal.lift.{u} (Module.rank ℤ (DRing G)) :=
  LeanDring.DRing.rank_dring

end LeanDring.Paper

/-! ## 4. Axiom audit for this file

Every declaration above depends only on the three standard axioms
`[propext, Classical.choice, Quot.sound]` (some purely computational ones on a
proper subset). -/

#print axioms LeanDring.Paper.dring_isomorphism_of_5_5_twins
#print axioms LeanDring.Paper.rank_dring_coordinate1
#print axioms LeanDring.Paper.rank_dring_coordinate2
#print axioms LeanDring.Paper.burnside_isomorphism_of_5_5_twins
#print axioms LeanDring.Paper.dring_isomorphism_of_presented_5_5_twins
#print axioms LeanDring.Paper.exceptional_p4_twins_separated
#print axioms LeanDring.Paper.p4_pairwise_species_distinct
#print axioms LeanDring.Paper.p4_species_classifies
#print axioms LeanDring.Paper.order_p4_exceptional_case_impossible
#print axioms LeanDring.Paper.burnsideEquivOfOddOrder
#print axioms LeanDring.Paper.gauss_eq
#print axioms LeanDring.Paper.burnsideEquivOfCyclicTwoGroup
#print axioms LeanDring.Paper.species_injective
#print axioms LeanDring.Paper.mark_injective
#print axioms LeanDring.Paper.rank_dring
