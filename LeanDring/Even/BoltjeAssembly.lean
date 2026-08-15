/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Even.ConductorAtSpecies
import LeanDring.Even.ATSeparation

/-!
# The conductor dictionary, assembled: `Boltje + group facts ⟹ D(B) ≇ D(C)`

**EVEN-ORDER LAYER.** Inside the root module's build closure and audit:
no `sorry`, three standard axioms. The results here are
verified *implications*; their hypotheses are named `Prop`s (see §7.6 of
the paper).

`LeanDring/Even/ConductorAtSpecies.lean` §12 reduced the whole conductor dictionary
to a single named `Prop`, `BoltjeIntegrality`:

```
IsolatingValue H h n ↔ |N_G(H, hH')| ∣ n · |H'|      (for every pair (H, hH'))
```

and proved `isIndexValue_iff_of_boltje`: given it, the ring-theoretic
predicate `IsIndexValue` (conductor multiplicities, the only thing a
D-ring isomorphism sees) coincides with the group-theoretic `ind*`-value
predicate `IsIndStarValue`.

This file is the last mile: it restates the group-theoretic hypotheses of
Theorem BC-n (`LeanDring/Even/BCSeparation.lean`) and of the Theorem-AT endgame
(`LeanDring/Even/ATSeparation.lean`) **in `IsIndStarValue` form** — i.e. purely in
the language of subgroups, pair normalizers and commutator subgroups, the
form in which GAP verifies them and in which the mathematics is stated —
and proves both separation theorems from those, given `BoltjeIntegrality`.

The chain is then, end to end and kernel-checked:

* `BoltjeIntegrality` (one `Prop`, Boltje's integrality congruence
  ([Boltje04] Cor. 2.8) + Müller's idempotent-coefficient computation)
* `+` the anisotropic-point witness and the `P₁` dichotomy for `B`/`C`
  (resp. the spectrum hole and the twin witness for `A`/`T`), both stated
  as `IsIndStarValue` facts about the groups
* `⟹` `IsEmpty (DRing B ≃+* DRing C)` (resp. `DRing A ≃+* DRing T`).

The corollaries live here rather than in `LeanDring/Even/BCSeparation.lean` /
`LeanDring/Even/ATSeparation.lean` for import reasons: `ConductorAtSpecies` already
imports `BCSeparation` transitively (via
`SpeciesRationality → SpeciesSurjectivity → SpeciesSeparation →
ConductorDictionaryGalois → ConductorDictionaryProofs → ConductorDictionary
→ BCSeparation`), so the `_of_boltje` corollaries cannot be added to those
files without a cycle.

No `sorry`, no custom axiom.
-/

set_option linter.unusedFintypeInType false

namespace LeanDring

namespace Even

universe u

/-! ## The group-theoretic (`ind*`) forms of the four inputs -/

/-- The `ind*`-form of `BAnisotropicWitness`: `v = |B|/(N_B(H,hH'): H')`
for the anisotropic-point pair, with no reference to conductors. -/
def BAnisotropicIndStar (B : Type u) [Group B] [Fintype B] (v : ℕ) : Prop :=
  IsIndStarValue B v

/-- The `ind*`-form of `CIndexDichotomy`. -/
def CIndStarDichotomy (C : Type u) [Group C] [Fintype C] (q n : ℕ) : Prop :=
  ∀ x : ℕ, IsIndStarValue C x → x < q ^ (2 * n) → x = 1 ∨ iota q n ∣ x

/-- The `ind*`-form of `SpectrumHole`. -/
def SpectrumHoleIndStar (A : Type u) [Group A] [Fintype A] (n : ℕ) : Prop :=
  ∀ x : ℕ, IsIndStarValue A x → x ≤ holeLo n ∨ holeHi n ≤ x

/-- The `ind*`-form of `TwinWitness`. -/
def TwinWitnessIndStar (T : Type u) [Group T] [Fintype T] (n ρ : ℕ) : Prop :=
  IsIndStarValue T (n.choose 3 * ρ) ∧ n - 3 < ρ ∧ 10 * ρ < 3 * ((n - 3) * (n - 4))

/-! ## Translation, given Boltje integrality -/

theorem bAnisotropicWitness_of_indStar (hB : BoltjeIntegrality.{u})
    {B : Type u} [Group B] [Fintype B] {v : ℕ} (h : BAnisotropicIndStar B v) :
    BAnisotropicWitness B v :=
  (isIndexValue_iff_of_boltje hB B v).mpr h

theorem cIndexDichotomy_of_indStar (hB : BoltjeIntegrality.{u})
    {C : Type u} [Group C] [Fintype C] {q n : ℕ} (h : CIndStarDichotomy C q n) :
    CIndexDichotomy C q n :=
  fun x hx hlt => h x ((isIndexValue_iff_of_boltje hB C x).mp hx) hlt

theorem spectrumHole_of_indStar (hB : BoltjeIntegrality.{u})
    {A : Type u} [Group A] [Fintype A] {n : ℕ} (h : SpectrumHoleIndStar A n) :
    SpectrumHole A n :=
  fun x hx => h x ((isIndexValue_iff_of_boltje hB A x).mp hx)

theorem twinWitness_of_indStar (hB : BoltjeIntegrality.{u})
    {T : Type u} [Group T] [Fintype T] {n ρ : ℕ} (h : TwinWitnessIndStar T n ρ) :
    TwinWitness T n ρ :=
  ⟨(isIndexValue_iff_of_boltje hB T _).mpr h.1, h.2.1, h.2.2⟩

/-! ## The two separation theorems, on group-theoretic hypotheses -/

/-- **Theorem BC-n, on purely group-theoretic hypotheses.**

Given Boltje integrality (the one open `Prop` of the dictionary), and

* `|B| = |C|`,
* the anisotropic-point pair of `B` has `ind*`-value `v` (`2v = q^n·w`,
  `w = q^n ∓ 1`),
* every `ind*`-value of `C` below `q^{2n}` is `1` or divisible by
  `ι₁ = [C: P₁]`,

there is no ring isomorphism `D(B) ≅ D(C)`.  No conductor-side hypothesis
survives: the two group facts are exactly what the GAP scripts check. -/
theorem bcSeparation_of_boltje (hBo : BoltjeIntegrality.{u})
    {B C : Type u} [Group B] [Group C] [Fintype B] [Fintype C]
    {q n v w : ℕ} (hq : 3 ≤ q) (hn : 3 ≤ n)
    (hw : w + 1 = q ^ n ∨ w = q ^ n + 1) (hv : 2 * v = q ^ n * w)
    (hcard : Nat.card B = Nat.card C)
    (hB : BAnisotropicIndStar B v) (hC : CIndStarDichotomy C q n) :
    IsEmpty (DRing B ≃+* DRing C) :=
  bcSeparation hq hn hw hv hcard (bAnisotropicWitness_of_indStar hBo hB)
    (cIndexDichotomy_of_indStar hBo hC)

/-- **Theorem BC-n, isomorphism form, on group-theoretic hypotheses.** -/
theorem not_nonempty_dringEquiv_of_bcSeparation_of_boltje (hBo : BoltjeIntegrality.{u})
    {B C : Type u} [Group B] [Group C] [Fintype B] [Fintype C]
    {q n v w : ℕ} (hq : 3 ≤ q) (hn : 3 ≤ n)
    (hw : w + 1 = q ^ n ∨ w = q ^ n + 1) (hv : 2 * v = q ^ n * w)
    (hcard : Nat.card B = Nat.card C)
    (hB : BAnisotropicIndStar B v) (hC : CIndStarDichotomy C q n) :
    ¬ Nonempty (DRing B ≃+* DRing C) := fun ⟨Φ⟩ =>
  (bcSeparation_of_boltje hBo hq hn hw hv hcard hB hC).elim Φ

/-- **The Theorem-AT endgame, on purely group-theoretic hypotheses.** -/
theorem atSeparation_of_boltje (hBo : BoltjeIntegrality.{u})
    {A T : Type u} [Group A] [Group T] [Fintype A] [Fintype T]
    {n ρ : ℕ} (hn : 10 ≤ n) (hcard : Nat.card A = Nat.card T)
    (hA : SpectrumHoleIndStar A n) (hT : TwinWitnessIndStar T n ρ) :
    IsEmpty (DRing A ≃+* DRing T) :=
  atSeparation hn hcard (spectrumHole_of_indStar hBo hA)
    (twinWitness_of_indStar hBo hT)

/-- **The Theorem-AT endgame, isomorphism form, on group-theoretic
hypotheses.** -/
theorem not_nonempty_dringEquiv_of_atSeparation_of_boltje (hBo : BoltjeIntegrality.{u})
    {A T : Type u} [Group A] [Group T] [Fintype A] [Fintype T]
    {n ρ : ℕ} (hn : 10 ≤ n) (hcard : Nat.card A = Nat.card T)
    (hA : SpectrumHoleIndStar A n) (hT : TwinWitnessIndStar T n ρ) :
    ¬ Nonempty (DRing A ≃+* DRing T) := fun ⟨Φ⟩ =>
  (atSeparation_of_boltje hBo hn hcard hA hT).elim Φ

/-! ## The separating-multiplicity witness

`LeanDring/Even/SimpleRigidity.lean` asks its two separation `Prop`s
(`ExceptionSeparation`, `TwinSeparation`) for an explicit conductor
multiplicity `c` at which `D(G)` and `D(H)` differ, whereas every
separation lane in this development concludes `IsEmpty (DRing G ≃+* DRing H)`
— which does *not* formally imply the `∃ c` form.  The two lemmas below
perform the conversion, so the `ind*`-side facts the mathematics actually
proves can discharge the `SimpleRigidity` inputs.

Only the conductor value `c` supplied by `IsIndexValue G x` is needed: the
same `c` cannot occur in `D(H)`, because `c · x = |G| = |H|` would then
make `x` an index value of `H` too. -/

/-- **The witness-extraction lemma.**  If `x` is an index value of `G`
but not of `H`, and `|G| = |H|`, then some conductor
multiplicity distinguishes `D(G)` from `D(H)` — the exact shape
`ExceptionSeparation` / `TwinSeparation` demand. -/
theorem exceptionSeparation_witness
    {G H : Type u} [Group G] [Group H] [Fintype G] [Fintype H] {x : ℕ}
    (hcard : Nat.card G = Nat.card H)
    (hG : IsIndexValue G x) (hH : ¬ IsIndexValue H x) :
    ∃ c : ℕ, conductorMultiplicity (DRing G) c ≠ conductorMultiplicity (DRing H) c := by
  obtain ⟨c, hc, hcx⟩ := hG
  exact ⟨c, fun hEq => hH ⟨c, by rw [← hEq]; exact hc, hcx.trans hcard⟩⟩

/-- **The same, on purely group-theoretic hypotheses.**  This is the form
in which the mathematics is stated: `v ∈ I(B)`, `v ∉ I(C)`
(Theorem BC-n), or `ι(S) ≠ ι(T)` turned into a value that one `ind*` set
has and the other does not (the twin lanes).  The `ind*` ⟶ conductor step
is `BoltjeIntegrality`. -/
theorem exceptionSeparation_witness_indStar (hBo : BoltjeIntegrality.{u})
    {G H : Type u} [Group G] [Group H] [Fintype G] [Fintype H] {x : ℕ}
    (hcard : Nat.card G = Nat.card H)
    (hG : IsIndStarValue G x) (hH : ¬ IsIndStarValue H x) :
    ∃ c : ℕ, conductorMultiplicity (DRing G) c ≠ conductorMultiplicity (DRing H) c :=
  exceptionSeparation_witness hcard ((isIndexValue_iff_of_boltje hBo G x).mpr hG)
    fun h => hH ((isIndexValue_iff_of_boltje hBo H x).mp h)

/-! ## `BoltjeIntegrality ⟹ OrderTransfer`

`OrderTransfer` and the conductor dictionary appear in the development as
independent hypotheses, but they are not independent: Boltje integrality
already produces, at *every* integer point of `D(G)`, an isolated value
`n = (N_G(H,hH'): H')`, and `n ≤ |N_G(H,hH')| ≤ |G|`.  That is precisely
`MullerIsolationWeak`, whose companion half `MullerTrivialBound` is
**proven** (`LeanDring/Even/MullerBound.lean`, Burnside mark triangularity).  So
`OrderTransfer` is a `BoltjeIntegrality` consequence. -/

/-- **[PROVEN from `BoltjeIntegrality`]** At every integer point of `D(G)`
some positive value `≤ |G|` is isolated.  The point is a species
`φ_{H,h}` (`ringHom_eq_species`); the index `n = (N_G(H,hH'): H')` is an
isolating value there by the `←` half of Boltje integrality, and
`n ≤ n·|H'| = |N_G(H,hH')| ≤ |G|` by Lagrange. -/
theorem mullerIsolationWeak_of_boltje (hBo : BoltjeIntegrality.{u}) :
    MullerIsolationWeak.{u} := by
  intro G _ _ p
  obtain ⟨H, h, hHh⟩ := ringHom_eq_species (G := G) (complexify (DRing G) p)
  obtain ⟨n, hn⟩ := card_commutator_dvd_card_pairNormalizer H h
  have hNpos : 0 < Nat.card (pairNormalizer H (h : G)) := Nat.card_pos
  have hcomm : 0 < Nat.card ↥⁅H, H⁆ := Nat.card_pos
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [hn, Nat.mul_zero] at hNpos
      exact absurd hNpos (lt_irrefl 0)
    · exact hpos
  have hNle : Nat.card (pairNormalizer H (h : G)) ≤ Nat.card G :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card _)
  have hnle : n ≤ Nat.card G :=
    le_trans (by rw [hn]; exact Nat.le_mul_of_pos_left n hcomm) hNle
  obtain ⟨x, hx⟩ :=
    isolates_of_isolatingValue p hHh ((hBo G H h n).mpr ⟨1, by rw [hn]; ring⟩)
  exact ⟨n, x, hnpos, hnle, hx⟩

/-- **[PROVEN from `BoltjeIntegrality`] Müller's Satz 2.3.4**: a D-ring
isomorphism forces equal group orders.  Combines
`mullerIsolationWeak_of_boltje` with the *proven* `mullerTrivialBound`
through `orderTransfer_of_muller'`, so the `OrderTransfer` input of
`LeanDring/Even/SimpleRigidity.lean` is not an independent external hypothesis. -/
theorem orderTransfer_of_boltje (hBo : BoltjeIntegrality.{u}) : OrderTransfer.{u} :=
  orderTransfer_of_muller' (mullerIsolationWeak_of_boltje hBo) mullerTrivialBound

end Even

end LeanDring

/-! ## Axiom audit -/

#print axioms LeanDring.Even.bAnisotropicWitness_of_indStar
#print axioms LeanDring.Even.cIndexDichotomy_of_indStar
#print axioms LeanDring.Even.spectrumHole_of_indStar
#print axioms LeanDring.Even.twinWitness_of_indStar
#print axioms LeanDring.Even.bcSeparation_of_boltje
#print axioms LeanDring.Even.not_nonempty_dringEquiv_of_bcSeparation_of_boltje
#print axioms LeanDring.Even.atSeparation_of_boltje
#print axioms LeanDring.Even.not_nonempty_dringEquiv_of_atSeparation_of_boltje
#print axioms LeanDring.Even.exceptionSeparation_witness
#print axioms LeanDring.Even.exceptionSeparation_witness_indStar
#print axioms LeanDring.Even.mullerIsolationWeak_of_boltje
#print axioms LeanDring.Even.orderTransfer_of_boltje
