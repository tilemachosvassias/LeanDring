/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import LeanDring.Even.OrderTransfer
import LeanDring.Even.ConductorDictionary

/-!
# The simple-group lane: conductor dictionary, solvability, order rigidity

**EVEN-ORDER LAYER.** Inside the root module's build closure and audit:
no `sorry`, three standard axioms. The results here are
verified *implications*; their hypotheses are named `Prop`s (see §7.6 of
the paper).

This file types the conductor reading of the simple-group landscape
and proves the assemblies that
are free given the typed inputs.  Nothing here is asserted as proven
mathematics beyond what the Lean kernel checks; every open ingredient is
a named `Prop`.

## The conductor side

* `IsPerfectSelfNormalizing U` — `⁅U,U⁆ = U` and `N_G(U) = U`;
* `PerfectSelfNormalizingClass G` — the conjugacy classes of such `U`
  (an honest quotient type: `conjSubgroup` and its setoid are built
  here, no `Pointwise` instance archaeology);
* `ConductorDictionary` — **[OPEN formally; Müller Satz 2.3.3/2.3.7]**
  `conductorMultiplicity (D(G)) 1 = #` of those classes.  This is the
  dictionary Theorem BC1 runs on;
* `card_perfectSelfNormalizingClass_eq_of_dringEquiv` — **[PROVEN from
  the dictionary]** the class count is a D-ring invariant (the BC1
  invariance half, in dictionary form);
* `SolvabilityDetector`, `solvabilityDetector_of_conductorDictionary` —
  **[PROVEN from the dictionary]** a *nontrivial solvable* group has no
  perfect self-normalizing subgroup, hence conductor-1 multiplicity `0`.
  Only this direction is stated: see the caveat below;
* `solvabilityDetector_of_pairDictionary` — **[PROVEN from the *reduced*
  lane]** the same detector from `ConductorPairDictionary`
  (`LeanDring/Even/ConductorDictionary.lean`), hence from `BoltjeIntegrality` alone.
  `ConductorDictionary` is therefore **not** needed for solvability; the
  two lanes are typings of the same Satz 2.3.3, and this is the part of
  the merge that goes through.  What does not: `ConductorPairDictionary`
  is a *non-vanishing* statement and `ConductorDictionary` a *count*, so
  the counting consequences do not cross.  `conductorMultiplicity_card_ne_zero`
  records the one counting-adjacent fact the non-vanishing form does give
  (the top conductor is always attained).

  **The counting upgrade is not an independent gap.**  The bijection
  `{integer points of conductor c} ↔ {fully fused pair classes of index c}`
  needs three things: that every complex point is a species — *already
  proven unconditionally*, `OddOrder.everyComplexPointIsSpecies`, and this
  layer already imports that file; that the integer points are the
  ℤ-valued species, which is routine given the first; and the conductor
  evaluation `c(H,hH') = (N_G(H,hH'): H')`, which is Satz 2.3.3, i.e.
  `BoltjeIntegrality` once more.  So `ConductorDictionary` and
  `TopConductorDetectsFitting` reduce to the same single root as the rest
  of the lane;
* `not_isSolvable_of_dringEquiv_of_simple` — **[PROVEN from the
  dictionary]** if `G` is nonabelian simple and `D(G) ≅ D(H)` with `H`
  nontrivial, then `H` is nonsolvable ("what transfers
  unconditionally").

**Caveat.**  The converse of direction (i) ("conductor-1 multiplicity `0` ⟹
solvable") is *false* if read through the conductor dictionary: in
`G = A5 × C2` every perfect subgroup
lies in `A5 × 1` (a perfect group has trivial image in `C2`), so the
perfect subgroups are `1` and `A5 × 1`, whose normalizers are `G` — no
perfect self-normalizing subgroup exists, yet `G` is nonsolvable.  So
`SolvabilityDetector` is deliberately one-directional here; the development
only ever uses that direction.

## The CFSG side

Lie-type groups do not exist in Mathlib, so the CFSG order theorem is
not faithfully *stateable*; the house pattern applies — it is a typed
`Prop` with the exception family carried as a `Prop`-valued parameter:

* `SimpleOrderRigidity Exc` — **[OPEN formally; CFSG order theorem
  (Artin–Tits)]** equal-order nonabelian simple groups are isomorphic or
  `Exc` holds of the pair (instantiate `Exc` with the `A8/L3(4)` and
  `B_n(q)/C_n(q)` families);
* `IsFittingFree`, `FittingFreeDetector`, `FittingFreeOrderForcesSimple`
  — the ingredients of SR1;
* `simpleDRigidity_of_orderRigidity`, `dtoB_simple_of_orderRigidity`,
  `simpleRecognition_of_detectors`, `dtoB_simpleRecognition` —
  **[PROVEN]** the assemblies, mirroring
  `dtoB_extraspecial_of_recognition` (`LeanDring/Even/Separation.lean`);
* `simpleDRigidity_of_muller` — **[PROVEN]** the same, with order
  transfer supplied by the two Müller halves of `LeanDring/Even/OrderTransfer.lean`
  instead of assumed.

## The formal closure of the simple-group project

* `ExceptionSeparation Exc` — **[PROVEN at the paper level for both
  members of the family: `{B_n(q), C_n(q)}`, `n ≥ 3`, `q` odd by Theorem
  BC-n, and `{A₈, L₃(4)}` by `ι`-separation; OPEN
  formally]** every exceptional pair is separated by *some* conductor
  multiplicity;
* `simpleDRigidity_of_exceptionSeparation`, `dtoB_simple_of_exceptionSeparation`
  — **[PROVEN]** with that input the exception clause disappears:
  simple-vs-simple D-rigidity, and `D ⇒ B`, hold unconditionally.  This is
  the formal statement that the simple-group project reduces to CFSG plus
  per-pair conductor separation — the first external, the second
  *not*: see the dependency statement at the end of this docstring.

## The order-60 fragment

* `not_isSolvable_of_isFittingFree` — **[PROVEN]** a nontrivial solvable
  group has a nontrivial abelian normal subgroup (the last nontrivial
  derived term), so Fitting-free ⟹ nonsolvable;
* `NonsolvableOrderSixty` — **[OPEN formally; classical, CFSG-free]**
  every nonsolvable group of order `60` is `A5`.  Mathlib has
  `alternatingGroup.isSimpleGroup` but not this classification (its proof
  is a Sylow count), so it stays a typed `Prop`;
* `fittingFreeOrderForcesSimple_of_card_sixty` — **[PROVEN from it]**
  worked instance: at order `60` every Fitting-free group is
  simple, so `A5` is D-rigid among all finite groups as soon as the
  detectors are supplied.

## THE simple-group theorem

The headline of the whole lane, assembled from everything above:

* `TwinSeparation` — **[COMPLETE at the paper level over all of CFSG
  (Theorem AT for `A_n`, Theorem SPT for the 26 sporadics and
  the Tits group, and the `L₂/U₃/Sz/R/L₃/S₄/G₂/³D₄/²F₄/F₄/E₆/²E₆/E₇/E₈/
  L_d/U_d/Sp/Ω/PΩ^±` towers); OPEN formally, and its instantiation routes
  through the conductor dictionary — see the dependency statement
  below]** the *global* replacement for the per-order hypothesis
  `FittingFreeOrderForcesSimple` of SR1.  Where SR1 asks that no
  Fitting-free non-simple group share `|G|` at all, `TwinSeparation`
  allows the twin to exist and only asks that some conductor multiplicity
  see the difference — the same shape `ExceptionSeparation` uses on the
  simple-vs-simple side;
* `TwinSeparationFor G`, `twinSeparation_iff_forall`,
  `simpleGroupTheorem_of_twinSeparationFor` — **[PROVEN]** the per-target
  form of the same input, so a single family's twin elimination can be
  recorded (and consumed) without the global `∀ G`;
* `simpleGroupTheorem` — **[PROVEN]** for `G` nonabelian simple and
  *arbitrary* finite `H`, `D(G) ≅ D(H) ⟹ G ≅ H`.  Five typed inputs:
  `OrderTransfer` (Müller §2.3, derivable here via
  `orderTransfer_of_muller`, and also from `BoltjeIntegrality`
  alone via `LeanDring/Even/BoltjeAssembly.lean`'s `orderTransfer_of_boltje`),
  `FittingFreeDetector` (Müller Satz 2.3.6 = [Mueller2011] Prop. 3.7, derivable from
  `TopConductorDetectsFitting` below), `SimpleOrderRigidity Exc` (CFSG
  order theorem), `ExceptionSeparation Exc` (the `A₈/L₃(4)` and `B_n/C_n`
  census), `TwinSeparation` (the Fitting-free-twin census).  No exception
  clause, no order hypothesis;
* `simpleGroupTheorem_dtoB` — **[PROVEN]** the `D ⇒ B` corollary: under
  the same inputs `D(G) ≅ D(H) ⟹ B(G) ≅ B(H)` for `G` nonabelian simple
  and arbitrary finite `H`.

## Dependency statement

> **Only `SimpleOrderRigidity Exc` — the Artin–Tits order theorem,
> carried with its exception family as an opaque parameter because
> Mathlib has no groups of Lie type — is external to D-ring theory.**
> The other four are discharged by the mathematics of this program
> (Theorem BC-n for `B_n(q)/C_n(q)` with `n ≥ 3` and `q` odd, the
> `ι`-separation of `A₈` from `L₃(4)`, and the complete twin elimination
> over CFSG) **only through Müller's conductor dictionary, Satz 2.3.3
> together with Satz 2.3.6** — because those results are proven about
> `ind*`-values, `ι` and `κ`, which are group-theoretic quantities,
> whereas the Lean `Prop`s here speak of conductor multiplicities.  That
> dictionary is formalized in this development and reduced,
> kernel-checked, to **one** named open statement, `BoltjeIntegrality`
> (`LeanDring/Even/ConductorAtSpecies.lean` §12, consumed by
> `LeanDring/Even/BoltjeAssembly.lean`).  The group-theoretic censuses themselves
> rest on the standing literature package: CFSG and its order theorem,
> the Kleidman–Liebeck / Bray–Holt–Roney-Dougal / Vasilyev
> maximal-subgroup and minimal-degree tables, ATLAS `Maxes`
> completeness, Zsygmondy, Bochert, Dickson, and two David-type
> effective constants.  **In short: kernel-checked assembly and
> invariance; conditional on one open ring-theoretic `Prop`
> (`BoltjeIntegrality`), the CFSG order theorem plus CFSG itself, and a
> named list of classical group-theoretic citations.  It is not, at
> present, a formal proof of the theorem, and the two separation `Prop`s
> are not independent of the D-ring machinery.**

The wiring that makes this concrete lives in `LeanDring/Even/BoltjeAssembly.lean`:
`orderTransfer_of_boltje`
(so `OrderTransfer` is a
`BoltjeIntegrality` consequence, `MullerTrivialBound` being proven), and
`exceptionSeparation_witness` / `exceptionSeparation_witness_indStar`
(which convert the `ind*`-side facts the separation lanes actually prove
into the `∃ c, conductorMultiplicity … ≠ …` shape the two separation
`Prop`s below demand).
-/

set_option linter.unusedFintypeInType false

namespace LeanDring

namespace Even

universe u

open DRing

/-! ## Perfect self-normalizing subgroups and their conjugacy classes -/

section PerfectSelfNormalizing

variable {G : Type u} [Group G]

/-- A **perfect self-normalizing** subgroup: `U` is its own commutator
subgroup and its own normalizer.  By Müller's Satz 2.3.3 these are
exactly the subgroups carrying a conductor-`1` species pair `(U, 1)`. -/
structure IsPerfectSelfNormalizing (U : Subgroup G) : Prop where
  /-- `U` is perfect. -/
  perfect : ⁅U, U⁆ = U
  /-- `U` is self-normalizing. -/
  selfNormalizing : Subgroup.normalizer (U : Set G) = U

/-- The conjugate `gUg⁻¹` of a subgroup. -/
def conjSubgroup (g : G) (U : Subgroup G) : Subgroup G :=
  U.map (MulAut.conj g).toMonoidHom

theorem mem_conjSubgroup {g x : G} {U : Subgroup G} :
    x ∈ conjSubgroup g U ↔ g⁻¹ * x * g ∈ U := by
  constructor
  · rintro hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    have : g⁻¹ * (g * u * g⁻¹) * g = u := by group
    rw [show (MulAut.conj g).toMonoidHom u = g * u * g⁻¹ from rfl, this]
    exact hu
  · intro hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hx, ?_⟩
    change g * (g⁻¹ * x * g) * g⁻¹ = x
    group

theorem conjSubgroup_one (U : Subgroup G) : conjSubgroup 1 U = U := by
  ext x; rw [mem_conjSubgroup]; group

theorem conjSubgroup_conjSubgroup (g k : G) (U : Subgroup G) :
    conjSubgroup k (conjSubgroup g U) = conjSubgroup (k * g) U := by
  ext x
  rw [mem_conjSubgroup, mem_conjSubgroup, mem_conjSubgroup]
  constructor
  · intro h; rw [show (k * g)⁻¹ * x * (k * g) = g⁻¹ * (k⁻¹ * x * k) * g by group]; exact h
  · intro h; rw [show g⁻¹ * (k⁻¹ * x * k) * g = (k * g)⁻¹ * x * (k * g) by group]; exact h

variable (G) in
/-- Conjugacy of perfect self-normalizing subgroups. -/
instance perfectSelfNormalizingSetoid :
    Setoid {U : Subgroup G // IsPerfectSelfNormalizing U} where
  r U V := ∃ g : G, conjSubgroup g U.1 = V.1
  iseqv := by
    refine ⟨fun U => ⟨1, conjSubgroup_one U.1⟩, ?_, ?_⟩
    · rintro U V ⟨g, hg⟩
      refine ⟨g⁻¹, ?_⟩
      rw [← hg, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
    · rintro U V W ⟨g, hg⟩ ⟨k, hk⟩
      exact ⟨k * g, by rw [← conjSubgroup_conjSubgroup, hg, hk]⟩

variable (G) in
/-- The conjugacy classes of perfect self-normalizing subgroups — the
combinatorial side of Müller's conductor-`1` dictionary. -/
def PerfectSelfNormalizingClass : Type u :=
  Quotient (perfectSelfNormalizingSetoid G)

/-- A nonabelian simple group is perfect and self-normalizing in itself,
so its class of perfect self-normalizing subgroups is nonempty. -/
theorem nonempty_perfectSelfNormalizingClass_of_simple [IsSimpleGroup G]
    (hab : ¬ ∀ a b : G, a * b = b * a) :
    Nonempty (PerfectSelfNormalizingClass G) := by
  have htop : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := by
    rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G)
      inferInstance) with h | h
    · exact absurd (IsSimpleGroup.comm_iff_isSolvable.mpr
        ⟨1, by rw [derivedSeries_one]; exact h⟩) hab
    · exact h
  exact ⟨Quotient.mk _ ⟨⊤, ⟨htop, le_antisymm le_top Subgroup.le_normalizer⟩⟩⟩

/-- Everything normalizes the trivial subgroup. -/
theorem mem_normalizer_bot (x : G) :
    x ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  simp only [Subgroup.mem_bot]
  constructor
  · rintro rfl; group
  · intro h
    have h2 : x⁻¹ * (x * n * x⁻¹) * x = x⁻¹ * 1 * x := by rw [h]
    rw [show x⁻¹ * (x * n * x⁻¹) * x = n by group,
      show x⁻¹ * (1 : G) * x = 1 by group] at h2
    exact h2

/-- **A nontrivial solvable group has no perfect self-normalizing
subgroup.**  (`⊥` is normalized by everything; a nontrivial subgroup of a
solvable group strictly contains its commutator subgroup.) -/
theorem isEmpty_perfectSelfNormalizing_of_solvable [Nontrivial G]
    (hsol : IsSolvable G) :
    IsEmpty {U : Subgroup G // IsPerfectSelfNormalizing U} := by
  haveI := hsol
  refine ⟨fun U => ?_⟩
  rcases eq_or_ne U.1 ⊥ with hbot | hne
  · obtain ⟨a, ha⟩ := exists_ne (1 : G)
    have hn := U.2.selfNormalizing
    rw [hbot] at hn
    have : a ∈ (⊥ : Subgroup G) := hn ▸ mem_normalizer_bot a
    exact ha (Subgroup.mem_bot.mp this)
  · exact absurd U.2.perfect (IsSolvable.commutator_lt_of_ne_bot hne).ne

theorem isEmpty_perfectSelfNormalizingClass_of_solvable [Nontrivial G]
    (hsol : IsSolvable G) : IsEmpty (PerfectSelfNormalizingClass G) := by
  haveI := isEmpty_perfectSelfNormalizing_of_solvable hsol
  exact ⟨fun q => Quotient.inductionOn q fun a => isEmptyElim a⟩

end PerfectSelfNormalizing

/-! ## The conductor dictionary and its consequences -/

/-- **[OPEN formally — Müller Satz 2.3.3, specialized to conductor `1`
(Satz 2.3.7)]** The conductor-`1` multiplicity of `D(G)` counts the
conjugacy classes of perfect self-normalizing subgroups of `G`.  This is
the dictionary Theorem BC1 evaluates: `≥ 15` for `Ω(7,3)`
against exactly `6` for `PSp(6,3)`. -/
def ConductorDictionary : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    conductorMultiplicity (DRing G) 1 = Nat.card (PerfectSelfNormalizingClass G)

/-- **[PROVEN from the dictionary]** The number of conjugacy classes of
perfect self-normalizing subgroups is a D-ring invariant — the invariance
half of BC1, transported through the kernel-checked
`conductorMultiplicity_eq_of_ringEquiv`. -/
theorem card_perfectSelfNormalizingClass_eq_of_dringEquiv
    (hdict : ConductorDictionary.{u})
    {G H : Type u} [Group G] [Group H] [Fintype G] [Fintype H]
    (Φ : DRing G ≃+* DRing H) :
    Nat.card (PerfectSelfNormalizingClass G) =
      Nat.card (PerfectSelfNormalizingClass H) := by
  rw [← hdict G, ← hdict H]
  exact conductorMultiplicity_eq_of_ringEquiv Φ 1

/-- **Satz 2.3.7, the direction used**: a nontrivial solvable group
has conductor-`1` multiplicity `0`.  (The converse fails under this
dictionary — see the module docstring, `A5 × C2`.) -/
def SolvabilityDetector : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], Nontrivial G → IsSolvable G →
    conductorMultiplicity (DRing G) 1 = 0

/-- **[PROVEN]** The conductor dictionary yields the solvability
detector. -/
theorem solvabilityDetector_of_conductorDictionary
    (hdict : ConductorDictionary.{u}) : SolvabilityDetector.{u} := by
  intro G _ _ hnt hsol
  haveI := hnt
  haveI := isEmpty_perfectSelfNormalizingClass_of_solvable (G := G) hsol
  rw [hdict G, Nat.card_eq_zero.mpr (Or.inl ‹IsEmpty (PerfectSelfNormalizingClass G)›)]

/-! ### Merging the two conductor lanes

`ConductorDictionary` above and `ConductorPairDictionary`
(`LeanDring/Even/ConductorDictionary.lean`) are two typings of the *same* published
theorem, Müller Satz 2.3.3.  Only the second has been reduced to a single
root `Prop`: `ConductorAtSpecies.lean` proves `conductorAtSpecies_of_boltje`
from `BoltjeIntegrality`.  Leaving them unconnected made the open surface
look larger than it is, so we discharge what can be discharged from the
reduced lane.

The obstruction to a full merge is shape, not difficulty:
`ConductorPairDictionary` is a *non-vanishing* statement
(`multiplicity ≠ 0 ↔ ∃ pair`) whereas `ConductorDictionary` is a *count*
(`multiplicity 1 = #classes`).  `SolvabilityDetector` only ever asks for
vanishing, so it crosses; the counting statements do not. -/

/-- `⁅H,H⁆ ≤ H`, with no normality hypothesis (`Subgroup.commutator_le_left`
wants `H` normal in `G`, which is not available here). -/
theorem commutator_self_le {G : Type u} [Group G] (H : Subgroup G) :
    ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

/-- `⁅⊥,⊥⁆ = ⊥`. -/
theorem commutator_bot_self {G : Type u} [Group G] :
    ⁅(⊥ : Subgroup G), (⊥ : Subgroup G)⁆ = ⊥ :=
  le_bot_iff.mp (commutator_self_le ⊥)

/-- **[PROVEN from the reduced lane]** The top conductor is always
attained: the trivial pair `(⊥, 1)` is fully fused, its pair normalizer is
all of `G` and its commutator subgroup is trivial, so it has conductor
exactly `|G|`.

This is the `≥ 1` half that any proof of `TopConductorDetectsFitting`
must start from; what the non-vanishing dictionary cannot supply is the
*uniqueness* (`= 1`) for Fitting-free `G`, nor the second point
(`≥ 2`) when a nontrivial abelian normal subgroup exists.  Both of those
need the multiplicity as a count, i.e. a bijection between the rational
conductor-`c` points and the pair classes — see the note on
`TopConductorDetectsFitting`. -/
theorem conductorMultiplicity_card_ne_zero
    (hpd : ConductorPairDictionary.{u})
    (G : Type u) [Group G] [Fintype G] :
    conductorMultiplicity (DRing G) (Nat.card G) ≠ 0 :=
  (hpd G (Nat.card G)).mpr
    ⟨⊥, 1, fullyFused_bot, by
      simp⟩

/-- **[PROVEN from the *reduced* lane]** The solvability detector follows
from `ConductorPairDictionary`, hence — via `conductorAtSpecies_of_boltje`
— from `BoltjeIntegrality` alone.  It does **not** need the counting form
`ConductorDictionary`.

At `c = 1` the dictionary supplies a fully fused pair with
`|⁅H,H⁆| = |N_G(H,hH')|`.  Since `⁅H,H⁆ ≤ H ≤ N_G(H,hH')`, equal
cardinality collapses the chain: `H` is perfect.  A perfect subgroup of a
solvable group is trivial, and for `H = ⊥` the pair normalizer is all of
`G`, so the same equation reads `1 = |G|` — impossible for `G`
nontrivial. -/
theorem solvabilityDetector_of_pairDictionary
    (hpd : ConductorPairDictionary.{u}) : SolvabilityDetector.{u} := by
  intro G _ _ hnt hsol
  by_contra hne
  obtain ⟨H, h, -, hcard⟩ := (hpd G 1).mp hne
  rw [one_mul] at hcard
  -- `⁅H,H⁆ ≤ H ≤ N_G(H,hH')`, with the two ends equinumerous
  have hHle : H ≤ pairNormalizer H (h : G) := le_pairNormalizer H h
  have hCle : ⁅H, H⁆ ≤ H := commutator_self_le H
  -- so `|H| ≤ |N| = |⁅H,H⁆|`, and `⁅H,H⁆ ≤ H` then forces equality
  have hcardH : Nat.card H ≤ Nat.card ↥⁅H, H⁆ := by
    rw [hcard]; exact Nat.card_le_card_of_injective _ (Set.inclusion_injective hHle)
  have hperf : ⁅H, H⁆ = H := Subgroup.eq_of_le_of_card_ge hCle hcardH
  -- a perfect subgroup of a solvable group is trivial
  have hbot : H = ⊥ := by
    by_contra hH
    exact absurd hperf (IsSolvable.commutator_lt_of_ne_bot hH).ne
  -- and then the pair normalizer is all of `G`, so `hcard` reads `1 = |G|`
  subst hbot
  have hh : (h : G) = 1 := Subgroup.mem_bot.mp h.2
  rw [hh] at hcard
  simp only [pairNormalizer_bot, commutator_bot_self, Subgroup.card_bot,
    Subgroup.card_top] at hcard
  have h1 : 1 < Nat.card G := Finite.one_lt_card
  omega

/-- **[PROVEN from the dictionary] Nonsolvability transfers**: if `G` is
nonabelian simple and `D(G) ≅ D(H)` with `H` nontrivial, then `H` is
nonsolvable.  ("what transfers unconditionally".) -/
theorem not_isSolvable_of_dringEquiv_of_simple
    (hdict : ConductorDictionary.{u})
    {G H : Type u} [Group G] [Group H] [Fintype G] [Fintype H]
    [IsSimpleGroup G] (hab : ¬ ∀ a b : G, a * b = b * a) [Nontrivial H]
    (Φ : DRing G ≃+* DRing H) : ¬ IsSolvable H := by
  intro hsol
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (SetLike.coe : Subgroup G → Set G) SetLike.coe_injective
  haveI : Finite {U : Subgroup G // IsPerfectSelfNormalizing U} := Subtype.finite
  haveI : Finite (PerfectSelfNormalizingClass G) :=
    Finite.of_surjective (Quotient.mk (perfectSelfNormalizingSetoid G))
      Quotient.mk_surjective
  haveI := nonempty_perfectSelfNormalizingClass_of_simple (G := G) hab
  have hpos : 0 < Nat.card (PerfectSelfNormalizingClass G) := Nat.card_pos
  haveI := isEmpty_perfectSelfNormalizingClass_of_solvable (G := H) hsol
  rw [card_perfectSelfNormalizingClass_eq_of_dringEquiv hdict Φ,
    Nat.card_eq_zero.mpr (Or.inl ‹IsEmpty (PerfectSelfNormalizingClass H)›)] at hpos
  exact absurd hpos (lt_irrefl 0)

/-! ## The CFSG order theorem, typed -/

/-- **[OPEN formally — CFSG order theorem (Artin–Tits); not faithfully
stateable in Mathlib, which has no Lie-type groups]** Two nonabelian
finite simple groups of equal order are isomorphic, unless the
exceptional predicate `Exc` holds of the pair.  Instantiating `Exc` with
"`{G,H} = {A8, L3(4)}` or `{B_n(q), C_n(q)}` with `n ≥ 3` and `q` odd"
recovers the classical statement; the `ι`-invariant separates the first pair
(`ι(A₈) = ι(L₄(2)) = 15` against `ι(L₃(4)) = 21`, hence
`κ(A₈) = 20160/15 = 1344` against `κ(L₃(4)) = 20160/21 = 960`), and
(Theorem BC-n) separates the second family.

**The restrictions `n ≥ 3` and `q` odd are load-bearing** (side-condition 1): `B₂ ≅ C₂` and
`B_n(2^f) ≅ C_n(2^f)`, so an `Exc` that
held of those pairs would hold of *isomorphic* pairs, and
`ExceptionSeparation Exc` — which demands a conductor multiplicity
*difference* — would then be outright false.  Note also that `Exc` is a
bare parameter with no non-degeneracy constraint: taking
`Exc G H := ¬ Nonempty (G ≃* H)` makes `SimpleOrderRigidity Exc` a
tautology and dumps all content into `ExceptionSeparation Exc`.  Any
published dependency statement must therefore name the intended `Exc`
rather than say "for some `Exc`". -/
def SimpleOrderRigidity
    (Exc : ∀ (G : Type u) [Group G] (H : Type u) [Group H], Prop) : Prop :=
  ∀ (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H],
    IsSimpleGroup G → IsSimpleGroup H →
      (¬ ∀ a b : G, a * b = b * a) → (¬ ∀ a b : H, a * b = b * a) →
        Nat.card G = Nat.card H → Nonempty (G ≃* H) ∨ Exc G H

/-- **Simple-vs-simple D-rigidity**: order transfer plus the
CFSG order theorem give rigidity up to the exceptional family. -/
theorem simpleDRigidity_of_orderRigidity
    {Exc : ∀ (G : Type u) [Group G] (H : Type u) [Group H], Prop}
    (hord : SimpleOrderRigidity Exc) (htr : OrderTransfer.{u})
    (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H]
    (hG : IsSimpleGroup G) (hH : IsSimpleGroup H)
    (hGa : ¬ ∀ a b : G, a * b = b * a) (hHa : ¬ ∀ a b : H, a * b = b * a)
    (hD : Nonempty (DRing G ≃+* DRing H)) :
    Nonempty (G ≃* H) ∨ Exc G H :=
  hord G H hG hH hGa hHa (htr G H hD)

/-- **`D ⇒ B` on simple-vs-simple pairs** off the exceptional family:
rigidity gives the Burnside isomorphism outright. -/
theorem dtoB_simple_of_orderRigidity
    {Exc : ∀ (G : Type u) [Group G] (H : Type u) [Group H], Prop}
    (hord : SimpleOrderRigidity Exc) (htr : OrderTransfer.{u})
    (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H]
    (hG : IsSimpleGroup G) (hH : IsSimpleGroup H)
    (hGa : ¬ ∀ a b : G, a * b = b * a) (hHa : ¬ ∀ a b : H, a * b = b * a)
    (hexc : ¬ Exc G H) (hD : Nonempty (DRing G ≃+* DRing H)) :
    Nonempty (BurnsideRing G ≃+* BurnsideRing H) := by
  rcases simpleDRigidity_of_orderRigidity hord htr G H hG hH hGa hHa hD with h | h
  · exact h.elim fun θ => ⟨burnsideRingCongr θ⟩
  · exact absurd h hexc

/-- **[PROVEN]** The same, with order transfer supplied by the two Müller
halves (`LeanDring/Even/OrderTransfer.lean`) rather than assumed. -/
theorem simpleDRigidity_of_muller
    {Exc : ∀ (G : Type u) [Group G] (H : Type u) [Group H], Prop}
    (hord : SimpleOrderRigidity Exc)
    (hiso : MullerIsolation.{u}) (hbd : MullerTrivialBound.{u})
    (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H]
    (hG : IsSimpleGroup G) (hH : IsSimpleGroup H)
    (hGa : ¬ ∀ a b : G, a * b = b * a) (hHa : ¬ ∀ a b : H, a * b = b * a)
    (hD : Nonempty (DRing G ≃+* DRing H)) :
    Nonempty (G ≃* H) ∨ Exc G H :=
  simpleDRigidity_of_orderRigidity hord (orderTransfer_of_muller hiso hbd)
    G H hG hH hGa hHa hD

/-! ## Closing the exception family by conductor separation -/

/-- **[PROVEN at the paper level for the whole exception family; OPEN
formally]** Every exceptional pair of equal-order nonabelian simple
groups is separated by *some* conductor multiplicity.

The two members, matching the two CFSG order coincidences:

* `{B_n(q), C_n(q)}`, `n ≥ 3`, `q` odd — **Theorem BC-n** (addendum,
  audit PASSED): the anisotropic-point orbit
  gives `v_ε = qⁿ(qⁿ − ε)/2 ∈ I(B_n(q))`, while every `ind*` value of
  `PSp_{2n}(q)` below `q^{2n}` is `1` or divisible by `ι₁`, and
  `ι₁ ∤ v_ε`.  Formalized in `LeanDring/Even/BCSeparation.lean` (`bcSeparation`)
  and, on purely group-theoretic hypotheses, in
  `LeanDring/Even/BoltjeAssembly.lean` (`bcSeparation_of_boltje`);
* `{A₈, L₃(4)}` — the `ι`-separation (`ι(A₈) = 15` vs
  `ι(L₃(4)) = 21`).  Do **not** cite the subgroup-class-count /
  element-order argument: the addendum rejects those as computed
  evidence, not a proven D-ring separation.

This is the exact shape the ring theory needs: a multiplicity difference
is all it takes, because `conductorMultiplicity_eq_of_ringEquiv`
(`LeanDring/Even/OrderTransfer.lean`, kernel-checked) makes any such difference
contradict a D-ring isomorphism.  Nothing about the exception family's
*definition* is used — which is why this stays stateable even though
`Exc` itself is not.

**Not external to the ring theory.**  Both members
are proven about `ind*`-values / `ι`, group-theoretic quantities; the
conversion to `conductorMultiplicity` is Müller Satz 2.3.3 + 2.3.6, i.e.
`BoltjeIntegrality`.  The last mile is `exceptionSeparation_witness`
(`LeanDring/Even/BoltjeAssembly.lean`), which turns `x ∈ I(G)`, `x ∉ I(H)`,
`|G| = |H|` into exactly the `∃ c` below.  Note also that this `Prop`
does not require `G ≇ H`, so `Exc` must be false on isomorphic pairs —
see `SimpleOrderRigidity`. -/
def ExceptionSeparation
    (Exc : ∀ (G : Type u) [Group G] (H : Type u) [Group H], Prop) : Prop :=
  ∀ (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H],
    IsSimpleGroup G → IsSimpleGroup H → Nat.card G = Nat.card H → Exc G H →
      ∃ c : ℕ, conductorMultiplicity (DRing G) c ≠ conductorMultiplicity (DRing H) c

/-- **[PROVEN] Simple-vs-simple D-rigidity, unconditionally** — the
formal closure of the simple-group project.  Given the CFSG
order theorem (typed as `SimpleOrderRigidity Exc`, `Exc` an opaque
parameter because Mathlib has no Lie-type groups) and a conductor
separation for its exception family, `D(G) ≅ D(H)` forces `G ≅ H` with
*no* exception clause: the disjunction either hands over the isomorphism
or lands in `Exc`, and there the separating multiplicity contradicts the
given D-ring isomorphism through `conductorMultiplicity_eq_of_ringEquiv`.

Of the two inputs only `SimpleOrderRigidity` is external to the ring
theory (CFSG is classical).  `ExceptionSeparation` is a per-pair census
— proven at the paper level for both members of the family — but its
*instantiation* goes through Müller's conductor dictionary, hence through
`BoltjeIntegrality`; see the `ExceptionSeparation` docstring and the
dependency statement in the module docstring. -/
theorem simpleDRigidity_of_exceptionSeparation
    {Exc : ∀ (G : Type u) [Group G] (H : Type u) [Group H], Prop}
    (hord : SimpleOrderRigidity Exc) (hsep : ExceptionSeparation Exc)
    (htr : OrderTransfer.{u})
    (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H]
    (hG : IsSimpleGroup G) (hH : IsSimpleGroup H)
    (hGa : ¬ ∀ a b : G, a * b = b * a) (hHa : ¬ ∀ a b : H, a * b = b * a)
    (hD : Nonempty (DRing G ≃+* DRing H)) :
    Nonempty (G ≃* H) := by
  rcases simpleDRigidity_of_orderRigidity hord htr G H hG hH hGa hHa hD with h | hexc
  · exact h
  · obtain ⟨c, hc⟩ := hsep G H hG hH (htr G H hD) hexc
    obtain ⟨Φ⟩ := hD
    exact absurd (conductorMultiplicity_eq_of_ringEquiv Φ c) hc

/-- **[PROVEN] `D ⇒ B` on simple-vs-simple pairs, unconditionally**: the
same closure at the Burnside level. -/
theorem dtoB_simple_of_exceptionSeparation
    {Exc : ∀ (G : Type u) [Group G] (H : Type u) [Group H], Prop}
    (hord : SimpleOrderRigidity Exc) (hsep : ExceptionSeparation Exc)
    (htr : OrderTransfer.{u})
    (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H]
    (hG : IsSimpleGroup G) (hH : IsSimpleGroup H)
    (hGa : ¬ ∀ a b : G, a * b = b * a) (hHa : ¬ ∀ a b : H, a * b = b * a)
    (hD : Nonempty (DRing G ≃+* DRing H)) :
    Nonempty (BurnsideRing G ≃+* BurnsideRing H) :=
  (simpleDRigidity_of_exceptionSeparation hord hsep htr G H hG hH hGa hHa hD).elim
    fun θ => ⟨burnsideRingCongr θ⟩

/-! ## SR1: recognition against an arbitrary partner -/

/-- **Fitting-free**: no nontrivial abelian normal subgroup (equivalently,
trivial Fitting subgroup — Mathlib has no `Fitting`, and this form is
what the downstream argument uses). -/
def IsFittingFree (G : Type u) [Group G] : Prop :=
  ∀ N : Subgroup G, N.Normal → (∀ a b : N, a * b = b * a) → N = ⊥

/-- A nonabelian simple group is Fitting-free. -/
theorem isFittingFree_of_simple {G : Type u} [Group G] [IsSimpleGroup G]
    (hab : ¬ ∀ a b : G, a * b = b * a) : IsFittingFree G := by
  intro N hN hcomm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N hN with h | h
  · exact h
  · refine absurd (fun a b => ?_) hab
    have ha : a ∈ N := h ▸ Subgroup.mem_top a
    have hb : b ∈ N := h ▸ Subgroup.mem_top b
    exact congrArg Subtype.val (hcomm ⟨a, ha⟩ ⟨b, hb⟩)

/-- A Fitting-free group with more than one element is nonabelian. -/
theorem not_comm_of_fittingFree {G : Type u} [Group G] [Nontrivial G]
    (hff : IsFittingFree G) : ¬ ∀ a b : G, a * b = b * a := by
  intro hcomm
  exact absurd (hff ⊤ inferInstance fun a b =>
    Subtype.ext (hcomm a.1 b.1)) top_ne_bot

/-- **[OPEN formally — Müller Satz 2.3.6]** Fitting-freeness is
a D-ring invariant: it is detected by the uniqueness of the
conductor-`|G|` idempotent. -/
def FittingFreeDetector : Prop :=
  ∀ (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H],
    Nonempty (DRing G ≃+* DRing H) → IsFittingFree G → IsFittingFree H

/-- **[OPEN formally — Müller Satz 2.3.6, in the multiplicity form]** The
top conductor `|G|` is simple exactly for the Fitting-free groups.

Müller's Satz 2.3.6 reads: a primitive idempotent `e_{(H,hH')}` of
`D_{Q(ζ)}(G)` with Führer `|G|` has `H` an abelian normal subgroup of `G`
and `h ∈ Z(G)`; in particular `G` has a nontrivial abelian normal
subgroup iff *more than one* primitive idempotent has Führer `|G|`.  The
statement below is that content restricted to the rational (fully fused)
species, which is what `conductorMultiplicity` counts.  The restriction
is harmless in both directions:

* `⟸` the trivial pair `(1, 1)` always has conductor `(G: 1) = |G|`
  (`conductorAtSpecies_trivial`), so the multiplicity is `≥ 1`; if `G` is
  Fitting-free, Satz 2.3.6 forces any other conductor-`|G|` pair to have
  `H` abelian normal, hence `H = 1`, hence the trivial pair again;
* `⟹` if `1 ≠ N ⊴ G` is abelian then the pair `(N, 1·N')` has `N' = 1`
  and `N_G(N, 1) = N_G(N) = G`, so conductor `|G|`; and it is fully fused
  because `h = 1`, so it is a genuinely *rational* second point.

**Why this is not derived here.**  Both directions are about a *count* of
integer points, whereas the formalized dictionary
(`ConductorPairDictionary`, `BoltjeIntegrality`) is a non-vanishing
statement, `conductorMultiplicity ≠ 0 ↔ ∃ pair`.  Upgrading it to a
bijection pairs-classes ↔ integer points is real work, not wiring, so this
development leaves it as a named `Prop` and only wires the consequence
below. -/
def TopConductorDetectsFitting : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    conductorMultiplicity (DRing G) (Nat.card G) = 1 ↔ IsFittingFree G

/-- **[PROVEN from `TopConductorDetectsFitting` + `OrderTransfer`]**
`FittingFreeDetector` is not an independent input: the top conductor is
read at `|G| = |H|` on both sides (order transfer), and every conductor
multiplicity is a ring-isomorphism invariant.  This is
reducible to the same open `Prop`. -/
theorem fittingFreeDetector_of_topConductor
    (hdet : TopConductorDetectsFitting.{u}) (htr : OrderTransfer.{u}) :
    FittingFreeDetector.{u} := by
  intro G H _ _ _ _ hD hGff
  obtain ⟨Φ⟩ := hD
  have hcard : Nat.card G = Nat.card H := htr G H ⟨Φ⟩
  refine (hdet H).mp ?_
  rw [← hcard, ← conductorMultiplicity_eq_of_ringEquiv Φ (Nat.card G)]
  exact (hdet G).mpr hGff

/-- **The SR1 order hypothesis** (pure CFSG arithmetic): at the order
of `G`, every Fitting-free group is simple.  Verified for
`|A5| = 60`, `|L2(7)| = 168`, `|A6| = 360`, `|A8| = 20160`, `|M11| =
7920`. -/
def FittingFreeOrderForcesSimple (G : Type u) [Group G] [Fintype G] : Prop :=
  ∀ (H : Type u) [Group H] [Fintype H],
    Nat.card H = Nat.card G → IsFittingFree H → IsSimpleGroup H

/-- **Theorem SR1, assembled**: for `G` nonabelian simple whose
order forces Fitting-free partners to be simple, any `H` with
`D(G) ≅ D(H)` is isomorphic to `G` — unless the pair is exceptional for
the CFSG order theorem. -/
theorem simpleRecognition_of_detectors
    {Exc : ∀ (G : Type u) [Group G] (H : Type u) [Group H], Prop}
    (hord : SimpleOrderRigidity Exc) (htr : OrderTransfer.{u})
    (hdet : FittingFreeDetector.{u})
    (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H]
    (hG : IsSimpleGroup G) (hGa : ¬ ∀ a b : G, a * b = b * a)
    (harith : FittingFreeOrderForcesSimple G)
    (hD : Nonempty (DRing G ≃+* DRing H)) :
    Nonempty (G ≃* H) ∨ Exc G H := by
  haveI := hG
  have hcard : Nat.card H = Nat.card G := (htr G H hD).symm
  have hGff : IsFittingFree G := isFittingFree_of_simple hGa
  have hHff : IsFittingFree H := hdet G H hD hGff
  have hHsimple : IsSimpleGroup H := harith H hcard hHff
  -- `H` is nontrivial because `G` is (a one-element group is abelian)
  haveI : Nontrivial H := by
    rcases subsingleton_or_nontrivial H with hsub | hnt
    · have h1 : Nat.card H = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
      have h2 : Nat.card G = 1 := by rw [← hcard]; exact h1
      haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h2).1
      exact absurd (fun a b => Subsingleton.elim (a * b) (b * a)) hGa
    · exact hnt
  have hHa : ¬ ∀ a b : H, a * b = b * a := not_comm_of_fittingFree hHff
  exact hord G H hG hHsimple hGa hHa hcard.symm

/-- **A nontrivial solvable group is never Fitting-free**: the last
nontrivial term of the derived series is normal and abelian.  Hence
Fitting-free groups are nonsolvable — the link between the two
hypotheses. -/
theorem not_isSolvable_of_isFittingFree {G : Type u} [Group G] [Nontrivial G]
    (hff : IsFittingFree G) : ¬ IsSolvable G := by
  rintro ⟨n, hn⟩
  classical
  have hex : ∃ m : ℕ, derivedSeries G m = ⊥ := ⟨n, hn⟩
  set m := Nat.find hex with hm
  have hmbot : derivedSeries G m = ⊥ := Nat.find_spec hex
  cases hmc : m with
  | zero =>
    rw [hmc] at hmbot
    rw [derivedSeries_zero] at hmbot
    exact top_ne_bot hmbot
  | succ k =>
    have hk : derivedSeries G k ≠ ⊥ := by
      have := Nat.find_min hex (m := k) (by omega)
      exact this
    have habel : ∀ a b : derivedSeries G k, a * b = b * a := by
      have hcomm : ⁅derivedSeries G k, derivedSeries G k⁆ = ⊥ := by
        rw [← derivedSeries_succ, ← hmc]; exact hmbot
      have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      intro a b
      have ha := hcent a.2
      have := Subgroup.mem_centralizer_iff.mp ha b.1 b.2
      exact Subtype.ext this.symm
    exact hk (hff (derivedSeries G k) (derivedSeries_normal G k) habel)

/-- **[OPEN formally — classical, CFSG-free]** Every nonsolvable group of
order `60` is isomorphic to `A5`.  (Mathlib has `alternatingGroup` and its
simplicity, `alternatingGroup.isSimpleGroup`, but not this classification;
the classical proof is a Sylow count.  Typed here because worked
instance `|A5| = 60` depends on exactly this statement.) -/
def NonsolvableOrderSixty : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G], Nat.card G = 60 → ¬ IsSolvable G →
    Nonempty (G ≃* alternatingGroup (Fin 5))

/-- **[PROVEN from `NonsolvableOrderSixty`]** The SR1 order hypothesis
holds at order `60`: every Fitting-free group of order `60` is simple.
(Fitting-free ⟹ nonsolvable ⟹ `≅ A5` ⟹ simple.) -/
theorem fittingFreeOrderForcesSimple_of_card_sixty
    (h60 : NonsolvableOrderSixty.{u})
    (G : Type u) [Group G] [Fintype G] (hG : Nat.card G = 60) :
    FittingFreeOrderForcesSimple G := by
  intro H _ _ hcard hff
  have hcard60 : Nat.card H = 60 := by rw [hcard, hG]
  haveI : Nontrivial H := by
    rcases subsingleton_or_nontrivial H with hs | hnt
    · have h1 : Nat.card H = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hs, ⟨1⟩⟩
      omega
    · exact hnt
  obtain ⟨e⟩ := h60 H hcard60 (not_isSolvable_of_isFittingFree hff)
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  exact e.isSimpleGroup

/-- **`D ⇒ B` in the SR1 range**: off the exceptional family, recognition
plus rigidity give the Burnside isomorphism. -/
theorem dtoB_simpleRecognition
    {Exc : ∀ (G : Type u) [Group G] (H : Type u) [Group H], Prop}
    (hord : SimpleOrderRigidity Exc) (htr : OrderTransfer.{u})
    (hdet : FittingFreeDetector.{u})
    (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H]
    (hG : IsSimpleGroup G) (hGa : ¬ ∀ a b : G, a * b = b * a)
    (harith : FittingFreeOrderForcesSimple G) (hexc : ¬ Exc G H)
    (hD : Nonempty (DRing G ≃+* DRing H)) :
    Nonempty (BurnsideRing G ≃+* BurnsideRing H) := by
  rcases simpleRecognition_of_detectors hord htr hdet G H hG hGa harith hD with h | h
  · exact h.elim fun θ => ⟨burnsideRingCongr θ⟩
  · exact absurd h hexc

/-! ## THE simple-group theorem -/

/-- **Twin separation**: every Fitting-free *non-simple* group sharing the
order of a nonabelian simple group is separated from it by some conductor
multiplicity.

This is the global replacement for SR1's per-order hypothesis
`FittingFreeOrderForcesSimple`.  SR1 demands that no such partner exist at
`|G|` at all; `TwinSeparation` lets the twin exist and asks only that the
conductor multiset notice it — exactly the shape `ExceptionSeparation` has
on the simple-vs-simple side, and exactly what
`conductorMultiplicity_eq_of_ringEquiv` (kernel-checked,
`LeanDring/Even/OrderTransfer.lean`) converts into a contradiction with a D-ring
isomorphism.

**[COMPLETE at the paper level over all of CFSG; OPEN formally]**
(status as addendum, "twin elimination is COMPLETE for all of
CFSG"; the uniform-Diophantine route was permanently abandoned (addendum 2) and replaced by the
`ind*` route):

| family | source | mechanism |
|---|---|---|
| `A_n`, `n ≥ 9` | Theorem AT | `ind*` value set / `κ`; (H2′) discharged |
| 26 sporadics + Tits | Theorem SPT | 14 census-empty; 10 orbit floor; 3 floor + `\|Out\|` |
| `L₂` | Theorem L2-T | `ι(L₂(q)) = q+1`, orbit floor, Lemma C |
| `U₃`, `Sz`, `R` | U3-T/Sz-T/Ree-T | `ι` lemmas, `3 ∤ \|Sz(q)\|` |
| `L₃`, `S₄`, `G₂`, `³D₄`, `²F₄` |,  | Lemma B/EQ-EX |
| `F₄, E₆, ²E₆, E₇, E₈` |  | Lemma MO-EX |
| `L_d`, `U_d`, `d ≥ 4` | LU-T | Lemma Z/X′/DEG/PACK-TOP |
| `Sp_{2n}, Ω_{2n+1}, PΩ^±_{2n}` |  | Lemma MO-SPO |

**Instantiation is not external to the ring theory.**  The *census-empty* rows
make this `Prop`'s hypotheses unsatisfiable
at that `G`, so they instantiate it vacuously and dictionary-free.  Every
other row proves `ι(T) ≠ ι(S)`, hence `κ(T) ≠ κ(S)`, and converting that
into the `∃ c` below is Müller Satz 2.3.3 + 2.3.6, i.e.
`BoltjeIntegrality`; `exceptionSeparation_witness`
(`LeanDring/Even/BoltjeAssembly.lean`) is the last mile.  Instantiating it also
needs **CFSG itself** (to enumerate the candidate socle factors of `H`),
a strictly larger citation than `SimpleOrderRigidity`'s order theorem,
plus the standing literature package H1 and the `(AB-S)` residue
for the 13 non-census sporadic rows. -/
def TwinSeparation : Prop :=
  ∀ (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H],
    IsSimpleGroup G → (¬ ∀ a b : G, a * b = b * a) →
      IsFittingFree H → ¬ IsSimpleGroup H → Nat.card H = Nat.card G →
        ∃ c : ℕ, conductorMultiplicity (DRing G) c ≠ conductorMultiplicity (DRing H) c

/-- **Twin separation at a single target `G`** ( item 5): the
per-family form of `TwinSeparation`, so that one family's twin
elimination — Theorem AT for `A_n`, Theorem SPT for a sporadic, a row of
the Lie towers — can be recorded and consumed on its own, without the
global `∀ G`. -/
def TwinSeparationFor (G : Type u) [Group G] [Fintype G] : Prop :=
  ∀ (H : Type u) [Group H] [Fintype H],
    IsFittingFree H → ¬ IsSimpleGroup H → Nat.card H = Nat.card G →
      ∃ c : ℕ, conductorMultiplicity (DRing G) c ≠ conductorMultiplicity (DRing H) c

/-- **[PROVEN]** The global `Prop` is exactly the per-target one, ranged
over all nonabelian simple `G`. -/
theorem twinSeparation_iff_forall :
    TwinSeparation.{u} ↔
      ∀ (G : Type u) [Group G] [Fintype G],
        IsSimpleGroup G → (¬ ∀ a b : G, a * b = b * a) → TwinSeparationFor G :=
  ⟨fun h G _ _ hG hGa H _ _ => h G H hG hGa,
    fun h G H _ _ _ _ hG hGa => h G hG hGa H⟩

/-- **THE simple-group theorem [PROVEN].**  For `G` nonabelian simple and
`H` an *arbitrary* finite group, `D(G) ≅ D(H)` forces `G ≃* H`.  No order
hypothesis, no exception clause.

The five typed inputs, with their honest provenance (**only the
third is external to the ring theory**):

* `htr: OrderTransfer` — Müller Satz 2.3.4.  `orderTransfer_of_muller`
  derives it from the two halves of `LeanDring/Even/OrderTransfer.lean`, and
  `orderTransfer_of_boltje` (`LeanDring/Even/BoltjeAssembly.lean`) derives it from
  `BoltjeIntegrality` alone, `MullerTrivialBound` being proven;
* `hdet: FittingFreeDetector` — Müller Satz 2.3.6;
  `fittingFreeDetector_of_topConductor` derives it from the multiplicity
  form `TopConductorDetectsFitting` plus order transfer;
* `hord: SimpleOrderRigidity Exc` — the CFSG order theorem, with its
  exception family carried as the opaque parameter `Exc` because Mathlib
  has no Lie-type groups.  **The one genuinely external input**;
* `hsep: ExceptionSeparation Exc` — conductor separation of that family
  (Theorem BC-n for `B_n/C_n`, `ι` for `A₈`/`L₃(4)`), routed through the
  conductor dictionary;
* `htwin: TwinSeparation` — conductor separation of Fitting-free
  non-simple order-twins (complete over CFSG at the paper level),
  likewise routed through the dictionary and additionally citing
  CFSG itself.

Proof: order transfer gives `|H| = |G|`; `G` is Fitting-free, hence so is
`H` by the detector.  If `H` were not simple, `TwinSeparation` would
produce a conductor multiplicity distinguishing the two, contradicting
`conductorMultiplicity_eq_of_ringEquiv` applied to the given isomorphism.
So `H` is simple, and nonabelian because a Fitting-free group with more
than one element is; `simpleDRigidity_of_exceptionSeparation` closes it. -/
theorem simpleGroupTheorem
    {Exc : ∀ (G : Type u) [Group G] (H : Type u) [Group H], Prop}
    (hord : SimpleOrderRigidity Exc) (hsep : ExceptionSeparation Exc)
    (htr : OrderTransfer.{u}) (hdet : FittingFreeDetector.{u})
    (htwin : TwinSeparation.{u})
    (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H]
    (hG : IsSimpleGroup G) (hGa : ¬ ∀ a b : G, a * b = b * a)
    (hD : Nonempty (DRing G ≃+* DRing H)) :
    Nonempty (G ≃* H) := by
  haveI := hG
  have hcard : Nat.card H = Nat.card G := (htr G H hD).symm
  have hGff : IsFittingFree G := isFittingFree_of_simple hGa
  have hHff : IsFittingFree H := hdet G H hD hGff
  have hHsimple : IsSimpleGroup H := by
    by_contra hns
    obtain ⟨c, hc⟩ := htwin G H hG hGa hHff hns hcard
    obtain ⟨Φ⟩ := hD
    exact hc (conductorMultiplicity_eq_of_ringEquiv Φ c)
  haveI := hHsimple
  exact simpleDRigidity_of_exceptionSeparation hord hsep htr G H hG hHsimple hGa
    (not_comm_of_fittingFree hHff) hD

/-- **THE simple-group theorem, `D ⇒ B` form [PROVEN]**: under the same
five inputs, `D(G) ≅ D(H)` forces `B(G) ≅ B(H)` for `G` nonabelian simple
and arbitrary finite `H`.  This is `DtoBConjecture` restricted to a simple
left-hand side, settled in the strong (rigidity) form. -/
theorem simpleGroupTheorem_dtoB
    {Exc : ∀ (G : Type u) [Group G] (H : Type u) [Group H], Prop}
    (hord : SimpleOrderRigidity Exc) (hsep : ExceptionSeparation Exc)
    (htr : OrderTransfer.{u}) (hdet : FittingFreeDetector.{u})
    (htwin : TwinSeparation.{u})
    (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H]
    (hG : IsSimpleGroup G) (hGa : ¬ ∀ a b : G, a * b = b * a)
    (hD : Nonempty (DRing G ≃+* DRing H)) :
    Nonempty (BurnsideRing G ≃+* BurnsideRing H) :=
  (simpleGroupTheorem hord hsep htr hdet htwin G H hG hGa hD).elim
    fun θ => ⟨burnsideRingCongr θ⟩

/-- **THE simple-group theorem, per-target form [PROVEN]**: the twin
input is needed only at `G` itself, so a family whose twin elimination is
recorded as `TwinSeparationFor G` (Theorem AT at one `A_n`, Theorem SPT
at one sporadic, one row of a Lie tower) already gets `D`-rigidity of
that `G` against arbitrary finite `H`.  Same proof as
`simpleGroupTheorem`, with the global `∀ G` of `TwinSeparation` unused. -/
theorem simpleGroupTheorem_of_twinSeparationFor
    {Exc : ∀ (G : Type u) [Group G] (H : Type u) [Group H], Prop}
    (hord : SimpleOrderRigidity Exc) (hsep : ExceptionSeparation Exc)
    (htr : OrderTransfer.{u}) (hdet : FittingFreeDetector.{u})
    (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H]
    (htwin : TwinSeparationFor G)
    (hG : IsSimpleGroup G) (hGa : ¬ ∀ a b : G, a * b = b * a)
    (hD : Nonempty (DRing G ≃+* DRing H)) :
    Nonempty (G ≃* H) := by
  haveI := hG
  have hcard : Nat.card H = Nat.card G := (htr G H hD).symm
  have hHff : IsFittingFree H := hdet G H hD (isFittingFree_of_simple hGa)
  have hHsimple : IsSimpleGroup H := by
    by_contra hns
    obtain ⟨c, hc⟩ := htwin H hHff hns hcard
    obtain ⟨Φ⟩ := hD
    exact hc (conductorMultiplicity_eq_of_ringEquiv Φ c)
  haveI := hHsimple
  exact simpleDRigidity_of_exceptionSeparation hord hsep htr G H hG hHsimple hGa
    (not_comm_of_fittingFree hHff) hD

end Even

end LeanDring

/-! ## Axiom audit

Every line below must report exactly `[propext, Classical.choice,
Quot.sound]` — in particular no `sorry`.  (`LeanDring/AxiomAudit.lean`
audits the *root* module only; the `Even/` layer audits itself in each
file, as in `LeanDring/Even/BCSeparation.lean`.) -/

#print axioms LeanDring.Even.card_perfectSelfNormalizingClass_eq_of_dringEquiv
#print axioms LeanDring.Even.solvabilityDetector_of_conductorDictionary
#print axioms LeanDring.Even.commutator_self_le
#print axioms LeanDring.Even.solvabilityDetector_of_pairDictionary
#print axioms LeanDring.Even.conductorMultiplicity_card_ne_zero
#print axioms LeanDring.Even.not_isSolvable_of_dringEquiv_of_simple
#print axioms LeanDring.Even.simpleDRigidity_of_exceptionSeparation
#print axioms LeanDring.Even.fittingFreeDetector_of_topConductor
#print axioms LeanDring.Even.fittingFreeOrderForcesSimple_of_card_sixty
#print axioms LeanDring.Even.twinSeparation_iff_forall
#print axioms LeanDring.Even.simpleGroupTheorem
#print axioms LeanDring.Even.simpleGroupTheorem_dtoB
#print axioms LeanDring.Even.simpleGroupTheorem_of_twinSeparationFor
