/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Even.BCSeparation
import Mathlib.GroupTheory.Commutator.Basic

/-!
# The conductor dictionary: `IsIndexValue` in group-theoretic terms

**EVEN-ORDER LAYER.** Inside the root module's build closure and audit:
no `sorry`, three standard axioms. The results here are
verified *implications*; their hypotheses are named `Prop`s (see §7.6 of
the paper).

`LeanDring/Even/BCSeparation.lean` and `LeanDring/Even/ATSeparation.lean` both run on

```
IsIndexValue G x:= ∃ c, conductorMultiplicity (DRing G) c ≠ 0 ∧ c * x = |G|
```

a purely ring-theoretic predicate (`conductor` = least positive isolated
value at an integer point of the ring, `LeanDring/Even/OrderTransfer.lean`).  Both
lanes turn on the same joint: the identification of that ring-side
quantity with the group-theoretic `ind*`-value

```
ind*(H, hH') = |G| / (N_G(H, hH'): H')            [Müller, Satz 2.3.3]
```

is unformalized.  This file closes the *reduction*: it defines the
group-theoretic side honestly inside Mathlib, states Satz 2.3.3 as one
named hypothesis `ConductorPairDictionary`, and **proves** that this
hypothesis is exactly equivalent to the two-sided dictionary
`isIndexValue_iff`.  After that, `BCSeparation`/`ATSeparation` are
conditional on group theory only: their index-value hypotheses may be
read (and verified in GAP) entirely in the language of pairs, normalizers
and commutator subgroups.

## Müller's index set, in Mathlib terms

Müller (Diss. Jena 2008, §1.2/§2.3) sets
`D(G):= {(H, hH'): H ≤ G, h ∈ H}` with `H' = ⁅H, H⁆`, lets `G` act by
simultaneous conjugation, and writes
`N_G(H, hH') = {g ∈ G: (gHg⁻¹, ghg⁻¹H') = (H, hH')}` for the stabilizer,
so that `H ≤ H·C_G(H) ≤ N_G(H, hH') ≤ N_G(H)`.  Here:

* `pairNormalizer H h: Subgroup G` — the stabilizer, as a *subgroup*
  (`LeanDring/Even/BCSeparation.lean` only had it as a `Set`;
  `coe_pairNormalizer` identifies the two).
* `FullyFused H h` — the pair class is stable under the Galois action
  `hH' ↦ h^a H'`, `gcd(a, |G|) = 1`.  **This qualifier is forced by the
  Lean definition of `conductor`**, which ranges over *integer* points
  `D(G) →+* ℤ`; a species `φ_{H,h}` is ℤ-valued exactly on the fully
  fused (= rational) classes.  The equivalence is
  `Even.fullyFused_iff_exists_intPoint` (`LeanDring/Even/SpeciesRationality.lean`).
* `IsIndStarValue G x` — `x` is an `ind*`-value:
  `x · |N_G(H, hH')| = |G| · |H'|`, the division-free form of
  `x = |G| / (N_G(H,hH'): H')`.

## Status

| item | status |
|---|---|
| `pairNormalizer` is a subgroup, `H ≤ · ≤ N_G(H)` | **PROVEN** |
| `commutator_le_pairNormalizer` (`H' ≤ N_G(H,hH')`) | **PROVEN** |
| `ConductorPairDictionary` (Satz 2.3.3 + fusion) | **PROVEN from `BoltjeIntegrality`** |
| ⋯ i.e. `Even.conductorPairDictionary_of_boltje` | |
| `isIndexValue_iff`: `IsIndexValue ↔ IsIndStarValue` | **PROVEN from it** |
| `isIndexValue_one` (the trivial pair is always there) | **PROVEN from it** |

No `sorry`, no custom axiom.
-/

set_option linter.unusedFintypeInType false

namespace LeanDring

namespace Even

universe u

section PairNormalizer

variable {G : Type u} [Group G]

/-- Conjugation by an element of `N_G(H)` preserves `H' = ⁅H, H⁆`. -/
theorem conj_mem_commutator_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer H) {d : G} (hd : d ∈ ⁅H, H⁆) :
    g * d * g⁻¹ ∈ ⁅H, H⁆ := by
  have hmap : H.map (MulAut.conj g).toMonoidHom = H := by
    refine le_antisymm ?_ ?_
    · rintro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
      · refine (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g)).mpr ?_
        simpa [mul_assoc] using hx
      · simp [MulAut.conj, mul_assoc]
  have : (MulAut.conj g).toMonoidHom d ∈ ⁅H, H⁆.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hd
  rw [Subgroup.map_commutator, hmap] at this
  simpa [MulAut.conj, mul_assoc] using this

/-- **Müller's pair normalizer `N_G(H, hH')` as a subgroup of `G`.**
`g` normalizes `H` and fixes the coset `hH'` under conjugation; the coset
condition is written as `⁅g, h⁆ = g h g⁻¹ h⁻¹ ∈ H'`. -/
def pairNormalizer (H : Subgroup G) (h : G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer H ∧ g * h * g⁻¹ * h⁻¹ ∈ ⁅H, H⁆}
  one_mem' := by simp
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have key : a * b * h * (a * b)⁻¹ * h⁻¹
        = a * (b * h * b⁻¹ * h⁻¹) * a⁻¹ * (a * h * a⁻¹ * h⁻¹) := by group
    rw [key]
    exact mul_mem (conj_mem_commutator_of_mem_normalizer ha hb') ha'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    have key : a⁻¹ * h * a⁻¹⁻¹ * h⁻¹ = a⁻¹ * (a * h * a⁻¹ * h⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [key]
    exact conj_mem_commutator_of_mem_normalizer (inv_mem ha) (inv_mem ha')

@[simp] theorem mem_pairNormalizer {H : Subgroup G} {h g : G} :
    g ∈ pairNormalizer H h ↔
      g ∈ Subgroup.normalizer H ∧ g * h * g⁻¹ * h⁻¹ ∈ ⁅H, H⁆ := Iff.rfl

/-- The subgroup `pairNormalizer` and the `Set` `PairNormalizer` of
`LeanDring/Even/BCSeparation.lean` are the same object. -/
theorem coe_pairNormalizer (H : Subgroup G) (h : G) :
    (pairNormalizer H h : Set G) = PairNormalizer H h := rfl

/-- `N_G(H, hH') ≤ N_G(H)` — the erratum repair, subgroup form. -/
theorem pairNormalizer_le_normalizer' (H : Subgroup G) (h : G) :
    pairNormalizer H h ≤ Subgroup.normalizer H := fun _ hg => hg.1

/-- `H ≤ N_G(H, hH')` for `h ∈ H` (Müller: `H ≤ H·C_G(H) ≤ N_G(H,hH')`). -/
theorem le_pairNormalizer (H : Subgroup G) (h : H) :
    H ≤ pairNormalizer H (h : G) := by
  intro g hg
  refine ⟨Subgroup.le_normalizer hg, ?_⟩
  have hc := Subgroup.commutator_mem_commutator (H₁ := H) (H₂ := H) hg h.2
  rw [commutatorElement_def] at hc
  simpa [mul_assoc] using hc

/-- `H' ≤ N_G(H, hH')`. -/
theorem commutator_le_pairNormalizer (H : Subgroup G) (h : H) :
    ⁅H, H⁆ ≤ pairNormalizer H (h : G) :=
  le_trans (Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]; exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb))
    (le_pairNormalizer H h)

/-- Hence `|H'|` divides `|N_G(H, hH')|`: the index `(N_G(H,hH'): H')` is
an honest natural number. -/
theorem card_commutator_dvd_card_pairNormalizer (H : Subgroup G) (h : H) :
    Nat.card ↥⁅H, H⁆ ∣ Nat.card (pairNormalizer H (h : G)) :=
  Subgroup.card_dvd_of_le (commutator_le_pairNormalizer H h)

/-- **Full fusion (rationality) of the pair class `[H, hH']`**: for every
`a` coprime to `|G|`, the Galois-conjugate pair `(H, h^a H')` is
`G`-conjugate to `(H, hH')`.  Since conjugation must carry `H` to `H`,
the conjugating element lies in `N_G(H)`.

This is the qualifier the Lean-side `conductor` imposes: it ranges over
integer points `D(G) →+* ℤ`, i.e. over the *rational* species, which are
exactly the fully fused classes. -/
def FullyFused (H : Subgroup G) (h : H) : Prop :=
  ∀ a : ℕ, Nat.Coprime a (Nat.card G) →
    ∃ g ∈ Subgroup.normalizer H,
      (g * (h : G) * g⁻¹) * ((h : G) ^ a)⁻¹ ∈ ⁅H, H⁆

/-- The trivial pair `(1, 1)` is fully fused. -/
theorem fullyFused_bot : FullyFused (⊥ : Subgroup G) 1 :=
  fun _ _ => ⟨1, Subgroup.one_mem _, by simp⟩

/-- `N_G(1, 1) = G`. -/
@[simp] theorem pairNormalizer_bot : pairNormalizer (⊥ : Subgroup G) 1 = ⊤ := by
  ext g
  simp only [mem_pairNormalizer, Subgroup.mem_top, iff_true]
  refine ⟨Subgroup.mem_normalizer_iff.mpr fun n => ?_, by simp⟩
  constructor
  · intro hn; rw [Subgroup.mem_bot] at hn ⊢; simp [hn]
  · intro hn
    rw [Subgroup.mem_bot] at hn ⊢
    have : g⁻¹ * (g * n * g⁻¹) * g = g⁻¹ * 1 * g := by rw [hn]
    simpa [mul_assoc] using this

end PairNormalizer

/-! ## The group-theoretic side of the dictionary -/

/-- **`x` is an `ind*`-value of `G`**: there is a fully fused pair
`(H, hH')` with

`x · |N_G(H, hH')| = |G| · |H'|`,

the division-free form of Müller's `x = |G| / (N_G(H,hH'): H')`. -/
def IsIndStarValue (G : Type u) [Group G] [Fintype G] (x : ℕ) : Prop :=
  ∃ (H : Subgroup G) (h : H), FullyFused H h ∧
    x * Nat.card (pairNormalizer H (h : G)) = Nat.card G * Nat.card ↥⁅H, H⁆

/-- **[OPEN formally — Müller Satz 2.3.3 = [Mueller2011] Thm. 3.5, together with
the identification of the integer points of `D(G)` with the fully fused
(rational) species classes]**

A natural number `c` occurs as a conductor of `D(G)` iff it is the index
`(N_G(H, hH'): H')` of some fully fused pair. -/
def ConductorPairDictionary : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (c : ℕ),
    conductorMultiplicity (DRing G) c ≠ 0 ↔
      ∃ (H : Subgroup G) (h : H), FullyFused H h ∧
        c * Nat.card ↥⁅H, H⁆ = Nat.card (pairNormalizer H (h : G))

/-- **The dictionary, proven from Satz 2.3.3**: the ring-theoretic
predicate `IsIndexValue` used by `BCSeparation`/`ATSeparation` is exactly
the group-theoretic `ind*`-value predicate. -/
theorem isIndexValue_iff (hdict : ConductorPairDictionary.{u})
    (G : Type u) [Group G] [Fintype G] (x : ℕ) :
    IsIndexValue G x ↔ IsIndStarValue G x := by
  constructor
  · rintro ⟨c, hc, hcx⟩
    obtain ⟨H, h, hfus, hcH⟩ := (hdict G c).mp hc
    refine ⟨H, h, hfus, ?_⟩
    calc x * Nat.card (pairNormalizer H (h : G)) = x * (c * Nat.card ↥⁅H, H⁆) := by
          rw [hcH]
      _ = (c * x) * Nat.card ↥⁅H, H⁆ := by ring
      _ = Nat.card G * Nat.card ↥⁅H, H⁆ := by rw [hcx]
  · rintro ⟨H, h, hfus, hx⟩
    obtain ⟨c, hcN⟩ := card_commutator_dvd_card_pairNormalizer H h
    have hpos : 0 < Nat.card ↥⁅H, H⁆ := Nat.card_pos
    refine ⟨c, (hdict G c).mpr ⟨H, h, hfus, by rw [hcN]; ring⟩, ?_⟩
    have : (c * x) * Nat.card ↥⁅H, H⁆ = Nat.card G * Nat.card ↥⁅H, H⁆ := by
      rw [← hx, hcN]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos this

/-- Sanity check that the dictionary is correctly oriented: the trivial
pair `(1, 1)` has conductor `(G: 1) = |G|` (Müller Satz 2.3.4), hence
`ind* = 1` is always an index value. -/
theorem isIndexValue_one (hdict : ConductorPairDictionary.{u})
    (G : Type u) [Group G] [Fintype G] : IsIndexValue G 1 := by
  refine (isIndexValue_iff hdict G 1).mpr ⟨⊥, 1, fullyFused_bot, ?_⟩
  have h1 : Nat.card (pairNormalizer (⊥ : Subgroup G) 1) = Nat.card G := by
    rw [pairNormalizer_bot]
    exact Nat.card_congr (Subgroup.topEquiv.toEquiv)
  have h2 : Nat.card ↥⁅(⊥ : Subgroup G), (⊥ : Subgroup G)⁆ = 1 := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (by simp)]
    simp
  rw [show ((1 : (⊥ : Subgroup G)) : G) = 1 from rfl, h1, h2, one_mul, mul_one]

/-- The `ind*`-form of the transfer used by `BCSeparation` / `ATSeparation`:
`ind*`-values transport along a D-ring isomorphism between groups of equal
order. -/
theorem IsIndStarValue.transfer (hdict : ConductorPairDictionary.{u})
    {G H : Type u} [Group G] [Group H] [Fintype G] [Fintype H]
    (Φ : DRing G ≃+* DRing H) (hcard : Nat.card G = Nat.card H) {x : ℕ}
    (hx : IsIndStarValue G x) : IsIndStarValue H x :=
  (isIndexValue_iff hdict H x).mp
    (((isIndexValue_iff hdict G x).mpr hx).transfer Φ hcard)

end Even

end LeanDring

/-! ## Axiom audit -/

#print axioms LeanDring.Even.conj_mem_commutator_of_mem_normalizer
#print axioms LeanDring.Even.le_pairNormalizer
#print axioms LeanDring.Even.commutator_le_pairNormalizer
#print axioms LeanDring.Even.card_commutator_dvd_card_pairNormalizer
#print axioms LeanDring.Even.pairNormalizer_bot
#print axioms LeanDring.Even.fullyFused_bot
#print axioms LeanDring.Even.isIndexValue_iff
#print axioms LeanDring.Even.isIndexValue_one
#print axioms LeanDring.Even.IsIndStarValue.transfer
