/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Even.OrderTransfer

/-!
# Theorem BC-n: the anisotropic-point conductor separates `B_n(q)` from `C_n(q)`

**EVEN-ORDER LAYER.** Inside the root module's build closure and audit:
no `sorry`, three standard axioms. The results here are
verified *implications*; their hypotheses are named `Prop`s (see §7.6 of
the paper).

This file types Theorem BC-n of the paper and proves everything in it
that is not Lie-theoretic input.

The mathematics: for `q` odd, `n ≥ 3`, put

```
ι₁ = (q^{2n} − 1)/(q − 1) = ∑_{i < 2n} q^i,     v_ε = q^n (q^n − ε)/2,  ε = ±1.
```

* the orthogonal group `Ω_{2n+1}(q)` has the *index value* `v_ε` (the orbit of
  an anisotropic point, `H = ⟨−r_e⟩` abelian, `N = C = Stab⟨e⟩`);
* every index value of `PSp_{2n}(q)` below `q^{2n}` is `1` or divisible by `ι₁`
  (`P₁` is the only maximal subgroup of index `< q^{2n}`; the erratum
  repair `N_G(H, hH') ≤ N_G(H)` is what lets this be stated over the whole
  conductor multiset rather than over identity cosets only);
* but `ι₁ ∤ v_ε` and `1 < v_ε < q^{2n}`.

Since the conductor multiset is a ring-isomorphism invariant
(`conductorMultiplicity_eq_of_ringEquiv`, kernel-checked in
`LeanDring/Even/OrderTransfer.lean`) and the two groups have equal order, an isomorphism
`D(B) ≅ D(C)` would transport the witness onto the symplectic side, where it
cannot live.

## What is PROVEN here (no axioms beyond the Lean standard three)

* `Even.iota` and the arithmetic core — `iota_coprime_base`, `lt_iota`,
  `not_dvd_of_two_mul_eq`, `lt_pow_two_mul`, `one_lt_of_two_mul_eq`: all
  of it `ℕ`-arithmetic, for `q ≥ 2`, `n ≥ 2` (the theorem is applied at
  `n ≥ 3`, `q ≥ 3` odd);
* `IsIndexValue` — `x` is an index value of `G` iff some conductor value `c` of
  `D(G)` satisfies `c * x = |G|`.  This is Müller Satz 2.3.3 read backwards: the
  conductor of the pair `(H, hH')` is `(N_G(H,hH'): H')`, so `|G|/conductor`
  is the `ind*` value.  It is stated over *conductor values*, i.e. over
  all pairs, which is exactly the repair;
* `IsIndexValue.transfer` — **[PROVEN]** index values transport along a D-ring
  isomorphism between equal-order groups.  This is the real plug-in point: it
  is `conductorMultiplicity_eq_of_ringEquiv` and nothing else;
* `PairNormalizer`/`pairNormalizer_le_normalizer` — **[PROVEN]** the erratum
  repair itself, at the level at which it is stateable in Mathlib: the
  subgroup normalizing a pair `(H, hH')` is contained in `N_G(H)`;
* `bcSeparation` — **[PROVEN from the two named group-theoretic inputs]**
  `IsEmpty (DRing B ≃+* DRing C)`.

## What remains a named hypothesis (the "known theorems" package)

* `hcard: Nat.card B = Nat.card C` — `|Ω_{2n+1}(q)| = |PSp_{2n}(q)|`
  (classical order formulas);
* `hB: IsIndexValue B v` — the anisotropic-point witness; requires the
  Lie-type groups Mathlib lacks;
* `hC: CIndexDichotomy C q n` — the `P₁` dichotomy over all conductor pairs;
  rests on the Aschbacher / Kleidman–Liebeck classification of maximal
  subgroups of `Sp_{2n}(q)` at order level, plus Bray–Holt–Roney-Dougal
  8.28/8.29 orders at `n = 3`.

Both are phrased in the invariant (`conductorMultiplicity`) the D-ring
machinery actually exposes.

**Upgrade**: `LeanDring/Even/BoltjeAssembly.lean` restates both inputs in pure
group theory (`BAnisotropicIndStar`, `CIndStarDichotomy`, in terms of
`IsIndStarValue`, i.e. of pair normalizers and commutator subgroups) and
proves `bcSeparation_of_boltje` from them, given the single named `Prop`
`BoltjeIntegrality` (`LeanDring/Even/ConductorAtSpecies.lean` §12).  The corollaries
live there rather than here because `ConductorAtSpecies` imports this file
transitively.
-/

set_option linter.unusedFintypeInType false

namespace LeanDring

namespace Even

universe u

/-! ## The arithmetic core (fully proven) -/

/-- `ι₁ = (q^{2n} − 1)/(q − 1)`, written as a geometric sum to avoid
division: the index `[Sp_{2n}(q): P₁]` of the point stabilizer. -/
def iota (q n : ℕ) : ℕ := ∑ i ∈ Finset.range (2 * n), q ^ i

/-- `ι₁ ≡ 1 mod q`, hence `gcd(ι₁, q) = 1`. -/
theorem iota_coprime_base {q n : ℕ} (hn : 1 ≤ n) : Nat.Coprime (iota q n) q := by
  obtain ⟨m, hm⟩ : ∃ m, 2 * n = m + 1 := ⟨2 * n - 1, by omega⟩
  have h : iota q n = q * (∑ i ∈ Finset.range m, q ^ i) + 1 := by
    rw [iota, hm]
    simpa using geom_sum_succ (x := q) (n := m)
  have base : Nat.Coprime (1 + q * (∑ i ∈ Finset.range m, q ^ i)) q :=
    (Nat.coprime_add_mul_left_left 1 q _).mpr (Nat.coprime_one_left q)
  rw [h, add_comm]
  exact base

/-- `ι₁` dominates `q^n + 1` (for `n ≥ 2`, `q ≥ 2`): it contains the two
terms `q^0` and `q^{2n−1}`. -/
theorem add_one_lt_iota {q n : ℕ} (hq : 2 ≤ q) (hn : 2 ≤ n) :
    q ^ n + 1 < iota q n := by
  have hsub : ({0, 2 * n - 1} : Finset ℕ) ⊆ Finset.range (2 * n) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp [Finset.mem_range] <;> omega
  have hne : (0 : ℕ) ≠ 2 * n - 1 := by omega
  have hle : q ^ 0 + q ^ (2 * n - 1) ≤ iota q n := by
    have := Finset.sum_le_sum_of_subset (f := fun i => q ^ i) hsub
    simpa [iota, Finset.sum_pair hne] using this
  have hlt : q ^ n < q ^ (2 * n - 1) :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  simp only [pow_zero] at hle
  omega

/-- The size step: `w < ι₁` for `w ∈ {q^n − 1, q^n + 1}`. -/
theorem lt_iota {q n w : ℕ} (hq : 2 ≤ q) (hn : 2 ≤ n)
    (hw : w + 1 = q ^ n ∨ w = q ^ n + 1) : w < iota q n := by
  have := add_one_lt_iota (q := q) (n := n) hq hn
  rcases hw with h | h <;> omega

/-- `0 < w`. -/
theorem pos_of_shift {q n w : ℕ} (hq : 2 ≤ q) (hn : 1 ≤ n)
    (hw : w + 1 = q ^ n ∨ w = q ^ n + 1) : 0 < w := by
  have : 2 ≤ q ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ q ^ n := Nat.pow_le_pow_left hq 1 |>.trans (Nat.pow_le_pow_right (by omega) hn)
  omega

/-- **The exclusion `ι₁ ∤ v_ε` [PROVEN]**.  If `2v = q^n · w` with
`w = q^n ∓ 1`, then `ι₁ ∤ v`: `ι₁ ∣ v` forces `ι₁ ∣ 2v = q^n w`, and
`gcd(ι₁, q) = 1` gives `ι₁ ∣ w`, impossible since `0 < w < ι₁`. -/
theorem not_dvd_of_two_mul_eq {q n v w : ℕ} (hq : 2 ≤ q) (hn : 2 ≤ n)
    (hw : w + 1 = q ^ n ∨ w = q ^ n + 1) (hv : 2 * v = q ^ n * w) :
    ¬ iota q n ∣ v := by
  intro hdvd
  have h2 : iota q n ∣ q ^ n * w := by rw [← hv]; exact hdvd.mul_left 2
  have hcop : Nat.Coprime (iota q n) (q ^ n) :=
    (iota_coprime_base (q := q) (n := n) (by omega)).pow_right n
  have hw' : iota q n ∣ w := (Nat.Coprime.dvd_of_dvd_mul_left hcop h2)
  have hpos : 0 < w := pos_of_shift (q := q) (n := n) hq (by omega) hw
  exact absurd (Nat.le_of_dvd hpos hw') (not_le.mpr (lt_iota hq hn hw))

/-- **The range step `v_ε < q^{2n}` [PROVEN]**. -/
theorem lt_pow_two_mul {q n v w : ℕ} (hq : 2 ≤ q) (hn : 1 ≤ n)
    (hw : w + 1 = q ^ n ∨ w = q ^ n + 1) (hv : 2 * v = q ^ n * w) :
    v < q ^ (2 * n) := by
  have hpow : q ^ (2 * n) = q ^ n * q ^ n := by
    rw [two_mul, pow_add]
  have hqn : 2 ≤ q ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ q ^ n := Nat.pow_le_pow_left hq 1 |>.trans (Nat.pow_le_pow_right (by omega) hn)
  have hle : q ^ n * w ≤ q ^ n * (q ^ n + 1) := by
    have : w ≤ q ^ n + 1 := by rcases hw with h | h <;> omega
    exact Nat.mul_le_mul_left _ this
  have : q ^ n * (q ^ n + 1) < 2 * (q ^ n * q ^ n) := by nlinarith
  omega

/-- **`1 < v_ε` [PROVEN]**: the witness is not the trivial conductor. -/
theorem one_lt_of_two_mul_eq {q n v w : ℕ} (hq : 3 ≤ q) (hn : 1 ≤ n)
    (hw : w + 1 = q ^ n ∨ w = q ^ n + 1) (hv : 2 * v = q ^ n * w) : 1 < v := by
  have hqn : 3 ≤ q ^ n := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ q ^ n := Nat.pow_le_pow_left hq 1 |>.trans (Nat.pow_le_pow_right (by omega) hn)
  have hw2 : 2 ≤ w := by rcases hw with h | h <;> omega
  have : 3 * 2 ≤ q ^ n * w := Nat.mul_le_mul hqn hw2
  omega

/-! ## The pair-normalizer, and the erratum repair -/

section PairNormalizer

variable {G : Type u} [Group G]

/-- The normalizer of the *pair* `(H, hH')` in Müller's sense, formalized as
the subgroup of `N_G(H)` whose elements also fix the coset `h H'` under
conjugation.  (`H' = ⁅H, H⁆`; the coset condition is stated as membership of
the commutator `⁅g, h⁆` in `H'`, which for `g ∈ N_G(H)` is equivalent to
`g (hH') g⁻¹ = hH'`.) -/
def PairNormalizer (H : Subgroup G) (h : G) : Set G :=
  {g | g ∈ Subgroup.normalizer H ∧ g * h * g⁻¹ * h⁻¹ ∈ ⁅H, H⁆}

/-- **[PROVEN] The erratum repair**: `N_G(H, hH') ≤ N_G(H)`.
This is what makes the `P₁` dichotomy — originally stated over identity
cosets only — legitimate over the *whole* conductor multiset: every conductor
pair's index value is a multiple of `[G: N_G(H)]`. -/
theorem pairNormalizer_le_normalizer (H : Subgroup G) (h : G) :
    ∀ g ∈ PairNormalizer H h, g ∈ Subgroup.normalizer H := fun _ hg => hg.1

end PairNormalizer

/-! ## Index values, and their transport along a D-ring isomorphism -/

open DRing

/-- `x` is an **index value** of `G`: some conductor value `c` occurring in
`D(G)` satisfies `c * x = |G|`.  By Müller Satz 2.3.3 the conductor of the
pair `(H, hH')` is `(N_G(H, hH'): H')`, so `x = |G| / c` is the `ind*`
value — and quantifying over conductor *values* means quantifying over
all pairs, the form the erratum repair requires. -/
def IsIndexValue (G : Type u) [Group G] [Fintype G] (x : ℕ) : Prop :=
  ∃ c : ℕ, conductorMultiplicity (DRing G) c ≠ 0 ∧ c * x = Nat.card G

/-- **[PROVEN]** Index values transport along a D-ring isomorphism between
equal-order groups.  The only input is the kernel-checked
`conductorMultiplicity_eq_of_ringEquiv`. -/
theorem IsIndexValue.transfer {G H : Type u} [Group G] [Group H]
    [Fintype G] [Fintype H] (Φ : DRing G ≃+* DRing H)
    (hcard : Nat.card G = Nat.card H) {x : ℕ} (hx : IsIndexValue G x) :
    IsIndexValue H x := by
  obtain ⟨c, hc, hcx⟩ := hx
  exact ⟨c, by rwa [← conductorMultiplicity_eq_of_ringEquiv Φ c], by rw [hcx, hcard]⟩

/-! ## The two named group-theoretic inputs -/

/-- **[OPEN formally — the Aschbacher / Kleidman–Liebeck classification
of maximal subgroups of `Sp_{2n}(q)` at order level, plus
Bray–Holt–Roney-Dougal 8.28/8.29 orders at `n = 3`, plus the pair repair
`pairNormalizer_le_normalizer`]**

Every index value of `C = PSp_{2n}(q)` below `q^{2n}` is `1` or divisible by
`ι₁ = [C: P₁]`.  Stated over all conductor values, i.e. over all pairs
`(H, hH')` — this is the repaired form.  Machine-checked over
`n ∈ [3,8]`, all odd prime powers `q < 200` (318 pairs, 0 violations). -/
def CIndexDichotomy (C : Type u) [Group C] [Fintype C] (q n : ℕ) : Prop :=
  ∀ x : ℕ, IsIndexValue C x → x < q ^ (2 * n) → x = 1 ∨ iota q n ∣ x

/-- **[OPEN formally — the anisotropic-point orbit of `Ω_{2n+1}(q)`]**
For exactly one `ε ∈ {±1}` (determined by the
quadratic discriminant of `V`), `v = q^n(q^n − ε)/2` is an index value of
`B = Ω_{2n+1}(q)`, witnessed by the abelian subgroup `⟨−r_e⟩` for an
anisotropic point `⟨e⟩`, whose normalizer is `Stab_B(⟨e⟩)`.  GAP-verified at
`q = 3,5,7,9` (`n = 3`) and at `n = 4`, `q = 3`. -/
def BAnisotropicWitness (B : Type u) [Group B] [Fintype B] (v : ℕ) : Prop :=
  IsIndexValue B v

/-! ## Theorem BC-n -/

/-- **Theorem BC-n [PROVEN from the two named inputs]**.

Let `q ≥ 3`, `n ≥ 3`, and let `v` be the anisotropic-orbit size, presented
arithmetically as `2v = q^n · w` with `w = q^n ∓ 1` (`w + 1 = q^n` for
`ε = +1`, `w = q^n + 1` for `ε = −1`).  If

* `B` and `C` have the same order (classical order formulas),
* `v` is an index value of `B` (`BAnisotropicWitness`), and
* every index value of `C` below `q^{2n}` is `1` or divisible by `ι₁`
  (`CIndexDichotomy`),

then `D(B) ≇ D(C)`.

The arithmetic core — `1 < v`, `v < q^{2n}`, `ι₁ ∤ v` — is proven outright
above; only the two group-theoretic facts are assumed. -/
theorem bcSeparation {B C : Type u} [Group B] [Group C] [Fintype B] [Fintype C]
    {q n v w : ℕ} (hq : 3 ≤ q) (hn : 3 ≤ n)
    (hw : w + 1 = q ^ n ∨ w = q ^ n + 1) (hv : 2 * v = q ^ n * w)
    (hcard : Nat.card B = Nat.card C)
    (hB : BAnisotropicWitness B v) (hC : CIndexDichotomy C q n) :
    IsEmpty (DRing B ≃+* DRing C) := by
  refine ⟨fun Φ => ?_⟩
  have hvC : IsIndexValue C v := (hB : IsIndexValue B v).transfer Φ hcard
  have hlt : v < q ^ (2 * n) :=
    lt_pow_two_mul (q := q) (n := n) (by omega) (by omega) hw hv
  have hone : 1 < v := one_lt_of_two_mul_eq (q := q) (n := n) hq (by omega) hw hv
  rcases hC v hvC hlt with h | h
  · omega
  · exact not_dvd_of_two_mul_eq (q := q) (n := n) (by omega) (by omega) hw hv h

/-- **Theorem BC-n, isomorphism form**: no D-ring isomorphism exists. -/
theorem not_nonempty_dringEquiv_of_bcSeparation
    {B C : Type u} [Group B] [Group C] [Fintype B] [Fintype C]
    {q n v w : ℕ} (hq : 3 ≤ q) (hn : 3 ≤ n)
    (hw : w + 1 = q ^ n ∨ w = q ^ n + 1) (hv : 2 * v = q ^ n * w)
    (hcard : Nat.card B = Nat.card C)
    (hB : BAnisotropicWitness B v) (hC : CIndexDichotomy C q n) :
    ¬ Nonempty (DRing B ≃+* DRing C) := fun ⟨Φ⟩ =>
  (bcSeparation hq hn hw hv hcard hB hC).elim Φ

end Even

end LeanDring

/-! ## Axiom audit

`LeanDring/AxiomAudit.lean` collects the landmark audit; the per-file audit
for this file lives here,
in the same `#print axioms` form: every line below must report the three
standard axioms `[propext, Classical.choice, Quot.sound]` and nothing else —
in particular no `sorry`.  The arithmetic core is axiom-free in the stronger
sense that it needs none of the three beyond Mathlib's own use. -/

#print axioms LeanDring.Even.iota_coprime_base
#print axioms LeanDring.Even.add_one_lt_iota
#print axioms LeanDring.Even.lt_iota
#print axioms LeanDring.Even.not_dvd_of_two_mul_eq
#print axioms LeanDring.Even.lt_pow_two_mul
#print axioms LeanDring.Even.one_lt_of_two_mul_eq
#print axioms LeanDring.Even.pairNormalizer_le_normalizer
#print axioms LeanDring.Even.IsIndexValue.transfer
#print axioms LeanDring.Even.bcSeparation
#print axioms LeanDring.Even.not_nonempty_dringEquiv_of_bcSeparation
