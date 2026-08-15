/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Even.ConductorDictionary
import LeanDring.Theory.DRing.SpeciesInjectivity
import LeanDring.Theory.DRing.Adams

/-!
# Discharging part of the conductor-dictionary lemma chain

**EVEN-ORDER LAYER.** Inside the root module's build closure and audit:
no `sorry`, three standard axioms. The results here are
verified *implications*; their hypotheses are named `Prop`s (see §7.6 of
the paper).

`LeanDring/Even/ConductorDictionary.lean` reduced the ring-side/group-side dictionary
to the single Prop `ConductorPairDictionary`, which splits into four items.
This file discharges the *ring-theoretic* substrate of item (3) and of the
"cheap bound" (the conductor bound feeding `MullerIsolation`), all
unconditionally:

* **`Isolates` is an arithmetic**: isolated values at a fixed integer point
  `p` are closed under `+`, `·`, `ℕ`-scaling, and truncated `-`
  (`Isolates.add`, `Isolates.mul`, `Isolates.nsmul`, `Isolates.sub`).
* **`conductor_dvd`** — *the* Führer property, proven outright: the
  conductor of an integer point divides **every** value isolated at it.
  (Numerically: the set of isolated values is a submonoid of `ℕ` closed
  under differences, hence `c·ℕ`.)  This is what makes `conductor`
  deserve its name and was previously only implicit.
* **`PointsSeparate`** — the ℂ-points of a ring separate its elements;
  **proven for `D(G)`** (`dring_pointsSeparate`) from
  `DRing.species_injective`.
* **item (3), the direction the dictionary consumes**: at a separated ring,
  an isolating element is *unique* (`Isolates.unique`) and is `n` times an
  idempotent: `x * x = n • x` (`Isolates.mul_self`), more generally
  `x * y = n • y` for any other isolating element (`Isolates.mul_eq_nsmul`).
  So "`Isolates p x n`" really does say `x = n · e_p`, as the docstring of
  `LeanDring/Even/OrderTransfer.lean` claimed without proof.
* **`MullerIsolationWeak`** — the weakening of `MullerIsolation` that
  `mullerOrder_dring_eq_card` actually consumes (*some* positive isolated
  value `≤ |G|`, not necessarily `= |G|`), together with
  `mullerOrder_dring_eq_card'` proving Satz 2.3.4 from it, and
  `MullerIsolation.weak` showing it is indeed weaker.  The `|G|`-on-the-nose
  form is then recovered as a *theorem* at the distinguished point
  (`conductor_eq_card_of_trivialBound`).

Unconditionally true index-value facts (`IsIndexValue.pos`,
`IsIndexValue.dvd_card`) are recorded at the end, for use by the BC-n and AT
separation arguments (`LeanDring/Even/BCSeparation.lean`, `LeanDring/Even/ATSeparation.lean`).

No `sorry`, no custom axiom.  What remains of `ConductorPairDictionary` after
this file is the analytic half of item (2), discharged in
`LeanDring/Even/ConductorDictionaryGalois.lean`.
-/

set_option linter.unusedFintypeInType false

namespace LeanDring

namespace Even

universe u

section IsolatesArithmetic

variable {R : Type u} [CommRing R] {p : R →+* ℤ}

@[simp] theorem isolates_zero : Isolates p (0 : R) 0 := by
  refine ⟨by simp, fun q _ => by simp⟩

/-- Isolated values add. -/
theorem Isolates.add {x y : R} {n m : ℕ} (hx : Isolates p x n) (hy : Isolates p y m) :
    Isolates p (x + y) (n + m) := by
  refine ⟨by push_cast [map_add, hx.1, hy.1]; ring, fun q hq => ?_⟩
  rw [map_add, hx.2 q hq, hy.2 q hq, add_zero]

/-- Isolated values multiply. -/
theorem Isolates.mul {x y : R} {n m : ℕ} (hx : Isolates p x n) (hy : Isolates p y m) :
    Isolates p (x * y) (n * m) := by
  refine ⟨by push_cast [map_mul, hx.1, hy.1]; ring, fun q hq => ?_⟩
  rw [map_mul, hx.2 q hq, zero_mul]

/-- Isolated values scale by naturals. -/
theorem Isolates.nsmul {x : R} {n : ℕ} (hx : Isolates p x n) (k : ℕ) :
    Isolates p (k • x) (k * n) := by
  refine ⟨by push_cast [map_nsmul, hx.1]; ring, fun q hq => ?_⟩
  rw [map_nsmul, hx.2 q hq, smul_zero]

/-- Isolated values subtract (truncated subtraction, `m ≤ n`). -/
theorem Isolates.sub {x y : R} {n m : ℕ} (hx : Isolates p x n) (hy : Isolates p y m)
    (hmn : m ≤ n) : Isolates p (x - y) (n - m) := by
  refine ⟨?_, fun q hq => ?_⟩
  · rw [map_sub, hx.1, hy.1, Nat.cast_sub hmn]
  · rw [map_sub, hx.2 q hq, hy.2 q hq, sub_zero]

end IsolatesArithmetic

section ConductorDvd

variable {R : Type u} [CommRing R]

/-- The conductor is a lower bound for every positive isolated value. -/
theorem conductor_le_of_isolates (p : R →+* ℤ) {x : R} {n : ℕ} (hn : 0 < n)
    (hx : Isolates p x n) : conductor R p ≤ n :=
  Nat.sInf_le ⟨hn, x, hx⟩

/-- If some positive value is isolated at `p`, the conductor is itself
attained: it is positive and isolated. -/
theorem conductor_spec (p : R →+* ℤ) {x : R} {n : ℕ} (hn : 0 < n)
    (hx : Isolates p x n) :
    0 < conductor R p ∧ ∃ y : R, Isolates p y (conductor R p) := by
  have hne : {n : ℕ | 0 < n ∧ ∃ x : R, Isolates p x n}.Nonempty := ⟨n, hn, x, hx⟩
  exact Nat.sInf_mem hne

/-- **The Führer property, proven outright.** The conductor of an integer
point divides every value isolated at that point.

The isolated values form a submonoid of `ℕ` closed under truncated
difference (`Isolates.add`, `Isolates.sub`, `Isolates.nsmul`), hence a
numerical subgroup `c·ℕ` with `c` its least positive element. -/
theorem conductor_dvd (p : R →+* ℤ) {x : R} {n : ℕ} (hn : 0 < n)
    (hx : Isolates p x n) : conductor R p ∣ n := by
  obtain ⟨hcpos, y, hy⟩ := conductor_spec p hn hx
  set c := conductor R p with hc
  refine Nat.dvd_of_mod_eq_zero ?_
  by_contra hr
  have hrpos : 0 < n % c := Nat.pos_of_ne_zero hr
  -- `x - (n / c) • y` isolates `n % c`
  have hkey : Isolates p (x - (n / c) • y) (n - (n / c) * c) := by
    refine hx.sub (hy.nsmul (n / c)) ?_
    exact Nat.div_mul_le_self n c
  have hdm : (n / c) * c + n % c = n := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod n c
  have hmod : n - (n / c) * c = n % c := by omega
  rw [hmod] at hkey
  have := conductor_le_of_isolates p hrpos hkey
  exact absurd this (Nat.not_le.mpr (Nat.mod_lt _ hcpos))

end ConductorDvd

/-! ## The ℂ-points separate: item (3) of the lemma chain -/

section Separated

variable (R : Type u) [CommRing R]

/-- The complex points of `R` separate its elements (the "ghost-ring
embedding is injective" property). -/
def PointsSeparate : Prop :=
  ∀ x y : R, (∀ q : R →+* ℂ, q x = q y) → x = y

variable {R}

/-- **`D(G)` is separated by its ℂ-points**, because the species — which
are ℂ-points — already separate (`DRing.species_injective`). -/
theorem dring_pointsSeparate {G : Type u} [Group G] [Fintype G] :
    PointsSeparate (DRing G) := by
  intro x y hxy
  refine DRing.species_injective (G := G) ?_
  funext H m
  exact hxy (DRing.species H m)

variable {p : R →+* ℤ}

/-- At a separated ring, an isolating element is determined by its value:
this is the statement that `x = n · e_p` for a *unique* `e_p`. -/
theorem Isolates.unique (hsep : PointsSeparate R) {x y : R} {n : ℕ}
    (hx : Isolates p x n) (hy : Isolates p y n) : x = y := by
  refine hsep _ _ fun q => ?_
  by_cases hq : q = complexify R p
  · subst hq
    simp only [complexify, RingHom.coe_comp, Function.comp_apply, hx.1, hy.1]
  · rw [hx.2 q hq, hy.2 q hq]

/-- **Item (3), the direction the dictionary consumes**: an element
isolating the value `n` at `p` absorbs every other isolating element as a
scalar — `x * y = n • y`. -/
theorem Isolates.mul_eq_nsmul (hsep : PointsSeparate R) {x y : R} {n m : ℕ}
    (hx : Isolates p x n) (hy : Isolates p y m) : x * y = n • y := by
  refine (hx.mul hy).unique hsep ?_
  simpa [Nat.mul_comm] using hy.nsmul n

/-- **`x / n` is idempotent**: `x * x = n • x`.  So `Isolates p x n` does
say exactly `x = n · e_p` for the primitive idempotent `e_p` at `p`, as
`LeanDring/Even/OrderTransfer.lean` asserts informally. -/
theorem Isolates.mul_self (hsep : PointsSeparate R) {x : R} {n : ℕ}
    (hx : Isolates p x n) : x * x = n • x :=
  hx.mul_eq_nsmul hsep hx

/-- Consequently two isolating elements commute into each other: for
`Isolates p x n` and `Isolates p y m`, `m • x = n • y`. -/
theorem Isolates.nsmul_comm (hsep : PointsSeparate R) {x y : R} {n m : ℕ}
    (hx : Isolates p x n) (hy : Isolates p y m) : m • x = n • y := by
  rw [← hx.mul_eq_nsmul hsep hy, ← hy.mul_eq_nsmul hsep hx, mul_comm]

end Separated

/-! ## The cheap bound: what `MullerIsolation` is really needed for -/

/-- **The weakening of `MullerIsolation` that Satz 2.3.4 actually
consumes**: at every integer point of `D(G)` *some* positive value at most
`|G|` is isolated.  (`MullerIsolation` asks for the value `|G|` itself.) -/
def MullerIsolationWeak : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (p : DRing G →+* ℤ),
    ∃ (n : ℕ) (x : DRing G), 0 < n ∧ n ≤ Nat.card G ∧ Isolates p x n

/-- `MullerIsolation` is the stronger of the two. -/
theorem MullerIsolation.weak (h : MullerIsolation.{u}) : MullerIsolationWeak.{u} := by
  intro G _ _ p
  obtain ⟨x, hx⟩ := h G p
  exact ⟨Nat.card G, x, Nat.card_pos, le_rfl, hx⟩

/-- Every conductor of `D(G)` is bounded by `|G|`, given the weak form. -/
theorem conductor_le_card (hiso : MullerIsolationWeak.{u})
    (G : Type u) [Group G] [Fintype G] (p : DRing G →+* ℤ) :
    conductor (DRing G) p ≤ Nat.card G := by
  obtain ⟨n, x, hn, hnle, hx⟩ := hiso G p
  exact le_trans (conductor_le_of_isolates p hn hx) hnle

/-- **At the distinguished point of `MullerTrivialBound`, the conductor is
exactly `|G|`** — no longer an assumption but a consequence of the Führer
property `conductor_dvd` plus the weak bound. -/
theorem conductor_eq_card_of_trivialBound (hiso : MullerIsolationWeak.{u})
    (G : Type u) [Group G] [Fintype G] {p : DRing G →+* ℤ}
    (hp : ∀ (x : DRing G) (n : ℕ), Isolates p x n → Nat.card G ∣ n) :
    conductor (DRing G) p = Nat.card G := by
  obtain ⟨n, x, hn, hnle, hx⟩ := hiso G p
  obtain ⟨hcpos, y, hy⟩ := conductor_spec p hn hx
  exact Nat.le_antisymm (conductor_le_card hiso G p)
    (Nat.le_of_dvd hcpos (hp y _ hy))

/-- **Satz 2.3.4 from the weak isolation hypothesis.**  Strengthens
`mullerOrder_dring_eq_card` (`LeanDring/Even/OrderTransfer.lean`), which assumed the
full `MullerIsolation`. -/
theorem mullerOrder_dring_eq_card' (hiso : MullerIsolationWeak.{u})
    (hbd : MullerTrivialBound.{u}) (G : Type u) [Group G] [Fintype G] :
    mullerOrder (DRing G) = Nat.card G := by
  obtain ⟨p₀, hp₀⟩ := hbd G
  have hle := conductor_le_card hiso G
  have hp₀c : conductor (DRing G) p₀ = Nat.card G :=
    conductor_eq_card_of_trivialBound hiso G hp₀
  refine le_antisymm (csSup_le ⟨_, ⟨p₀, rfl⟩⟩ ?_) (le_csSup ?_ ⟨p₀, hp₀c⟩)
  · rintro n ⟨p, rfl⟩; exact hle p
  · exact ⟨Nat.card G, by rintro n ⟨p, rfl⟩; exact hle p⟩

/-- **Order transfer from the weak halves.**  Strengthens
`orderTransfer_of_muller`. -/
theorem orderTransfer_of_muller' (hiso : MullerIsolationWeak.{u})
    (hbd : MullerTrivialBound.{u}) : OrderTransfer.{u} := by
  intro G H _ _ _ _ hD
  obtain ⟨Φ⟩ := hD
  rw [← mullerOrder_dring_eq_card' hiso hbd G, ← mullerOrder_dring_eq_card' hiso hbd H]
  exact mullerOrder_eq_of_ringEquiv Φ

/-! ## Item (2): the Adams surrogate for the Galois action

The Galois action on species values is *not* formalized, but its algebraic
shadow is: `LeanDring/Theory/DRing/Adams.lean` proves `φ_{H,h} ∘ ψᵃ = φ_{H,hᵃ}`.  So
"the species class is Galois-stable" can be phrased without leaving the
ring, as stability of the *point* under coprime Adams operations, and the
two phrasings are equivalent (`species_adamsStable_iff`).  This is the shape
in which item (2) of the chain will be discharged; what is still missing is
the analytic half (values lie in `ℤ[ζ_{|G|}]`, `σ_a ∘ φ_{H,h} = φ_{H,hᵃ}`,
`ℤ[ζ] ∩ ℚ = ℤ`), which needs cyclotomic Galois theory. -/

/-- A complex point of `D(G)` is **Adams-stable** if it is unchanged by
every Adams operation `ψᵃ` with `a` coprime to `|G|`. -/
def AdamsStable (G : Type u) [Group G] [Fintype G] (q : DRing G →+* ℂ) : Prop :=
  ∀ a : ℕ, Nat.Coprime a (Nat.card G) → q.comp (MonRing.psi (A := ℂˣ) a) = q

/-- For a species, Adams-stability is exactly stability of the pair under
`h ↦ hᵃ` — the ring-internal form of "the class `[H, hH']` is fully
fused". -/
theorem species_adamsStable_iff {G : Type u} [Group G] [Fintype G]
    (H : Subgroup G) (h : H) :
    AdamsStable G (DRing.species H h) ↔
      ∀ a : ℕ, Nat.Coprime a (Nat.card G) → DRing.species H (h ^ a) = DRing.species H h := by
  constructor
  · intro hst a ha
    rw [← DRing.species_comp_psi H h a]
    exact hst a ha
  · intro hst a ha
    rw [DRing.species_comp_psi H h a]
    exact hst a ha

/-! ## Unconditional facts about index values -/

/-- Index values are positive. -/
theorem IsIndexValue.pos {G : Type u} [Group G] [Fintype G] {x : ℕ}
    (hx : IsIndexValue G x) : 0 < x := by
  obtain ⟨c, _, hcx⟩ := hx
  rcases Nat.eq_zero_or_pos x with rfl | h
  · rw [Nat.mul_zero] at hcx
    exact absurd hcx.symm Nat.card_pos.ne'
  · exact h

/-- Index values divide the group order (`c · x = |G|`). -/
theorem IsIndexValue.dvd_card {G : Type u} [Group G] [Fintype G] {x : ℕ}
    (hx : IsIndexValue G x) : x ∣ Nat.card G := by
  obtain ⟨c, _, hcx⟩ := hx
  exact ⟨c, by rw [← hcx]; ring⟩

end Even

end LeanDring

/-! ## Axiom audit -/

#print axioms LeanDring.Even.Isolates.add
#print axioms LeanDring.Even.Isolates.mul
#print axioms LeanDring.Even.Isolates.nsmul
#print axioms LeanDring.Even.Isolates.sub
#print axioms LeanDring.Even.conductor_dvd
#print axioms LeanDring.Even.dring_pointsSeparate
#print axioms LeanDring.Even.Isolates.unique
#print axioms LeanDring.Even.Isolates.mul_eq_nsmul
#print axioms LeanDring.Even.Isolates.mul_self
#print axioms LeanDring.Even.Isolates.nsmul_comm
#print axioms LeanDring.Even.MullerIsolation.weak
#print axioms LeanDring.Even.conductor_eq_card_of_trivialBound
#print axioms LeanDring.Even.mullerOrder_dring_eq_card'
#print axioms LeanDring.Even.orderTransfer_of_muller'
#print axioms LeanDring.Even.species_adamsStable_iff
#print axioms LeanDring.Even.IsIndexValue.pos
#print axioms LeanDring.Even.IsIndexValue.dvd_card
