# v_task69 — discharging the conductor-dictionary chain, part 1

Date 2026-08-08.  New file: `lean_dring/LeanDring/Even/ConductorDictionaryProofs.lean`
(~250 lines).  Nothing pre-existing was edited — the file is purely additive,
so `ConductorDictionary`, `BCSeparation`, `ATSeparation`, `OrderTransfer` are
untouched.

Checked serially, one taskset-pinned process:

```
cd lean_dring
taskset -c 0 lake build LeanDring.Even.ConductorDictionary LeanDring.Theory.DRing.SpeciesInjectivity
taskset -c 0 lake build LeanDring.Theory.DRing.Adams
taskset -c 0 lake env lean LeanDring/Even/ConductorDictionaryProofs.lean
taskset -c 0 lake build LeanDring.Even.ATSeparation LeanDring.Even.ConductorDictionaryProofs
```

**0 errors, 0 warnings, 0 `sorry`** (the one string `sorry` in the file is prose
in the module docstring).  All axiom audits: `[propext, Classical.choice,
Quot.sound]` — no custom axiom.

---

## 1. What was discharged

### (a) The arithmetic of `Isolates` — unconditional

At a fixed integer point `p : R →+* ℤ` of any `CommRing R`:

| lemma | statement |
|---|---|
| `isolates_zero` | `Isolates p 0 0` |
| `Isolates.add` | `Isolates p x n → Isolates p y m → Isolates p (x+y) (n+m)` |
| `Isolates.mul` | `… → Isolates p (x*y) (n*m)` |
| `Isolates.nsmul` | `Isolates p x n → Isolates p (k • x) (k*n)` |
| `Isolates.sub` | `… → m ≤ n → Isolates p (x-y) (n-m)` |

### (b) `conductor_dvd` — the Führer property, proven outright

```
theorem conductor_dvd (p : R →+* ℤ) {x : R} {n : ℕ} (hn : 0 < n)
    (hx : Isolates p x n) : conductor R p ∣ n
```

Plus `conductor_le_of_isolates` (`conductor ≤ n`) and `conductor_spec`
(when some positive value is isolated, the conductor is itself positive and
*attained*: `∃ y, Isolates p y (conductor R p)`).

Proof: the isolated values form a subset of `ℕ` closed under `+`, `ℕ`-scaling
and truncated `−`, so `x − (n / c) • y` isolates `n % c`; if that were
positive it would beat the infimum.  **This is what makes `conductor`
deserve the name "Führer", and it was previously only implicit.**  It is the
lemma that upgrades `MullerTrivialBound` from an assumption on *all* isolated
values to a statement about the conductor alone.

### (c) `PointsSeparate` — and item (3) of the chain

```
def PointsSeparate (R) : Prop := ∀ x y : R, (∀ q : R →+* ℂ, q x = q y) → x = y
theorem dring_pointsSeparate {G} [Group G] [Fintype G] : PointsSeparate (DRing G)
```

proven from `DRing.species_injective` (species *are* ℂ-points, so a point-wise
agreement in particular gives species-wise agreement).  From it:

| lemma | statement |
|---|---|
| `Isolates.unique` | `Isolates p x n → Isolates p y n → x = y` |
| `Isolates.mul_eq_nsmul` | `Isolates p x n → Isolates p y m → x * y = n • y` |
| `Isolates.mul_self` | `Isolates p x n → x * x = n • x` |
| `Isolates.nsmul_comm` | `Isolates p x n → Isolates p y m → m • x = n • y` |

**This is item (3) in the direction the dictionary consumes**: `Isolates p x n`
really does say `x = n · e_p` for a *unique* element `e_p = x/n` which is
idempotent (`x*x = n•x`) and absorbs every other isolating element.  The claim
"ring-theoretically, `x = n·e_p`" in the `Even/OrderTransfer.lean` docstring is
now a theorem, not a gloss.  Note what is *not* claimed: the idempotent `e_p`
itself need not lie in `R` (only `n·e_p` does) — which is exactly the content
of the conductor.

### (d) The cheap milestone: `MullerIsolation` weakened, and Satz 2.3.4 re-proved

`MullerIsolation` (`OrderTransfer.lean`) asks for an isolating element of value
**exactly** `|G|` at every integer point.  Inspecting `mullerOrder_dring_eq_card`
shows that is more than the proof uses.  Formalized here:

```
def MullerIsolationWeak : Prop :=
  ∀ (G) [Group G] [Fintype G] (p : DRing G →+* ℤ),
    ∃ (n : ℕ) (x : DRing G), 0 < n ∧ n ≤ Nat.card G ∧ Isolates p x n
```

with

| lemma | statement |
|---|---|
| `MullerIsolation.weak` | `MullerIsolation → MullerIsolationWeak` |
| `conductor_le_card` | weak form ⟹ `conductor (D(G)) p ≤ |G|` for all `p` |
| `conductor_eq_card_of_trivialBound` | weak form + the `MullerTrivialBound` point `p₀` ⟹ `conductor (D(G)) p₀ = |G|` **on the nose** |
| `mullerOrder_dring_eq_card'` | `MullerIsolationWeak → MullerTrivialBound → mullerOrder (D(G)) = |G|` |
| `orderTransfer_of_muller'` | hence `OrderTransfer` |

So the §4a gap now rests on a *strictly weaker* pair of hypotheses than before:
the `= |G|` in `MullerIsolation` is recovered as a theorem at the one point
where it matters, from `conductor_dvd`.

**Honest scoping note.** `conductor p ≤ |G|` is *not* provable outright: `conductor`
is an `sInf` over a possibly-empty set, so the bound is vacuous unless an
isolating element exists, and producing one is precisely items (1)+(3)+(4).
`MullerIsolationWeak` is therefore the honest residue of the "cheap milestone" —
the existence content survives, the `= |G|` does not need assuming.
**`MullerIsolation` is not closed; it is replaced by a weaker hypothesis that
suffices.**

### (e) Item (2): the Adams surrogate for the Galois action

`Theory/DRing/Adams.lean` already proves `φ_{H,h} ∘ ψᵃ = φ_{H,hᵃ}`
(`DRing.species_comp_psi`) — the algebraic half of the Galois action, which the
v_task68 write-up did not notice was available.  Recorded here:

```
def AdamsStable (G) (q : DRing G →+* ℂ) : Prop :=
  ∀ a : ℕ, Nat.Coprime a (Nat.card G) → q.comp (MonRing.psi a) = q

theorem species_adamsStable_iff (H : Subgroup G) (h : H) :
    AdamsStable G (DRing.species H h) ↔
      ∀ a, Nat.Coprime a (Nat.card G) → DRing.species H (h ^ a) = DRing.species H h
```

i.e. "fully fused", read ring-internally, is Adams-stability of the point.  This
is the shape item (2) will be discharged in; what is still missing is the
*analytic* half (see §2).

### (f) Unconditional index-value facts

`IsIndexValue.pos` (`0 < x`) and `IsIndexValue.dvd_card` (`x ∣ |G|`) — used
informally in the BC-n/AT write-ups, now theorems.

## 2. Remaining surface, restated precisely

`ConductorPairDictionary` still stands.  Updated inventory:

1. **`species_surjective_onto_points`** — untouched, still the largest item:
   every `q : D(G) →+* ℂ` equals `DRing.species H h` for some pair, and
   `species H h = species U u` iff the pairs are `G`-conjugate.  Needs the
   basis `[K,λ]` of `D(G)` (`Theory/DRing/Induced.lean` has `basisElt` and
   `species_basisElt`, so the *evaluation* half exists) plus a spanning
   statement.  **Estimate: 2–3 sessions.**
2. **`integerPoint_iff_fullyFused`** — halved.  The ring-internal half is now
   `species_adamsStable_iff`.  The missing analytic half: values of
   `species H h` lie in `ℤ[ζ_{|G|}]`, `σ_a ∘ species H h = species H (h^a)`,
   and `ℤ[ζ] ∩ ℚ = ℤ` (Mathlib: `IsIntegrallyClosed`, `IsCyclotomicExtension`).
   Also still needed: `species H h` depends only on the coset `hH'`, which is
   *not* in the corpus (`SpeciesConj.species_conj` gives conjugation-invariance,
   not `H'`-invariance).  **Estimate: 1–1.5 sessions.**
3. **item (3)** — the consumed direction is **done** (§1c).  What remains is the
   converse packaging: for each point `p`, an `x` with `Isolates p x n` *exists*
   for some `n` (existence of `n·e_p` in the lattice).  That is species-table
   invertibility over ℚ(ζ) and is really part of item 1.  **Estimate: folded
   into item 1.**
4. **`conductor_eq_index`** — Müller (2.8) and the coefficient computation.
   `Induced.lean` carries `induced`, `speciesSum_induced`, `basisElt` and
   `species_basisElt` sorry-free, which is more than v_task68 assumed, but no
   Mackey/coefficient formula.  **Estimate: 1.5–2 sessions.**

**Revised total: 4.5–6.5 sessions**, essentially unchanged from v_task68 — the
work done here was the shallow layer.  What *did* change is that the residual
hypotheses are now cleanly separated from proven ring theory: everything that
can be proven without knowing what the points of `D(G)` are, has been.

## 3. Axiom audit (all entries)

```
Isolates.add, Isolates.mul, Isolates.nsmul, Isolates.sub,
conductor_dvd, dring_pointsSeparate, Isolates.unique,
Isolates.mul_eq_nsmul, Isolates.mul_self, Isolates.nsmul_comm,
MullerIsolation.weak, conductor_eq_card_of_trivialBound,
mullerOrder_dring_eq_card', orderTransfer_of_muller',
species_adamsStable_iff, IsIndexValue.pos, IsIndexValue.dvd_card
    : [propext, Classical.choice, Quot.sound]
```
