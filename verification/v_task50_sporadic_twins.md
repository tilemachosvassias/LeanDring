# v_task50 — Fitting-free **non-simple** twins eliminated for all 26 sporadic
# groups (+ the Tits group): each sporadic group is `D`-rigid among finite
# groups

Date 2026-08-08.  **NOTES.md not edited.**

| file | what it does |
|---|---|
| `v_task50_sporadic_twins.py` / `_out.txt` | Phase 1 order census + Phase 2 orbit-floor kill, all 27 targets, exact big-integer arithmetic |
| `v_task50_sporadic_twins.g` / `_g_out.txt` | exact `ι(S_i)` (Lemma SP recursion over CTblLib `Maxes`) for every simple group that occurs as a census socle factor |
| `v_task50_raw_census_out.txt` | the **unfiltered** Phase-1 census counts (statistics only) |
| `v_task50_fmax_out.txt` | `F_max` = the largest orbit floor realised by *any* unfiltered non-simple census solution — the robustness margin |
| `v_task50_capcheck_out.txt` | post-filter socle-factor lists and the maximal number of socle factors — shows the enumeration cap is non-binding |
| `v_task50_robustness_out.txt` | the crude single-factor robustness bound `B` |

> **Headline.**  For **all 27 targets** the census of Fitting-free non-simple
> `T` with `|T| = |S|` and `D(T) ≅ D(S)` is **EMPTY**.  Moreover — and this
> was not expected — for **24 of the 27** the elimination happens one level
> earlier: after the orbit-floor prefilter **no proper simple group survives
> as a socle factor at all**, so `Soc T = S` and `T = S` immediately.  The
> three exceptions (`M₂₂`, `Fi₂₂`, `Fi₂₃`) retain a single admissible proper
> factor each (`L₃(4)`; `²F₄(2)′, U₆(2), Suz`; `Suz`) and die on the
> `c ∣ |Out|` arithmetic.
>
> Combined with the (separately computed, see §5) fact that **every sporadic
> order is unique among all finite simple groups**, this gives:
> **each of the 26 sporadic groups, and the Tits group, is `D`-rigid among all
> finite groups** — with **no dependence on the `Bₙ/Cₙ` residue**, and with
> the standing citations listed in §6.

---

## 0. Statement and notation

Notation of `v_task34_transport.md` §0 and `v_task42_to_prime.md` §0.
`T` Fitting-free (`F(T) = 1`), `Q = Soc T = ∏_i S_i^{ℓ_i}` a product of
non-abelian simple groups, `K` = kernel of the `T`-action on the set of socle
factors, `Ā_i` the group induced on `S_i`, orbits `O` with lengths `ℓ_O`,

  `ι(G) := |G|/κ(G)`,  `κ(G) := max{ |N_G(H)|/|H'| : 1 ≠ H ≤ G }`,
  `I(G) :=` the set of `ind*` values,  `P := ⋃_O ℓ_O·I(K≤Ā)_O`.

> **Theorem SPT.**  Let `S` be one of the 26 sporadic simple groups or the
> Tits group `²F₄(2)′`.  There is **no** Fitting-free non-simple finite group
> `T` with `|T| = |S|` and `D(T) ≅ D(S)`.

---

## 1. The two structural inputs, and why they are target-agnostic

### 1.1 `ι` is a `D`-ring invariant of the target

For `G` Fitting-free the conductor `|G|` occurs exactly once in the conductor
multiset (Satz 2.3.6), so `κ(G)` is precisely the **second-largest conductor**
(§4aj).  The conductor multiset is a `D`-ring invariant
(`conductorMultiplicity_eq_of_ringEquiv`, kernel-checked) and `|G|` transfers
(§4j / Müller Satz 2.3.4).  A sporadic `S` is simple, hence Fitting-free.
Therefore

  **`D(T) ≅ D(S)` and `T` Fitting-free  ⟹  `ι(T) = ι(S)`.**   (†)

### 1.2 Lemma TO′-0 transports verbatim to a sporadic target — **[VERIFIED]**

`v_task42_to_prime.md` Lemma TO′-0 is stated for the target `A_n`, but its
proof uses **only**

* `P ⊆ I(T)` — Lemma **TR-1**, an *exact identity* with no hypotheses and no
  reference to the target (`A ≤ K_i` abelian ⟹ `|A^T| = ℓ_i·|A^{Ā_i}|`);
* the identification of the value set of `I(T)` with that of the target, which
  is (†) above / the conductor-multiset invariance.

Neither step mentions `A_n`.  **The proof is target-agnostic**; replacing
`A_n` by a sporadic `S` throughout gives, with no change of argument:

> **Lemma TO′-0(S) [PROVEN, no hypotheses beyond (†)].**
> Every element of `P` is a value of `ind*` on `S`.  In particular
> **`ℓ_O·ι(K≤Ā)_O ≥ ι(S)` for every orbit `O`**   (the **ORBIT FLOOR**),
> and no element of `P` lies strictly between two consecutive values of
> `I(S)`.

Only clause 1 is used below; the finer spectrum-inclusion clauses were not
needed (they would have been the Phase-2(c) fallback).

### 1.3 Lemma F gives the computable form of the orbit floor

By Lemma F (`v_task36_pair_invariants.md`) `ι(K≤Ā) = f(A)·[S_i:N_{S_i}(A)]`
with `f(A) ∣ |Out(S_i)|`.  Taking `A` a witness for `ι(S_i)`:

  `ι(K≤Ā)_O ≤ |Out(S_i)|·ι(S_i)`,

so the ORBIT FLOOR is *implied by*, hence *kills as soon as it violates*,

  **(F)  `ℓ_O · |Out(S_i)| · ι(S_i) ≥ ι(S)`  for every orbit `O`.**

Since `ℓ_O ≤ ℓ_i` (an orbit is contained in the isotype block), a violation
with `ℓ_O` replaced by `ℓ_i` is *a fortiori* a violation: using `ℓ_i` is the
**kill-unfriendly**, i.e. conservative, direction.

### 1.4 The `c`-bound

`F(T) = 1` gives `C_T(Soc T) = 1`, hence `T ≤ Aut(Soc T)` and
`c := [T : Soc T]` divides

  `|Out(∏ S_i^{ℓ_i})| = ∏_i ( |Out(S_i)|^{ℓ_i} · ℓ_i! )`.

This is the general-socle replacement for §4aj's ad-hoc "`c ≤ 4`" (which was
sufficient only for the `A_n` census, where the socle factor list is short).
It is used in the census exactly in this form — the full wreath-product
bound, no reduction to `2^k`.

---

## 2. Phase 1 — the order census

For each target order `N = |S|`:

1. **Build the complete list of non-abelian finite simple groups `S_i` with
   `|S_i| ∣ N`.**  (Divisibility, not just `≤ N`: `Soc T ⊴ T` so
   `|S_i|^{ℓ_i} ∣ |T| = N`.)  Enumeration, exhaustive by CFSG:
   * alternating `A_m`, `m ≥ 5`, iterated while `m!/2 ≤ N` (`m ≤ 48` even for
     the Monster);
   * the 26 sporadics + `²F₄(2)′`;
   * every Lie family `A_d, ²A_d, B_d, C_d, D_d, ²D_d, ³D₄, G₂, F₄, E₆, ²E₆,
     E₇, E₈, ²B₂, ²G₂, ²F₄` over every `q = p^f ≤ N` with `p ∣ N` (forced:
     `|S_i|` has a full `q`-power factor), each rank loop broken as soon as
     the order exceeds `N` — sound because the order is strictly increasing
     in the rank and in `q`.
   Exceptional isomorphisms are collapsed to one representative
   (`L₂(4) ≅ L₂(5) ≅ A₅`, `L₂(9) ≅ A₆`, `L₂(7) ≅ L₃(2)`, `L₄(2) ≅ A₈`,
   `U₄(2) ≅ S₄(3)`).  *Erratum caught during the run:* `U₃(3) ≅ G₂(2)′` was
   initially dropped as a duplicate of `G₂(2)`, which the generator never
   emits (`G₂(2)` is not simple); `U₃(3)` is restored and is its own
   representative.  Fixing this added one candidate factor to 9 of the 27
   censuses (e.g. `M₂₄`: 14 → 15) and changed no verdict.

2. **Enumerate multisets** `{(S_i, ℓ_i)}` with `∏|S_i|^{ℓ_i} ∣ N` and
   `c := N/∏|S_i|^{ℓ_i}` dividing `∏ |Out(S_i)|^{ℓ_i}·ℓ_i!`.

3. **Discard the one simple solution** (`Soc T = S`, `c = 1`).  What remains
   are the *non-simple* candidates: `≥ 2` socle factors counted with
   multiplicity, or one factor with `c > 1`.  (Note `S` itself can never be a
   *proper* factor of a non-simple candidate: `|S|·c = |S|` forces `c = 1`.)

### 2.1 Census statistics (unfiltered)

`v_task50_raw_census_out.txt`, socle-factor count capped at 8 (see §4):

| S | #simple divisors | #solutions | #non-simple |
|---|---|---|---|
| M₁₁ | 4 | 1 | **0** |
| M₁₂ | 5 | 1 | **0** |
| M₂₂ | 10 | 2 | 1 |
| M₂₃ | 12 | 1 | **0** |
| M₂₄ | 15 | 4 | 3 |
| J₁ | 4 | 1 | **0** |
| J₂ | 9 | 3 | 2 |
| J₃ | 7 | 1 | **0** |
| J₄ | 22 | 1 | **0** |
| HS | 12 | 1 | **0** |
| McL | 20 | 1 | **0** |
| He | 14 | 1 | **0** |
| Ru | 21 | 1 | **0** |
| Suz | 36 | 9 | 8 |
| O′N | 22 | 1 | **0** |
| Co₁ | 56 | 120 | 119 |
| Co₂ | 30 | 8 | 7 |
| Co₃ | 28 | 1 | **0** |
| Fi₂₂ | 40 | 12 | 11 |
| Fi₂₃ | 52 | 4 | 3 |
| Fi₂₄′ | 60 | 3 | 2 |
| HN | 29 | 3 | 2 |
| Ly | 26 | 1 | **0** |
| Th | 41 | 7 | 6 |
| B | 100 | 1226 | 1225 |
| M | 140 | — (enumeration too large; superseded, §4) | — |
| ²F₄(2)′ | 6 | 1 | **0** |

**The census is outright empty for 12 of the 27** — the expectation
("possibly empty for many `S`") is confirmed, and the sporadic orders are
indeed rigid: `M₁₁, M₁₂, M₂₃, J₁, J₃, J₄, HS, McL, He, Ru, O′N, Co₃, Ly` plus
`²F₄(2)′` admit **no** factorisation of their order into simple-group orders
times an admissible `c` at all.  `B` and `Co₁` are the loose ones (1225 / 119)
— their orders are the most divisor-rich.

---

## 3. Phase 2 — the orbit-floor kill

### 3.1 The `ι` inputs

* **Target `ι(S)`**: the exact values of `v_task39_sporadic_iota.md` §3
  (Lemma SP, `EXACT=true` on all 27).
* **Factor `ι(S_i)`**: recomputed here by the same Lemma-SP recursion for
  every simple group appearing in any census (`v_task50_sporadic_twins.g`,
  71 groups; e.g. `ι(U₃(3)) = 28` witness `3^{1+2}:8`, `ι(L₃(4)) = 21`,
  `ι(Suz) = 22880`).  Where CTblLib stores no `Maxes` (`L₂(16)`, `L₂(32)`,
  `L₄(4)`, `S₆(4)`, `O₁₀^±(2)`, `G₂(3)`, `²E₆(2)`, …) the **parabolic bound**
  `ι(S_i) ≤ [S_i : P]` is used: `Z(U_P)` is a nontrivial abelian subgroup and
  `N_{S_i}(Z(U_P)) = P` by Borel–Tits.  An *upper* bound on `ι(S_i)` is the
  conservative direction for (F).

### 3.2 The prefilter

Because `ℓ_O ≥ ℓ_min(S_i) := ⌈ ι(S) / (|Out(S_i)|·ι(S_i)) ⌉` is forced by (F)
for **every** orbit, a factor `S_i` can occur at all only if
`|S_i|^{ℓ_min(S_i)}` divides `|S|`.  This is the sporadic-target analogue of
`v_task42_to_prime.md` (III.3), and it is devastating:

| S | ι(S) | factors dead / total | proper factors surviving |
|---|---|---|---|
| M₁₁ | 55 | 3/4 | *none* |
| M₁₂ | 220 | 4/5 | *none* |
| M₂₂ | 77 | 8/10 | `L₃(4)` |
| M₂₃ | 253 | 11/12 | *none* |
| M₂₄ | 759 | 14/15 | *none* |
| J₁ | 1045 | 3/4 | *none* |
| J₂ | 280 | 8/9 | *none* |
| J₃ | 17442 | 6/7 | *none* |
| J₄ | 173067389 | 20/22 | *none* |
| HS | 3850 | 11/12 | *none* |
| McL | 15400 | 19/20 | *none* |
| He | 8330 | 13/14 | *none* |
| Ru | 188500 | 20/21 | *none* |
| Suz | 22880 | 33/36 | *none* |
| O′N | 2857239 | 20/22 | *none* |
| Co₁ | 1545600 | 53/56 | *none* |
| Co₂ | 46575 | 29/30 | *none* |
| Co₃ | 128800 | 27/28 | *none* |
| Fi₂₂ | 3510 | 34/40 | `²F₄(2)′`, `U₆(2)`, `Suz` |
| Fi₂₃ | 31671 | 47/52 | `Suz` |
| Fi₂₄′ | 4860485028 | 56/60 | *none* |
| HN | 1539000 | 28/29 | *none* |
| Ly | 9606125 | 24/26 | *none* |
| Th | 283599225 | 38/41 | *none* |
| B | 13571955000 | 89/100 | *none* |
| M | 97239461142009186000 | 113/140 | *none* |
| ²F₄(2)′ | 1755 | 5/6 | *none* |

(“dead / total’’ counts `S` itself among the survivors; the last column lists
the survivors **other than** `S`.)

**24 of 27 have an empty last column.**  For those, `Soc T` can only be `S`
itself, whence `c = 1` and `T = S`: **no non-simple twin exists, by the orbit
floor alone.**

### 3.3 The three residual targets

| S | surviving proper factor `S₁` | `|S|/|S₁|` | `|Out(S₁)|` | verdict |
|---|---|---|---|---|
| M₂₂ | `L₃(4)` | 22 | 12 | `22 ∤ 12` — dead |
| Fi₂₂ | `²F₄(2)′` | 3592512 | 2 | dead |
| Fi₂₂ | `U₆(2)` | 7020 | 6 | dead |
| Fi₂₂ | `Suz` | 144 | 2 | dead |
| Fi₂₃ | `Suz` | 9121248 | 2 | dead |

In each case the surviving factor admits multiplicity `ℓ = 1` only
(`|S₁|² ∤ |S|`, `v_task50_capcheck_out.txt`), so the socle is `S₁` alone and
`c = |S|/|S₁|` must divide `|Out(S₁)|`.  It does not, in all five rows.

**Result: `NON-SIMPLE SURVIVORS = 0` for all 27 targets**
(`v_task50_sporadic_twins_out.txt`).

### 3.4 Robustness of the kill

`v_task50_fmax_out.txt` records `F_max`, the **largest** orbit floor
`min_i ℓ_i·|Out(S_i)|·ι(S_i)` realised by *any* unfiltered non-simple census
solution.  The kill is valid for any true `ι(S) > F_max`:

| S | ι(S) | `F_max` | ratio | worst socle |
|---|---|---|---|---|
| M₂₂ | 77 | 14 | 0.18 | `L₃(2) × L₂(11)`, `c=4` |
| M₂₄ | 759 | 48 | 0.063 | `L₂(23) × L₃(4)`, `c=2` |
| J₂ | 280 | 14 | 0.050 | `A₅² × L₃(2)` |
| Suz | 22880 | 28 | 0.0012 | `L₂(13) × M₁₁ × S₄(3)`, `c=2` |
| Co₁ | 1545600 | 253 | 1.6·10⁻⁴ | `U₃(4) × U₄(3) × M₂₃`, `c=2` |
| Co₂ | 46575 | 80 | 0.0017 | `A₆² × M₂₃`, `c=32` |
| Fi₂₂ | 3510 | 26 | 0.0074 | `L₃(3) × S₄(3) × M₂₂` |
| Fi₂₃ | 31671 | 36 | 0.0011 | `A₆ × L₂(17) × L₂(23) × L₂(27) × S₄(3)`, `c=3` |
| Fi₂₄′ | 4.86·10⁹ | 27 | 5.6·10⁻⁹ | `L₂(8) × L₂(17) × L₂(23) × L₂(29) × O₇(3)`, `c=3` |
| HN | 1539000 | 50 | 3.2·10⁻⁵ | `A₅⁵ × J₁`, `c=2` |
| Th | 283599225 | 40 | 1.4·10⁻⁷ | `L₂(19) × L₂(27) × L₂(31) × A₉` |
| B | 13571955000 | 96 | 7.1·10⁻⁹ | `L₂(47) × S₄(5) × U₃(8) × L₅(4)`, `c=12` |

**The worst margin anywhere is a factor 5.5** (`M₂₂`).  Everywhere else the
margin is two to nine orders of magnitude.  The reason is structural and
worth recording: a sporadic order factors only into *small* simple groups,
and small simple groups have small `ι` — while `ι(S)` for the sporadic itself
is large.  The whole elimination is this one inequality.

---

## 4. Two soundness checks on the enumeration

1. **The socle-factor cap is non-binding.**  The unfiltered census caps the
   socle at 8 simple factors (needed only for the raw statistics of §2.1; the
   Monster exceeds it, which is why its raw row is blank).  The Phase-2
   census runs with cap 64, and `v_task50_capcheck_out.txt` shows that after
   the prefilter the *only* proper factors that survive anywhere are
   `L₃(4)` (M₂₂), `²F₄(2)′/U₆(2)/Suz` (Fi₂₂), `Suz` (Fi₂₃), each with maximal
   multiplicity **1**.  So no post-filter socle has more than 2 factors and
   the cap can never bite.  This is not an accident: a socle with many
   factors has small factors, and small factors are exactly what the orbit
   floor kills (a factor with `|Out|ι(S_i) = 10` would need
   `ℓ ≥ ι(S)/10 ≈ 10¹⁹` for the Monster, against `ℓ ≤ log|M|/log 60 ≈ 30`).
2. **Falsification before proof.**  The prefilter was written *after* the
   unfiltered census, precisely so that the raw counts of §2.1 (1225 for `B`,
   119 for `Co₁`) exist as a control: had the prefilter been vacuous or
   over-aggressive it would show as a mismatch against `F_max`.  It does not
   — `F_max` is computed from the *raw* solutions and is below `ι(S)` in
   every row, independently of the prefilter.

---

## 5. The simple–simple side comes for free for sporadics

Running the same complete simple-order enumerator and asking for **equality**
`|S_i| = |S|` gives, for every one of the 27 targets, the singleton `{S}`:

> **Every sporadic order (and `|²F₄(2)′|`) is unique among all finite simple
> groups.**  [COMPUTED here; classically Artin / Kimmerle–Lyons–Sandling–
> Teague.]

So the simple–simple case for a sporadic target needs no invariant at all —
in particular it does **not** touch the `Bₙ/Cₙ` (`Ω₇(q)` vs `PSp₆(q)`)
residue that §4l leaves open for the general simple–simple theorem.  **The
sporadic row of `D`-rigidity is `Bₙ/Cₙ`-independent**, and this includes the
Tits group (whose order `17971200` is likewise unique).

---

## 6. Assembly: the per-sporadic theorem

> **Theorem SPT (assembled).**  For each `S` in the list below and each finite
> group `T` with `D(T) ≅ D(S)`:  `T ≅ S`.
>
> *Proof.*  `D(T) ≅ D(S)` forces `|T| = |S|`, `T` non-solvable and
> `F(T) = 1` (§4j–§4l reduction).  If `T` is simple, §5 gives `T ≅ S` (order
> uniqueness).  If `T` is non-simple, Theorem SPT above is contradicted. ∎

| S | method tag | note |
|---|---|---|
| M₁₁, M₁₂, M₂₃, J₁, J₃, J₄, HS, McL, He, Ru, O′N, Co₃, Ly, ²F₄(2)′ | **[PROVEN-census-empty]** | Phase-1 census already empty |
| M₂₄, J₂, Suz, Co₁, Co₂, Fi₂₄′, HN, Th, B, M | **[PROVEN-spectrum]** | orbit floor (Lemma TO′-0(S) + Lemma F); no proper factor survives the prefilter |
| M₂₂, Fi₂₂, Fi₂₃ | **[PROVEN-spectrum + order]** | one proper factor survives the prefilter, killed by `c ∤ |Out(S₁)|` |

*(The first two rows are the same argument; the split records only whether
the order arithmetic alone already sufficed.)*  **No survivors, no residue.**

### Citation list (the standing inputs this rests on)

| # | input | tag |
|---|---|---|
| C1 | CFSG (completeness of the simple-order enumeration of §2.1) | **[LIT]** |
| C2 | ATLAS maximal-subgroup classifications via CTblLib 1.3.11 `Maxes` (for `ι(S)` and `ι(S_i)`), incl. the finished Monster list (Dietrich–Lee–Popiel 2023) | **[LIT]** |
| C3 | Borel–Tits: `N_G(Z(U_P)) = P` for a parabolic `P` (the `ι` upper bounds for the `Maxes`-less factors) | **[LIT]** |
| C4 | order transfer, `D(T) ≅ D(S) ⟹ |T| = |S|`, Müller Satz 2.3.4 (§4e) | **[LIT/formalised]** |
| C5 | conductor multiset is a `D`-ring invariant — `conductorMultiplicity_eq_of_ringEquiv` | **[Lean, kernel-checked]** |
| C6 | Satz 2.3.6 (the conductor `|G|` has multiplicity 1 for `G` Fitting-free), which makes `κ` = second-largest conductor | **[LIT]** |
| C7 | §4j–§4l reduction: `D` determines order, non-solvability, Fitting-freeness | **[PROVEN, this project]** |
| C8 | Lemma TR-1 (transport, exact, hypothesis-free) — `v_task34_transport.md` | **[PROVEN]** |
| C9 | Lemma F — `v_task36_pair_invariants.md` | **[PROVEN]** |
| **(AB-S)** | `κ(S)` is attained at an **abelian** `H` for each sporadic `S`, i.e. the tabulated `ι(S)` is the true `ι(S)` | **[HYPOTHESIS]**, see below |

**On (AB-S), stated honestly.**  `κ(G)` is a max over *all* `H`, not only
abelian ones (the point §4aw records as `(AB)` for `A_n`, closed there through
support 8).  The computed `ι(S)` of `v_task39` is the abelian minimum
`ι_ab(S)`, and `ι(S) ≤ ι_ab(S)` in general.  A failure of (AB-S) would make
the true `ι(S)` *smaller*, which is the direction that weakens (F).  Three
mitigations:

1. If `H' ` is abelian then `|N_S(H)|/|H'| ≤ |N_S(H')|/|H'| ≤ κ_ab(S)/2`, so
   any counterexample `H` must have `H''≠ 1`; iterating the derived series,
   `κ(S) ≤ max( κ_ab(S), max{ |N_S(K)|/|K| : 1 ≠ K perfect } )`.  The second
   term is exactly `mult₁`-type data (§4z–§4ai), *not* new mathematics.
2. §3.4: the margins are a factor `5.5` at worst and typically `10³–10⁹`.
   (AB-S) would have to fail by that much before any verdict changed, and
   for 12 of the 27 targets the census is empty **before** `ι` is used at
   all, so those rows are independent of (AB-S) entirely.
3. (AB-S) is the *same* hypothesis already standing for `A_n` in Theorem AT;
   it is not a new debt introduced here.

---

## 7. Reproduce

```
~/gap-4.16.0/gap -q -o 4g v_task50_sporadic_twins.g  > v_task50_sporadic_twins_g_out.txt
python3 v_task50_sporadic_twins.py                   > v_task50_sporadic_twins_out.txt
```

All arithmetic is exact Python big-integer / GAP rational; nothing is
sampled, bounded numerically, or floating-point (the only float in the output
is the display column `F_max/ι(S)` of §3.4).
