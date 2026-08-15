# v_task47 — the census aimed at the pinned configuration: rows 2 and 3 of
# Theorem AT die, by the **ind\*-spectrum gap**, for every `n ≥ 10¹¹`

Date 2026-08-08.  **NOTES.md not edited.**

| file | what it does |
|---|---|
| `v_task47_spec_Vs.g` / `_out.txt` | exhaustive `V_s` for `s = 3..9` (all `H`, and abelian-only); independent exhaustive `ind*` spectrum of `A₉`, `A₁₀` |
| `v_task47_lie_witness.g` / `_out.txt` | `L₃(q)`: full abelian `ind*` spectrum `q ≤ 11`, and `N_S(Z(Syl_p)) = B` for `q ≤ 27`; `L_d(q)`: `N_S(U_{P₂}) = P₂` |
| `v_task47_ranges.py` / `_out.txt` | the two numeric inequalities, log-space, `10¹¹ ≤ n ≤ 10^(10⁶)`, all `f` |
| `v_task47_diag.g` / `_out.txt` | the diagonal-psn route the task proposed, checked and found empty |

---

## 0.  Verdict, stated first

> **Row 2 (`S* = L₃(p^f)`, `f ≥ 2`, `ℓ* ≥ 2`) and row 3 (`S* = L₅(q)`, any
> `f`, any `ℓ*`) are BOTH EMPTY for every `n ≥ 10¹¹`.**
>
> Hence, combined with the existing scan `n ≤ 10¹¹` (v_task45) and with
> row 1 (closed for all `n`, v_task44), **Theorem AT holds for every
> `n ≥ 9`**, with input list reduced to **(H1)** cited classical facts and
> **(H2)** the standing convention (AB).  The two `ℓ*`-families are gone.

The kill is *not* `mult₁` and *not* the psn census.  The task's premise —
"compare `mult₁(T)` with `mult₁(A_n)`" — remains as dead in the pinned
configuration as v_task41 found it in general (§5 below re-checks the
diagonal route explicitly, in GAP, and it fails).  What works is the
**other** end of the same intrinsic multiset: the *set of values* of
`ind*`, which the pinned configuration over-determines.  In one line:

> the R1 equation pins `ℓ*·a₁ = C(n,3)`; the socle factor `S*` carries a
> **second, explicit abelian `ind*`-value** whose ratio to `a₁` is `≈ q`
> (row 2) or `≈ q²` (row 3); the pinned size bounds put that ratio strictly
> between `n` and `n^{3/2}`; and `A_n` has **no `ind*`-value at all** in the
> corresponding window `(4C(n,4), 6C(n,5))`.

Two corrections to the task statement are recorded up front:

* the task says "`q > n ≥ 10¹¹`" for both rows.  This is right for row 2
  (Lemma Q) but **false for row 3**, where v_task46 §2.5 proves `q < n`
  (indeed `q ≍ n^{2/3}` at `f = 1`).  The argument below does not need
  `q > n` in either row; it needs the two-sided bounds, which hold in both.
* the "index of a diagonal normalizer" the task proposed to use is not an
  `ind*`-value of the shape `A_n` can be tested against, because the
  diagonals are **not** psn once a third orbit is present (§5).

---

## 1.  The invariant, and the object that replaces PSN-A

Notation of `v_task34_transport.md` §0 and `v_task37_two_orbit.md` §0.  For
`1 ≠ H ≤ G`,

  `ind*(H) := [G : N_G(H)]·|H′|  ( = |G| / conductor(H, H′) )`,

and `I(G)` denotes the set of its values; by §4aj this is a `D`-ring
invariant once `|G|` is fixed, so `D(T) ≅ D(A_n)` gives

  **`I(T) = I(A_n)`.**   (†)

### Theorem SPEC  [PROVEN]

> For every `n` and every `1 ≠ H ≤ A_n` with `s := |supp(H)| ≤ n − 2`,
>
>   `ind*(H) = C(n,s) · w`,  `w = s!·|H′| / |N_{S_s}(H)| ∈ V_s`,
>
> where `V_s := { s!·|H′|/|N_{S_s}(H)| : 1 ≠ H ≤ A_s fixed-point-free }` is a
> **finite set depending only on `s`**.  Hence
>
>   **`I(A_n) = ⋃_{s=3}^{n} C(n,s)·V_s`.**

*Proof.*  `supp(H)` is `N_{A_n}(H)`-invariant, so
`N_{A_n}(H) = (N_{S_s}(H) × S_{n−s}) ∩ A_n`, of order
`|N_{S_s}(H)|(n−s)!/2` when `n − s ≥ 2` (the product always contains an odd
element then).  Divide into `n!/2`.  `H` has all elements even and support
`s`, so `H ≤ A_s`; `s ≥ 3` since `A_2 = 1`. ∎

**This is the object the task asked for, and it is *not* PSN-A.**  The
program's obstruction PSN-A ("a generating function for `mult₁(A_n)`,
requiring the classification of transitive perfect self-normalising groups
of every degree") is the wrong target: the alternating input actually
needed is `V_s`, a **finite computation per support size**, uniform in `n`,
with no classification anywhere.  `V_s` for `s ≤ 9` is computed exhaustively
in `v_task47_spec_Vs_out.txt`:

| `s` | `V_s` (all `H`) | `V_s` (abelian `H`) |
|---|---|---|
| 3 | `{1}` | `{1}` |
| 4 | `{1, 3, 4}` | `{1, 3}` |
| 5 | `{6, 30, 60}` | `{6}` |
| 6 | `{10,15,20,45,60,90,180,360}` | `{10,15,20,45}` |
| 7 | min `35` | min `35` |
| 8 | min `30` | min `30` |
| 9 | min `280` | min `280` |

Reading the first three rows off reproduces, in one stroke and with no case
analysis, the program's `ι₁ … ι₄`:

  `ι₁ = C(n,3)`, `ι₂ = C(n,4)`, `ι₃ = 3C(n,4)`, `ι₄ = 4C(n,4)`
  (Lemma ι₂-A, Lemma ι₃-A — witnesses `C₃`, `V₄`, `⟨(12)(34)⟩`, `A₄`),

and continues it: `ι₅ = 6C(n,5)` (witness `C₅`), `ι₆ = 10C(n,6)`
(witness `C₃×C₃`), … for all `n` past the obvious threshold.

### Theorem GAP  [PROVEN for `n ≥ n₀`; see §2 for `n₀`]

> `I(A_n) ∩ ( 4·C(n,4) , 6·C(n,5) ) = ∅`.
> Under (AB) (abelian `H` only) the empty interval widens to
> `( 3·C(n,4) , 6·C(n,5) )`.

*Proof.*  Let `ind*(H) < 6C(n,5)`, `s = |supp(H)|`.

* `s ≤ 5`: by Theorem SPEC the value is in
  `C(n,3)V_3 ∪ C(n,4)V_4 ∪ C(n,5)V_5`, i.e. in
  `{C(n,3)} ∪ {1,3,4}C(n,4) ∪ {6,30,60}C(n,5)` — all outside the open
  interval, the two boundary values `4C(n,4)` and `6C(n,5)` being excluded
  by openness.
* `6 ≤ s ≤ n−6`: `ind*(H) ≥ C(n,s) ≥ C(n,6) = C(n,5)(n−5)/6 > 6C(n,5)` for
  `n > 41`.
* `s ≥ n−5`: `C(n,s) ≥ 1` and `min V_s > 6C(n,5)` by **Lemma V-BIG**. ∎

### Lemma V-BIG  [PROVEN for abelian `H`; see the status table for general `H`]

> For `s ≥ 10⁶` and `1 ≠ H ≤ A_s` abelian and fixed-point-free,
> `[S_s : N_{S_s}(H)] > s⁶`.

*Proof.*  `H` abelian and transitive on each orbit ⟹ **regular** on each
orbit.  Let `d` = largest orbit size, `m` = number of orbits of size `d`,
`W` their union, `r` = total number of orbits, `N = N_{S_s}(H)`, and let
`d₀ = d₀(s)` be least with `d₀!/d₀^{1+log₂ d₀} > s⁶` (so `d₀ = Θ(log s/log log s)`;
`d₀ ≤ 60` for `s ≤ 10^{11}`, and `d₀ ≤ 6·log s` always).

1. **`d ≥ d₀`.**  `W` is `N`-invariant, and `N|_W` normalises `H^W`, which is
   abelian with `m` regular orbits of size `d`.  The normaliser in `Sym(O)`
   of a **regular** subgroup `A` is its holomorph, of order `d·|Aut(A)| ≤
   d^{1+log₂ d}`; hence `|N| ≤ (d^{1+log₂d})^m·m!·(s−dm)!` and
   `[S_s:N] ≥ C(s,dm)·(dm)!/((d^{1+log₂d})^m m!) ≥ C(s,dm)·(d!/d^{1+log₂d})^m`
   (using `(dm)! ≥ (d!)^m m!`).  The second factor already exceeds `s⁶`.
2. **`d < d₀` and `s − dm ≥ 20`.**  Then `C(s,dm) = C(s,s−dm) ≥ C(s,20) > s⁶`.
3. **`d < d₀` and `s − dm ≤ 19`.**  Then `m ≥ (s−19)/d₀ ≥ √s`, and the orbit
   partition alone gives
   `[S_s:N] ≥ s!/(∏_d (d!)^{m_d} m_d!) ≥ s!/(d₀^{s}·(s/2)!)`,
   whose `log₂` is `≥ (s/2)log₂ s − s(log₂ d₀ + 1) > 6log₂ s` for `s ≥ 10⁶`.
   ∎

**Honest note on general (non-abelian) `H`.**  The same three cases go
through with `|H′|` replacing the regularity input in case 1 (if the
constituent on the dominant orbit contains `A_d` then `|H′| ≥ d!/2`;
otherwise its normaliser in `S_d` is a proper transitive group, of index
`≥ min(⌊(d+1)/2⌋!, 2^{d/2})` by Bochert plus the imprimitive bound), but
case 3 in the non-abelian setting needs a routine minimisation of the
set-partition count over block shapes which is not written out here.  Since
the whole program already carries (AB) as hypothesis **(H2)**, the abelian
form is what Theorem AT actually consumes, and no new hypothesis is
introduced.

**`n₀` is genuinely needed, and the exhaustive `A₉`/`A₁₀` runs say why.**
`I(A₉)` has no value in `(504, 756)`; `I(A₁₀)` has two, `945` and `1350` —
and both come from `s ≥ n−2`, i.e. from exactly the large-support regime
Lemma V-BIG handles only asymptotically.  This is the only place in the
argument where a threshold appears; the pinned configuration lives at
`n ≥ 10¹¹`, eleven orders of magnitude above it.

---

## 2.  The Lie-side witnesses  [PROVEN, and machine-checked]

Write `S = S*`, `ι₁ = ι(S)`.  For `1 ≠ A ≤ S` abelian, Lemma TR-1 gives the
`T`-value `ℓ*·[Ā : N_Ā(A)] = ℓ*·f_A·[S : N_S(A)]` with `f_A` the fusion
number, `1 ≤ f_A ≤ |Out(S)|`.  The R1 equation is `ℓ*·f₁·ι₁ = C(n,3)` with
`f₁ ∈ {1,2}`.  Hence for any such `A`,

  **`ind*_T(A) = C(n,3)·ρ_A`,  `ρ_A = f_A·[S:N_S(A)] / (f₁·ι₁)`,**  (‡)

and by (†) plus Theorem GAP, `ρ_A ∉ ( n−3 , 0.3(n−3)(n−4) )`
(because `4C(n,4)/C(n,3) = n−3` and `6C(n,5)/C(n,3) = 0.3(n−3)(n−4)`).

### Row 2: `S = L₃(q)`, witness `A = Z(Syl_p(S))`

`A` is the long root subgroup, elementary abelian of order `q`, and
`N_S(A) = B` (the Borel): the only root subgroups normalising `X_γ`
(`γ = α+β`) are those `X_δ` with `δ+γ` not a root, i.e. `X_{±α}`… `X_{−α}`
fails since `γ−α = β` is a root, so `N_S(A) ⊇ B` and contains no negative
root subgroup, giving `N_S(A) = B`.  So

  `[S : N_S(A)] = (q+1)(q²+q+1) = (q+1)·ι₁`,  hence `ρ_A = f_A(q+1)/f₁`.

**Machine check** (`v_task47_lie_witness_out.txt`): `[S:N_S(Z(Syl_p))] =
(q+1)(q²+q+1)` verified for `q = 2,3,4,5,7,8,9,11,13,16,17,19,23,25,27`
(15 values, both `f = 1` and `f ≥ 2`).  Independently, the *complete*
abelian `ind*` spectrum of `L₃(q)` was computed for `q ≤ 11`: its two
smallest values are exactly `q²+q+1` and `(q+1)(q²+q+1)` for every `q ≥ 3`
— so this witness is in fact `ι₂(L₃(q))`, i.e. the program's `R^p = q+1`
for the `L₃` row is now *proven at the source* rather than assumed.

### Row 3: `S = L₅(q)`, witness `A = U_{P₂}`

The unipotent radical of the 2-space parabolic is abelian (type `A`,
`U_{P₂} ≅ Hom(V/W,W) ≅ q⁶`) and `N_S(U_{P₂}) = P₂` (Borel–Tits).  So

  `[S : N_S(A)] = [5,2]_q = (q²+1)·[5]_q = (q²+1)·ι₁`,  `ρ_A = f_A(q²+1)/f₁`.

**Machine check**: `N_S(U_{P₂}) = P₂` and `[S:N] = [d,2]_q` verified by
direct normaliser computation in `L₄(2)`, `L₅(2)`, `L₄(3)`, `L₆(2)`; in each
case `U_{P₂}` is confirmed abelian of order `q^{2(d−2)}`.

### The two-sided bound on `ρ_A`

`1 ≤ f_A ≤ |Out(S)|` and `1 ≤ f₁ ≤ 2` give

  row 2: `(q+1)/2 ≤ ρ_A ≤ 6f(q+1)`;  row 3: `(q²+1)/2 ≤ ρ_A ≤ 10f(q²+1)`,

using `|Out(L₃(q))| = 2f·gcd(3,q−1) ≤ 6f`, `|Out(L₅(q))| ≤ 10f`.  The
pinned bounds, all PROVEN upstream and all uniform in `ℓ*`, are

| | lower bound on `q` | upper bound on `q` |
|---|---|---|
| row 2 | `q ≥ (f n²/8.1)^{f/(2f−1)}` (Q-LB, v_task46 §2.3) | `q² < ι₁ = C(n,3)/(ℓ*f₁) ≤ C(n,3)/2` |
| row 3 | `q^{4−1/f} ≥ f n(n−2)/3.13` (MASTER, v_task46 §2.5) | `q⁴ < ι₁ ≤ C(n,3)` |

together with `q = p^f ≥ 2^f`.

**Result** (`v_task47_ranges_out.txt`, log-space, exact inequalities):
for every `n ≥ 10¹¹` and every live `f`,

  `ρ_A^{min} > n−3`  **and**  `ρ_A^{max} < 0.3(n−3)(n−4)`,

so `ρ_A` lies strictly inside the forbidden window.  **0 failures** on the
grid `n ∈ {10^{11}, 10^{12}, 10^{15}, 10^{20}, 10^{30}, 10^{60}, 10^{120},
10^{300}, 10^{1000}, 10^{10⁴}, 10^{10⁶}}` × all `f`; the tightest margin is
row 2 at `n = 10¹¹`, `f = 26`, where `ρ^{min}/(n−3) = e^{0.398} = 1.49`, and
every margin increases with `n`.  Asymptotically:

* `ρ^{min}/(n−3) ≥ (fn²/8.1)^{f/(2f−1)}/(2n)`, exponent `2f/(2f−1) > 1` at
  fixed `f`; and at large `f`, `q^{2−1/f} ≥ fn²/8.1` with `p = q^{1/f} ≥ 2`
  gives `q ≥ 0.497√f·n`, so `ρ^{min}/(n−3) ≥ 0.248√f → ∞`.  (Row 3: exponent
  `4f/(4f−1) > 1`, constant `(f/3.13)^{1/2} → ∞`.)
* `ρ^{max}/(0.3n²) = O(f·n^{−1/2}) = O(log n/√n) → 0`, since `f ≤ log₂ q`
  and `q < n^{3/2}`.

Both margins are therefore monotone past the grid.  **Rows 2 and 3 are
empty for every `n ≥ 10¹¹`.** ∎

---

## 3.  Why this is not the census route, and why the census route still fails

The task asked for a `mult₁`-based separation.  Three things were checked
and all three confirm v_task41's refutation *inside* the pinned shape:

1. **Diagonals are not psn in `T`.**  For `S` simple, `N_{S×S}(Δ_α) = Δ_α`
   for every `α ∈ Aut(S)` — verified in GAP for `S = L₂(7)`, both twisted
   diagonals (`v_task47_diag_out.txt`).  But `T` is not `S×S`: with a swap
   present `[N_T(Δ):Δ] = 2` (verified), and with a **third orbit** present
   the remaining socle factors centralise `Δ` outright.  Only *subdirect*
   subgroups covering **every** simple factor of `Q` can be psn in `T`.
2. **The subdirect count is divided out, not multiplied up.**  The `Q`-classes
   of subdirect subgroups are the Goursat data mod `Inn`: a partition of the
   factor set into blocks of isomorphic factors together with `|Out(S)|^{|B|−1}`
   gluings per block `B`.  Such a `U` is psn in `T` **iff** its stabiliser in
   `T/Q` is trivial, so the number of `T`-classes is
   `#{free points}/|T/Q|` — and `|T/Q|` divides
   `∏_O |Out(S_O)|^{ℓ_O}ℓ_O!`, which dominates the count.  At `ℓ* = 2` the
   orbit contributes `1 + |Out(S*)|` data against `|T/Q|`-many identifications:
   **no lower bound on `mult₁(T)` survives**, exactly as v_task41 concluded.
3. **The comparison target is unavailable anyway.**  `mult₁(A_n)` is unknown
   past `n = 12`, and the census-trivial padding of Lemma CT is not excluded
   by the pinned constraints either: the task asked whether census-trivial
   families can satisfy the other orbits' smoothness/conductor floors, and
   they can — `L₂(2^f)` with `f` an odd prime is strongly census-trivial with
   `ι = 2^f+1` unbounded, `|Out| = f`, and nothing in Lemma BP or TO′-0
   forbids an orbit of such factors.

The reason the `ind*` route wins where the census route loses is
structural, and worth stating: `mult₁` reads the conductor multiset at
**multiplicity of the value 1**, which outer glue can only *lower* and which
requires knowing `A_n`'s value; `ind*` reads it as a **set of values**, on
which the pinned configuration is over-determined — the R1 equation fixes
one value and the group `S*` then *forces* a second one, at a ratio the
`A_n` spectrum has a provable hole at.

---

## 4.  Status table

| statement | status |
|---|---|
| Theorem SPEC (`I(A_n) = ⋃_s C(n,s)V_s`, `V_s` finite) | **[PROVEN]**, new |
| `V_s` for `s ≤ 9`, all `H` and abelian-only | **[COMPUTED]**, exhaustive GAP |
| `ι₁..ι₄ = C(n,3), C(n,4), 3C(n,4), 4C(n,4)` reproved; `ι₅ = 6C(n,5)` | **[PROVEN]**, from `V_3,V_4,V_5` |
| Lemma V-BIG, abelian `H`, `s ≥ 10⁶` | **[PROVEN]**, new |
| Lemma V-BIG, general `H` | **[PROVEN modulo one routine set-partition minimisation]**; not needed under (AB) = (H2) |
| Theorem GAP (`I(A_n) ∩ (4C(n,4), 6C(n,5)) = ∅`, `n ≥ n₀`) | **[PROVEN]** given V-BIG; independently verified exhaustively at `n = 9` (and the `n = 10` intruders are exactly the large-support ones) |
| `N_{L₃(q)}(Z(Syl_p)) = B`, `ind* = (q+1)ι₁` | **[PROVEN]** (root-system argument) + **[COMPUTED]** `q ≤ 27` |
| `ι₂(L₃(q)) = (q+1)(q²+q+1)` (i.e. `R^p = q+1`) | **[COMPUTED]** exhaustively `3 ≤ q ≤ 11`; the program had used only `R^p > n−3` |
| `N_{L₅(q)}(U_{P₂}) = P₂`, `ind* = (q²+1)ι₁` | **[PROVEN]** (Borel–Tits) + **[COMPUTED]** `L₄(2), L₅(2), L₄(3), L₆(2)` |
| `ρ_A` inside the forbidden window, both rows, all `f`, `n ≥ 10¹¹` | **[PROVEN]** (two-sided bounds are all upstream-PROVEN) + **[COMPUTED]** grid to `n = 10^{10⁶}` |
| **Rows 2 and 3 empty for all `n ≥ 10¹¹`** | **[PROVEN]** |
| Task premise "`q > n`" in row 3 | **REFUTED** (v_task46 §2.5: `q < n` always there) |
| Diagonal-psn route | **[CHECKED, EMPTY]** — diagonals self-normalise in `Q` but never in `T` with ≥3 orbits |

---

## 5.  Effect on Theorem AT

> **Theorem AT (final).**  For every `n ≥ 9`, every Fitting-free non-simple
> `T` with `|T| = |A_n|` has `D(T) ≇ D(A_n)`; with `simpleGroupTheorem`,
> `A_n` is D-rigid among all finite groups.
>
> Inputs: **(H1)** cited classical facts; **(H2)** the standing convention
> (AB).  The `n ≤ 10¹¹` range is v_task45's scan; `n ≥ 10¹¹` is §2 above.
> Rows 2 and 3 — the last two open rows — are closed.  **No Diophantine
> input is used anywhere in the closure**, which vindicates the original
> "group theory, not number theory" reading of the residue while
> superseding v_task41's naming of the obstruction: the alternating input
> needed was never PSN-A (a `mult₁` generating function), it was `V_s`
> (a finite per-support spectrum computation), and the Lie input needed was
> never PSN-LIE-q (uniform psn counts), it was **one** further abelian
> `ind*`-value per family.

What would still improve the write-up, in decreasing order of value:

1. finish Lemma V-BIG for non-abelian `H` (removes any reliance on (AB) in
   the new step, and is a step towards discharging (H2) globally);
2. compute `V_s` for `10 ≤ s ≤ 12` (cheap; extends Theorem SPEC's usable
   window and would let the same gap argument be run at other supports);
3. re-run the two upstream inequalities Q-LB and MASTER with the explicit
   constants at `n = 10¹¹` in exact integer arithmetic — the margin there
   (factor `1.49`) is the thinnest number in the whole closure, and it is
   the only place where a constants slip could matter.
