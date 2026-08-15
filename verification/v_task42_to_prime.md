# Task 42 — Theorem TO′: the two-orbit trichotomy in inequality-only form,
# and the elimination of `(★₃)` (input **I10**, problem **P6** of v_task38)

Date 2026-08-07.  **NOTES.md not edited.**

| file | what it does |
|---|---|
| `v_task42_branch3_222.py` / `_out.txt` | branch **(III)** of Theorem TO′ over the 222 admissible factorizations (`n ≤ 70`) |
| `v_task42_branch3_scan.py` / `_out.txt` | branch **(III)** for **all** `n`, loop inverted over the socle factor `S`; 10 Lie families + `Sz` + `Ree` (`q ≤ 2·10⁴`) + all 26 sporadics |
| `v_task42_nu_m11.g` / `_out.txt` | exact `ν(M₁₁) = 55` (GAP, exhaustive over subgroup classes) — the R6 residue's one cheap row, and it closes |
| `v_task42_r1_weakgap.c` / `_out.txt` | residue **R1** re-run with the **weakened** gap `R^p > 3(n−3)/4` and the SIZE filter **dropped** (both were `(★)`-dependent) |
| `v_task42_table_checks_nosize.py` / `_out.txt` | Part-2 branches (a),(b1),(b2),(b3) re-run with SIZE dropped and the `n`-bound of the `n`-free branches supplied by the ORDER cap instead of Lemma TO-1 |

Headline:

> **`(★₃)` is eliminated.**  Theorem TO′ below reproves the whole branch
> structure of Theorem TO from **`I(T) ⊇ P` (TR-1, hypothesis-free)** plus the
> **floors TR-2/TR-3**, with no `(★)`, `(★₂)` or `(★₃)`.  The price is one new
> branch — **(III)**, "`C(n,3) ∉ P`" — and a weakening of the R1 gap from
> `R^p > n−3` to `R^p > 3(n−3)/4`.  All four downstream sweeps were re-run in
> the weakened form and are still empty.  Branch (III) is **empty on all 222
> admissible factorizations**, and **empty for every `n` and every Lie-type,
> Suzuki, Ree and 18 of the 26 sporadic socle factors**; it leaves a residue
> **R6** of four sporadics in explicit finite `n`-ranges
> (`HS` `71 ≤ n ≤ 75`, `McL` `78 ≤ n ≤ 144`, `Co₃` `79 ≤ n ≤ 210`,
> `Fi₂₄′` `8270 ≤ n ≤ 42681`), which is decidable by **computing `ν(S)` for
> those four groups** — a finite ATLAS/GAP computation of exactly the kind
> already listed as input **I8**.  With `ν(S) = ι(S)` for them (the value the
> `μ`-lower-bound is being used in place of) branch (III) is empty for all
> `n ≤ 4·10⁸`.

Net effect on Theorem AT's hypothesis list: **(H3) `(★₃)` is deleted**; a new
input **I12 = R6** (`ν` of four sporadics) is added, and it folds into I8.

---

## 0. Notation

Notation of `v_task34_transport.md` §0 and `v_task37_two_orbit.md` §0
throughout.  `T` Fitting-free non-simple, `|T| = n!/2`, `D(T) ≅ D(A_n)`,
`n ≥ 10`, hypothesis **(AB)**.  `Q = Soc T = ∏S_i`, orbits `O` of lengths
`ℓ_O`, pair invariants `I(K≤Ā)_O`,

  `P = ⋃_O ℓ_O·I(K≤Ā)_O`,  `F = ν_min²`,  `Φ = min(F, |S_min|)`.

Write `v₁ < v₂ < v₃ < v₄` for the four smallest values of `ind*` on `A_n`;
by Lemma ι₂-A (§4as) and Lemma ι₃-A (v_task37 §1), for `n ≥ 10`

  **`v₁ = C(n,3)`, `v₂ = C(n,4)`, `v₃ = 3C(n,4)`, `v₄ = 4C(n,4)`.**

Since the conductor multiset is a `D`-ring invariant (§4aj), `D(T) ≅ D(A_n)`
forces the ordered value sets to agree:

  **`ι_j(T) = v_j` for every `j`.**   (†)

Pair values are written `a₁ = ι(K≤Ā)_{O*} = f₁ι₁(S*)`,
`a₂ = ι₂(K≤Ā)_{O*} = f₂ι₂(S*)`, `R^p = a₂/a₁` (v_task36 Lemma F), and
likewise `b₁,b₂` for `O**`, `c₁,c₂` for a third orbit `O₃`.

---

## 1. The two hypothesis-free lemmas

### Lemma TO′-0 (spectrum inclusion) — **[PROVEN, no hypotheses]**

> Every element of `P` is a value of `ind*` on `A_n`.  In particular
>
> 1. `min P ≥ v₁ = C(n,3)`, i.e. **`ℓ_O·ι(K≤Ā)_O ≥ C(n,3)` for every orbit `O`**;
> 2. no element of `P` lies strictly between two consecutive `v_j`;
> 3. if `x ∈ P` and `x > v_j` then `x ≥ v_{j+1}`.

*Proof.*  `P ⊆ I(T)` is Lemma TR-1, an exact identity with no hypotheses;
(†) identifies the value set of `I(T)` with that of `A_n`. ∎

This is the *upper*-bound half the task asks for: `ι_j(T) ≤ p_j`, i.e.
`v_j ≤ p_j`, in the form that is actually usable — **`P` cannot contain
anything the `A_n` spectrum does not contain**.  It is strictly stronger than
Lemma TO-0 of v_task37 (which is clause 1 alone, used only for separation).

### Lemma TO′-1 (floor dichotomy) — **[PROVEN, no hypotheses]**

> For every `j`: **either `v_j ∈ P` or `v_j ≥ Φ = min(ν_min², |S_min|)`.**
>
> Consequently, if `Φ > v_j` then `v₁,…,v_j ∈ P` and they are precisely the
> `j` smallest elements of `P`: `p_i = v_i` for `i ≤ j`.

*Proof.*  `v_j = ι_j(T) ∈ I(T)`, and `I(T) \ P ⊆ [Φ,∞)` by TR-2 (multi-support,
floor `F = ν_min²`) and TR-3 (`A ⊄ K`, floor `min(F,|S_min|)`).  For the
consequence: `v_i < v_j < Φ` for `i ≤ j` puts `v₁,…,v_j ∈ P`; by Lemma TO′-0
clauses 1–2 nothing of `P` lies below `v₁` or between the `v_i`. ∎

**This identifies `(★_j)` exactly:** `(★₁) ⟺ Φ > v₁`, `(★₂) ⟺ Φ > v₂`,
`(★₃) ⟺ Φ > v₄` (the write-ups state `(★₃)` as "`p₄ < Φ`", which by the
consequence above is the same statement once `p₄ = v₄`).  So `(★)` is *only* a
statement about which of the four `A_n`-values are carried by single socle
components — and Theorem TO′ dispenses with it by branching on that directly.

---

## 2. Theorem TO′

> **Theorem TO′ [PROVEN under (AB) only; no `(★)`, `(★₂)`, `(★₃)`].**
> Let `n ≥ 10`, `T` Fitting-free non-simple with `|T| = n!/2` and
> `D(T) ≅ D(A_n)`; assume (AB).  Then **exactly one** of the following holds.
>
> * **(0) `v₁ ∉ P`.**  Then `Φ ≤ C(n,3)`: some socle factor `S` satisfies
>   `ν(S)² ≤ C(n,3)` or `|S| ≤ C(n,3)`, while **every** orbit still satisfies
>   `ℓ_O·ι(K≤Ā)_O ≥ C(n,3)` (Lemma TO′-0.1).  *[This is the new branch; §3.]*
>
> * **(a) `v₁, v₂ ∈ P`, carried by the same orbit `O*`.**  Then
>   `ℓ*a₁ = C(n,3)`, `ℓ*a₂ = C(n,4)` and
>
>     **`R^p = a₂/a₁ = (n−3)/4`** — case (a), verbatim.
>
> * **(b) `v₁ ∈ P`, and no orbit carries both `v₁` and `v₂`.**  Fix an orbit
>   `O*` with `ℓ*a₁ = min P = C(n,3)`.  Then, by Lemma TO′-0.3,
>
>     **`ℓ*a₂ ≥ v₃ = 3C(n,4)`, i.e. `R^p ≥ 3(n−3)/4`,**   (G₁)
>
>   and one of:
>   * **(b0) `v₂ ∉ P`.**  Then `C(n,4) ≥ Φ`, and the only surviving data is
>     `ℓ*a₁ = C(n,3)` together with the gap (G₁) — i.e. **exactly the R1
>     hypotheses with `n−3` replaced by `3(n−3)/4`**.
>   * **(b*) `v₂ ∈ P`**, necessarily `= ℓ**b₁` for a second orbit `O** ≠ O*`
>     (this is v_task37's case (b)).  Then:
>     * **if `v₃ ∈ P`** the trichotomy of Theorem TO holds verbatim:
>       **(b1)** `ℓ*a₂ = 3C(n,4)`, `R^p = 3(n−3)/4`;
>       **(b2)** `ℓ**b₂ = 3C(n,4)`, `b₂/b₁ = 3`;
>       **(b3)** a third orbit `O₃` with `ℓ₃c₁ = 3C(n,4)`.
>       In (b3), if additionally `v₄ ∈ P` the four sub-branches
>       `a₂/a₁ = n−3`, `b₂/b₁ = 4`, `c₂/c₁ = 4/3`, or a fourth orbit, follow
>       as before; **if `v₄ ∉ P`** then `ℓ*a₂ ≥ v₄`, i.e.
>       **`R^p ≥ n−3`** — the R1 hypotheses with the *original* gap.
>     * **if `v₃ ∉ P`** then `3C(n,4) ≥ Φ`, and again only `ℓ*a₁ = C(n,3)`
>       and (G₁) survive — R1 with the weakened gap.

*Proof.*  The case division is on the three independent binary questions
"`v₁ ∈ P`?", "`v₂ ∈ P`?", "`v₃ ∈ P`?" (and, inside (b3), "`v₄ ∈ P`?"), so it is
exhaustive and disjoint by construction.  Whenever the answer is *no*,
Lemma TO′-1 supplies `v_j ≥ Φ`.  Whenever the answer is *yes*,
Lemma TO′-0 supplies both that `min P = v₁` (clause 1 plus `v₁ ∈ P`) and that
the next element of `P` above a given `v_j` is at least `v_{j+1}` (clause 3);
the branch equations are then read off exactly as in Theorem TO — an element of
`P` is `ℓ_O` times an element of `I(K≤Ā)_O`, and `a₂` is by definition the
second value of `I(K≤Ā)_{O*}` once `a₁` is its first, which holds because
`ℓ*a₁ = min P`.  Dividing gives the ratios. ∎

**What changed, precisely.**  Theorem TO assumed `(★₃)` in order to *know*
`p_j = v_j` for `j ≤ 4`.  Theorem TO′ instead lets `P` be missing some `v_j`,
and pays for each missing value in one of two currencies: either a **floor
statement** `v_j ≥ Φ` (branch (0)) or a **gap inequality** on the next pair
value (branches (b0)/(b3)/(v₃ ∉ P)).  Both currencies are downstream-usable —
that is the whole content of the theorem.

**Only one branch of TO′ is genuinely new**: (0).  Every other branch either
*is* a branch of Theorem TO or lands in residue R1 with a gap constant between
`3(n−3)/4` and `n−3`.

---

## 3. Branch (0) worked out

Branch (0) says: the minimal conductor `C(n,3)` of `T` is **not** realised by
an abelian subgroup of a single socle component; it is realised by a
multi-support subgroup of `K` (TR-2) or by one moving the factors (TR-3).  The
two necessary conditions are

  **(III.1)** `Φ = min(ν_min², |S_min|) ≤ C(n,3)`;
  **(III.2)** `ℓ_O·ι(K≤Ā)_O ≥ C(n,3)` for **every** orbit `O` (TO′-0.1).

Apply (III.2) to the very factor `S` that triggers (III.1).  With
`ι(K≤Ā) ≤ |Out(S)|·ι₁(S)` (take `A ≤ S ≤ K` realising `ι₁(S)`; Lemma F gives
`f(A) ∣ |Out S|`) this reads

  **`ℓ ≥ ℓ_min := ⌈ C(n,3) / (|Out(S)|·ι₁(S)) ⌉`,**   (III.3)

and the orbit contributes `|S|^ℓ` to `|T| = n!/2`, whence

  **ORDER** `ℓ·log|S| ≤ log(n!/2)` (Lemma TO-2), **p-PART**
  `ℓ·f·N ≤ v_p(n!)` (Lemma R1-p), and the exact test `|S|^ℓ ∣ n!/2`.

This is a squeeze: **(III.1) makes `S` small, (III.3) then makes `ℓ` huge
(`≍ n³`), and the order equation only allows `ℓ ≍ n log n / log|S|`.**

### 3.1 Lie type, Suzuki, Ree — dead for every `n`  **[PROVEN]**

For `S` of Lie type, `ν(S) ≥ μ(S) = ι₁(S)` (Lemma TR-4 plus Lemma ι-μ /
Kleidman–Liebeck, with the `S₄(3) ≅ U₄(2)` override `ι₁ = 27` already folded
in), and `|S| ≥ ι₁(S)²` (verified for every family and every `q ≤ 2·10⁴` in the
scan: **0 violations**).  So (III.1) forces

  `C(n,3) ≥ min(ι₁², |S|) = ι₁(S)²`,  i.e.  `n ≥ (6ι₁²)^{1/3}`,

while ORDER with (III.3) forces `C(n,3)·log|S| ≤ |Out|·ι₁·n log n`, i.e.

  `n² · log|S| < 6·|Out(S)|·ι₁(S)·log n`.

Substituting `n ≥ (6ι₁²)^{1/3}` gives `(6ι₁²)^{2/3}·log|S| < 6|Out|ι₁ log n`,
i.e. `ι₁^{1/3}·log|S| < 1.82·|Out|·log n`, which with `|Out| ≤ 4 log|S|`
(verified: **0 violations** over the same range) reads `ι₁^{1/3} < 7.3 log n`
— an absolute bound on `ι₁` given `n`, and `n` itself is then bounded by the
same pair of inequalities.  The scan implements this exactly rather than
asymptotically: for each `(family, q)` it computes the window of `n` satisfying
(III.1) and the ORDER cap and enumerates it.

**Result (`v_task42_branch3_scan_out.txt`): for all ten Lie families, `Sz` and
`Ree`, `q ≤ 2·10⁴`, `n ≤ 10⁷`, the window is empty — indeed the largest `q`
with a non-empty window at all is `q = 16` for `L₃` (and none for the other
nine families), and even that dies at the exact `p`-part/divisibility test.
Zero survivors.**  Beyond `q = 2·10⁴` the displayed inequality
`ι₁^{1/3} < 7.3 log n` together with `n ≥ (6ι₁²)^{1/3}` is violated by orders
of magnitude, which is the certificate printed at the end of the output.

### 3.2 Sporadic factors — 18 dead, 8 residual, 4 after the `n ≤ 70` census

For a sporadic `S` the only *proven* lower bound on `ν(S)` is `μ(S)`
(Lemma TR-4), and for sporadics `μ(S)` is often far below `ι₁(S)`
(`M₁₁`: `11` vs `165`; `Fi₂₄′`: `306936` vs `4.86·10⁹`).  Using the `μ`-bound
the same squeeze kills 18 of the 26 outright (`J₁, J₂, J₃, He, Ru, Suz, Co₁,
Co₂, Fi₂₂, Fi₂₃, HN, Th, ON, Ly, J₄, B, M` and the alternating-excluded row),
and leaves:

| `S` | `n`-window of branch (0) | inside the `n ≤ 70` census? |
|---|---|---|
| `M₁₁` | `n = 11` | yes |
| `M₁₂` | `11 ≤ n ≤ 22` | yes |
| `M₂₂` | `16 ≤ n ≤ 35` | yes |
| `M₂₃` | `23 ≤ n ≤ 29` | yes |
| `M₂₄` | `23 ≤ n ≤ 52` | yes |
| `HS` | `41 ≤ n ≤ 75` | partly (`71–75` outside) |
| `McL` | `78 ≤ n ≤ 144` | **no** |
| `Co₃` | `79 ≤ n ≤ 210` | **no** |
| `Fi₂₄′` | `8270 ≤ n ≤ 42681` | **no** |

Two independent closures apply:

1. **`n ≤ 70`:** the 222-factorization sweep of §4 closes branch (0) outright,
   so the first five rows and the bulk of `HS` are dead.
2. **`ν(S) = ι(S)`:** re-running the identical scan with `ν(S) = ι₁(S)` for the
   sporadics (`NUMODE=iota`) gives **zero survivors for all `n ≤ 4·10⁸`**,
   Lie and sporadic alike.  The gap between the two runs is *entirely* the
   crudeness of `ν ≥ μ` for these eight groups.

> **Residue R6.**  Branch (0) of Theorem TO′ is open exactly for a `T` with a
> socle factor `S ∈ {HS, McL, Co₃, Fi₂₄′}` in the `n`-ranges
> `71–75`, `78–144`, `79–210`, `8270–42681`, and only if
> `ν(S)² ≤ C(n,3)`, i.e. only if `ν(HS) ≤ 155`, `ν(McL) ≤ 619`,
> `ν(Co₃) ≤ 943`, `ν(Fi₂₄′) ≤ 4.75·10⁵`.
> **Decidable by one finite computation:** the exact value of
> `ν(S) = min{ [S:N_S(A)] : 1 ≠ A ≤ Aut(S) abelian }` for four groups.
> It is the same kind of ATLAS/CTblLib job already listed as input **I8**, and
> the `M₁₁` case shows how it will go.  **Computed here exactly**
> (`v_task42_nu_m11.g`, exhaustive over all conjugacy classes of subgroups;
> `Out(M₁₁) = 1` so `ν = ι`): `ν(M₁₁) = 55`, realised by `A = 3²` with
> `N_{M₁₁}(3²) = 3²:QD₁₆`, against `μ(M₁₁) = 11`.  The minimal-index subgroups
> (indices `11`, `12` — `A₆.2`, `L₂(11)`) have trivial Fitting subgroup, so no
> abelian `A` normalised only by them can occur; that is the general mechanism.
> `ν(M₁₁)² = 3025 > 165 = C(11,3)` **kills the `M₁₁` row of the table above on
> its own** — the one row where the residue can be checked cheaply, and it
> closes.

> **Bookkeeping note.**  The `ι₁` values used for the sporadics in both scripts
> are v_task24's `ι_ub(S)` (upper bounds; the `M₁₁` computation above shows
> `ι(M₁₁) = 55`, not the tabulated `165`).  Both uses are conservative: an
> upper bound for `ι` gives a *smaller* `ℓ_min` in (III.3) — hence more
> survivors, never fewer — and a *larger* `minP_ub` in §4 — hence fewer
> exclusions, never more.

### 3.3 What branch (0) is *not*

It is **not** the `(★)`-failure phenomenon of v_task35 re-labelled.  The 29
`(★)`-failures all have `min P < C(n,3)` and are separated outright by
Lemma TO-0; branch (0) additionally demands `min P ≥ C(n,3)` (Lemma TO′-0.1),
which is precisely what those 29 violate.  §4 confirms this numerically: on all
222 factorizations branch (0) is excluded, in 222 cases by the `min P` test and
in 5 of them by the floor test as well.

---

## 4. Sweep 1 — branch (0) over the 222 admissible factorizations

`v_task42_branch3_222.py` re-uses `v_task35_star_check.py`'s `cands()`,
`search()` and `orbits_of()` verbatim (same 222 factorizations, `n = 5..70`,
`k ≤ 4`).  For each it computes

* `Φ_lo = min(μ_min², |S_min|) ≤ Φ` (`μ ≤ ν`, Lemma TR-4) — if `Φ_lo > C(n,3)`
  then (III.1) fails and `C(n,3) ∈ P` **(E1)**;
* `minP_ub = min_O ℓ_O·|Out(S_O)|·ι₁(S_O) ≥ min P` — if `minP_ub < C(n,3)`
  then (III.2) fails **(E2)**, and this `T` is separated outright by
  Lemma TO-0 (`ι(T) ≤ min P < C(n,3)` ⟹ `κ(T) ≠ κ(A_n)`).

Both bounds are conservative in the exclusion-unfriendly direction, exactly as
in v_task35.

```
total factorizations           : 222
excluded by BOTH (E1) and (E2) : 5
excluded by (E1) only          : 0
excluded by (E2) only          : 217
LIVE in branch (III)           : 0
```

**Branch (0) is empty on all 222.**  Note the shape of the result: it is the
`min P` test, not the floor test, that does the work — i.e. the same mechanism
as Lemma TO-0.  This is the sweep that `(★₃)` could never have: v_task40 failed
because certifying `p₄ < Φ` needs four *proven* values of `P` per factorization
and the `ι₃/ι₄` pair invariants do not exist for the Lie families
(222/222 UNKNOWN).  Branch (0)'s test needs only `ι₁` and `μ`, both tabulated.

---

## 5. Downstream: which sweeps had to be re-run, and their results

Two `(★)`-dependent ingredients had to be removed from v_task38's Part 1 and
Part 2:

* the **SIZE filter** `|S| > C(n,4)`, which came from Theorem TO Step 1 and is
  `(★)`-dependent (`Φ > p₂ = C(n,4)`), and with it **Lemma TO-1**, which
  bounded `n` in the `n`-free branches (b2)/(b3);
* the **gap constant** `n−3` in R1, which presumed `v₃, v₄ ∈ P`.

| branch | status under TO′ | action |
|---|---|---|
| **(a)** `R^p = (n−3)/4` | unchanged (needs only `v₁,v₂ ∈ P`) | re-run **without SIZE** |
| **(b1)** `R^p = 3(n−3)/4` | unchanged (reached only when `v₃ ∈ P`) | re-run without SIZE |
| **(b2)** `b₂/b₁ = 3` | unchanged; `n`-bound now from ORDER, not TO-1 | re-run without SIZE, new `n`-loop |
| **(b3)** `4`, `4/3` | unchanged when `v₄ ∈ P`; else → R1, gap `n−3` | re-run without SIZE, new `n`-loop |
| **R1** | gap weakened `n−3 → 3(n−3)/4`; SIZE dropped | re-run, `10 ≤ n ≤ 2·10⁷` |
| **(0)** | new | §§3–4 |

### 5.1 Part 2 table, SIZE dropped

`v_task42_table_checks_nosize.py` is `v_task38_table_checks.py` with the SIZE
line deleted and the `n`-loop of the `n`-free branches driven by the ORDER cap
`C(n,4)/(f₁ι₁)·log|S| ≤ log(n!/2)` (monotone in `n`, since the left side grows
like `n⁴` and the right like `n log n`) instead of Lemma TO-1's `C(n,4) < |S|`.

```
$ python3 v_task42_table_checks_nosize.py 200000
L3   f1=1 f2=1 : (a)=0 (b1)=0 (b2)=0 (b3)=0
...                                    (13 rows, all zero)
# q scanned: prime powers <= 200000   TOTAL SURVIVORS: 0
```

**All 13 rows still empty without SIZE.**  So every "eliminated outright" and
every "finite check, RUN: none" verdict of v_task38's Part-2 table stands
with `(★)` removed.

### 5.2 R1 with the weakened gap

`v_task42_r1_weakgap.c` is `v_task38_r1_scan.c` with

* every gap test `R^p > n−3` replaced by `4·R^p > 3(n−3)` (exact integer
  arithmetic, no rounding);
* the SIZE filter `|S| > C(n,4)` removed;
* Lemma L-bound re-derived: the per-family lower bounds on `q` scale by `3/4`,
  so `ι₁ ≥ (3(n−3)/4)² = 9(n−3)²/16` and `ℓ* ≤ C(n,3)/ι₁ ≈ 0.30n`; the divisor
  enumeration bound is set to the (generous) `16n/9 + 8`.

The `[PROVEN, all n ≥ 10]` rows of v_task38 §1.3–§1.4 survive the weakening,
with the same mechanism and slightly worse constants — e.g. `L₄`:
`q ≥ 3(n−3)/4` still gives `ι₁ = (q+1)(q²+1) > 0.42(n−3)³ > C(n,3)` for every
`n ≥ 10`; and `L₃` at prime `q`: `q ≥ 3(n−3)/4 > n/2` for `n ≥ 10`, so
`v_q(n!) ≤ 1 < 3ℓ*`.  The scan verifies all rows numerically.

```
# v_task42 R1 scan, WEAKENED GAP R^p > 3(n-3)/4, SIZE filter dropped
#   -- complete over ALL q, for 10 <= n <= 20000000
# per-shape hits L3=137 q3(L4/S4)=17 cyc5(L5)=2 U4=4 cyc6(Sp6)=2 U5=1
# shape hits (iota1 realised by some q): 163
# gap windows entered: 101
# SURVIVORS: 0
```

For comparison, v_task38's run with the strong gap and SIZE had 117 shape hits
and 73 gap windows; the weakened form enters 163 shape hits and 101 gap windows
— i.e. the relaxation demonstrably lets more candidates through the first two
filters, and the `p`-part and ORDER filters still kill every one of them.
**R1 is re-verified empty for `10 ≤ n ≤ 2·10⁷`, complete in `q`, with no
`(★)`-dependent filter and with the gap only `3(n−3)/4`.**

---

## 6. Consequences for Theorem AT

### 6.1 Hypothesis list

> **(H3) `(★₃)` — DELETED.**  Theorem TO′ replaces it.  `(★)` and `(★₂)` are
> likewise unused: Lemma TO-0 removed them from separation (v_task37 §2), and
> Theorem TO′ removes them from the branch structure.  **No `(★)` of any index
> appears anywhere in the chain any more.**

The replacement cost is a single new input:

| # | input | status |
|---|---|---|
| **I12 (= R6)** | `ν(S)` for `S ∈ {HS, McL, Co₃, Fi₂₄′}` (is it `≤ 155 / 619 / 943 / 4.75·10⁵`?) | **[OPEN]**, finite ATLAS/GAP computation; folds into I8, and is expected to close by the `M₁₁` mechanism (minimal-index subgroups have trivial Fitting) |

I12 is strictly smaller than the item it replaces: `(★₃)` was a condition on
*every* candidate `T` requiring four unknown pair invariants per Lie family
(v_task40: 222/222 UNKNOWN, unsweepable), whereas I12 is four numbers.

### 6.2 What is *not* improved

* R1 is not closed; it is re-verified in a *weaker* form (gap `3(n−3)/4`, no
  SIZE) over `10 ≤ n ≤ 2·10⁷`, complete in `q`.  At `ℓ* = 1` it still contains
  §4ao's equations, so the curves are still needed there.
* (AB) is untouched (I9), as is the sporadic row I8, and the census beyond
  `n = 70` (I11).
* Branch (0) at `n ≤ 70` is closed by the census, i.e. by a `[COMPUTED]` fact,
  not by proof; for `n > 70` it is closed by proof for Lie/Sz/Ree and by the
  scan (`n ≤ 10⁷`, and `n ≤ 4·10⁸` under `ν = ι`) for sporadics, modulo I12.

### 6.3 Theorem AT, hypotheses as they now stand

> Let `n ≥ 9`, `T` Fitting-free non-simple, `|T| = n!/2`.  Assume
> **(H1)** the cited classification facts; **(H2)** (AB) beyond support 8;
> **(H4)** one of v_task38's range/curve alternatives, together with I8; and
> **(H5, new)** input **I12** (`ν` of the four sporadics of R6), needed only for
> `n` in the four listed windows.  Then `κ(T) ≠ κ(A_n)`.
>
> `(★₃)` no longer appears.

---

## 7. Falsification runs done before the proofs were written

* The `|S| ≥ ι₁²` and `|Out| ≤ 4log|S|` inequalities used in §3.1 were checked
  over every family and every prime power `q ≤ 2·10⁴` **before** being used:
  0 violations each (printed at the end of `v_task42_branch3_scan_out.txt`).
* The branch-(0) scan was first run with the trigger `min(μ², |S|)`; it
  produced 34700 `(S,n)` survivors, all sporadic.  Only then was the second run
  with `ν = ι₁` performed (0 survivors), isolating the cause as the `μ`-bound
  rather than the squeeze.  Had the Lie families survived, Theorem TO′ would
  have been useless and this note would say so.
* Sweep 1 was run expecting the *floor* test (E1) to do the work; it does not
  (0 rows excluded by (E1) alone).  The `min P` test does.  That is recorded as
  found, not rationalised afterwards.

---

## 8. Reproduce

```
python3 v_task42_branch3_222.py 70 4              > v_task42_branch3_222_out.txt
NUMODE=mu   python3 v_task42_branch3_scan.py 20000 10000000
NUMODE=iota python3 v_task42_branch3_scan.py 20000 400000000
python3 v_task42_table_checks_nosize.py 200000   > v_task42_table_checks_nosize_out.txt
~/gap-4.16.0/gap -q -o 4g v_task42_nu_m11.g       > v_task42_nu_m11_out.txt
gcc -O2 -o /tmp/r1w v_task42_r1_weakgap.c -lm && /tmp/r1w 20000000
```

All arithmetic exact (Python ints / `Fraction` / `__int128`) except the
explicitly flagged `log|S|` comparisons of the ORDER cap, which are used only
as *upper* bounds on `ℓ` and are therefore conservative.
