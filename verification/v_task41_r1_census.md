# v_task41 — the ≥3-orbit residue R1 attacked with the psn census, `mult₁`
# and the order equation: what closes, what does not, and why

Date 2026-08-07.  **NOTES.md not edited.**  No new number theory (Siegel /
Baker / curves) is used or proposed anywhere below.

Scripts / outputs in this directory:

| file | what it does |
|---|---|
| `v_task41_census.g` / `_out.txt` | exact `mult₁` (psn census) of 33 small simple groups — GAP 4.16, `RepresentativesPerfectSubgroups` + `Normalizer`, exhaustive |
| `v_task41_products.g` / `_out.txt` | `mult₁` of larger `L₂(q)`, `q ≤ 343` (**run interrupted** at `PSL(2,361)`) |
| `v_task41_prodcheck.g` / `_out.txt` | `mult₁` of direct products of census-trivial factors + two controls (Lemma CT-× and Lemma PSN-×, checked) |
| `v_task41_qside.c` / `_out.txt` | **q-side** scan of the R1 residue at `ℓ* = 1`, complete over all `n` for each `q`; `S₄` to `q ≤ 10¹²` (`n ≤ 2·10¹²`), `L₅` to `q ≤ 10⁸`, `L₃` to `q ≤ 10¹²` |

Headline, stated first:

> **The ≥3-orbit scenario is NOT empty by any argument found here, and the
> census route cannot make it empty.**  Two of the three surviving rows are
> improved: the **`S₄` row is proven to have `ℓ* = 1`** (Lemma R1-S₄-ℓ1), so
> it *is* §4ao's curve `C₆` restricted to odd non-prime `q` — now scanned to
> `n ≤ 2·10¹²`; and the **`L₃` row at `ℓ* = 1` is closed for all `n`**
> already, by §4ao's squeeze plus Theorem L3₂ (an import v_task38 did not
> make).  What remains is `L₃` with `ℓ* ≥ 2`, `L₅` with any `ℓ*`, and the
> `S₄` curve — none of them touched by `mult₁`, by the psn census, or by the
> order equation.  The census route fails for a *concrete, nameable* reason:
> `mult₁(A_n)` is not known as a function of `n`, and the ≥3-orbit shape
> imposes **no** lower bound on `mult₁(T)` — the program's own `A₁₀` datum is
> a 2-orbit twin whose `mult₁` equals `A₁₀`'s exactly.

---

## 0.  The scenario, restated

`T` Fitting-free, `|T| = n!/2`, `D(T) ≅ D(A_n)`, `n ≥ 10`, `Q = Soc T`
with `k ≥ 3` orbits.  The ι-minimal orbit `O*` is a **single** factor
(`ℓ* = 1` in the branch the task names) `S ∈ {L₃(p^f) f≥2, L₅(q),
S₄(q) odd non-prime}` with

* `ℓ*·f₁·ι₁(S) = C(n,3)`  (the R1 equation),
* `a₂ > (n−3)a₁`  (spectral gap at `O*`),
* a second orbit `O** ≠ O*` with `ℓ**·f·ι₁(S**) = C(n,4)` and `b₂ > 4b₁`,
* at least one further orbit,
* `∏_O |S_O|^{ℓ_O} · c = n!/2`, `c ∣ ∏_O (|Out S_O|^{ℓ_O} ℓ_O!)`,
* **no alternating socle factor** (Theorem κ-A, B11).

---

# PART 1 — what the three surviving rows really are

## 1.1  Lemma R1-S₄-ℓ1 [PROVEN, all `n ≥ 10`] — `ℓ* = 1` is forced

*Let `O*` be the ι-minimal orbit with `S* = S₄(q)`, `q` odd.  Then
`ℓ* = 1`.*

*Proof.*  `S₄(q)` at odd `q` has no graph automorphism, so `f₁ = 1`
(v_task36 C5) and `ι₁ = (q+1)(q²+1) = q³+q²+q+1`.  The R1 gap window for
this row (v_task38 §1.5) is `q > (n−1)/2`, i.e. `n ≤ 2q`.  Hence

  `C(n,3) ≤ C(2q,3) = (2q)(2q−1)(2q−2)/6 = (4q³ − 6q² + 2q)/3 < (4/3)q³`,

while `2·f₁·ι₁ = 2q³ + 2q² + 2q + 2 > 2q³ > (4/3)q³`.  So
`ℓ* = C(n,3)/(f₁ι₁) < 2`, i.e. `ℓ* = 1`. ∎

**Consequence.**  The `S₄` row of R1 is *exactly* the set of odd
non-prime prime-power points of §4ao's genus-1 rank-3 curve

  `C₆ : q³ + q² + q + 1 = C(n,3)`  (§4ap: minimal model
  `y² = x³ + 72x − 5148`, conductor 3 983 580, rank 3, `κ ∉ 3E(ℚ)`),

with the extra conditions `q = p^f`, `f ≥ 2`, `p` odd, `n ≤ 2q`.  No
group-theoretic constraint in the program removes it; but it is now a
**one-parameter** search, which is why the q-side scan of §1.4 reaches
`n ≤ 2·10¹²` instead of `2·10⁷`.

## 1.2  The `L₃` row at `ℓ* = 1` is closed for all `n` [PROVEN — an import]

At `ℓ* = 1` the R1 equation for `S* = L₃(q)` reads
`f₁(q² + q + 1) = C(n,3)` with `f₁ ∈ {1,2}` — *verbatim* §4ao's `L₃`
equation with `m = f₁`.  Both cases are **solved outright, for every `n`**:

* `m = 1`: §4ao's discriminant squeeze (`D(t) = t⁴ − 72t² − 144t − 288`
  strictly between consecutive squares for `t ≥ 83`, plus the finite
  check `t ≤ 82`);
* `m = 2`: **Theorem L3₂** (§4ap), the only one of the eight §4ao curves
  that closes by hand.

v_task38 §1.5/§1.8 lists `L₃ (q = p^f, f ≥ 2)` as *"open for `n > 2·10⁷`"*
without making this import.  Corrected statement:

> **The `L₃` row of R1 survives only with `ℓ* ≥ 2`.**

(Independent numerical re-confirmation: `v_task41_qside.c` scans
`f₁(q²+q+1) = C(n,3)` over *all* non-prime prime powers `q ≤ 10¹²` —
0 hits.)

## 1.3  The `L₅` row: `ℓ*` is genuinely free

Gap window `q² ≥ n−3` (`R^p = q²+1 > n−3`), `ι₁ = q⁴+q³+q²+q+1`, so
`ℓ* = C(n,3)/(f₁ι₁)` can be as large as `≈ q²/(6f₁)`.  Neither the
p-part filter nor the order filter bounds it:

* **p-part.**  `10fℓ* ≤ v_p(n!) < n/(p−1)` combined with
  `ℓ* ≈ n³/(6f₁q⁴)` gives only `n ≤ q²·√(0.6f₁/(f(p−1))) ≤ 1.1q²`,
  which the gap already implies.
* **order (TO-2).**  `ℓ*·log|S| ≤ log(n!/2)` gives
  `n² ≤ f₁q⁴ ln n /(4 ln q)`; writing `q² = x(n−3)`, the condition is
  `x² ≳ 2/f₁`, so it bites only on the band `x < √(2/f₁)`, i.e. it kills
  nothing outside a narrow strip immediately above the gap threshold.
  (This is the honest form of the "factor 1.8" asymptotic squeeze of
  v_task37 §5 — P5(ii) — transported to R1, where it does *not* close.)

So the `L₅` row keeps `ℓ*` free and remains n-side scan territory
(v_task38: empty for `n ≤ 2·10⁷`, complete in `q`).

## 1.4  The q-side scan at `ℓ* = 1` [COMPUTED]

`v_task41_qside.c`: for each prime power `q` it forms the exact
`D = 6·f₁·ι₁(q)`, solves `n(n−1)(n−2) = D` exactly (`long double` cube
root as a seed, `unsigned __int128` verification over a ±3 window), and
applies the window and p-part filters to any hit.  Complete over **all
`n`** for each `q` — the dual of v_task38's n-side scan and a fully
independent code path.  Positive control: `solve_cubic(2184) = 14`
(the `G₂/Sp₆`, `q = 3`, `n = 14` coincidence of §4ao) and a `10¹²`-scale
control both pass.

```
$ gcc -O2 -o /tmp/qside v_task41_qside.c -lm
$ /tmp/qside 1000000000000 100000000 1000000000000
# selftest solve_cubic: 2184 -> 14 (expect 14); 1e12-scale -> 1000000000001 (ok)
# S4 (odd non-prime q) q <= 1e12 ; L5 q <= 1e8 ; L3 (non-prime q) q <= 1e12
# raw shape hits: 0
# SURVIVORS (window + p-part): 0
```

Ranges in `n` covered at `ℓ* = 1`:

| row | `q` range | implied `n` range | previous (v_task38) |
|---|---|---|---|
| `S₄(q)` odd non-prime | `≤ 10¹²` | `n ≤ 2·10¹²` (window `n ≤ 2q`) | `n ≤ 2·10⁷` |
| `L₃(q)` non-prime | `≤ 10¹²` | `n ≤ 10¹² + 3` (window `n ≤ q/f₁+3`) | `n ≤ 2·10⁷` — and now **proven** for all `n`, §1.2 |
| `L₅(q)` | `≤ 10⁸` | `n ≤ q² + 3 = 10¹⁶`, but the equation itself caps `n ≈ 1.8q^{4/3} ≈ 8·10¹⁰` | `n ≤ 2·10⁷` |

(For `ℓ* ≥ 2` the q-side scan is not competitive — cost `Σ_q q` — so
`L₃`/`L₅` at `ℓ* ≥ 2` remain at v_task38's `n ≤ 2·10⁷`.)

---

# PART 2 — the psn census over a product socle (task item 1)

## 2.1  What is provable

**Lemma PSN-×  [PROVEN].**  *For a direct product `G = G₁ × … × G_k` and
subgroups `U_i ≤ G_i`, `N_G(∏U_i) = ∏ N_{G_i}(U_i)`.  Hence
`mult₁(∏G_i) ≥ ∏ mult₁(G_i)`, with equality iff `G` has no **proper
subdirect** psn subgroup.*

*Proof.*  Normalisation in a direct product is componentwise. ∎

This is the exact analogue of step (5) of Theorem PSN-GF (§4af); the
"distinctness" phenomenon there is here the subdirect/diagonal correction.

**Definition.**  Call a simple group `S` **census-trivial** if
`mult₁(S) = 1`, i.e. `S` has no *proper* nontrivial perfect
self-normalising subgroup; call it **strongly census-trivial** if it has
no proper nontrivial perfect subgroup at all.

**Lemma CT [PROVEN].**  *`L₂(2^f)` is strongly census-trivial for every
odd prime `f`; so is `L₂(p)` for every prime `p ≥ 7` with
`p ≡ ±3 (mod 10)`.*

*Proof.*  Dickson's subgroup classification of `L₂(q)`: every subgroup is
elementary-abelian-by-cyclic (Frobenius), cyclic, dihedral, `A₄`, `S₄`,
`A₅`, or `PSL₂(q₀)`/`PGL₂(q₀)` for a subfield `F_{q₀} ⊆ F_q`.  Of these
only `A₅` and the subfield groups are perfect and nontrivial.
(i) `q = 2^f`, `f` an odd prime: the only proper subfield is `F₂`, and
`L₂(2)` is not perfect; and `A₅ ≤ L₂(2^f)` requires `5 ∣ 4^f − 1`,
i.e. `2 ∣ f` — false.  (ii) `q = p` prime: no proper subfield, and
`A₅ ≤ L₂(p)` requires `p ≡ ±1 (mod 10)` or `p = 5`. ∎

**Lemma CT-× [PROVEN].**  *If `S₁,…,S_k` are pairwise non-isomorphic and
each strongly census-trivial, then `G = ∏S_i` has exactly one psn
subgroup, namely `G`; so `mult₁(G) = 1`.*

*Proof.*  Let `U ≤ G` be psn, `U_i = π_i(U)`.  `U` is perfect, so each
`U_i` is perfect, hence `U_i ∈ {1, S_i}`.  Also
`C_G(U) = ∏ C_{S_i}(U_i) ≤ N_G(U) = U`; if `U_i = 1` then
`C_{S_i}(U_i) = S_i ≤ U`, forcing `U_i = S_i` — contradiction.  So `U` is
subdirect in `G` with all `U_i = S_i`, and by Goursat a subdirect
subgroup of a product of simple groups is a product of diagonals over
blocks of pairwise isomorphic factors; pairwise non-isomorphic gives
`U = G`. ∎

**Checked** (`v_task41_prodcheck_out.txt`, exhaustive GAP):

| group | `mult₁` | psn orders | reading |
|---|---|---|---|
| `L₂(7) × L₂(13)` | **1** | `183456` | Lemma CT-× ✓ |
| `L₂(7) × L₃(3)` | **1** | `943488` | Lemma CT-× ✓ |
| `L₂(7) × L₂(7)` | 3 | `168, 168, 28224` | control A: the *pairwise non-isomorphic* hypothesis is necessary — the two diagonals appear |
| `L₂(7) × L₂(11)` | 3 | `10080 (×2), 110880` | control B: `= mult₁(L₂(7))·mult₁(L₂(11)) = 1·3`, i.e. Lemma PSN-× with **equality**, the psn's being exactly `L₂(7) × A₅` |

(The `L₂(7)×L₂(13)×L₂(17)` row of the same script returned `mult₁ = 0`,
which is impossible — `G` itself is psn — so
`RepresentativesPerfectSubgroups` silently failed at order `4.5·10⁸`.
That row is **discarded**, not used.)

**Lemma A-2 [PROVEN].**  *`mult₁(A_n) ≥ 2` for every `n ≥ 6`* — the point
stabiliser `A_{n−1}` is perfect (`n−1 ≥ 5`), proper, and maximal hence
self-normalising.  (Data: `mult₁(A_6..A_9) = 3, 5, 7, 6`.)

> **Criterion CT [PROVEN, new].**  If `T = Soc T` (i.e. `c = 1`) and
> `Soc T` is a product of pairwise non-isomorphic strongly census-trivial
> simple groups, then `mult₁(T) = 1 < 2 ≤ mult₁(A_n)`, so
> `D(T) ≇ D(A_n)`.

This is a genuine new separation criterion, independent of `κ`.  It is
**not** applicable to R1: it needs *all* socle factors census-trivial,
and R1's `S* ∈ {L₃(q), L₅(q), S₄(q)}` is not (e.g. `mult₁(L₃(4)) = 16`).

## 2.2  Why the census route cannot close R1 — three independent reasons

**(R-i) Census-trivial simple groups exist, in an infinite family, with
unbounded `ι`.**  The task asked whether "all other factors
census-trivial" is vacuous.  It is not:
`ι(L₂(2^f)) = 2^f + 1 → ∞` along odd primes `f`, and every one of those
groups is *strongly* census-trivial (Lemma CT).  Machine-confirmed:

| `q` | 8 | 32 | 128 | 243 | 7 | 13 | 17 | 23 | 25 | 27 | 37 | 43 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `mult₁(L₂(q))` | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |

(`v_task41_census_out.txt`, `v_task41_products_out.txt`; contrast
`mult₁(L₂(q)) = 3` at `q = 9,11,19,29,31,41,49,81,121,169`, where the two
`A₅`-classes are psn.)  So a socle whose non-`O*` factors contribute
nothing to the census is entirely realisable, and in R1 those factors are
*required* to have large `ι` — which `L₂(2^f)` supplies.  **No
contradiction is available from "the other factors must be
census-trivial".**

**(R-ii) A ≥2-orbit socle can match `mult₁(A_n)` exactly — the program's
own data says so.**  §4w: `mult₁(A₁₀) = 4`, and the twin with socle
`A₆ × A₇` has `mult₁ = 4` as well.  That coincidence is precisely why
`κ` was introduced (§4aj).  So "a product census cannot match a simple
census" is **false**, and no refinement of it is going to become true for
`k ≥ 3`: the same data shows the outer glue *reduces* the census
(`mult₁(A₆)·mult₁(A₇) = 3·5 = 15`, while the seven `A₁₀`-twins realise
`10,4,10,7,11,3,11`).  Lemma PSN-× gives a lower bound only when
`T = Soc T`; with `c > 1` there is no lower bound at all, and `3` is
attained.

**(R-iii) `mult₁(A_n)` is unknown.**  Even granting a census formula for
`T`, the comparison needs `mult₁(A_n)` for the *specific* `n` solving the
curve, and the known values stop at `n = 12` (`6, 4, 7, 12` for
`n = 9..12`).  See PART 4 for exactly what a formula would require.

## 2.3  `mult₁` across a ≥3-orbit socle (task item 2)

`mult₁` has one coincidence in the program (`A₁₀`, §4w) and that
coincidence is itself a multi-orbit socle.  Adding orbits does not push
`mult₁` up: by (R-ii) it can push it *down*.  The only proven direction is
Lemma PSN-× (lower bound, `c = 1` only).  Concretely, in R1 the census of
`T` would be

  `mult₁(T) = |{U ≤ Q psn in T}| + |{U ⊄ Q psn in T}|`,

and the first term is bounded below by `∏_O (∏_{ℓ_O} mult₁(S_O))` only
when `T = Q`; here `c ≥ |Out|`-sized glue is present precisely because the
order equation `∏|S_O|^{ℓ_O}·c = n!/2` almost never balances with `c = 1`.
**No usable inequality exists in the direction needed.**

---

# PART 3 — the order equation with ≥3 factors (task item 3)

## 3.1  The gap conditions turned into lower bounds

Since `O*` is ι-minimal, every other orbit `O` satisfies
`ℓ_O·f_O·ι₁(S_O) ≥ C(n,3)` with `f_O ≤ 2`, hence

  `ι₁(S_O) ≥ C(n,3)/(2ℓ_O)`,  and since `ι₁` is an index,
  `|S_O| > ι₁(S_O) ≥ C(n,3)/(2ℓ_O)`.

(TR-4 `ν ≥ μ` and Kleidman–Liebeck sharpen `ι₁ = μ` for most families but
change nothing below, because the binding inequality is `|S| > ι₁`, which
is trivial.)

## 3.2  Lemma ORB [PROVEN] — the order equation does **not** limit the
## number of orbits

*Each orbit `O` contributes at least
`ℓ_O·log|S_O| ≥ min_{ℓ≥1} ℓ·log max(60, C(n,3)/(2ℓ)) = log(C(n,3)/2)`
to `log|Q| ≤ log(n!/2)`.*

*Proof.*  `h(ℓ) = ℓ·log max(60, C/(2ℓ))` is `≥ log(C/2)` at `ℓ = 1` and
increasing thereafter (for `ℓ ≤ C/120` the derivative is
`log(C/2ℓ) − 1 > 0` as soon as `C/(2ℓ) > e`; beyond that `h(ℓ) =
ℓ log 60` is increasing). ∎

**Consequence.**  The number of socle orbits is bounded only by

  `k ≤ log(n!/2)/log(C(n,3)/2) ≈ (n ln n)/(3 ln n) = n/3`.

An orbit costs `≈ 3 log n` out of a budget of `≈ n log n`.  **So "≥ 3
orbits" is arithmetically free** — the hypothesis carries no order
content whatever, and the third orbit in R1 cannot be contradicted by
counting.  This is the precise reason task item (3) does not close: the
`ι`-lower bounds it produces (`|S_O| ≳ n³/6`) are polynomial, against a
factorial budget.

## 3.3  The unused `C(n,4)` bullet

v_task38 §1.1 explicitly used only the first two R1 bullets.  The third,
`ℓ**·f·ι₁(S**) = C(n,4)` with `b₂ > 4b₁`, is a *second* §4ao-type
equation, but with `ℓ**` free and only the weak gap `R^p > 4`; it is
satisfied by a wide range of `(S**, ℓ**, n)` (e.g. any `L₂(q)` with
`ℓ**(q+1) = C(n,4)`, of which there are many for each `n`).  Adding it to
the scan therefore removes no `n` that the first bullet does not already
remove — verified indirectly: the first bullet alone already has **zero**
solutions in every scanned range, so the conjunction is vacuously empty
too.  It is recorded as *available but non-binding*.

---

# PART 4 — the obstruction, named precisely

The census route needs, and does not have, the following two objects.
Neither is number theory; both are group theory of the size of a paper.

> **Obstruction PSN-A (the alternating analogue of Theorem PSN-GF).**
> A generating function for `mult₁(A_n)`.  The structural half is
> straightforward and is proved here in outline:
>
> Let `U ≤ A_n` be psn, with orbits `Ω₁,…,Ω_r` and fixed-point set `F`.
> 1. `|F| ≤ 2`.  (`|F| ≥ 3` gives a 3-cycle on `F` centralising `U`,
>    which is even and outside `U`.)
> 2. No two orbits are equivalent `U`-sets of **even** size.  (A `U`-set
>    isomorphism `Ω_i → Ω_j` gives a permutation centralising `U`, of sign
>    `(−1)^{|Ω_i|}`; it lies outside `U` since `U` preserves its orbits.)
>    For odd-size equivalent orbits the swap is odd and survives only if
>    `N_{S_n}(U)` contains no other odd element — the exact analogue of
>    the class-splitting corrections E1/E5 of §4ac/§4af.
> 3. Hence `mult₁(A_n) = [x^n]\,(1 + x + x²)·∏_d (1 + x^d)^{t_d}` **up to**
>    (a) the parity correction of 2 and (b) proper subdirect subgroups of
>    `∏ U_i`, where `t_d` is the number of `S_d`-classes of transitive
>    perfect self-normalising subgroups of degree `d`.
>
> **Both corrections are genuine here and are exactly the ones that were
> *absent* in the symplectic case:** step (3) of PSN-GF used the block
> scalars `s_i = (−1_{W_i}, 1) ∈ Sp` to kill subdirect products, and `A_n`
> has no such element.  Computing the `t_d` is the classification of
> transitive perfect self-normalising permutation groups of degree `d` for
> all `d ≤ n` — strictly harder than the transitive-group databases, which
> stop at `d = 47`.
>
> **Obstruction PSN-LIE-q.**  Uniform-in-`q` psn counts for `L₃(q)`,
> `L₅(q)`, `S₄(q)` (the R1 survivors) — the exact analogue of the
> `p_d(q)` project of §4af/§4ah, which for `Sp₆`/`Ω₇` alone consumed
> §4z–§4ai and is still open in dimensions 4, 6, 7.

Until *both* exist, "match the census" is not a decidable condition, and
the R1 branch cannot be closed by it.  I stop here rather than invent a
substitute.

---

# PART 5 — verdict per surviving row

| row | status after this note |
|---|---|
| **`L₃(p^f)`, `f ≥ 2`, `ℓ* = 1`** | **CLOSED for all `n`** [PROVEN] — §4ao squeeze (`f₁=1`) + Theorem L3₂ (`f₁=2`); the import v_task38 missed.  Re-confirmed numerically, `q ≤ 10¹²`. |
| **`L₃(p^f)`, `f ≥ 2`, `ℓ* ≥ 2`** | **OPEN**; empty for `n ≤ 2·10⁷` (v_task38, complete in `q`).  Not touched by p-part, order, census or `mult₁`. |
| **`S₄(q)`, `q` odd non-prime** | `ℓ* = 1` **PROVEN** (Lemma R1-S₄-ℓ1) ⟹ the row *is* §4ao's curve `C₆` at odd non-prime `q`.  **OPEN**; empty for `n ≤ 2·10¹²` (this note, up from `2·10⁷`). |
| **`L₅(q)`, any `ℓ*`** | **OPEN**; `ℓ*` provably free; empty for `n ≤ 2·10⁷` (all `ℓ*`, v_task38) and for `n ≲ 8·10¹⁰` at `ℓ* = 1` (this note). |
| sporadic row (I8) | untouched here. |

**Proven vs computed vs open.**

* *Proven here*: Lemma R1-S₄-ℓ1; Lemma PSN-× ; Lemma CT; Lemma CT-× ;
  Lemma A-2; Criterion CT; Lemma ORB; the `L₃` `ℓ*=1` import.
* *Computed here*: `mult₁` of 44 groups (GAP, exhaustive; one further row
  discarded as unreliable); the q-side
  scan (`S₄` to `n ≤ 2·10¹²`, `L₃` to `q ≤ 10¹²`, `L₅` to `q ≤ 10⁸`).
* *Still open*: the three equations above (two after the `L₃` `ℓ*=1`
  import), and with them §4ao's `C₆` and the `L₅` curves.  The ≥3-orbit
  hypothesis has been shown to carry **no** additional arithmetic content
  (Lemma ORB) and **no** census content (PART 2), so the honest status of
  the R1 branch is unchanged in kind: *it is the curves, and only the
  curves.*

## Honest one-line status of R1

> R1 is **not** killed group-theoretically.  It shrinks: the `S₄` row is a
> single curve (`ℓ*=1` forced) verified to `n ≤ 2·10¹²`, and the `L₃` row
> loses its `ℓ*=1` half outright.  The census/`mult₁` route is **refuted
> as a mechanism** — census-trivial simple groups with unbounded `ι` exist
> (`L₂(2^f)`, `f` an odd prime), and a multi-orbit socle already matches
> `mult₁(A_n)` exactly at `n = 10`.  What is missing is not an idea but
> two large computations, named as Obstructions PSN-A and PSN-LIE-q.

## Reproduce

```
gap -q -b v_task41_census.g          # ~2 min
gap -q -b v_task41_products.g        # L2(q) rows; PSL(2,361) does not finish
gap -q -b v_task41_prodcheck.g       # ~15 min
gcc -O2 -o /tmp/qside v_task41_qside.c -lm
/tmp/qside 1000000000000 100000000 1000000000000     # ~2 min, 50 MB
```
All scan arithmetic is exact (`unsigned __int128`); the cube root is a
seed only and every candidate is verified by exact multiplication.
