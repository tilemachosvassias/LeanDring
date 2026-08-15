# v_task54 — the residual **rank-1** gaps closed:
# **U3-T, Sz-T, Ree-T are unconditional**

Date 2026-08-08.  **NOTES.md not edited.**
Closes `(G2′)`, `(G3)`, `(G3a)`, `(G4)` of `v_task53_rank1_twins.md`.
`(G1)` — Lemma C — was closed in `v_task52_lemmaC.md`.

| file | what it does |
|---|---|
| `v_task54_rank1_gaps.py` | PART 1 the `θ = D/μ` table; PART 2 **Lemma W** (the window lemma) with the exact per-family threshold; PART 3 **(G2′)** the Suzuki 3-coprimality kill; PART 4 **(G4)** **Lemma EQ** and its finite window; PART 5 (G4) the rank-1 socle branch with exact thresholds + exhaustive check; PART 6 (G3) the residual bookkeeping |
| `v_task54_rank1_gaps_out.txt` | its output — **0 hits everywhere** |
| `v_task54_rank1_gaps.g` / `_g_out.txt` | GAP: **(G3a)** the Ree `ι` witness at `q = 27`, machine-verified; the `3 ∤ |Sz(q)|` check; the `N − μ` table cross-checked |

All arithmetic exact (Python big integers / `Fraction`, GAP rationals).

---

> ### Headline
>
> **Theorem U3-T [PROVEN, all prime powers `q ≥ 3`, unconditional].**
> **Theorem Sz-T [PROVEN, all `q = 2^{2m+1} ≥ 8`, unconditional — and with
> no census, no window, no scan at all].**
> **Theorem Ree-T [PROVEN, all `q = 3^{2m+1} ≥ 27`, unconditional].**
>
> There is no Fitting-free **non-simple** finite group `T` with `|T| = |S|`
> and `D(T) ≅ D(S)`, for `S = U₃(q)`, `Sz(q)`, `R(q)`.  With `v_task53` §2
> (order-uniqueness among simple groups, CFSG order theorem):
> **`U₃(q)`, `Sz(q)`, `R(q)` are `D`-rigid among all finite groups.**
> No dependence on **(AB)**, none on the `Bₙ/Cₙ` residue, none on Lemma B.
>
> Three new uniform tools, all target-agnostic and reusable:
>
> * **Lemma W** (window): `ι(S)^{D₁} < (4d₁f₁g₁)^{D₁}(6d₁|S|)^{μ₁}` is
>   necessary — a socle family dies uniformly as soon as `θ₁ := D₁/μ₁ > a/b`.
> * **Lemma EQ** (equal characteristic): `q₁^{N₁−μ₁} < 4 d₁ f₁ g₁`.  Since
>   `N₁ = μ₁` **exactly** for the rank-1 families and `N₁ > μ₁` for every
>   rank `≥ 2`, this is a 71-element finite window, independent of the target.
> * **the 3-coprimality kill** for `Sz`, which turns `Sz` from the *weakest*
>   of the three rows (`v_task53` (G2)) into the *strongest*.

---

## 1. Standing setup

`T` Fitting-free, `|T| = |S|`, `D(T) ≅ D(S)`.  Steps 2–3 of `v_task53` §4 —
which rested on Lemma C, **now `[PROVEN]` (`v_task52`)** — give
`Soc T = S₁` **simple** (`T` almost simple) and

```
(E)   c·|S₁| = |S| ,   c ≥ 2 ,   c | |Out(S₁)| ;
(F)   |Out(S₁)|·ι(S₁) ≥ ι(S)                    [orbit floor, ℓ = 1].
```

For the three targets (`v_task53` §1, `ι` **proven over all subgroups**):

| `S` | `|S|` | `|S|_p = q^N` | `ι(S) = q^N+1` | `a` | `b = N` | `a/b` |
|---|---|---|---|---|---|---|
| `U₃(q)` | `q³(q²−1)(q³+1)/e` | `q³` | `q³+1` | 8 | 3 | `8/3` |
| `Sz(q)` | `q²(q−1)(q²+1)` | `q²` | `q²+1` | 5 | 2 | `5/2` |
| `R(q)` | `q³(q−1)(q³+1)` | `q³` | `q³+1` | 7 | 3 | `7/3` |

Note the structural fact used throughout: **for a rank-1 group the minimal
parabolic is the Borel**, so `ι(S) = |S|_p + 1` exactly, i.e. `b = N`.

Machine inputs from `v_task52`, both `[PROVEN]`:
`(T1) |G| ≥ q₁^{D}/(12d)`, `(T2) ῑ ≤ 4q₁^{μ}`, `(T3) |Out| = d·f·g, g ≤ 6`.

---

## 2. Lemma W and the `θ = D/μ` table  — the answer to (G2′)'s question

> **Lemma W [PROVEN].**  If `S₁` is of Lie type over `F_{q₁}` with
> parameters `(D₁, μ₁, d₁, f₁, g₁)` and satisfies (E)+(F), then
> ```
>       ι(S)^{D₁}  <  (4 d₁ f₁ g₁)^{D₁} · (6 d₁ |S|)^{μ₁} .
> ```

*Proof.*  (F) with (T2)/(T3): `4d₁f₁g₁·q₁^{μ₁} ≥ |Out(S₁)|ι(S₁) ≥ ι(S)`.
(E) with (T1) and `c ≥ 2`: `q₁^{D₁} ≤ 12d₁|S₁| = 12d₁|S|/c ≤ 6d₁|S|`.
Raise the first to the power `D₁`, the second to the power `μ₁`, and
eliminate `q₁^{μ₁D₁}`. ∎

Writing `|S| ≍ q^a`, `ι(S) ≍ q^b`, Lemma W reads `q^{bD₁ − aμ₁} <
(\text{polylog})`, so **every family with `θ₁ := D₁/μ₁ > a/b` dies for all
but finitely many `q`**, and the threshold is explicit.  `f₁` is bounded by
the same inequality (`f₁ ≤ log₂(6d₁|S|)/D₁`), and so is the rank
(`2^{D₁} ≤ 6d₁|S|`), so the whole test is a finite exact computation.

### 2.1 The `θ` table (PART 1, exact `Fraction` arithmetic)

| family | `D` | `μ` | `θ = D/μ` | | family | `θ` |
|---|---|---|---|---|---|---|
| `²G₂ = R` | 7 | 3 | **7/3 ≈ 2.333** | | `A₁ = L₂` | 3 |
| `²B₂ = Sz` | 5 | 2 | **5/2 = 2.500** | | `³D₄` | 28/9 ≈ 3.111 |
| `²F₄` | 26 | 10 | **13/5 = 2.600** | | `Sp₄ = C₂` | 10/3 ≈ 3.333 |
| `²A₂ = U₃` | 8 | 3 | **8/3 ≈ 2.667** | | `U₅` | 24/7 ≈ 3.429 |
| `G₂` | 14 | 5 | 14/5 = 2.800 | | `F₄` | 52/15 ≈ 3.467 |
| `U₄` | 15 | 5 | 3 | | `L₃` | 4 |
| | | | | | `E₆, ²E₆` | 39/8 |
| | | | | | `E₇` | 133/25 |
| | | | | | `E₈` | 248/51 |

`θ → ∞` with the rank in every classical family
(`Lₙ: θ = n+1`; `Uₙ: (n²−1)/(2n−3)`; `Bₙ/Cₙ: (2n²+n)/(2n−1)`;
`Dₙ: (2n²−n)/(2n−2)`), so **`{θ ≤ Θ}` is finite for every `Θ`**, and the
minimum is `7/3`, attained by the **Ree** family — exactly the extremal row
of Lemma C (`v_task52` §2).

### 2.2 The surviving families, per target  [the requested answer]

| target | `a/b` | families with `θ ≤ a/b` (**not** killed by Lemma W) |
|---|---|---|
| `U₃(q)` | `8/3` | `R (7/3)`, `Sz (5/2)`, `²F₄ (13/5)`, **`U₃ (8/3)` boundary** |
| `Sz(q)` | `5/2` | `R (7/3)`, **`Sz (5/2)` boundary** |
| `R(q)`  | `7/3` | **`R (7/3)` boundary only** |

**This is the exact diagnosis (G2′) asked for.**  The task brief's guess
"`D/μ ≤ 5/2` families die" was the right shape but the wrong direction of
inequality: the correct criterion is `θ > a/b` **kills**, and for `Sz` the
only non-killed families are `²G₂` and `²B₂` itself — the boundary case is
indeed the target's own family, as predicted.

### 2.3 The thresholds, exactly (PART 2)

Computed by doubling + bisection on the exact integer inequality, with the
conservative surrogates `|S| ≤ q^3(q²−1)(q³+1)` etc. (`e = 1`) and
`f₁` at its cap.  Sample rows:

```
target U3 (a/b = 8/3):   G2 excluded for q > 1.449e19 ;  A1 for q > 3.91e9 ;
                         U4 q > 3.86e9 ; 3D4 q > 32100 ; C2 q > 19147 ;
                         U5 q > 8962 ; L3 q > 444 ; ... (33 more rows, q > 8)
                         SURVIVING ALL q : 2A(3), 2B2, 2G2, 2F4
target Sz (a/b = 5/2):   U3  excluded for q > 1.078e30 ; 2F4 q > 5.17e27 ;
                         G2 q > 3.5e10 ; U4, A1 q > 7.7e8 ; ...
                         SURVIVING ALL q : 2B2, 2G2
target Ree (a/b = 7/3):  Sz  excluded for q > 7.626e12 ; U3 q > 1.29e8 ;
                         2F4 q > 19683 ; A1, U4, G2 q > 2187 ; ...
                         SURVIVING ALL q : 2G2
```

**Honest reading.**  Lemma W is a *uniform* kill but its constants are bad:
for `U₃` the `G₂` threshold `1.4·10¹⁹` is far outside any census.  So Lemma W
is **not** the load-bearing argument for `U₃` and `R` — the `ppmax³` kill of
`v_task53` §5.2 (thresholds `179` and `2187`) is much sharper there, and it
is what we use.  Lemma W's value is (i) the *diagnosis* of §2.2, (ii) an
independent, characteristic-free confirmation, and (iii) the rank bound
`2^{D₁} ≤ 6d₁|S|`, which is what makes the rank `≤ 6` restriction of
`v_task53`'s `--sub` scan (debt (G3)) unnecessary.

---

## 3. (G2′) — the Suzuki cross-characteristic branch: **closed, uniformly**

The right tool for `Sz` is not the `2`-part at all (as the brief already
suspected) and not `D/μ` either.  It is the **`3`-part**.

> **Lemma Sz-3 [PROVEN, one line].**  `3 ∤ |Sz(q)|` for every
> `q = 2^{2m+1}`.
>
> *Proof.*  `f` odd ⟹ `q = 2^f ≡ 2 (mod 3)`; hence `q − 1 ≡ 1 (mod 3)` and
> `q² + 1 ≡ 2 (mod 3)`; and `q²` is a `2`-power.  So no factor of
> `|Sz(q)| = q²(q−1)(q²+1)` is divisible by `3`. ∎
> (PART 3: checked for all 200 targets `f ≤ 401`; GAP PART S at
> `q = 8, 32, 128, 512`.)

> **Theorem Sz-cross [PROVEN, all `q`].**  In (E), `S₁ ≅ Sz(q₁)` for some
> `q₁ = 2^{2m₁+1}`.
>
> *Proof.*  `|S₁|` divides `|S| = |Sz(q)|`, so `3 ∤ |S₁|`.  By the classical
> corollary of CFSG **[LIT: the simple groups of order coprime to 3 are
> exactly the Suzuki groups; Thompson's `N`-group analysis, Glauberman]**,
> `S₁ ≅ Sz(q₁)`. ∎

So for `Sz` there is **no** cross-characteristic branch, **no** alternating
branch (`3 | |A_m|` for all `m ≥ 5`), **no** sporadic branch (`3` divides
every sporadic order) and **no** equal-characteristic branch other than the
subfield one.  The census and the `--sub` scan become entirely redundant.

> **Lemma Sz-subfield [PROVEN, all `q`].**  `(E)` has no solution with
> `S₁ = Sz(q₁)`, `q₁ < q`.
>
> *Proof.*  `4f₁ ≥ 12`, so by **Zsygmondy** `2^{4f₁} − 1` has a primitive
> prime divisor `r`; `r | q₁²+1` (the only block of `|Sz(q₁)|` of order
> `4f₁`), hence `r | |Sz(q)|`.  Every odd prime divisor of `|Sz(q)|` divides
> `(q−1)(q²+1) | 2^{4f} − 1`, so `ord_r(2) = 4f₁` divides `4f`, i.e.
> **`f₁ | f`**.  With `f₁ < f` and `f, f₁` both odd, `f/f₁` is odd `≥ 3`, so
> `f ≥ 3f₁` and `q/q₁ ≥ q₁²`.  Then
> ```
>   c = |Sz(q)|/|Sz(q₁)| > (q/q₁)^5 · (1−1/q) / (1+q₁^{−2}) ≥ 0.85·q₁^{10} ≥ 9·10^8 ,
> ```
> while `c ≤ |Out(Sz(q₁))| = f₁ ≤ log₂ q₁`.  Contradiction. ∎
> (PART 3 checks every pair `f₁ | f`, `f ≤ 201`, exactly: **0 hits**;
> smallest ratio `c/|Out|` observed is `1 205 899 264/3` at `(f,f₁)=(9,3)`.)

`q₁ = q` gives `c = 1`, excluded by `c ≥ 2`.  Hence:

> **Theorem Sz-T [PROVEN, all `q`, unconditional].**  ∎
>
> **`Sz` needs no census, no window, no scan.**  It is now the *cleanest*
> row in the whole programme, having been the *dirtiest* in `v_task53`.

---

## 4. (G4) — the equal-characteristic branch, written out properly

> **Lemma EQ [PROVEN; uniform; the same statement for all three targets].**
> Let `S₁` be of Lie type over `F_{q₁}`, `q₁ = p^{f₁}`, in the **defining**
> characteristic `p` of the rank-1 target `S`, satisfying (E)+(F).  Then
> ```
>              q₁^{N₁ − μ₁}  <  4 d₁ f₁ g₁ .
> ```
>
> *Proof.*  (E) gives `|S₁|_p | |S|_p`, i.e. `q₁^{N₁} ≤ q^{N}`.
> (F) with (T2)/(T3) gives `4d₁f₁g₁·q₁^{μ₁} ≥ ι(S) = q^{N}+1 > q^{N} ≥
> q₁^{N₁}`.  Divide. ∎

The point is the **target-free** shape: only the fact that the target is
rank 1 (so `ι(S) = |S|_p + 1`) enters.

> **Lemma P [PROVEN, classical].**  For simple `G` of Lie type,
> `N − μ = 0` **iff** `G` has rank 1 (`A₁, ²A₂, ²B₂, ²G₂`), where the minimal
> parabolic is the Borel and `[G:B] = q₁^{N}+1`; `N − μ ≥ 1` for every rank
> `≥ 2`.
> ```
> L₃ 1   L₄ 3   U₄ 1   U₅ 3   S₄ 1   S₆ 4   G₂ 1
> ³D₄ 3  ²F₄ 2  F₄ 9   E₆ 20  E₇ 38  E₈ 69   Dₙ (n−1)(n−2)  Bₙ/Cₙ (n−1)²
> ```
> (GAP `_g_out.txt` PART E; the `|G|_p = q^{N}` half spot-checked directly
> at `U₃(4,5,7,8,9)`, `Sz(8,32)`, `R(27)`, `L₃(4,8,9)`.)

### 4.1 Rank `≥ 2` socle — a 71-element window, 0 hits (PART 4)

`f₁ ≤ log₂ q₁` and `d₁ ≤ max(n₁,4)`, `g₁ ≤ 6`, so Lemma EQ forces
`q₁ < 24·d_max·log₂ q₁` already at `N₁−μ₁ = 1`, and the window is empty for
every `N₁−μ₁ ≥ 7`.  The **complete** window (all characteristics at once):

| family | `N₁−μ₁` | admissible `q₁` |
|---|---|---|
| `L₃` | 1 | `2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,32,64,81,128` |
| `L₄` | 3 | `2, 3` |
| `U₄` | 1 | `2,…,49,64,81,128` (22 values) |
| `U₅` | 3 | `2, 3, 4` |
| `S₄` | 1 | `2,3,4,5,7,8,9,11,13,16,25,27,32,64` |
| `D₄ = O₈⁺` | 6 | `2` |
| `G₂` | 1 | `2,3,4,5,7,8,9,16,32` |
| `³D₄` | 3 | `2` |

**71 triples.**  Imposing (E) — `c·|S₁| = |S|` with `2 ≤ c | |Out(S₁)|`,
and solving for the target `q` by exact integer `k`-th roots (`solve_U3`,
`solve_Sz`, `solve_Ree` of `v_task53`, positive-controlled at
`U₃(9)`, `Sz(32)`, `R(243)`): **190 `(S₁,c)` pairs, 0 hits.**

So **no socle of rank `≥ 2` in the defining characteristic**, for any of the
three targets, for **every** `q`.

### 4.2 Rank-1 socle — the exponent comparison (PART 5)

Here `N₁ = μ₁` and Lemma EQ is vacuous.  Put `X := q₁^{N₁} = |S₁|_p`,
`Y := q^{N} = |S|_p`, `w := |Out(S₁)|`, `θ₁ := D₁/N₁ ∈ {3, 8/3, 5/2, 7/3}`
for `L₂, U₃, Sz, R`.  Then

```
(α)  X | Y  (so X ≤ Y)          (β)  w(X+1) ≥ Y+1  (so X ≥ Y/w − 1)
```

— `X` is pinned to `Y` within the factor `w = O(log Y)`.  For all four
rank-1 families `∏(1−q₁^{−d_i}) ≥ 1/2`, so
`X^{θ₁}/(2d₁) ≤ |S₁| ≤ X^{θ₁}/d₁`.  Hence, with `a/N` the target's exponent:

* **`θ₁ < a/N`:**  `c = |S|/|S₁| > d₁|S|/Y^{θ₁} → ∞`, against `c ≤ w`.
* **`θ₁ > a/N`:**  `c ≤ 2d₁|S|/X^{θ₁} ≤ 2d₁|S|/(Y/w−1)^{θ₁} → 0`, against
  `c ≥ 2`.
* **`θ₁ = a/N`:**  `S₁` lies in the target's **own** family — the subfield
  case, §4.3.

Both inequalities are integer inequalities after raising to the power `N₁`.
Exact thresholds `q₀` (kill valid for all `q ≥ q₀`), PART 5:

| target `S` | `S₁` family | `θ₁` | `a/N` | kill for all `q ≥` |
|---|---|---|---|---|
| `U₃` | `L₂` | 3 | 8/3 | **4 812 208** |
| `U₃` | `Sz` | 5/2 | 8/3 | 122 |
| `U₃` | `R` | 7/3 | 8/3 | 3 (i.e. always) |
| `U₃` | `U₃` | 8/3 | 8/3 | subfield, §4.3 |
| `Sz` | `L₂` | 3 | 5/2 | 1 102 736 (`= 2^{20.07}`, i.e. `f ≥ 21`) |
| `Sz` | `U₃` | 8/3 | 5/2 | `1.08·10²¹` (`f ≥ 70`) |
| `Sz` | `R` | 7/3 | 5/2 | 128 |
| `Sz` | `Sz` | 5/2 | 5/2 | subfield, §4.3 |
| `R` | `L₂` | 3 | 7/3 | 593 |
| `R` | `U₃` | 8/3 | 7/3 | 1 197 041 (`f ≥ 13`) |
| `R` | `Sz` | 5/2 | 7/3 | `1.16·10⁸` (`f ≥ 17`) |
| `R` | `R` | 7/3 | 7/3 | subfield, §4.3 |

Below every threshold the branch is checked **exhaustively and exactly**:
for each target `q`, (α)+(β) admit only `O(log_p w)` values of `f₁`, so the
check is cheap.  Ranges: `U₃`, all prime powers `q ≤ 5·10⁶` (> 4 812 208);
`Sz` and `R`, `f` odd `≤ 199` (`q ≤ 2^{199}`, `3^{199}`, astronomically past
every threshold).  **0 hits**: `U₃` 348 939 targets / 698 084 socle
candidates surviving the floor; `Sz` 99 / 1 211; `R` 99 / 895.

*(For `Sz` this section is redundant — §3 already excludes every `S₁` other
than `Sz(q₁)` — but it is run anyway, as an independent cross-check.)*

### 4.3 The subfield case, `S₁` in the target's own family

> **Lemma SUB [PROVEN, all three families, all `q`].**  (E) has no solution
> with `S₁` in the target's family over a proper subfield.
>
> *Proof.*  `q₁ = q` gives `c = 1`.  For `q₁ < q`, Zsygmondy applied to the
> largest cyclotomic block gives `f₁ | f`:
> `q₁²−q₁+1` carries a primitive prime of `q₁^6−1` (`U₃`, `R`;
> the exception `(a,n) = (2,6)` is excluded since `U₃(2)` is not simple and
> the Ree characteristic is `3`), and `q₁²+1` carries a primitive prime of
> `2^{4f₁}−1` (`Sz`); in each case every `p′`-prime of `|S|` divides
> `q^{6}−1` resp. `2^{4f}−1`, forcing `f₁ | f`.  Then
> `f ≥ 2f₁` (`U₃`) resp. `f ≥ 3f₁` (`Sz`, `R`: `f/f₁` odd), so
> `q/q₁ ≥ q₁` resp. `q₁²`, and
> ```
> U₃ :  c ≥ 0.285·(q/q₁)^8  ≥ 0.285·q₁^8  ≥ 1870   vs   c ≤ 6f₁ ≤ 6 log₂ q₁ ≤ 9.6   (q₁ ≥ 3)
> Sz :  c ≥ 0.85 ·q₁^{10}   ≥ 9·10^8               vs   c ≤ f₁  ≤ log₂ q₁ = 3        (q₁ ≥ 8)
> R  :  c ≥ 0.9  ·q₁^{14}   ≥ 4·10^{19}            vs   c ≤ f₁  ≤ log₃… ≤ 3          (q₁ ≥ 27)
> ```
> Contradiction in every case. ∎

---

## 5. (G3a) — the Ree `ι` witness, **machine-verified** (GAP)

`v_task53` recorded that `ι(R(q)) = q³+1` had **no** machine check at any
`q`: `ReeGroup(q)` is a `7`-dimensional matrix group, `R(27)` has no stored
`Maxes`, and `Normalizer(G, Z(Syl₃))` was out of reach.  Route that works
(`v_task54_rank1_gaps.g` PART R, runs in minutes):

1. `P := Syl₃(R(27))`, `|P| = 19683 = q³` ✓; `A := Z(P)`, `|A| = 27 = q`,
   **elementary abelian**, `A′ = 1` ✓.
2. The `P`-fixed subspace of the natural `GF(27)^7` module is
   **1-dimensional** ✓; its `G`-orbit under `OnLines` — the **ovoid** — has
   length **19684 = q³+1** ✓.
3. The induced permutation representation is **faithful** (order `10 073 444 472`)
   and **2-transitive** ✓.  So the point stabiliser `B` is **maximal**, of
   index `q³+1 = 19684` ✓.
4. `Syl₃(B)` has order `19683` and is **normal in `B`** ✓, so `B` normalises
   `A = Z(Syl₃(B))` ✓.
5. `A` fixes **exactly one** point of the ovoid ✓, so `N_G(A) ≤ B`.
6. `Normalizer(G_perm, A)` computes in the permutation image and returns
   **exactly `B`** ✓:
   ```
   [G : N_G(A)] = 19684 ,   ind*(A) = 19684 · |A'| = 19684 = q³+1 .
   ```

> **(G3a) CLOSED.**  `ι(R(q)) ≤ q³+1` now has an independent machine
> witness at `q = 27`, of exactly the same shape as the `U₃`/`Sz` rows
> (`A = Z(Syl_p)`, `N_S(A) = B`, Borel–Tits).  The remaining literature
> input for the Ree row is only the **lower** bound
> `m(R(q)) = q³+1` **[LIT: Ward 1966]** — the same status the `U₃` and `Sz`
> rows have always had (Cooperstein / Suzuki).  `MaximalSubgroupClassReps`
> on the degree-19684 group does not terminate and is not attempted.

---

## 6. (G3) — the `--sub` scan is no longer load-bearing

`v_task53` (G3) was: the direct scan of (E) used `q₁ ≤ 10⁵`, rank `≤ 6`.
After §§3–4 nothing depends on it.

| target | residual window after §§3–4 | covered by |
|---|---|---|
| `Sz(q)` | **none** | the uniform proof of §3 |
| `U₃(q)` | `q < 179` (cross-char, `v_task53` §5.2) and `q ∈ {3,4,7}` (Step 3) | census `q ≤ 50 000`, **raw and empty** |
| `R(q)` | `q ∈ {27, 243}` (cross-char) | census `q ≤ 1.3·10²⁹`, **raw and empty** |

* **Rank is bounded by proof, not by fiat.**  In general `2^{D₁} ≤ 6d₁|S|`
  (Lemma W's second inequality); in equal characteristic Lemma EQ empties
  the window for `N₁−μ₁ ≥ 7`; in cross characteristic
  `q₁^{N₁} ≤ ppmax_{p′}(|S|)` (`v_task53` Lemma K) gives
  `N₁ ≤ 1 + 2log₂(q+1)` for `U₃`, so `n₁ ≤ 17` and `|Out(S₁)| ≤ 34f₁`,
  **inside** the `78f₁` cap that `v_task53` §5.2 assumed.  The `rank ≤ 12`
  hypothesis of §5.2 is thereby discharged.
* **Alternating and sporadic socles** were already complete in `q`
  (`v_task53` §5.4, `|Out| ≤ 4` resp. `≤ 2`); for `Sz` they are additionally
  excluded by 3-coprimality.

---

## 7. Status ledger — per gap

| gap (`v_task53` §7) | status now |
|---|---|
| **(G1)** Lemma C unproven | **CLOSED** in `v_task52` — Lemma C `[PROVEN]`, no exceptions |
| **(G2′)** `Sz` cross-characteristic, uniform | **CLOSED**, §3: `3 ∤ |Sz(q)|` + the CFSG corollary force `S₁ = Sz(q₁)`; the subfield count kills it.  *No window at all.* |
| **(G3)** `--sub` socle range bounded | **CLOSED**, §6: rank and `q₁` are bounded by proof; the residual `q`-windows are `q < 179` (`U₃`) and `q ∈ {27,243}` (`R`), both inside the exhausted census |
| **(G3a)** no GAP check of the Ree `ι` | **CLOSED**, §5: witness verified at `q = 27` via the ovoid action, incl. `N_G(A) = B` computed outright |
| **(G4)** equal-characteristic proof only sketched | **CLOSED**, §4: Lemma EQ (uniform, target-free) + the 71-element window (0 hits) + the rank-1 exponent comparison with exact thresholds (0 hits) + Lemma SUB |

### Final theorem statuses

| theorem | status |
|---|---|
| **U3-T** | **[PROVEN, all prime powers `q ≥ 3`, unconditional]** |
| **Sz-T** | **[PROVEN, all `q = 2^{2m+1} ≥ 8`, unconditional; uniform — census-free]** |
| **Ree-T** | **[PROVEN, all `q = 3^{2m+1} ≥ 27`, unconditional]** |

Hence `U₃(q)`, `Sz(q)`, `R(q)` are **`D`-rigid among all finite groups**,
with no dependence on **(AB)**, on Lemma B, or on the `Bₙ/Cₙ` residue.

### Literature actually invoked (beyond `v_task52`/`v_task53`)

| # | input | tag |
|---|---|---|
| L1 | the finite simple groups of order coprime to `3` are exactly the Suzuki groups | **[LIT: CFSG corollary; Thompson, Glauberman]** |
| L2 | Zsygmondy's theorem on primitive prime divisors of `a^n−1` (exception `(2,6)` only, in the range used) | **[LIT: Zsygmondy 1892]** |
| L3 | minimal parabolic = Borel in rank 1, `[G:B] = q^N+1`; `N−μ ≥ 1` in rank `≥ 2` | **[LIT: Kleidman–Liebeck]**, GAP-cross-checked |
| L4 | `m(R(q)) = q³+1` (minimal degree, **lower** bound) | **[LIT: Ward 1966]** — the one remaining literature-only step in the Ree row |

---

## 8. Reusable for the next targets (`L₃(q)`, `U₄(q)`)

* **Lemma EQ is target-agnostic in shape**: for a target with
  `ι(S) ≥ |S|_p / κ`, it becomes `q₁^{N₁−μ₁} < 4κ d₁f₁g₁`.  For rank-1
  targets `κ = 1`; for `L₃(q)` (`ι = q²+q+1`, `|S|_p = q³`) `κ ≈ q`, so the
  window widens by one factor of `q` — still finite, but no longer uniform
  in `q`.  **This is the first place the rank-1 argument will strain.**
* **Lemma W generalises verbatim** and its criterion `θ₁ > a/b` is purely
  numerical: for `L₃(q)` (`a = 8, b = 2`, `a/b = 4`) it kills only the
  families with `θ > 4`, i.e. `Lₙ (n ≥ 4)`, `E₆`–`E₈`, high-rank classicals —
  **a much weaker cut than for the rank-1 targets**, confirming `v_task53`'s
  prediction that `L₃`/`U₄` will need the census to do real work.
* **The 3-coprimality trick does not generalise** — `Sz` is the only simple
  family of order prime to 3.  It is a one-off, and it is the reason `Sz` is
  now the cheapest theorem in the programme.
* **Refuted / do-not-re-attempt** (adding to `v_task53`'s list): *using the
  `2`-part of `|Sz(q)|` against cross-characteristic socles* — the brief's
  first instinct.  `L₂(q₁)` with `q₁ ≡ 3,5 (mod 8)` has `2`-part `4`, so the
  `2`-budget `q²` is no constraint at all.  The `3`-part is the right
  invariant, and it is a *total* obstruction rather than a numerical one.

---

## 9. Reproduce

```
python3 v_task54_rank1_gaps.py            > v_task54_rank1_gaps_out.txt     # ~15 min
~/gap-4.16.0/gap -q -o 8g v_task54_rank1_gaps.g > v_task54_rank1_gaps_g_out.txt  # ~5 min
```

Individual parts: `python3 v_task54_rank1_gaps.py 1` … `6`.
