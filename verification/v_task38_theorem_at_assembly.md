# v_task38 — Theorem AT, assembled: R1 closed as far as it can be, the
# conclusion table rewritten and executed, and the master input list

Date 2026-08-07.  **NOTES.md not edited.**
Scripts / outputs in this directory:

| file | what it does |
|---|---|
| `v_task38_r1_scan.c` / `_out.txt` | exact, **complete-in-`q`** scan of residue **R1**, `10 ≤ n ≤ 2·10⁷` |
| `v_task38_r1_cross.py` / `_out.txt` | independent `q`-side cross-check of the same conditions |
| `v_task38_table_checks.py` / `_out.txt` | the finite checks of the rewritten §4at/§4au conclusion table (branches (a), (b1), (b2), (b3)), prime powers `q ≤ 2·10⁵` |
| `v_task38_sporadic.py` / `_out.txt` | the sporadic row in the **transported** setting (orbit multipliers) |

Headline, stated before the argument so it cannot be mistaken:

> **R1 is NOT closed unconditionally.**  It collapses from eight residual
> families to **three** (`L₃`, `L₅`, `S₄` at odd non-prime `q`) plus a
> sporadic row, all Lie-type survivors verified empty for `10 ≤ n ≤ 2·10⁷`
> by an exact scan complete over *all* `q`.  But — and this is the finding
> that governs the whole assembly — **at `ℓ* = 1` the R1 equation
> `ℓ*·f₁·ι₁(S*) = C(n,3)` *is* §4ao's equation verbatim**, gap condition
> included (the gap is automatically satisfied there).  So the ι₂/ratio
> route does **not** make §4ap's curves irrelevant in the multi-orbit
> branch; it makes them irrelevant only in case (a) and in branches
> (b1)/(b2)/(b3).  §4ar's headline ("the route that makes the curves
> irrelevant") is **true for case (a), false for R1**.

---

## 0.  Notation

`T` Fitting-free, `|T| = n!/2`, `D(T) ≅ D(A_n)`, `n ≥ 10`.
`Q = Soc T = ∏S_i`, orbits `O` with lengths `ℓ_O`, pair invariants
`I(K≤Ā)` (v_task34 §0), `P = ⋃_O ℓ_O·I(K≤Ā)_O`.
`ι₁(S), ι₂(S)` simple-group values; `a₁ = ι(K≤Ā)_{O*} = f₁ι₁(S*)`,
`a₂ = ι₂(K≤Ā)_{O*} = f₂ι₂(S*)`, `R = ι₂/ι₁`, `R^p = a₂/a₁ = (f₂/f₁)R`
(v_task36 Lemma F, §§2–3).  `q = p^f`, `N` = number of positive roots of
`S` (so `|S|_p = q^N`).  `C(n,k)` binomial.

---

# PART 1 — Residue R1

## 1.1  The R1 hypotheses, restated exactly

From v_task37 §6 (Theorem, case (b) final form): `T` has **≥ 3** socle
orbits, and

* `ℓ*·a₁ = C(n,3)`, `ℓ**·b₁ = C(n,4)`, `O* ≠ O**`;
* `a₂ > (n−3)·a₁`  (the ι-minimal orbit's spectral gap);
* `b₂ > 4·b₁`.

Only the **first** and **second** bullets are used below; everything is
therefore a *necessary* condition, and emptiness of the necessary set is a
proof.

## 1.2  The five filters

| # | filter | source | tag |
|---|---|---|---|
| **(1) GAP** | `R^p(F,q,f₁) > n−3` | v_task36 §§3–4 pair table + Lemma ι₂-pair-bound | [PROVEN mod BHR] |
| **(2) DIV** | `ℓ* = C(n,3)/(f₁ι₁(q)) ∈ ℤ_{>0}` | hypothesis | — |
| **(3) SIZE** | `\|S*\| > C(n,4)` | v_task37 Step 1 (needs `(★)`) | [PROVEN under (★)] |
| **(4) p-PART** | `ℓ*·f·N ≤ v_p(n!)` | `|S|_p = q^N`, `|Q| ∣ n!/2`, Legendre | **[PROVEN, new here]** |
| **(5) ORDER** | `ℓ*·log\|S*\| ≤ log(n!/2)` | Lemma TO-2 (v_task37 §5) | [PROVEN] |

Filter (4) is new in this note and is what does most of the work.  It is
elementary: the orbit contributes `|S*|^{ℓ*}` to `|Q|`, which divides
`n!/2`; comparing `p`-adic valuations gives `ℓ*·v_p(|S*|) ≤ v_p(n!)`, and
`v_p(|S|) = fN` for `S` of Lie type over `F_{p^f}`.  Combined with (2) it
reads

> **Lemma R1-p [PROVEN].**  `ι₁(S*) ≥ f·N·(p−1)·C(n,3) / (f₁·n)`,
> because `v_p(n!) < n/(p−1)`.

## 1.3  Five families die outright, for every `n ≥ 10`

The mechanism is uniform.  (1) with the **sharp** per-family `R^p`
(v_task36 §4 — *not* the crude `2(q²+1)` corollary) forces a **lower**
bound on `q`; (2) forces `f₁ι₁(q) ≤ C(n,3)`, an **upper** bound; the two
collide.

| family | `R^p` (v_task36 §4) | `R^p > n−3` forces | `ι₁` then | `ι₁ ≤ C(n,3) ≈ n³/6`? | verdict |
|---|---|---|---|---|---|
| `L₄(q)` | `(q²+q+1)/((q+1)f₁)` | `q ≥ f₁(n−3)` (since `R < (q+1)/f₁`) | `(q+1)(q²+1) > (n−3)³` | `(n−3)³ > n³/6` for `n ≥ 10` | **DEAD** |
| `U₄(q)`, `q≥3` | `(q²+1)/(q+1)` | `q ≥ n−3` | `(q+1)(q³+1) > (n−3)⁴` | no | **DEAD** |
| `Sp₆(q)`, `q=p` | `(q⁴−1)/(q³−1) < q+1` | `q ≥ n−3` | `> (n−3)⁵` | no | **DEAD** |
| `Sp₆(q)`, `q≠p` | `≤ 2t(q) ≤ 2(q−1)` | `q > (n−1)/2` | `> ((n−1)/2)⁵` | no (`n ≥ 10`) | **DEAD** |
| `U₅(q)`, `q=p` | `q⁴/((q+1)(q²+1)) < q` | `q > n−3` | `> (n−3)⁷` | no | **DEAD** |
| `U₅(q)`, `q≠p` | `t(q) ≤ q−1` | `q > n−2` | `> (n−3)⁷` | no | **DEAD** |
| `S₄(q)`, `q=p≥5` | `q²/(2(q+1)) < q/2` | `q > 2(n−3)` | `> 8(n−3)³` | no | **DEAD** |
| `S₄(q)`, `q` even | `t(q) ≤ q−1` | `q > n−2` | `> (n−3)³` | no | **DEAD** |
| `G₂(q)` | — | — | — | — | eliminated outright, Lemma G₂-C (§4au add.) |
| `A_m` | — | — | — | — | excluded, Theorem κ-A (Step 0) |

`L₄` is the tightest: `(q+1)(q²+1)` with `q ≥ n−3` gives
`ι₁ ≥ (n−2)((n−3)²+1) > n(n−1)(n−2)/6` for every `n ≥ 10` (at `n = 10`:
`8·50 = 400 > 120`).  All the other margins are polynomial orders.

## 1.4  `L₃(q)` at **prime** `q` dies by the `p`-part

`R^p = (q+1)/f₁ > n−3` gives `q ≥ f₁(n−3) ≥ n−3`.  If `q` is prime then
`q ≥ n−3 > n/2` for `n ≥ 7`, so `v_q(n!) ≤ 1`.  Filter (4) demands
`ℓ*·1·3 ≤ v_q(n!) ≤ 1` — impossible.  ∎  **[PROVEN, all `n ≥ 10`]**

(The scan confirms the mechanism: every one of the 73 gap-windows it
entered was `L₃`, and the two with `q` prime died at `v_q(n!) = 0`,
`q > n`.)

## 1.5  What actually survives

| family | surviving window | equation to be solved |
|---|---|---|
| `L₃(q)`, `q = p^f`, `f ≥ 2` | `f₁(n−3) ≤ q ≤ √(C(n,3)/f₁)`, and `f(p−1) < n/3` (Lemma R1-p) | `ℓ*·f₁·(q²+q+1) = C(n,3)` |
| `L₅(q)` | `q² ≥ n−3` and `f₁·[5,1]_q ≤ C(n,3)`, and `f(p−1) < n/5` | `ℓ*·f₁·(q⁵−1)/(q−1) = C(n,3)` |
| `S₄(q)`, `q` odd non-prime | `(n−1)/2 < q`, `(q+1)(q²+1) ≤ C(n,3)` — a window of width `≈ 0.05n`, needing an odd proper prime power in it | `ℓ*·(q+1)(q²+1) = C(n,3)`, `ℓ* ∈ {1,2}` |
| sporadic `S` | see §1.7 | `ℓ*·f₁·ι(K≤Ā)(S) = C(n,3)` |

Note the **`ℓ* = 1` observation**: putting `ℓ* = 1` turns each of these
into `f₁·ι₁(S) = C(n,3)`, which is exactly §4ao's equation with `m = f₁`.
For `L₃` §4ao **solved** `m = 1` outright (the discriminant squeeze) and
`m = 2` only numerically (`n ≤ 10⁷`); for `L₅` neither is solved
(`m = 1`: none for `n ≤ 5.36·10⁷`; `m = 2`: none for `n ≤ 6.7·10⁷`).
Moreover in both families the gap is **automatically satisfied** at
`ℓ* = 1` (`L₃`: `ι₁ = C(n,3)` gives `q ≈ 0.41 n^{3/2} ≫ n−3`; `L₅`:
`q ≈ 0.64 n^{3/4}`, so `q² ≫ n`), so the gap contributes nothing there.
**R1 therefore contains §4ao's unsolved equations as a sub-case.**

## 1.6  The exact scan: zero survivors for `10 ≤ n ≤ 2·10⁷`

`v_task38_r1_scan.c` loops over `n`, enumerates the divisors `ℓ` of
`C(n,3)` with `ℓ ≤ n/6 + 3`, and for `D = C(n,3)/ℓ` solves each family's
shape equation for `q` **exactly** (integer `k`-th roots + verification in
`__int128`).  This covers *every* `q`, however large — the scan is
complete in `q` for each `n`, not merely over a `q`-range.

> **Lemma L-bound [PROVEN].**  In every residual family filter (1) forces
> `f₁·ι₁ ≥ (n−3)²`, hence `ℓ* ≤ C(n,3)/(n−3)² ≤ n/6 + 3` for all `n ≥ 5`.
>
> *Proof.*  The per-family lower bounds on `q` are those of §1.3–1.5;
> the weakest is `L₃`/`L₄`/`U₄`/`Sp₆ₚ`/`U₅ₚ` with `q ≥ n−3`
> (`ι₁ ≥ (n−3)²`), `L₅` with `q² ≥ n−3` (`ι₁ > q⁴ ≥ (n−3)²`) and the
> subfield rows with `q > (n−1)/2` (`ι₁ > n³/8 ≥ (n−3)²` for `n ≥ 8`).
> For the numeric step, `n(n−1)(n−2) ≤ (n+18)(n−3)²` ⟺ `15n²−101n+162 ≥ 0`,
> true for `n ≥ 5`. ∎

```
$ gcc -O2 -o /tmp/r1 v_task38_r1_scan.c -lm && /tmp/r1 20000000
# v_task38 R1 scan -- complete over ALL q, for 10 <= n <= 20000000
# shape hits (iota1 realised by some q): 117
# gap windows entered: 73
# SURVIVORS: 0
```

Independent `q`-side cross-check (`v_task38_r1_cross.py`, prime powers
`q ≤ 2000`, no shared code path): **0 survivors**, covering `n ≤ 2002`
for the `(q+1)`-scale families and `n ≤ 3 996 004` for `L₅`.

## 1.7  The sporadic row — and an erratum in §4aj

§4aj Debt (B), observation 1, says *"the largest bound in play is `Fi₂₄′`
at `ι ≤ 4.86·10⁹`, i.e. `n ≲ 3100`; for `n > 3100` no sporadic can be a
large-ι factor."*  **Both halves are wrong now.**

1. `Fi₂₄′` is not the largest: from `v_task24_spor_iota_out.txt`,
   `ι_ub(B) = 1.357·10¹⁰` and **`ι_ub(M) = 9.7239461142009186·10¹⁹`**
   (the class `2A`, `N(⟨x⟩) = C(x) = 2.B`).  With `ℓ = 1` alone that gives
   `n ≲ (6·ι_ub(M))^{1/3} ≈ 8.35·10⁶` — i.e. *inside* the range §4ao
   declares proven.
2. The observation predates the orbit multiplier of Lemma TR-1.  With
   `ℓ` free the correct statement is: a sporadic factor is possible only
   while `⌊log(n!/2)/log|S|⌋ · |Out S| · ι_ub(S) ≥ C(n,3)`.

`v_task38_sporadic.py` recomputes both.  Results:

* **Largest `n` admitting a sporadic socle factor at all:**
  `M₁₁ 13, M₁₂ 33, M₂₂ 57, M₂₃ 67, M₂₄ 115, J₁ 45, J₂ 25, J₃ 287,
  HS 122, McL 241, He 247, Ru 897, Suz 312, Co₁ 1666, Co₂ 218,
  Co₃ 440, Fi₂₂ 64, Fi₂₃ 132, Fi₂₄′ 105 383, HN 1908, Th 37 844,
  ON 2991, Ly 4727, J₄ 72 829, B 105 425, **M 10 179 020 383**.`
* **Exact solutions of `ℓ·m·ι_ub(S) = C(n,3)`** (all `ℓ` in range,
  `m ≤ |Out S|`), with the `p`-part filter applied:

  | | | verdict |
  |---|---|---|
  | `M₁₁`, `ℓ=1`, `m=1`, `n=11` | `C(11,3)=165=ι(M₁₁)` | **live coincidence** — realised by the admissible factorization `M₁₁ × A₇` (`7920·2520 = 11!/2`); killed by Theorem κ-A via the `A₇` factor, and it is one of the 29 `(★)`-failures of v_task35 |
  | `M₂₂`, `ℓ=12`, `n=56` | | killed, `p`-part at `p=2` |
  | `M₂₃`, `ℓ=4`, `n=46` | | killed, `p`-part at `p=23` |
  | `HS`, `ℓ=14`, `n=100` | | killed, `p`-part at `p=2` |
  | `Suz`, `ℓ=1`, `m=1`, `n=66` | `C(66,3)=45760=ι_ub(Suz)` | **live coincidence**; `n = 66 ≤ 70`, so inside §4am's exhaustive 222-factorization census, where Criterion AT holds |

  Both live coincidences lie inside `n ≤ 70` and are therefore covered.
  **But the search only ran `ℓ ≤ 200`; for `B` and `M` the admissible `ℓ`
  reaches `≈ 10⁷`, so the sporadic row is NOT exhaustively checked for
  `70 < n ≤ 1.02·10¹⁰`.**  This is a genuine, previously unrecorded gap
  (input **I8** below), and it is *inside* the range §4ao calls proven.

## 1.8  R1 — verdict

* **Closed by proof, all `n ≥ 10`:** `L₄`, `U₄`, `Sp₆` (both regimes),
  `U₅` (both regimes), `S₄` at prime `q`, `S₄` at even `q`, `G₂`, `A_m`,
  and `L₃` at prime `q`.
* **Closed computationally, `10 ≤ n ≤ 2·10⁷`, complete over all `q`:**
  `L₃` (`q = p^f`, `f ≥ 2`), `L₅`, `S₄` at odd non-prime `q`.
* **Open for `n > 2·10⁷`:** those same three equations — and at `ℓ* = 1`
  they *are* §4ao's `L₃(m=2)`, `L₅(m=1,2)` and `S₄(m=1)` equations.
* **Open for `70 < n ≤ 1.02·10¹⁰`:** the sporadic row (I8).

The advertised gain of the ι₂ route — "the curves become irrelevant" — is
**realised in case (a) and branches (b1),(b2),(b3)** (Part 2) and **not
realised in R1**.

---

# PART 2 — the conclusion table of §4at/§4au, rewritten and executed

Corrections folded in:

* **pair invariants** (v_task36): `a₁ = f₁ι₁`, `a₂ = f₂ι₂`,
  `R^p = (f₂/f₁)R`, `f₁,f₂ ∈ {1,2}`.  The fusion numbers `ρ = m₁/m₂` of
  §4ar/§4au are the *same* phenomenon as `f₁,f₂` and must **not** be
  carried in addition — see Problem P3 in Part 4.
* **prime/non-prime split** (v_task32): the `S₄`/`Sp₆`/`U₅` rows split
  into `q = p` (old closed form, [PROVEN]) and `q ≠ p` (subfield trap,
  `ι₂ = t(q)ι₁`, `t(q) = (q−1)/(q₀−1)`-type).
* **Erratum 1 of §4aw**: after transport the multiplier `ℓ` is free, so
  §4ar's **degree-mismatch** kills (`L₃`, `L₅`, `Sp₆`) do **not**
  transport; they are replaced by **Lemma TO-2** (order squeeze).
* **Erratum 2 of §4aw**: the non-prime kills are **size** kills, not
  divisibility kills, and are stated as such.
* **Erratum 3 of §4aw**: `L₃(3)`'s ratio 4 is the *simple-group* ratio;
  the pair ratio at `Ā = L₃(3).2` is 2.

Branches (v_task37 Theorem TO):
**(a)** one orbit carries both conductors, `R^p = (n−3)/4`;
**(b1)** `R^p = 3(n−3)/4`; **(b2)** `R^p = 3`;
**(b3)** `R^p ∈ {4, 4/3}` (fourth-value sub-branches).

## 2.1  The table

Every row ends in *eliminated outright* or a *finite check that was run*.
"scan" = `v_task38_table_checks.py`, prime powers `q ≤ 2·10⁵`, exact
`Fraction`/integer arithmetic, with filters DIV + SIZE + p-PART + ORDER
(the same five of §1.2 with (1) replaced by the branch equation).

| family / regime | `R^p` | (a) `R^p=(n−3)/4` | (b1) `=3(n−3)/4` | (b2) `=3` | (b3) `=4, 4/3` | verdict |
|---|---|---|---|---|---|---|
| `L₃(q)`, `q≥3`, `Ā⁻` | `q+1` | no divisibility kill (`n = 4q+7` always integral). **Lemma TO-2**: `ℓ* > 6.1q`, `ℓ*log\|S\| > 48q ln q` vs `log(n!/2) < 4q ln 4q` — contradiction for every `q ≥ 3` | same with `n = (4q+7+8)/3`; same TO-2 kill | `q+1=3` ⟹ `q=2`, outside family | `q+1=4` ⟹ `q=3`: run, none; `4/3` impossible | **eliminated outright** (TO-2) |
| `L₃(q)`, `Ā⁺` | `(q+1)/2` | ditto, `n = 2q+5` | ditto | `q=5`: run, none | `q=7`: run, none | **eliminated** (TO-2 + scan) |
| `L₄(q)`, `Ā⁻` | `(q²+q+1)/(q+1)` | `gcd(q+1,q²+q+1)=1` ⟹ `(q+1) ∣ 4` ⟹ `q ≤ 3`; run | `(q+1) ∣ 12` ⟹ `q ≤ 11`; run | `3q+3=q²+q+1` no integer root | `4q+4 = q²+q+1` no root; `4/3` no root | **eliminated outright** (divisibility) |
| `L₄(q)`, `Ā⁺` | `(q²+q+1)/(2(q+1))` | `2(q+1) ∣ 4` ⟹ `q ≤ 1` | `2(q+1) ∣ 12` ⟹ `q ≤ 5`; run | none | none | **eliminated outright** |
| `L₅(q)`, both `Ā` | `q²+1` | integral; **TO-2**: `n = 4q²+7`, `ℓ* ≈ 10.7q²`, `ℓ*log\|S\| ≈ 257q² ln q` vs `≈ 8q² ln q` | ditto | `q²+1=3` no | `q²+1=4` no; `4/3` no | **eliminated outright** (TO-2 — this is the row erratum 1 was about) |
| `U₄(q)`, `q≥3` | `(q²+1)/(q+1)` | `gcd ∣ 2` ⟹ `(q+1) ∣ 8` ⟹ `q ≤ 7`; run | `(q+1) ∣ 24` ⟹ `q ≤ 23`; run | `q²+1=3q+3` no root | `q²+1=4q+4` no root; `4/3` no | **eliminated outright** |
| `S₄(q)`, `q = p ≥ 5` | `q²/(2(q+1))` | `gcd(q²,q+1)=1` ⟹ `(q+1) ∣ 2` ⟹ none | `(q+1) ∣ 6` ⟹ `q ≤ 5`; run | `q² = 6(q+1)` no root | `q²=8(q+1)` no; `4/3` no | **eliminated outright** |
| `S₄(q)`, `q` odd, `q≠p`, no `δ` | `t(q)` | **size**: `n = 3+4t`, `C(n,3) ≈ 10.7t³ ≥ ι₁ ≈ q³` needs `t ≥ 0.45q`; `t = (q−1)/(q₀−1)` | ditto with `t/3` | `t=3`: run | `t=4`: run; `4/3` ∉ ℤ | **finite check, RUN: none** |
| `S₄(q)`, `q` odd, `q≠p`, with `δ` | `≤ 2t(q)` | ditto (constant ×4, still finite) | ditto | `2t=3` ∉ ℤ | `2t=4` ⟹ `t=2`: run | **finite check, RUN: none** |
| `S₄(q)`, `q` even, `Ā⁻`/`Ā⁺` | `t(q)` | leading-coefficient argument: `6ℓf₁ = 64` has no integer solution, so `q` bounded; run | ditto | `t=3` ⟹ `q=4`: run | `t=4`: run | **finite check, RUN: none** |
| `Sp₆(q)`, `q=p` | `(q⁴−1)/(q³−1)` | `gcd(q²+q+1, q³+q²+q+1)=1` ⟹ `(q²+q+1) ∣ 4` ⟹ none | `∣ 12` ⟹ none | none | none | **eliminated outright** |
| `Sp₆(q)`, `q≠p` | `≤2t(q)` | **size** (`ι₁ ≈ q⁵` vs `C(3+8t,3)`) | ditto | run | run | **finite check, RUN: none** |
| `U₅(q)`, `q=p` | `q⁴/((q+1)(q²+1))` | `gcd = 1` ⟹ `(q+1)(q²+1) ∣ 4` ⟹ none | `∣ 12` ⟹ none | none | none | **eliminated outright** |
| `U₅(q)`, `q≠p` | `t(q)` | **size** (`ι₁ ≈ q⁷`) | ditto | run | run | **finite check, RUN: none** |
| `G₂(q)`, `q ≥ 3` | `≤ 2(q+1)` (Bound G₂) | — | — | — | — | **eliminated outright** (§4au addendum, Lemma G₂-C) |
| `A_m` | `(m−3)/4` (`K=A_m`), `(m−2)/3` (`K=S_m`) | — | — | — | — | **eliminated outright** (Theorem κ-A / Step 0; `K=S_m` only strengthens it) |
| sporadic | not tabulated | — | — | — | — | **finite check, RUN partially** — see §1.7 / input I8 |

## 2.2  The run

```
$ python3 v_task38_table_checks.py 200000
L3   f1=1 f2=1 : (a)=0 (b1)=0 (b2)=0 (b3)=0
L3   f1=2 f2=1 : (a)=0 (b1)=0 (b2)=0 (b3)=0
L4   f1=1 f2=1 : ...        (13 rows, all zero)
# q scanned: prime powers <= 200000   TOTAL SURVIVORS: 0
```

Instrumented accounting over the same range: **exactly two** `(F,q,Ā,n)`
triples reach the DIV filter at all —

| candidate | killed by |
|---|---|
| `L₃(2)`, branch (a), `n = 15`, `ℓ = 65` | SIZE (`\|L₃(2)\| = 168 ≤ C(15,4) = 1365`), p-PART (`ℓfN = 195 > v₂(15!) = 11`), ORDER.  (`q = 2` is outside the family anyway.) |
| `L₄(3)`, branch (a), `n = 16`, `ℓ = 14` | p-PART (`ℓfN = 84 > v₃(16!) = 6`), ORDER |

So every row of the table closes, and the closure is not vacuous: the
filters demonstrably fire.

---

# PART 3 — the master input list of Theorem AT

Tags: **[P]** proven here or in a cited write-up; **[P/c]** proven modulo
a cited classification fact; **[C]** computed (exhaustive within a stated
range); **[H]** standing hypothesis; **[OPEN]**.

## 3.1  Invariants of `A_n`

| # | statement | where | tag |
|---|---|---|---|
| A1 | `κ = \|G\|/ι` is a D-ring invariant; the conductor multiset is | §4aj | [P] |
| A2 | `ι(A_n) = C(n,3)`, `n ≥ 9`, attained only at a 3-cycle | §4ak, re-proved §4as Step 2 | [P] |
| A3 | `ι₂(A_n) = C(n,4)`, `n ≥ 9` (Lemma ι₂-A) | §4as | [P] for abelian `H`, **support ≥ 9 abelian only** |
| A4 | `ι₃(A_n) = 3C(n,4)`, `ι₄ = 4C(n,4)`, `n ≥ 10`; `n = 9` exception `ι₃ = 135` | v_task37 §1 | [P] for `s ≤ 8` (all `H`), [P] for `s ≥ 9` (abelian only) |
| A5 | the DP bound `G(s)` and `g(m) ≤ 2.5^m` | §4as, v_task37 §1(b) | **[C]** exact `s ≤ 40`/`m ≤ 40`, asymptotic beyond — see P5 |
| A6 | `ν(A_m) = C(m,2)` | §4am | [C] `m = 5..12` |

## 3.2  Structure lemmas for `T`

| # | statement | where | tag |
|---|---|---|---|
| B1 | TR-1 `\|A^T\| = ℓ_i·\|A^{Ā_i}\|`; `I(T) ⊇ P` | v_task34 | [P] |
| B2 | TR-2 multi-support floor `≥ ν_min²` | v_task34 | [P] |
| B3 | TR-3 `A ⊄ K` ⟹ `≥ min(ν_min², \|S_min\|)` | v_task34 | [P] |
| B4 | TR-4 `ν(S) ≥ μ(S)` | v_task34 | [P] |
| B5 | Theorem TR (values of `ι(T), ι₂(T)`) | v_task34 | [P] under `(★)`/`(★₂)` |
| B6 | Lemma TO-0 `ι(T) ≤ min P` unconditionally; separation needs only the inequality | v_task37 §2 | [P] |
| B7 | Theorem TO trichotomy | v_task37 §3 | [P] under (AB), `(★₃)` |
| B8 | Lemma TO-2 order squeeze | v_task37 §5 | [P] |
| B9 | Lemma R1-p (`p`-part squeeze) | **this note §1.2** | [P] |
| B10 | Lemma L-bound (`ℓ* ≤ n/6+3`) | **this note §1.6** | [P] |
| B11 | Theorem κ-A: no `A_m` socle factor | §4aj–§4am | [P], all `n ≥ 9` |
| B12 | Criterion AT and the 222 admissible factorizations | §4am, reconstructed v_task35 | **[C]**, `n ≤ 70` only |

## 3.3  Pair invariants and fusion

| # | statement | where | tag |
|---|---|---|---|
| C1 | Lemma F `[Ā:N_Ā(A)] = f(A)[S:N_S(A)]`, `f ∣ \|Out S\|` | v_task36 §0 | [P] |
| C2 | (C1) only equal-index `S`-classes fuse | v_task36 §0 | [P] |
| C3 | Lemma P1: inner/diagonal/field automorphisms fix every parabolic type | v_task36 §2 | [P] |
| C4 | Cor. P2: `f(A) = \|Γ_Ā·J\|` for `A` char. in `U_{P_J}` | v_task36 §2 | [P] |
| C5 | `ι₁` **doubles** for `L_d(q)` and `Sp₄(2^f)` with a graph automorphism | v_task36 §2 | [P] (elementary fixed-space proof for `L_d`) |
| C6 | the per-family `(f₁,f₂,R^p)` table | v_task36 §4 | **[P/c]** — inherits BHR |
| C7 | Lemma ι₂-pair-bound; `ι₂(K≤Ā) ≤ 2(q²+1)ι(K≤Ā)` | v_task36 §6 | [P], **hypothesis `ι(S)=μ(S)`** — fails at `S₄(3) ≅ U₄(2)` |
| C8 | `ι₂` closed forms per family | §4at (CLAIMED) → v_task32 (three rows **refuted**, corrected) | **[P/c]** |
| C9 | Bound G₂ `ι₂(G₂(q)) ≤ (q+1)ι₁`, all `q ≥ 3` | v_task32 (`p=3`, `q≠p`) + v_task33 Lemma G₂-C (`q=p≥5`) | [P/c] — cites Borel–de Siebenthal, Kleidman 1988 Thm A |

## 3.4  Cited facts (not proven in this program)

| fact | used for | citation |
|---|---|---|
| CFSG | everything | — |
| BHR maximal-subgroup tables (dim ≤ 12) | the `I(S)` tables of §4at/§4au, hence C6, C8 | Bray–Holt–Roney-Dougal, *The maximal subgroups of the low-dimensional finite classical groups*, LMS Lecture Notes 407 (2013) |
| Kleidman–Liebeck minimal permutation degrees | `ι(S) = μ(S)` (Lemma ι-μ), TR-4's usefulness | Kleidman–Liebeck 1990 |
| Kleidman, *The maximal subgroups of the Chevalley groups `G₂(q)`*, J. Algebra 117 (1988), Thm A | existence/normalizer of the long-root `A₂` subsystem subgroup in `G₂` | Kleidman 1988 |
| Borel–de Siebenthal | closed subsystems of `Φ(G₂)` | classical |
| Artin / Cameron–Teague / Kimmerle–Lyons–Sandling–Teague (Proc. LMS 60 (1990) 89–122) | `SimpleOrderRigidity` | KLST 1990 |
| Borel–Tits | parabolics are `N_S(O_p(H))`; Lemma P1, Lemma R | classical |
| Zsygmondy | primitive prime divisors (used only in remarks) | classical |

## 3.5  Hypotheses still standing

| # | hypothesis | status |
|---|---|---|
| **(AB)** | the conductor reads `ind*(H) = [G:N_G(H)]·\|H′\|` over **all** `H`, not only abelian | closed for `A_n` through support 8 (v_task37 §1(a), exhaustive GAP); **[OPEN] for support ≥ 9 with non-abelian `H`** |
| **(★)/(★₂)** | `min P < Φ`, `p₂ < Φ` — needed for the *equality* `ι(T) = min P` and to locate `ι₂(T)` | fails on 29/222 (v_task35); **irrelevant for separation** by Lemma TO-0 (v_task37 §2) — this is the TO-0-style irrelevance, and it is genuine |
| **(★₃)** | the same for `p₄ < Φ` — needed for Theorem TO's trichotomy | **[OPEN]**, never swept; the TO-0 argument gives irrelevance for *separation* but **not** for the trichotomy, which needs the equalities |
| **(B)** | no factorization `n!/2 = c·∏\|S_i\|` with `ι(S_i) ≥ C(n,3)` for all `i` | §4aj; verified `n ≤ 150`; the sharpened Criterion AT verified `n ≤ 70` (222 factorizations) |
| **finite floor** | Theorem AT proven for `9 ≤ n ≤ 9.08·10⁶` | §4ao addendum — **but see Problem P1: that claim does not cover sporadic socle factors** |

## 3.6  Open inputs

| # | open input |
|---|---|
| **I5′** | R1's three surviving Lie equations (`L₃` `f≥2`, `L₅`, `S₄` odd non-prime) — verified empty `n ≤ 2·10⁷`, complete in `q` |
| **I8 [NEW]** | the **sporadic row in the transported setting**: `ℓ·f₁·ι(K≤Ā)(S) = C(n,3)` is unchecked for `70 < n ≤ 1.02·10¹⁰` (worst case `M`, `ι_ub = 9.72·10¹⁹`); needs exact `ι(S)` and `ι₂(S)` for the 26 sporadics |
| **I9 [NEW]** | (AB) for support `≥ 9`, non-abelian `H`, on the `A_n` side — the risk is *asymmetric*: a smaller true `ι₂(A_n)` invalidates the **target** `C(n,4)`, while on the `T` side (AB) is harmless (v_task36 §8) |
| **I10 [NEW]** | `(★₃)` unswept (v_task37 R4) |
| I11 | Criterion AT / the admissible-factorization census beyond `n = 70` |

---

# PART 4 — problems found (adversarial pass)

**P1 — the `9.08·10⁶` floor is not sporadic-complete.**  §4ao's scan runs
over *Lie-type families*, all prime powers `q ≤ 3·10⁵`.  §4aj's reason for
dropping sporadics (`n ≲ 3100`) uses `ι_ub(Fi₂₄′) = 4.86·10⁹` as the
maximum, but `ι_ub(M) = 9.72·10¹⁹` is 10 orders larger, giving
`n ≲ 8.35·10⁶` already at `ℓ = 1`, and `n ≲ 1.02·10¹⁰` with the orbit
multiplier.  So *"Theorem AT is proven for `9 ≤ n ≤ 9.08·10⁶`"* is
**overstated** unless the sporadic row is checked in `70 < n ≤ 1.02·10¹⁰`.
Two live coincidences already exist at small `n` (`M₁₁`/`n=11`,
`Suz`/`n=66`), both fortunately inside the exhaustive census.  Severity:
**high** (it is the headline number).

**P2 — no circularity found, but one near-miss.**  v_task36 §5 cross-checks
its data against v_task37 PART D and v_task37 §6 quotes v_task36's Lemma
ι₂-pair-bound.  The *logical* dependence is one-way: Lemma ι₂-pair-bound
uses only Lemma F (v_task36 §0), TR-4 (v_task34) and the `I(S)` tables
(§4at/§4au) — none of which uses anything from v_task37.  Conversely
v_task37's Lemma ι₃-A, Lemma TO-0 and Theorem TO use nothing from
v_task36.  **Clean.**  The near-miss is presentational: v_task36's
headline item 4 says the bound was "requested by the monitor for
v_task37", and v_task37 §6 says the bound is "one clean lemma away" — an
outside reader could take these for mutual support.  They are not.

**P3 — `ρ` and `f` double-count fusion.**  v_task37 §4 writes
`a₁ = m₁ι₁(S*)`, `a₂ = m₂ι₂(S*)`, `ρ = m₁/m₂`, and then runs "the
corrected §4au ratio table `r(q) = ι₂/ι₁`" against `r(q) = 3ρ`.  But
`m₁, m₂` **are** v_task36's `f₁, f₂`: both are the `Out(S)`-orbit length
on the realising class (Lemma F).  Carrying `ρ` *and* using simple-group
`R` is therefore either double counting or (worse) mixing `R` with `R^p`
in the same equation — precisely the slip v_task36's erratum 3 records for
`L₃(3)`.  **Repair:** state every branch as `R^p = ·` with
`R^p = (f₂/f₁)R` and no `ρ`.  I re-ran branches (a),(b1),(b2),(b3) in that
corrected form (`v_task38_table_checks.py`) and the conclusion is
unchanged — zero survivors — so nothing downstream breaks; only the
derivation in v_task37 §4 needs restating.

**P4 — Lemma ι₂-pair-bound's hypothesis fails where §4at's defect lives.**
The lemma assumes `ι(S) = μ(S)`.  That is exactly what is **false** for
`S₄(3) ≅ U₄(2)` (§4at: `ι = 27 < μ = 40`).  So the corollary
`ι₂(K≤Ā) ≤ 2(q²+1)ι(K≤Ā)` — and with it the R1 bound — is not available at
`q = 3` for `S₄`, nor at `q = 2` for `U₄`.  Harmless here (both `q` are
outside the family ranges `q ≥ 5` resp. `q ≥ 3`, and the R1 windows force
`q > (n−1)/2 ≥ 4.5`), but it must be *stated*, not assumed.  Likewise
`L₃(2)` is a genuine **re-ordering** (`ι₁` pair value `8` is the old `ι₂`),
so no multiplicative statement about `L₃` may be applied at `q = 2`.
v_task31's audit of the seven exceptional isomorphisms is the right
cross-check and it is clean apart from `S₄(3)`.

**P5 — three items are used at a higher tag than they carry.**
(i) §4as/v_task37 assert `g(m) ≤ 2.5^m` "verified `m ≤ 40`" and then use it
for **all** `m`; it is true (`g(2^k) ≈ 2^{k²+k}` against `2.5^{2^k}`) but
the write-ups give numerics, not a proof — **[C] used as [P]**.
(ii) v_task37 §5's `L₅` order squeeze is an asymptotic estimate
("contradiction by a factor 1.8, uniformly in `q`") presented as a kill;
Part 2 above replaces it with the explicit inequality
`ℓ*log|S| ≈ 257q² ln q > 8q² ln q` and the scan.
(iii) §4at's `ι₂` closed forms were tagged [CLAIMED] and **three were
subsequently refuted** at non-prime `q` (v_task32).  Any downstream use of
the §4at table as if proven is invalid; only the v_task32/v_task36
corrected forms may be used, and they are **[P/c]** (BHR), not [P].

**P6 — `(★₃)` is load-bearing and unchecked.**  Lemma TO-0 removes `(★)`
from *separation*, but Theorem TO's trichotomy identifies the 2nd, 3rd and
4th smallest elements of `I(T)` with those of `P`, which needs the
**equalities**, i.e. `(★₃)`.  v_task37 R4 notes this and then argues by
analogy with TO-0 — the analogy does not transfer, because a trichotomy is
not a separation.  Either `(★₃)` must be swept (as `(★)` was) or case (b)
must be restated so that only inequalities are used.

**P7 — the `S₄`/`Sp₆` "≤ 2t(q)" rows use an upper bound where an equality
is needed for the gap.**  In branch (b2)/(b3) the equation is
`R^p = 3` exactly; feeding an *upper* bound `R^p ≤ 2t(q)` is safe for R1
(where the condition is `R^p > n−3`, so an upper bound gives a valid
necessary condition) but is **not** safe for the equality branches.  The
scan uses the exact `t(q)`/`2t(q)` values there (v_task36 §3.4 makes
`f₂ ≤ 2` exact, `= 2` iff `(q−1)/(q₀−1)` is even), so the runs are sound;
the *table* must say which is used where.

**P8 — `q₀` is not unique.**  `t(q) = (q−1)/(q₀−1)` depends on the choice
of subfield.  §4au and v_task36 write "`t(q)`" as if it were a function of
`q` alone.  It is the **maximum** over maximal subfields that matters for
the `ι₂` value, and the maximum over *all* subfields for the upper bounds.
The scripts take `q₀ = p` (the largest `t`), which is the conservative
choice for R1; for the equality branches the correct `q₀` is the one with
`q₀ = q^{1/r}`, `r` the smallest prime divisor of `f`.  Both were run;
neither produces survivors.

---

# PART 5 — Theorem AT, final form

> **Theorem AT (alternating rigidity), as it now stands.**
>
> Let `n ≥ 9` and let `T` be a finite Fitting-free non-simple group with
> `|T| = |A_n| = n!/2`.  Assume:
>
> * **(H1)** the cited classification facts of §3.4 (CFSG; BHR maximal
>   subgroups in dimension ≤ 12; Kleidman–Liebeck minimal degrees;
>   Kleidman 1988 Thm A; Borel–de Siebenthal; Borel–Tits);
> * **(H2)** hypothesis **(AB)** for `A_n` beyond support 8 — i.e. that no
>   non-abelian `H ≤ A_n` with `|supp H| ≥ 9` has
>   `ind*(H) < 3C(n,4)`;
> * **(H3)** hypothesis **`(★₃)`** for `T` (`p₄ < Φ`), needed only in the
>   two-orbit branch;
> * **(H4)** one of:
>   * `9 ≤ n ≤ 9.08·10⁶` **and** the sporadic row of §1.7 checked in that
>     range (input **I8**); or
>   * `n ≤ 2·10⁷` **and** I8, in which case the ι₂ route supplies the
>     multi-orbit branches; or
>   * for all `n`: the five §4ao equations
>     (`S₄/L₄` `m=1`; `L₃`,`L₄`,`L₅` `m=2`; `U₄`,`L₅`,`G₂/Sp₆`,`U₅` `m=1`)
>     have no solutions — equivalently, R1's three surviving equations and
>     the sporadic equation have none.
>
> Then `κ(T) ≠ κ(A_n)`, hence `D(T) ≇ D(A_n)`.  Combined with
> `simpleGroupTheorem` (SR1 for `A_n`), **`A_n` is D-rigid among all finite
> groups.**

### What remains before Theorem AT is unconditional

1. **The three R1 equations** — `L₃(p^f)`, `f ≥ 2`, `q ≥ f₁(n−3)`;
   `L₅(q)`, `q² ≥ n−3`; `S₄(q)` odd non-prime, `q > (n−1)/2` — each with
   `ℓ*f₁ι₁ = C(n,3)`.  Verified empty `n ≤ 2·10⁷`, complete in `q`.
   At `ℓ* = 1` these *are* §4ao's `L₃(m=2)`, `L₅(m=1,2)`, `S₄(m=1)`
   equations, so **solving §4ao's curves remains necessary**; the ι₂ route
   removed them from case (a) and branches (b1)–(b3) only.
2. **I8, the sporadic row**, for `70 < n ≤ 1.02·10¹⁰` — needs exact
   `ι(S)`, and for the R1 gap also `ι₂(S)`, for the 26 sporadics.  This is
   a *finite* computation (CTblLib + ATLAS), not research, and it is the
   cheapest remaining item.
3. **(AB) beyond support 8** on the `A_n` side (I9).
4. **`(★₃)`** swept, or case (b) restated with inequalities only (I10, P6).
5. **Criterion AT / the admissible-factorization census** beyond `n = 70`
   (I11) — the only route that would make the whole thing uniform in `n`
   without solving any curve.

### Honest one-line summary

The group theory is complete and the pair-invariant/transport layer is
proven; the ι₂ route has removed the seven §4ap curves from every branch
**except** the ≥3-orbit residue R1, where it reproduces them; and the
finite floor, correctly stated, is
**`9 ≤ n ≤ 2·10⁷` modulo the sporadic row and (AB)/(★₃)** rather than the
unconditional `9.08·10⁶` of §4ao.

---

## Reproduce

```
gcc -O2 -o /tmp/r1 v_task38_r1_scan.c -lm && /tmp/r1 20000000   # ~10 min, 80 MB
python3 v_task38_r1_cross.py 2000
python3 v_task38_table_checks.py 200000
python3 v_task38_sporadic.py
```
All arithmetic exact (`__int128` / Python ints / `Fraction`) except the
explicitly flagged `log|S|` comparisons of Lemma TO-2 and the sporadic
`log(n!/2)` bounds, which are used only as *upper* bounds on `ℓ` and are
therefore conservative.
