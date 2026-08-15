# v_task55 — the first RANK-2 target: **Theorem L3-T**
# (Fitting-free non-simple twins of `L₃(q)` eliminated, all `q`)

Date 2026-08-08.  **NOTES.md not edited.**
Pipeline: the `L₂` pilot (`v_task51`) → rank-1 (`v_task53`, `v_task54`) →
**rank 2**, where the rank-1 argument was predicted to strain.

| file | what it does |
|---|---|
| `v_task55_l3_twins.py` | PART 1 the target's invariants + **Lemma K-L3** + the exact statement of the rank-2 strain; PART 2 **Lemma Q** (`T` is almost simple) via the `ℓ ≥ 3` kill and the **Lemma-B-violator** enumeration; PART 3 the cross-characteristic `ppmax³` kill; PART 4 the equal-characteristic branch (**D/N table**, the three surviving families killed one by one) and **PART 4.0** the factorisation-free exact equal-characteristic sweep to `q ≤ 10⁷`; PART 5 alternating/sporadic socle, complete in `q`; PART 6 the residual census with the orbit floor |
| `v_task55_l3_twins_out.txt` | its output |
| `v_task55_l3_twins.g` / `_g_out.txt` | GAP: orders, the **corrected `ι` witness**, exact `ι` and `ι₂` over the whole lattice, minimal degrees from `Maxes`, `|Out|`, the four raw census configurations and their death by the floor, and the `|L₃(25)| = 7·|L₄(5)|` near-miss |

All arithmetic exact (Python big integers / `Fraction`, GAP rationals).
Every enumerator is imported from `v_task50`–`v_task54`, so this is the same
implementation now exercised on 27 sporadic + 78 732 `L₂` + 5 296 rank-1 +
665 133 `L₃` targets.

---

> ### Headline
>
> **Theorem L3-T [PROVEN, all prime powers `q ≥ 3`, unconditional].**
> There is no Fitting-free **non-simple** finite group `T` with
> `|T| = |L₃(q)|` and `D(T) ≅ D(L₃(q))`.
> (`q = 2`: `L₃(2) ≅ L₂(7)` — already covered by **Theorem L2-T**, and
> excluded from the target range throughout.)
>
> With the CFSG order theorem this gives `D`-rigidity among all finite
> groups for every `q ≥ 3` **except `q = 4`**, where the simple–simple side
> meets the order coincidence `|L₃(4)| = |A₈| = |L₄(2)|`; that pair is
> §4j-classical and `A₈ = L₄(2)` is covered by Theorem AT (`n = 8`,
> §4aj–§4am).  **The non-simple twins of `L₃(4)` are eliminated here**, like
> those of every other `q`.
>
> No dependence on **(AB)** (§1), none on the `Bₙ/Cₙ` residue, none on
> Lemma B *as a hypothesis* — Lemma B appears only as the **classifier** of
> the finitely many groups that can sit in a multi-factor socle.
>
> **The predicted rank-2 strain is real and is resolved.**  The rank-1
> Step 2 (`ι(S)³ > |S|`) is **false for every `q`** here
> (`ι³/|S| ≤ 0.46`, PART 1), and the raw census is **no longer empty** —
> four genuine two-orbit configurations survive Phase 1 and are killed by
> the orbit floor.  The `ℓ = 2` window predicted in the brief **closes, but
> not by `ι₂`**: see §3.4.

---

## 0. Notation and the target's data

Notation of `v_task50` §0 / `v_task53` §0.  `q = p^f`, `e := gcd(3, q−1)`.

```
|S| = |L_3(q)| = q^3 (q^2-1)(q^3-1)/e = q^3 (q-1)^2 (q+1)(q^2+q+1)/e  ~ q^8
|S|_p = q^3        iota(S) = q^2+q+1        |Out(S)| = 2 f e
a := deg_q |S| = 8    b := deg_q iota(S) = 2    N := deg_q |S|_p = 3
```

Orders and `|Out|` GAP-verified at `q = 2,…,32` (`_g_out.txt` PARTS A, E).

---

## 1. `ι(L₃(q)) = q²+q+1` — over **all** subgroups, so (AB)-free

> **Lemma L3-ι [PROVEN, all prime powers `q ≥ 2`, no exceptions].**
> `ι(L₃(q)) = q²+q+1`.

*Proof.*
**(≤)** Let `P` be a maximal parabolic (the stabiliser of a projective
point) and `A := O_p(P)` its unipotent radical.  `A` is **elementary
abelian of order `q²`**, `A′ = 1`, and `N_S(A) = P` (Borel–Tits,
`N_G(Z(U_P)) = P` applied to the maximal parabolic), so
`ind*(A) = [S:P] = q²+q+1`.
**(≥)** For `1 ≠ H ≤ S`: if `N_S(H) = S` then `H = S` by simplicity and
`ind*(H) = |S| ≫`; otherwise `ind*(H) ≥ [S:N_S(H)] ≥ m(S)`, the minimal
degree, and `m(L₃(q)) = (q³−1)/(q−1) = q²+q+1` for **every** `q`
**[LIT: Cooperstein 1978; Kleidman–Liebeck Table 5.2.2]** — in particular
at `q = 4`, where `m(L₃(4)) = 21` despite the `A₈` order coincidence. ∎

The proof quantifies over **all** `H`, so — exactly as for `L₂` and the
rank-1 families — **(AB) is not a debt for an `L₃` target**.

> ### A rank-2 trap, recorded so it is not repeated
> At rank 1 the `ι`-witness is `A = Z(Syl_p(S))`.  **At rank 2 that witness
> is wrong**: `N_S(Z(Syl_p))` is the **Borel**, of index
> `(q+1)(q²+q+1)`, not `q²+q+1`.  GAP (`_g_out.txt` PART B, `q = 3, 4, 5,
> 7, 8, 9, 11, 13, 16, 17, 25, 27`) verifies **both** values:
> `ind*(O_p(P)) = q²+q+1` ✓ (12/12) and `ind*(Z(Syl_p)) = (q+1)(q²+q+1)` ✓
> (12/12).  The correct witness is the unipotent radical of a **maximal**
> parabolic.

**Exact `ι` and `ι₂` over the whole subgroup lattice** (`_g_out.txt` PART C):

| `S` | `ι` | claimed | `ι₂` | `ι₂/ι₁` | first six of `I(S)` |
|---|---|---|---|---|---|
| `L₃(2)` | 7 | `7` ✓ | 8 | 1.14 | `7, 8, 21, 28, 42, 56` |
| `L₃(3)` | 13 | `13` ✓ | **52 = (q+1)ι₁** | 4.0 | `13, 52, 104, 117, 144, 156` |

Minimal degrees from the stored `Maxes` (`_g_out.txt` PART D), `q = 2, 3, 4,
5, 7, 8, 9, 11`: `m = 7, 13, 21, 31, 57, 73, 91, 133` — `= q²+q+1` in **all
eight** rows.

**`ι₂(L₃(q)) = (q+1)(q²+q+1)`** (the Borel index) is confirmed as an `ind*`
value at 12 values of `q`, and as the *exact* second-smallest at `q = 3`.
The brief's `ι₂` guess is therefore right — but it is **not used**; see §3.4.

---

## 2. PART 1 — the strain, quantified

| statement | rank 1 (`U₃`, `Sz`, `R`) | rank 2 (`L₃`) |
|---|---|---|
| `ι(S)` vs `|S|_p` | `= |S|_p + 1` | `≈ |S|_p / q` |
| `ι(S)³ > |S|` (Step 2) | true, ratio `4.4 … 757` | **FALSE for every `q`**; `max ι³/|S| = 0.459` at `q = 4` |
| Lemma K′ `|S| < (|S|_p)³` | comfortable | `q⁸ < q⁹` — survives by **one** exponent |
| raw census | empty at all 5 296 targets | **4 survivors** below `q ≤ 23 816` |

> **Lemma K-L3 [PROVEN, elementary; 0 violations over all prime powers
> `3 ≤ q ≤ 3000`].**
> `ppmax_{p′}(|S|) ≤ max( 2(q−1)², (q²+q+1)/e )` and `ppmax(|S|) = q³`.
>
> *Proof.*  `gcd(q−1,q+1) | 2`; `q²+q+1 = q(q+1)+1` so
> `gcd(q+1, q²+q+1) = 1`; `q²+q+1 ≡ 3 (mod q−1)` so `gcd(q−1,q²+q+1) | 3`,
> and when `3 | q−1` the `3`-part of `q²+q+1` is exactly `3` and is cancelled
> by `e = 3`.  So every `r ≠ p` has its whole `r`-part inside one block, and
> the `2`-part of `(q−1)²(q+1)` is at most `2(q−1)²` because
> `min(|q−1|₂, |q+1|₂) = 2`. ∎

**Consequence.**  Step 2 and Step 3 of the rank-1 pipeline are *both*
unavailable.  PART 2 replaces them with a single, stronger statement.

---

## 3. PART 2 — **Lemma Q**: `T` is almost simple

Let `Soc T = ∏_j S_j^{ℓ_j}` (orbits `O_j`, lengths `ℓ_j`), so
`∏_j |S_j|^{ℓ_j} = |S|/c`.

> **Observation Q0 [PROVEN, one line].**  If `T` is **not** almost simple —
> i.e. some `ℓ_j ≥ 2` or there are `≥ 2` orbits — then **some socle factor
> `G` satisfies `|G|^{max(2,ℓ)} ≤ |S|`** (with `ℓ = ℓ_j` its orbit length),
> while the orbit floor gives `ℓ·|Out(G)|·ι(G) ≥ ι(S) = q²+q+1`.
>
> *Proof.* If `ℓ_j ≥ 2` for the orbit of `G`, then `|G|^{ℓ_j} ≤ |S|`.  If
> there are two orbits, the one with the smaller contribution has
> `|G|^{2ℓ_j} ≤ ∏_i |S_i|^{ℓ_i} ≤ |S|`. ∎

### 3.1 `ℓ ≥ 3` dies from **Lemma C** alone

Lemma C (`|Out|ι ≤ |G|^{2/3}`, `[PROVEN, v_task52]`) with `|G|^ℓ ≤ |S|`
gives the cube-cleared integer test `(q²+q+1)^{3ℓ} ≤ ℓ^{3ℓ}|S|²`.  PART 2a
solves it exactly:

```
l = 3 : possible only for q <= 140      l = 5 : q <= 8
l = 4 : possible only for q <= 12       l >= 6 : q <= 4  ...  l >= 11 : q <= 3
```

So **for `q ≥ 141` every socle orbit has length `ℓ ≤ 2`**, and by Q0 the
binding case is `|G|² ≤ |S|`.

### 3.2 The `ℓ ≤ 2` / two-orbit window is exactly the **Lemma-B violators**

Eliminating `q` between `|G|² ≤ |S| < q⁸` and `q²+q+1 ≤ 2|Out(G)|ι(G)`:

> **Lemma Q [PROVEN].**  A socle factor as in Q0 with `ℓ ≤ 2` satisfies
> ```
>            |G|  ≤  4 · ρ(G)² ,        ρ(G) := |Out(G)|·ῑ(G) ,
> ```
> i.e. `G` **violates Lemma B** (`α := log|G|/log ι ≤ 2`).

This is the exact point where the rank-2 target needs *more* than Lemma C:
Lemma C gives `ρ ≤ |G|^{2/3}` and `|G| ≤ q⁴`, hence `2ρ ≤ 2q^{8/3} > q²` —
**Lemma C alone does not close the `ℓ = 2` window.**  What closes it is that
`α ≤ 2` is a **finite** condition:

* **Lie type.**  `ρ ≍ q₁^{μ}·dfg`, `|G|^{1/2} ≍ q₁^{D/2}`, and `D/μ ≥ 7/3
  > 2` in **every** family (the `θ`-table of `v_task54` §2.1, minimum at
  the Ree groups), so `D/2 − μ > 0` and the condition fails for large `q₁`.
  PART 2b computes, per family and rank, the exact tail bound from the
  surrogate `(8 d f₁ g q₁^{μ})²·12d ≥ q₁^{D}` [(T1)+(T2)+(T3), `v_task52`]:
  **it fails for every `q₁ > 2 709 504`, in every family and every rank**,
  and for **every** `q₁ ≥ 2` once the rank is `≥ 25`.  The exact scan over
  `q₁ ≤ 2 709 504`, ranks `≤ 24`, is therefore **complete**.
* **Alternating** (`m ≤ 80`) and **sporadic** (27 + Tits): exact tables.

**Result (PART 2b): 56 Lemma-B violators in total**, of which **47** have a
non-empty target window `[q_lo, q_hi]`, and

```
every non-empty window lies in  q <= 23 815      (attained by  Th)
```

Sample rows: `A₅, L₂(4)` → `q ∈ [3,3]`; `L₃(4)` → `[12,21]`;
`J₁` → `[21,45]`; `O′N` → `[824,3380]`; `Th` → `[17357,23815]`;
`U₃(128)` → `[12449,13272]`.

> **Consequence [PROVEN].**  For `q > 23 815`, `T` is **almost simple**:
> ```
>    (E)   c·|S₁| = |S| ,   c ≥ 2 ,   c | |Out(S₁)| .
> ```
> For `q ≤ 23 816` the census of §6 settles it directly.

### 3.3 What this replaces

The rank-1 note reached (E) from `ι(S)³ > |S|` (Step 2) and
`(ι/ℓ)^{3ℓ/2} > |S|` (Step 3).  Both fail at rank 2.  Lemma Q reaches the
**same** conclusion from (i) Lemma C for `ℓ ≥ 3` and (ii) the *finiteness*
of the Lemma-B exception set for `ℓ ≤ 2`.  **Lemma Q is target-agnostic**:
it needs only `ι(S)² ≳ |S|^{1/2}`, i.e. `b ≥ a/4` — see §7.

### 3.4 The `ι₂` route: **not needed, and recorded as such**

The brief proposed killing the `ℓ = 2` window with the second conductor
`ι₂(S) = (q+1)ι₁(S)` and the per-family pair-ratio tables of `v_task36`.
That route is **not used**: Lemma Q closes the window with `ι₁` alone, and
does so uniformly in `q` and with no pair bookkeeping.  The `ι₂` formula is
nevertheless **confirmed** (§1) — `ι₂ = (q+1)(q²+q+1)`, the Borel index,
GAP-checked at 12 values of `q` and exactly at `q = 3` — and is recorded for
possible use at rank ≥ 3.  *(This also re-confirms the pilot's refutation of
`ι₂/ι₁`-gap arguments: at `q = 2` the ratio is `8/7`, at `q = 3` it is `4`;
there is no uniform gap.)*

---

## 4. PART 3 — almost simple, **cross characteristic**: closed at `q ≤ 97`

`S₁` of Lie type over `F_{q₁}`, `p₁ ≠ p`.  Then `|S₁|_{p₁} ≤ ppmax_{p′}(|S|)
=: P ≤ 2(q−1)²`, and Lemma K′ gives `|S₁| < P³`, so `|S| < c·P³` with
`c ≤ |Out(S₁)|`.  The rank is bounded by `2^{N₁} ≤ q₁^{N₁} ≤ P`, hence
`n₁ ≤ n_max(P)` and `c ≤ 6 n_max log₂P`.  PART 3 evaluates this exactly over
all prime powers `q ≤ 4000`:

```
survives only for  q in {3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32,
                         37,41,43,47,49,61,64,67,73,79,97}
```

i.e. `q ≤ 97` — the inequality is `q⁸ ≍ |S|` against `c·8q⁶`, monotone.
This is the **direct analogue of `v_task53` §5.2** and it is *sharper* here
(`q < 98`) than for `U₃` (`q < 179`), because `L₃`'s order is further from
`ppmax_{p′}³`.  All of `q ≤ 97` is inside the census.

---

## 5. PART 4 — almost simple, **equal characteristic**: closed for all `q`

### 5.1 Only three families survive the `D/N` test

`q₁^{N₁} | q³` and `|S₁| = |S|/c` give
`(q³)^{D₁/N₁} ≥ q₁^{D₁} ≥ |S|/c ≳ q⁸/(3c)`, i.e.

```
      3·(D₁/N₁)  ≥  8 − log_q(3c) .                            (*)
```

The `D/N` table (PART 4) has **exactly three rows with `D/N ≥ 8/3`**:

| family | `D` | `N` | `D/N` |
|---|---|---|---|
| `A₁ = L₂` | 3 | 1 | **3** |
| `A₂ = L₃` | 8 | 3 | **8/3** (the target's own) |
| `²A₂ = U₃` | 8 | 3 | **8/3** |

every other family (next value `5/2`: `L₄`, `U₄`, `C₂`, `²B₂`; then `12/5`,
`7/3`, …) needs `3c ≥ q^{1/2}` by (*).  With
`c ≤ |Out(S₁)| = d₁f₁g₁ ≤ 6 n₁ · 3f` and `n₁ ≤ 1+√(6 log_p q)`, this fails
for every `q ≥ 185 767` — a window entirely inside PART 4.0.

### 5.2 The three surviving families, killed uniformly

* **`S₁ = L₂(q₁)`.**  `q₁ = q³/p^j` with `p^j = c_p | c`, so
  `|S₁| ≈ q⁹/p^{3j}`; matching `|S| ≈ q⁸` forces `p^{3j} ≈ cq/d₁` while
  `p^j ≤ c ≤ 2f₁ ≤ 6f`, hence
  **`q ≤ 2c² ≤ 72 f² = 72 (log_p q)²`**, i.e. `q ≤ 12 163`.
  Exact scan over all prime powers `q ≤ 2·10⁵` and all `j`: **NONE**.
* **`S₁ = U₃(q₁)`.**  Zsygmondy: `q₁²−q₁+1` carries a primitive prime `r` of
  `p^{6f₁}−1` (the single exception `(2,6)` is `q₁ = 2`, and `U₃(2)` is not
  simple).  `r | |S₁| | |S|`, whose `p′`-part divides `q⁶−1 = p^{6f}−1`, so
  `ord_r(p) = 6f₁ | 6f`, i.e. **`f₁ | f`**.
  `f₁ = f`: `c·e·(q³+1) = e₁(q³−1)` with `e, e₁ ∈ {1,3}`, `c ≥ 2` — no
  solution.  `f₁ < f`: then `q ≥ q₁²` and
  `c ≥ (q/q₁)⁸/3 ≥ q₁⁸/3` against `c ≤ 2f₁e₁ ≤ 6 log₂ q₁`.  Exact scan
  `q ≤ 10⁵`: **NONE**.
* **`S₁ = L₃(q₁)`, `q₁ < q` (subfield).**  `q₁ = q` gives `c = 1`.
  Zsygmondy on `q₁²+q₁+1` (primitive prime of `p^{3f₁}−1`; exception
  `(2,6)`, i.e. `q₁ = 4`, checked separately) gives `3f₁ | 6f`, so
  `f₁ | 2f` and `f − f₁ ≥ f/3`; then `c ≥ p^{8f/3}/3` against `c ≤ 6f`.
  Exact scan `q ≤ 10⁵`: **NONE**.

### 5.3 PART 4.0 — the exact, factorisation-free sweep

Because `q₁^{N₁} | q³` bounds `f₁ ≤ 3f/N₁`, the **entire** equal-
characteristic branch is a finite exact test per target, needing **no
factorisation of `|S|`**.  Run over **every** family, every rank `≤ 29`,
every `f₁`:

```
targets (all prime powers 3 <= q <= 10^7)   : 665 133
divisor pairs |S_1| | |S| found             : 1 333 165
POSITIVE CONTROL (S_1 = S, c = 1 found)     : 665 133 / 665 133
HITS (c >= 2 and c | |Out(S_1)|)            : NONE
order-only NEAR-MISS (c | |Out| dropped)    : (q, S_1, c) = (25, L4(5), 7)
```

> **The one near-miss of the whole rank-2 row:**
> `|L₃(25)| = 7 · |L₄(5)|` **exactly** (`50 778 000 000 = 7 · 7 254 000 000`,
> GAP `_g_out.txt` PART G).  It dies because `7 ∤ |Out(L₄(5))| = 8` — killed
> by the Fitting-free constraint `c | |Out(S₁)|`, **not** by order
> arithmetic.  This is the rank-2 analogue of `v_task53`'s
> `|U₃(q)| = (q+1)|R(q)|`, and it is the reason the `c | |Out|` constraint
> must never be relaxed to `c ≤ |Out|`.

---

## 6. PARTS 5–6 — alternating/sporadic socle, and the residual census

**PART 5 (complete in `q`, not a range).**  `|L₃(q)| = M` is inverted
exactly for `q` (exact integer 8th roots, both values of `e`).  Over all
`A_m` with `|A_m| ≤ 10⁹⁰` and all 27 sporadics + Tits, with every
`c | |Out(S₁)|`, `c ≥ 2`: **74 `(S₁,c)` pairs, 0 hits**.
*Positive control:* the inverter must find the `c = 1` self-solutions — and
it returns exactly one, `|A₈| = |L₃(4)|`.  **The `A₈`/`L₃(4)` coincidence is
thus caught by the machinery and excluded only by `c ≥ 2`**, i.e. by `T`
being non-simple; the simple–simple separation `L₃(4)` vs `A₈` is
§4j-classical, and `A₈ = L₄(2)` is covered by Theorem AT.

**PART 6 (the residual census), all prime powers `3 ≤ q ≤ 23 816`
(2 715 targets):**

| | |
|---|---|
| positive-control failures | **0 / 2715** |
| **RAW** (Phase 1: order census + `c | ∏|Out|^{ℓ}ℓ!`) survivors | **4** |
| after Phase 2 (the orbit floor) | **0** |

```
q =   4 :  A5 x L3(2)          , c = 2
q =   9 :  A6 x L2(27)         , c = 12
q =  16 :  L2(16) x Sz(8)      , c = 12
q = 729 :  L2(729) x L2(19683) , c = 108
```

Each is a **two-orbit** configuration with both orbits of length 1, so each
factor must clear the floor `|Out(S_i)|ι(S_i) ≥ q²+q+1`, and each fails
(GAP `_g_out.txt` PART F, with the `ι` values computed over the full
lattice):

| `q` | `ι(S)` | the failing factor | `|Out|·ι` |
|---|---|---|---|
| 4 | 21 | `A₅` | `2·5 = 10` |
| 9 | 91 | `A₆` | `4·10 = 40` |
| 16 | 273 | `L₂(16)` | `4·17 = 68` |
| 729 | 532 171 | `L₂(729)` | `12·730 = 8760` |

> **This is the first target in the programme where the orbit floor is
> load-bearing.**  For `L₂` it killed one raw survivor; for the rank-1
> families the raw census was empty at all 5 296 targets and the floor was
> never used.  At rank 2 the raw census produces survivors at a rate of
> about `1.5 per 1000 targets`, and **all** of them are two-orbit
> configurations — exactly the branch that Lemma Q handles uniformly.

---

## 7. Status ledger

| step | status | range |
|---|---|---|
| `ι(L₃(q)) = q²+q+1` over **all** subgroups; (AB)-free | **[PROVEN]** | all `q` |
| Lemma K-L3 (`ppmax` bounds) | **[PROVEN]**, 0 violations | all `q` |
| `ℓ ≥ 3` killed (Lemma C) | **[PROVEN]** | `q ≥ 141` |
| Lemma Q ⟹ `T` almost simple | **[PROVEN]** | `q > 23 815` |
| cross characteristic empty | **[PROVEN]** | `q ≥ 98` |
| equal characteristic, `D/N ≤ 5/2` families | **[PROVEN]** | `q ≥ 185 767` |
| equal characteristic, `L₂`/`U₃`/`L₃` socle | **[PROVEN]**, uniform | all `q` |
| equal characteristic, exact sweep | **[COMPUTED]**, 0 hits | `q ≤ 10⁷` |
| alternating / sporadic socle | **[PROVEN]**, complete in `q` | all `q` |
| residual census (raw + floor) | **[COMPUTED]**, 0 survivors | `q ≤ 23 816` |
| simple–simple side | **[LIT: CFSG order theorem]** | all `q`; `q=4` is the `A₈` pair |

**Every finite window produced by a uniform argument lies strictly inside a
range that has been exhausted exactly**, so:

> **Theorem L3-T [PROVEN, all prime powers `q ≥ 3`, unconditional].**
> No Fitting-free non-simple twin.  Hence `L₃(q)` is `D`-rigid among all
> finite groups for every `q ≥ 3`, with the single caveat that for `q = 4`
> the *simple–simple* side is the classical `L₃(4)` vs `A₈` separation
> (§4j), not a consequence of this note.

### Honest gaps

1. **(H1) `ι`'s lower half is literature.**  `m(L₃(q)) = q²+q+1`
   [Cooperstein; Kleidman–Liebeck] is quoted, and machine-confirmed only at
   `q ≤ 11` (stored `Maxes`) — the same status the `U₃`/`Sz`/`R` rows have.
   The **upper** half (the witness) is GAP-verified at 12 values of `q`.
2. **(H2) The Lemma-B violator enumeration** rests on the surrogate
   (T1)/(T2)/(T3) bounds of `v_task52` for the tail, plus an exact scan
   inside it.  The tail bound (`q₁ ≤ 2.7·10⁶`, rank `≤ 24`) is *proved*, not
   assumed, but it inherits `v_task52`'s reliance on the standard order,
   parabolic-index and `d·f·g` tables.
3. **(H3) The `ῑ` values used in the floor** are parabolic **upper** bounds
   for Lie-type factors (conservative direction) and the exact
   `v_task39`/`v_task50` table for sporadics.  Sharper `ι` would only
   shrink the windows.
4. **(H4) `q ≤ 23 816` census range** is what the Lemma-Q windows demand;
   nothing beyond it was scanned *for the multi-factor branch*, and nothing
   needs to be.
5. **(H5)** The `q = 4` simple–simple row is inherited, not proved here.

---

## 8. Generalisation notes

### What transfers to `L_d(q)`, `U_d(q)`, `d ≥ 4`

* **`ι(S) = [S:P] = (q^d−1)/(q−1) ≍ q^{d−1}`** with the same witness
  (`O_p(P)` for a maximal parabolic, **not** `Z(Syl_p)`) and the same
  (AB)-free `(≥)` argument via the minimal degree.  `a = d²−1`,
  `b = d−1`.
* **Lemma Q generalises verbatim** and is the key tool: it needs
  `|G|^{1/2} ≤ 2ρ(G)` to be a *finite* condition, which it always is
  (`D/μ ≥ 7/3 > 2` for every Lie family — this is `v_task54`'s `θ`-table
  again).  **The `q`-window it produces grows with the target**, though: it
  is `q ≤ (2ρ_max)^{1/2}` where `ρ_max` ranges over the violator list, i.e.
  a *fixed* absolute bound `q ≤ 23 815` for `L₃` — and for `L_d` the window
  is `ι(S) ≤ 2ρ(G)`, i.e. `q^{d−1} ≲ 2ρ_max`, so the census range **shrinks**
  as `d` grows.  **Rank 2 is the worst case for Lemma Q, not the best.**
* **The `D/N ≥ a/N` test of §5.1 generalises exactly**: for `L_d(q)` the
  target's own ratio is `(d²−1)/(d(d−1)/2) = 2(d+1)/d`, which **decreases**
  with `d`, so *more* families pass the test and the equal-characteristic
  case analysis gets harder — this is where rank `≥ 3` will strain next
  (`d = 4`: `D/N ≥ 5/2` admits `L₂, L₃, L₄, U₃, U₄, C₂, ²B₂`).
* **The cross-characteristic `ppmax³` kill improves with `d`**:
  `ppmax_{p′} ≲ q^{d−1}` while `|S| ≍ q^{d²−1}`, so `|S| > c·ppmax³` as soon
  as `d²−1 > 3(d−1)`, i.e. `d ≥ 3`, with growing margin.
* **PART 4.0 (the factorisation-free equal-characteristic sweep) is the
  single most reusable piece**: `q₁^{N₁} | |S|_p` makes the branch finite
  per target with no factorisation, and it runs at ~10⁶ targets/second.

### Where rank 3+ will strain

1. **The equal-characteristic family list** (§5.1) — it grows with `d` while
   the uniform kills (`L₂` size argument, `U₃`/subfield Zsygmondy) are
   family-by-family.  A *uniform* treatment of the "`S₁` and `S` in the same
   characteristic with `D₁/N₁` close to the target's" case is the next tool
   to build.
2. **`mult₁` is still useless** (`≤ 3` for `L₂`, and the psn count for `L₃`
   is dominated by the two parabolic classes) — no comparison argument is
   available at any Lie target.
3. **`ι₂` remains unused.**  It is now *known* (`(q+1)ι₁` for `L₃`) but no
   argument has needed it.  Do not build the pair-spectrum machinery until
   a target actually requires it.

### Refuted / do-not-re-attempt (adding to the earlier lists)

* **`A = Z(Syl_p(S))` as the `ι`-witness at rank ≥ 2** — it gives the Borel
  index `(q+1)(q²+q+1)`, a factor `q+1` too large.  Use `O_p(P)` for a
  **maximal** parabolic.
* **Lemma C alone against the `ℓ = 2` window** — `2|G|^{2/3} ≥ 2q^{8/3} >
  q²`, so it cannot close it.  The exponent that closes it is the
  *per-family* `μ/D ≤ 3/7`, i.e. Lemma B, used as a **finiteness
  classifier**, not as a hypothesis.
* **Relaxing `c | |Out(S₁)|` to `c ≤ |Out(S₁)|`** — the near-miss
  `|L₃(25)| = 7·|L₄(5)|` survives the relaxed test.

---

## 9. Citations

| # | input | tag |
|---|---|---|
| C1 | `m(L₃(q)) = q²+q+1` (minimal degree, **lower** bound for `ι`) | **[LIT: Cooperstein 1978; Kleidman–Liebeck Table 5.2.2]** |
| C2 | Borel–Tits `N_G(Z(U_P)) = P` (the `ι` witness) | **[LIT]** + GAP-verified at 12 values of `q` |
| C3 | Zsygmondy's theorem (used at `p^{3f₁}−1`, `p^{6f₁}−1`) | **[LIT: Zsygmondy 1892]** |
| C4 | `|Out| = d·f·g`, the order and parabolic-index formulas | **[LIT: Kleidman–Liebeck; Atlas]**, GAP-checked |
| C5 | CFSG order theorem (`{A₈, L₃(4)}`, `{Bₙ, Cₙ}` only) | **[LIT: Artin; KLST]** |
| C6 | Lemma C, `|Out|ι ≤ |G|^{2/3}` | **[PROVEN, v_task52]** |
| C7 | Lemma TO′-0 + Lemma F (the orbit floor) | **[PROVEN, v_task42/v_task36]** |
| C8 | order transfer `D(T) ≅ D(S) ⟹ |T| = |S|` | **[LIT/formalised: Müller Satz 2.3.4]** |
| C9 | §4j–§4l reduction (Fitting-freeness a `D`-invariant) | **[PROVEN, this project]** |

---

## 10. Reproduce

```
python3 v_task55_l3_twins.py                    > v_task55_l3_twins_out.txt      # ~10 min
~/gap-4.16.0/gap -q -o 8g v_task55_l3_twins.g   > v_task55_l3_twins_g_out.txt    # ~3 min
```

Individual parts: `python3 v_task55_l3_twins.py 1` … `6`
(`40` = the exact equal-characteristic sweep; `6 <limit>` sets the census
range).
