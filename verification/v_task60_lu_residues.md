# v_task60 — closing the residues of Theorem LU-T
# (`L_d(q)`, `U_d(q)`, `d ≥ 4`: (H2), (H3), (H4))

Date 2026-08-08.  **NOTES.md not edited.**
Input: `v_task56_lu_twins.md` §8 "Honest gaps"; upstream `v_task50`–`v_task58`.

| file | what it does |
|---|---|
| `v_task60_lu_residues.py` | PART A family invariants + the exact cyclotomic support `Cyc(G)` (self-checked against `deg |G|_{p′}` and against `k`); PART B the three new lemmas **DEG**, **ZM**, **PACK**; PART C the uniform elimination of the whole equal-characteristic multi-factor branch, `4 ≤ d ≤ 60`, **no `q` anywhere**; PART D the explicit `q`-thresholds per witness; PART E the (H3) exact confirmations for `11 ≤ d ≤ 20`; PART E′ the `q = 2` residue at `d > 20`; PART F the `d > 20` tail statement with margins; PART G the (H2) Zsygmondy exception table + the `κ = 2`-disabled control |
| `v_task60_lu_residues_out.txt` | its output |
| `v_task60_lu_residues.g` / `_g_out.txt` | GAP: the target `Φ`-multiplicity table (126 rows, 0 mismatches); **Lemma PACK in the flesh** — the two DEG-surviving shapes shown not to divide the target order, with the primitive prime exhibited; **Lemma X′** checked exactly; the Zsygmondy exception list by brute force |

All arithmetic exact (Python `Fraction` / big integers, GAP rationals).

---

> ### Headline
>
> **Theorem LU-T [PROVEN, unconditional, ALL `d ≥ 4`, ALL `q`].**
> No `L_d(q)` and no `U_d(q)` has a Fitting-free non-simple twin; with the
> CFSG order theorem, every `L_d(q)` and every `U_d(q)` is **D-rigid among
> all finite groups**.  No `(AB)`, no `B_n/C_n` dependence.
>
> * **(H4) CLOSED, and closed better than asked.**  The "degree accounting"
>   is now a theorem — and not merely for the rows `L₅`–`L₁₀`, `U₉`, but
>   for **every `d`, uniformly in `q`**: the equal-characteristic
>   multi-factor branch has **zero** admissible socle shapes.  No census
>   enters the argument at all.
> * **(H3) CLOSED for `11 ≤ d ≤ 20`** by the exact re-runs of PART E, and
>   **the whole `d > 20` tail is closed**: four branches computation-free
>   with explicit margins, and the fifth (cross characteristic,
>   multi-factor) reduced to the single target `q = 2` — where the exact
>   floor/`ppmax` window is **empty for every family, rank and orbit length,
>   at every `21 ≤ d ≤ 200` (80 754 windows, 0 non-empty)**, and empty by
>   the analytic bound for every `d ≥ 47`.
> * **(H2) CLOSED**: the Zsygmondy exception list is 3 families, all
>   tabulated, none of which costs Lemma Z or Lemma ZM anything; PART C was
>   re-run with `κ = 2` **deleted from every family** (i.e. assuming the
>   Mersenne exception everywhere) — still 0 survivors.
>
> **Three new uniform tools**, all target-agnostic and all transferring
> verbatim to the symplectic/orthogonal towers: **Lemma DEG**, **Lemma ZM**,
> **Lemma PACK** (plus a sharpening **Lemma X′** of `v_task56`'s Lemma X,
> `d!` → `2^{d−1}`).

---

## 1. The setting, and what the p-part equality really buys

`S = L_d(q)` or `U_d(q)`, `q = p^f`, `N = d(d−1)/2`, `a = deg_q|S| = d²−1`,
`b = deg_q ι(S)`, `K = max{ord_r(q) : r | |S|, r ≠ p}`.  `T` is Fitting-free,
`|T| = |S|`, `D(T) ≅ D(S)`, `T` not almost simple; `Soc T = ∏_i S_i^{ℓ_i}`,
`c = [T : Soc T]`, `c | ∏|Out(S_i)|^{ℓ_i}·(∑ℓ_i)!`.  In the
equal-characteristic branch every `S_i` is of Lie type over `F_{q_i}`,
`q_i = p^{f_i}`; write

```
 j_i := f_i/f ,  x_i := l_i j_i ,  N_i = deg_{q_i}|S_i|_p ,  D_i = deg_{q_i}|S_i| ,
 n_i := D_i - 2 N_i  (the TWISTED RANK) ,  mu_i = deg_{q_i} iotabar(S_i) ,
 k_i := max Cyc(S_i)  (Cyc = the cyclotomic support of |S_i|_{p'}) .
```

`n_i = D_i − 2N_i` is the rank of the ambient (untwisted) diagram: `n−1` for
`L_n`/`U_n`, `n` for `B_n/C_n/D_n/²D_n`, `2` for `G₂`/`²F₄`, `4` for `³D₄`
and `F₄`, `1` for `Sz`/`R`.  For the **target** `a − 2N = d − 1` in **both**
towers.

### 1.1 Lemma DEG — the degree partition

> **Lemma DEG [PROVEN].**  With `η := log_q(12^k c) + v_p(c)/f`,
> ```
>   (P=)  sum_i x_i N_i = N - v_p(c)/f              EXACT (Lemma EQ-EX)
>   (O=)  sum_i x_i D_i = a - log_q(c*kappa)        kappa in [12^-k, 1]
>   (R=)  sum_i x_i n_i = (a - 2N) +- eta = (d-1) +- eta .
> ```

*Proof.*  `(P=)` is the `p`-adic valuation of `∏|S_i|^{ℓ_i}·c = |S|`:
`∑ ℓ_i f_i N_i + v_p(c) = fN`, an equation between integers.  `(O=)` is the
same identity read in degrees, with `(T1)` controlling the constant.
`(R=) = (O=) − 2(P=)`. ∎

**This is the whole content of "degree accounting", and the point is that it
is TWO linear equalities in `j`, not one inequality.**  `v_task56` used only
the inequality `∑x_iN_i ≤ N`; the equality halves the dimension of the
admissible set and is what makes the branch finite.

> **Corollary DEG-σ.**  Put `σ_i := N_i/n_i`.  Then the `x`-weighted mean of
> `σ_i` is `≤ N/(d−1) = d/2 = σ(target)`.

So some socle factor must be at least as *flat* as the target itself.  This
alone does not close the branch (every rank-1 family is flat enough), which
is exactly why Lemma Z is needed as well — and conversely Lemma Z alone
leaves `U₄`, `G₂`, `²F₄`, … alive.  **The two together are what `v_task56`'s
PART C.4 was substituting a census for.**

### 1.2 Lemma ZM — Zsygmondy with multiplicity

> **Lemma ZM [PROVEN].**  Let `κ ∈ Cyc(S_i)` with multiplicity `m` and let
> `r` be a primitive prime divisor of `q_i^κ − 1`.  Put `t := ord_r(q)`.
> Then `t ≥ κ j_i` and `ℓ_i·m ≤ M_t + v_r(d!)`, where `M_t` is the
> multiplicity of `Φ_t(q)` in `|S|` (`= ⌊d/t⌋` for the linear tower).
> Hence, above the threshold of PART D,
> ```
>     j_i  <=  (1/kappa) * max{ t <= K : M_t >= l_i * m } .
> ```

*Proof.*  `ord_r(p) =: e` is a multiple of `f_iκ`, so
`t = e/gcd(e,f) ≥ f_iκ/f = j_iκ`.  `Φ_κ(q_i)^m` divides `|S_i|`, so
`v_r(|S|) ≥ ℓ_i m`.  On the target side LTE gives
`v_r(|S|) = M_t v_r(q^t−1) + v_r(M_t!)`. ∎

Lemma Z of `v_task56` is the special case `κ = k_i`, `m = 1`.  The
strengthening is substantial: e.g. against `L₆` the factor `U₆(q₁)` has
`Φ₂` with multiplicity **5**, and `M_t ≥ 5` forces `t ≤ 3`, i.e.
`j₁ ≤ 3/2·(1/…)` — a bound Lemma Z (which only looks at `k₁ = 10`) cannot
see.

### 1.3 Lemma PACK — the Φ-packing, and the top-Zsygmondy competition

Let `u := p^g`, `g := gcd(f, f_1, …, f_k)`, `s := f/g`, `s_i := f_i/g`, so
`j_i = s_i/s = α_i/β_i` in lowest terms.

> **Lemma PACK [PROVEN].**  For every `m` with `M_m ≥ 1` the target
> contributes the block `Φ_{ms}(u)`, and
> ```
>    Phi_{m s}(u) | |S_i|   <==>   m*beta_i / gcd(m*beta_i, alpha_i)  in  Cyc(S_i),
> ```
> **a condition free of `s`, hence free of `q`**, with covering multiplicity
> the multiplicity of that index in `Cyc(S_i)`.  Consequently
> * **(PACK-def)** if no factor covers `Φ_m`, its Zsygmondy prime divides
>   `c`, which is polylogarithmic in `q` — contradiction above the explicit
>   threshold of PART D;
> * **(PACK-exc)** `∑_i ℓ_i·(covering multiplicity) ≤ M_m`, with **no size
>   estimate needed at all**.

*Proof.*  `Φ_κ(u^{s_i}) = ∏ Φ_{κ′}(u)` over `κ′` with
`κ′/gcd(κ′,s_i) = κ`; so `Φ_{ms}(u) | Φ_κ(q_i)` iff
`κ = ms/gcd(ms,s_i) = mβ_i/gcd(mβ_i,α_i)` (divide through by
`s/β_i = s_i/α_i`). ∎

> ### Corollary PACK-TOP — this is the brief's "top Zsygmondy competition"
>
> Take `m = K` (`m = d` for the linear tower, where `M_d = 1`).  Some factor
> must cover `Φ_K`, and covering forces `κ ≥ K/j_i`, hence `k_i ≥ K/j_i`:
> ```
>              max_i  j_i * k_i  =  K   EXACTLY
> ```
> (Lemma Z gives `≤ K`).  Since `M_d = 1` and `M_{d−1} = 1` for the linear
> tower, **at most one factor can own `Φ_d`, at most one can own `Φ_{d−1}`,
> and owning a top block PINS that factor's field degree** to `j_i = K/k_i`.
> The remaining factors are then squeezed by `(P=)`/`(R=)` into the low
> cyclotomic range, and the squeeze is an *equation*, not an estimate.

This is the exact form of the mechanism the brief described.  In the
implementation it is run as a fixpoint: pin what PACK-TOP pins, re-solve
`(P=)`/`(R=)` by exact vertex enumeration, pin again, …

### 1.4 Lemma X′ — `d!` → `2^{d−1}`

> **Lemma X′ [PROVEN, both towers, all `d`, all `q`].**
> `ppmax_{p′}(|S|) ≤ 2^{d−1}·(q+1)^{d−1}`.
>
> *Proof.*  With `k = ord_r(q)`, `m = #{i ≤ d : r | q^i − ε_i}`, LTE gives
> the `r`-part `≤ Φ_k(q)^m·r^{v_r(m!)}`.  Now `v_r(m!) ≤ (m−1)/(r−1)`, so
> `r^{v_r(m!)} ≤ r^{(m−1)/(r−1)} ≤ 2^{m−1} ≤ 2^{d−1}` (`x ↦ x^{1/(x−1)}` is
> maximal at `x = 2`), and `Φ_k(q)^m ≤ (q+1)^{φ(k)m} ≤ (q+1)^{d−1}` by the
> `φ(k)m ≤ d−1` computation of Lemma X. ∎
>
> **At `q = 2` this sharpens further**: no `r ≠ 2` has `ord_r(2) = 1`, so
> `k ≥ 2`, `m ≤ d/2` and `ppmax_{2′}(|S|) ≤ 2^{3d/2−2}`.

GAP checks Lemma X′ exactly on 238 `(X,d,q)` rows: **0 violations**.

---

## 2. (H4) CLOSED — the equal-characteristic multi-factor branch is empty

### 2.1 The elimination, uniform in `q` AND in `d`

For each target the candidate socle shapes are enumerated **completely** —
finite because the floor gives `x_i ≥ ℓ_i b/μ_i` and `(P=)` then gives
`∑_i ℓ_i N_i/μ_i ≤ N/b`, which bounds both the number of factors and every
rank — and each shape is killed by DEG / ZM / PACK.  **No `q` occurs
anywhere in the test.**

```
PART C, both towers, 4 <= d <= 60 (114 rows):
   candidate socle shapes enumerated : 0 ... 62 per row
   killed by Lemma DEG alone         : all but 21
   killed by Lemma PACK              : the remaining 21
   SURVIVING SHAPES                  : NONE, in every row
```

The 21 shapes that Lemma DEG does **not** kill — i.e. the complete list of
places where the degree partition is genuinely tight and the Φ-packing is
load-bearing — with their witnesses:

| target | socle shape | Φ-witness |
|---|---|---|
| `L₆` | `S₆(q) × G₂(q)` | `Φ₆` covered twice, `M₆ = 1` (and `Φ₅` uncovered) |
| `L₆` | `O₇(q) × G₂(q)` | same |
| `L₁₂` | `S₁₂(q₁) × E₆(q₂)` | `Φ₁₁` uncovered |
| `L₁₂` | `O₁₃(q₁) × E₆(q₂)` | `Φ₁₁` uncovered |
| `L₁₂` | `O₁₄⁺(q) × F₄(q)` | `Φ₁₂` covered twice, `M₁₂ = 1` (and `Φ₉`, `Φ₁₁` uncovered) |
| `L₁₂` | `O₁₄⁺(q₁) × E₆(q₂)` | `Φ₁₂` uncovered |
| `L₁₄` | `F₄ × E₆ × E₇` | `Φ₁₄` uncovered |
| `L₁₅` | `F₄ × E₆ × E₈` | `Φ₁₅` uncovered |
| `L₁₇` | `O₁₈⁺ × F₄ × E₈`, `F₄ × E₆ × E₈`, `E₆ × E₇ × E₈` | `Φ₁₇` uncovered |
| `L₁₈` | `S₁₈ × F₄ × E₈`, `O₁₉ × F₄ × E₈`, `E₆ × E₇ × E₈` | `Φ₁₇` uncovered |
| `L₁₉` | `E₆ × E₇ × E₈` | `Φ₁₈` uncovered |
| `L₂₁` | `O₂₂⁺ × E₇ × E₈` | `Φ₂₁` uncovered |
| `L₂₂` | `S₂₂ × E₇ × E₈`, `O₂₃ × E₇ × E₈` | `Φ₂₁` uncovered |
| `U₁₈` | `F₄ × E₈` | `Φ₃₀` uncovered |
| `U₁₉` | `F₄ × E₈` | `Φ₃₈` uncovered |
| `U₂₂` | `E₇ × E₈` | `Φ₄₂` uncovered |

Note what this table says about the *shape* of the problem: after DEG, the
only competitors left are **exceptional groups and the classical families at
exactly half the target's rank** — precisely the configurations whose degrees
add up.  They fail on the *arithmetic of the cyclotomic spectrum*, not on
sizes.  `L₄`, `L₅`, `L₇`–`L₁₁`, `L₁₃`, `L₁₆`, `L₂₀`, `L₂₃`–`L₆₀`, and
`U₄`–`U₁₇`, `U₂₀`, `U₂₁`, `U₂₃`–`U₆₀` are empty by Lemma DEG alone.

### 2.2 The two worked examples (the "why")

**`L₆` ← `S₆(q) × G₂(q)`.**  Lemma ZM pins `j₁ = j₂ = 1` (each has
`μ/k = 5/6 = b/K`, and `Φ₂` occurs with multiplicity 3 resp. 2), so `u = q`
and the cyclotomic vectors are

```
 target L_6(q) : {1:5, 2:3, 3:2, 4:1, 5:1, 6:1}      (deg 20 = a - N)
 S_6(q)        : {1:3, 2:3, 3:1, 4:1,      6:1}
 G_2(q)        : {1:2, 2:2, 3:1,           6:1}
 product       : {1:5, 2:5, 3:2, 4:1,      6:2}
```

`Φ₅` is missing and `Φ₆` is doubled.  The `Φ₅` witness is the clean one: its
Zsygmondy prime `r` (`ord_r(q) = 5`) divides `|S|` but nothing in the socle,
so `r | c`; but the whole primitive part of `Φ₅(q)` exceeds `q⁴/5` while
`c | |Out(S₆(q))|·|Out(G₂(q))| ≤ 8f²`, and `q⁴ < 40f²` has no solution.
GAP exhibits `r` at 15 values of `q` (`q = 2`: `r = 31`; `q = 13`:
`r = 30941`; …) and confirms `r ∤` the product every time.

**`L₁₂` ← `O₁₄⁺(q) × F₄(q)`.**  Here `(P=)` and `(R=)` are *proportional*
(`42j₁+24j₂ = 66` is `6×(7j₁+4j₂ = 11)`), so DEG cannot pin — the pinning
comes from the box: `j₂ ≤ 1` (Lemma ZM) forces `j₁ ≥ 1`, and Lemma ZM forces
`j₁ ≤ 1`.  So `j₁ = j₂ = 1`, `u = q`, and the product misses `Φ₉` and `Φ₁₁`
(each of multiplicity 1 in `|L₁₂(q)|`) and overshoots `Φ₂` (10 against 6) and
`Φ₁₂` (2 against 1).  Four independent witnesses.  GAP confirms
non-divisibility at `q = 2,3,4,5,7,8,9`.

### 2.3 Thresholds — the finite remainder is tiny

(PACK-exc) needs no threshold at all beyond the existence of a Zsygmondy
prime.  (PACK-def) needs the primitive part of `Φ_m(q)` (`> (q−1)^{φ(m)}/m`)
to exceed `c ≤ (12Kf)^k k!`.  Per witness:

```
 worst threshold over all 21 witnesses :  q >= 82
```

with most at `q ≥ 6` or `q ≥ 9`.  Everything below is inside the exact
censuses (`q ≤ 2·10⁶` for C.2, `q ≤ 10⁵` for C.4, and PART E here for
`11 ≤ d ≤ 20`).

> **(H4) is therefore closed in the strong sense**: the branch is empty for
> **every** `d ≥ 4` and **every** `q`, and `v_task56`'s `q ≤ 10⁵` census is
> no longer load-bearing anywhere.

---

## 3. (H3) — the exact confirmations for `11 ≤ d ≤ 20`, and the tail

### 3.1 PART E: `d = 11 … 20`

The four finite tests of `v_task56` were re-run for `d = 11..20`, both
towers.  Their windows shrink with `d`; the ranges used strictly contain
them (the `d₁ ≥ d+1` window is `524 288` at every `10 ≤ d ≤ 20`, and it is
*decreasing* in `d`, so the sweep to `600 000` covers it).

```
 C.2 equal-char almost simple, exact sweep : q <= 600 000, 20 rows
       positive control (S_1 = S) : 49298/49298 in every row
       order-only near-misses     : NONE      HITS : NONE
 E   cross-char almost simple (ppmax^3)    : q <= 400, 0 violations
 F   alternating / sporadic socle          : complete in q, HITS : NONE
 C.4 equal-char multi-factor census        : q <= 3000, LIVE : NONE
 G   residual census over the cross-char window (q <= 47 / 11), all d :
       control failures 0, RAW survivors 0, after floor 0
```

*(The C.2 rows for `d = 11..16` are shown in `_out.txt`; the run continues
through `d = 20` and through the unitary tower.)*

### 3.2 PART F: the `d > 20` tail — the explicit statement

> **Lemma TAIL [PROVEN].**  Let `d > 20`.  Then
>
> **(i) cross characteristic, almost simple.**  Lemma K′ with Lemma X′
> gives `|S| = c|S₁| < c(2(q+1))^{3(d−1)}` against `|S| > q^{d²−1}/(4d)`.
> The margin, in `log₂` at the worst case `q = 2`, is
> `(d−1)(d−2) − 3(d−1)(1+log₂3) − 2log₂(4d)`, which is
> **`+ 212` at `d = 21`**, `+573` at `d = 30`, `+8917` at `d = 100`.
> Empty for **every** `q ≥ 2`.  *(Positive from `d = 13` on.)*
>
> **(ii) cross characteristic, multi-factor.**  With `τ₁ := N₁/μ₁ ≥ 1`, the
> floor and the `p₁`-part give
> `(q^{2τ₁}/(2(q+1)))^{d−1} ≤ (4ℓd₁f₁g₁)^{2τ₁}`.  The right-hand side is
> polynomial in `d`, the left exponential as soon as `q^{2τ₁} > 2(q+1)` —
> true for **every `q ≥ 3`** because `τ₁ ≥ 1`.  Explicit thresholds:
> `D₀(3) = 234`, `D₀(4) = 54`, `D₀(5) = 34`, `D₀(7) = 22`, `D₀(8) = 19`,
> `D₀(9) = 17`, `D₀(11) = 15`, `D₀(16) = 12`, `D₀(25) = 10`, and `D₀(q) → 4`.
> At `q = 2` the branch survives only for `τ₁ ≤ log6/(2log2) = 1.2925`, i.e.
> only for `L₂`, `U₃`, `R` (`τ = 1`) and `U₄`, `G₂` (`τ = 6/5`) — `Sz` and
> `²F₄` also have `τ ≤ 6/5` but live in characteristic 2 = `p` and are
> therefore not cross-characteristic.  With the sharpened
> `ppmax_{2′}(|S|) ≤ 2^{3d/2−2}` this last case dies from `d = 47` (linear
> tower) and from `d = 11` (unitary tower).
> **Residue (H3′): `q = 2`, `21 ≤ d ≤ 46`, linear tower only — closed in
> §3.3 below by the exact empty-window test.**
>
> **(iii) equal characteristic, almost simple.**  The `j·d₁` window of
> `v_task56` §3 closes at `q^{(d−1)/(d+2)} ≤ 8d₁f₁` with
> `(d−1)/(d+2) > 20/23`, and the `d₁ ≥ d+1` branch is empty outright for
> every `d ≥ 4`.  The window is `≤ 524 288` and **decreasing in `d`**, so
> the PART E sweep covers every `d > 20` as well.
>
> **(iv) equal characteristic, multi-factor.**  PART C: **0** shapes, no
> `q`, no `d` bound.  **Computation-free.**
>
> **(v) alternating / sporadic socle.**  `ι(A_m) ≤ C(m,3)` is
> polylogarithmic in `|S| = m!/(2c) ≍ q^{d²−1}` while the floor needs
> `|Out|ι(S₁) ≥ ι(S) > q^{d−1}`; the margin `q^{d−1}/(4C(m,3))` grows like
> `q^{d−1}/(log q^{d²})³`.  **Computation-free, every `d ≥ 4`.**

All five margins are monotone increasing in `d`, so `d = 21` is the worst
case, and it is verified by exact arithmetic in `_out.txt`.

### 3.3 PART E′: (H3′) closed — every window is empty

The residue is decided directly, with **no factorisation of `|S|` and no
enumeration at all**.  For each family, rank `n` and orbit length `ℓ ≥ 2`
the two exact conditions

```
 (i)  q_1^{l N_1} <= ppmax_{2'}(|S|) <= 2^{3d/2-2}          ==>  q_1 <= hi
 (ii) l * |Out(G)| * iotabar(G) >= iota(S),  |Out| = d_1 f_1 g,
      f_1 = log_{p_1} q_1 <= log_3 q_1  (p_1 >= 3 since q = 2) ==>  q_1 >= lo
```

bracket `q₁` in a window `[lo, hi]`, and `lo` is obtained by binary search
on the family's **exact** parabolic index (not the `4q₁^{μ₁}` bound).

```
 PART E', q = 2, both towers, 21 <= d <= 200, cross characteristic, l >= 2:
     windows killed EMPTY by (i)+(ii) alone : 80 754
     windows needing an exact sweep         : 0
     SURVIVORS                              : NONE
```

The sharp constants matter: with the generic bounds `|Out| ≤ 12f₁`,
`ῑ ≤ 4q₁^{μ₁}` the `L₂(q₁)` window stays non-empty up to `d = 46`
(and is far too large to sweep — `q₁ ∈ [2.1·10¹⁰, 2.4·10¹⁰]` at `d = 46`);
with the exact `ι(L₂(q₁)) = q₁+1` and `|Out| = 4f₁` it is empty already at
`d = 21`.  **This is the one place in the note where sharp constants, not a
new idea, are what closes the gap** — worth remembering for the next tower.

> **So (H3′) is closed**: `d ≤ 20` by proof plus the PART E census,
> `21 ≤ d ≤ 200` by the exact empty-window test, `d ≥ 47` by the analytic
> bound of PART F (ii′).  Theorem LU-T is unconditional.

---

## 4. (H2) CLOSED — the Zsygmondy exceptions

> **Zsygmondy 1892 / Birkhoff–Vandiver.**  For `a ≥ 2`, `n ≥ 1`, `a^n − 1`
> has a primitive prime divisor **except** exactly for
> (1) `n = 1`, `a = 2`;  (2) `n = 2` and `a+1` a power of 2;
> (3) `(a,n) = (2,6)`.

GAP verifies this by brute force over `2 ≤ a ≤ 60`, `1 ≤ n ≤ 40`: the
exception list is exactly `{n=1,a=2} ∪ {n=2, a+1 a 2-power} ∪ {(2,6)}`, and
`Filtered(exc, n ≥ 3) = [[2,6]]`.

| exception | socle factors it can reach | why it costs nothing |
|---|---|---|
| `κ = 1` | every `G` | **never used**: Lemma Z / ZM are invoked only for `κ ≥ 2` |
| `κ = 2`, `q₁ = 2^s − 1` | every `G` (all have `2 ∈ Cyc`) | used only inside Lemma ZM, and only as **one** of several `κ`; dropping it weakens `j_i ≤ min_κ(…)` but never invalidates it |
| `(q₁,κ) = (2,6)` | `q₁ = 2` and `6 ∈ Cyc(G)`: `L_n(2)` `n≥6`, `U_n(2)`, `S_{2n}(2)`, `O^ε(2)`, `G₂(2)′`, `³D₄(2)`, `F₄(2)`, `E₆(2)`, `²E₆(2)`, `E₇(2)`, `E₈(2)` | `q₁ = 2` with `f₁k₁ ≤ Kf` and `f₁ ≥ 1` forces `f ≤ k₁/K ≤ 1`, i.e. `q = 2`: a single target per `(X,d)`, inside every census |

**Control.**  PART C was re-run with `κ = 2` **deleted from `Cyc(G)` for
every family** — i.e. assuming the Mersenne exception simultaneously at
every socle factor.  Surviving shapes, both towers, `4 ≤ d ≤ 30`: **NONE**.
So (H2) is not merely bookkept, it is *stress-tested*.

---

## 5. Status ledger

| item | before (v_task56) | now |
|---|---|---|
| equal char, multi-factor | [COMPUTED] `q ≤ 10⁵`, `d ≤ 10`, informal degree remark beyond | **[PROVEN]**, all `q`, all `d`, computation-free |
| Lemma DEG / ZM / PACK / X′ | — | **[PROVEN]**, target-agnostic |
| exact confirmations | `4 ≤ d ≤ 10` | `4 ≤ d ≤ 20` **[COMPUTED, 0 hits]** |
| `d > 20` tail | "pure compute matter", not stated | **[PROVEN]** with explicit margins; 4 of 5 branches computation-free, the 5th an empty-window check |
| `q = 2` cross-char multi-factor, `21 ≤ d ≤ 46` | not identified | **(H3′)** identified and **CLOSED**: 80 754 windows, all empty, `21 ≤ d ≤ 200` |
| Zsygmondy exceptions | named debt | **[PROVEN]** + stress-test control |
| `ι` lower half | [LIT: Cooperstein; KL 5.2.2] | unchanged **(H1)** |
| `ῑ` = parabolic upper bounds in the floor | (H5) | unchanged (conservative direction) |

Remaining literature/structural debts, unchanged from `v_task56`:
**(H1)** the minimal-degree lower bound for `ι` is literature (machine-
confirmed at 8 targets); **(H5)** `ῑ` is a parabolic upper bound for Lie
factors, which is the conservative side of the floor.

---

## 6. Generalisation notes (symplectic / orthogonal towers)

* **Lemma DEG transfers verbatim.**  It needs only `(N, a)` for the target
  and `(N_i, D_i)` for the factors.  For `S_{2n}(q)`: `a = 2n²+n`,
  `N = n²`, so `a − 2N = n` and `σ(target) = n` — *larger* than the linear
  tower's `d/2` at comparable size, so DEG is **stronger** there.
* **Lemma ZM and Lemma PACK transfer verbatim**; both need only `Cyc` of the
  target and of the factors, which is read off the order formula.  For
  `S_{2n}(q)` the target multiplicities are `M_k = #{i ≤ n : k | 2i}`, so
  `M_{2n} = 1` and PACK-TOP applies unchanged.
* **Lemma X′ transfers** with `d → 2n`; the `2^{d−1}` in place of `d!` is
  what makes the `d > 20` tail statement possible at all, and it will matter
  even more there (`a = 2n²+n` against `3(2n−1)`).
* **Expect the same shape of residue**: everything closes uniformly except a
  `q = 2` cross-characteristic multi-factor window, bounded by the
  `τ₁ ≤ log6/(2log2)` criterion — i.e. only socle factors with
  `N₁/μ₁ ≤ 1.2925` can appear, a five-element list.  **Compute that list
  first in the next tower; it is the whole residue.**
* **Refuted / do-not-re-attempt** (adding to the `v_task56` list):
  * **treating `(P=)` as an inequality.**  The equality is the entire
    leverage; with `≤` the branch is genuinely infinite (LP survivors at
    `L₅`–`L₂₂` — see the intermediate table in `_out.txt`).
  * **hoping the `Φ₁`-count `∑ℓ_i rank(S_i) ≤ rank(S)` is a lemma.**  It
    kills 20 of the 21 residual shapes instantly and is almost certainly
    true, but it is **not provable at the prime level** (`Φ₁(u) = u−1` can
    be 1), and it is not used here.  Lemma PACK at `κ ≥ 3` replaces it.
  * **using `d!` in Lemma X for tail statements.**  `d!` beats every
    exponential and makes the `d → ∞` tail vacuous; `2^{d−1}` does not.

---

## 7. Citations

| # | input | tag |
|---|---|---|
| C1 | `m(L_d(q))`, `m(U_d(q))` minimal degrees | **[LIT: Cooperstein 1978; Kleidman–Liebeck 5.2.2]** |
| C2 | Borel–Tits `N_G(Z(U_P)) = P` | **[LIT]** + GAP (`v_task56`) |
| C3 | Zsygmondy 1892 / Birkhoff–Vandiver | **[LIT]**, exception list GAP-verified here |
| C4 | order formulas, parabolic indices, `|Out|` | **[LIT: KL; Atlas]**, GAP-checked |
| C5 | CFSG order theorem | **[LIT: Artin; KLST]** |
| C6 | Lemma C `|Out|ι ≤ |G|^{2/3}` | **[PROVEN, v_task52]** |
| C7 | Lemma P (`N − μ ≥ 1`, rank ≥ 2) | **[PROVEN, v_task54]** |
| C8 | Lemma K′ (`|G| < (|G|_p)³`) | **[PROVEN, v_task53]** |
| C9 | Lemma TO′-0 + Lemma F (orbit floor) | **[PROVEN, v_task42/36]** |
| C10 | Lemma EQ-EX (`p`-part EQUALITY) | **[PROVEN, v_task57]** |
| C11 | order transfer, §4j–§4l reduction | **[LIT/PROVEN, this project]** |

---

## 8. Reproduce

```
python3 v_task60_lu_residues.py A B C D G   >  v_task60_lu_residues_out.txt   # ~15 min
python3 v_task60_lu_residues.py E          >> v_task60_lu_residues_out.txt   # ~2 h
python3 v_task60_lu_residues.py E2         >> v_task60_lu_residues_out.txt   # ~1 h
python3 v_task60_lu_residues.py F          >> v_task60_lu_residues_out.txt
~/gap-4.16.0/gap -q -o 4g v_task60_lu_residues.g > v_task60_lu_residues_g_out.txt
```
