# v_task46 — can an effective bound *uniform in the multiplier* close rows 2
# and 3 of Theorem AT?

Date 2026-08-08.  **NOTES.md not edited.**

Scripts / outputs in this directory:

| file | what it does |
|---|---|
| `v_task46_ec.sage` / `v_task46_ec_out.txt` | integral points of `C_c : k³−k = c(q²+q+1)` (via `E_c : Y² = X³ − 16c²X − 48c⁴` plus the divisibility `4c∣X`) for every admissible `c ≤ 216`; the decisive size comparison against the hypothetical solution point; Lang- and Hall-type checks |
| `v_task46_sizes.py` / `v_task46_sizes_out.txt` | certification of the new effective size lemmas (MASTER, SIZE-UP, Q-LB, SM) and of the elementary facts they rest on; the `q > n` crossover arithmetic |

---

## 0.  Verdict, stated first

> **(a) Row 2 does NOT close by any effective uniform-in-`c` Diophantine
> bound — and this is not a matter of constants: the statement such a bound
> would have to prove is FALSE.**  The curve `C_c : k³−k = c(q²+q+1)` itself
> — *not* the ambient `E_c`, and with the task's divisibility `4c ∣ X`
> imposed — genuinely possesses integral points *larger* than the smallest
> point a row-2 solution could ever produce.  The cleanest witness is a single
> integer identity:
>
>   `1994³ − 1994 = 30·(16256² + 16256 + 1)`,   `log(4·30·1994) = 12.3854`,
>
> against a required `B(30) < 7.4955`.  Any correct `B(30)` is already too big
> by a factor of `1.65` in the logarithm.  This happens at `c = 24, 30, 72, 90,
> 102, 120, 168` — 7 of the 36 admissible `c ≤ 216` (§3, table).  Effective Diophantine geometry is dead on
> this row at the level of what is *true*, not of what is *provable*.
>
> **(b) The task's hoped-for instant kill (`q > n ⟹ p ∤ n!`) is real, and the
> crossover is `n ≥ 20`, not `3·10¹⁴` — but it only bites when `f = 1`, and
> the `f = 1` sub-rows are exactly the ones already dead (row 2) or provably
> out of reach of it (row 3).**  §2 proves `q > n` for row 2 for **every**
> `n ≥ 20`, **every** `f ≥ 2` and **every** `ℓ*`, with an explicit constant
> chase — a genuinely new effective statement.  There is **no gap to close**:
> the crossover sits nine orders of magnitude below the existing scan floor
> `10¹¹`.  But `q = p^f > n` with `f ≥ 2` gives only `p > n^{1/f}`, and
> `n^{1/f} ≤ n`, so no `p ∤ n!` contradiction follows.  In row 3 the same chain
> gives `q ≍ n^{2/3} < n` — the phenomenon does not even occur there.
>
> **(c) The factorisation route (`Φ_e(p^f)` splits for `f ≥ 2`) is correct but
> does not close anything.**  §4 works out the splitting exactly and derives
> the resulting rigid divisor system on `n(n−1)(n−2)`; it is a strong
> constraint with no contradiction in it.
>
> **(d) What is genuinely gained** (all `[PROVEN]`, all uniform in `ℓ*`, all new):
> the MASTER inequality; `SIZE-UP` (`N f (p−1) ≤ (n−1)/L_min`); the lower bound
> `q ≥ (f n²/8.1)^{f/(2f−1)}` and hence `q > n` in row 2 and `q < n` in row 3;
> the multiplier bound `c ≤ 3.19 n^{1/3}` in the `f = 2` sub-row (against
> v_task45's `c < 2.77 n/ln n` — an improvement from `n^{1−ε}` to `n^{1/3}`);
> and **Lemma SM**: in the `f = 2` sub-row of row 2, `n`, `n−1` and `n−2` are
> all `1.88 n^{2/3}`-smooth.
>
> **Both rows remain OPEN.**  The residue is unchanged in kind from v_task45,
> but the Diophantine escape route named there as option (i) is now
> **eliminated**, not merely "hard".  Only option (ii) — a new group-theoretic
> invariant (PSN-A / PSN-LIE-q) — survives.

---

## 1.  Setup and the live sub-rows

`M := n(n−1)(n−2)`, `k := n−1`, `c := 6 f₁ ℓ*` with `f₁ ∈ {1,2}`, `q = p^f`.

  **(R1)  `M = c · F(q)`,  `F = Φ_e`.**

| row | `S*` | `e` | `deg F` | `N := v_p(|S*|)/f` | `ℓ*` | gap |
|---|---|---|---|---|---|---|
| 2 | `L₃(q)` | 3 | 2 | 3 | `≥ 2` | `q ≥ f₁(n−3)` |
| 3 | `L₅(q)` | 5 | 4 | 10 | `≥ 1` | `q² ≥ n−3` |

Two proven inputs are used throughout:

* **(BP-p)** `ℓ*·N·f ≤ v_p(n!/2) ≤ v_p(n!)` — Lemma BP (v_task45 §2.1) at `r = p`,
  using `v_p(|L₃(p^f)|) = 3f`, `v_p(|L₅(p^f)|) = 10f`;
* **(LEG)** `v_p(n!) = (n − s_p(n))/(p−1) ≤ (n−1)/(p−1)` — Legendre
  (re-verified exhaustively for `p ≤ 200`, `n ≤ 20000`, `v_task46_sizes_out.txt` STEP 0).

### Which `(f, ℓ*)` sub-rows are live  [settled]

* **Row 2, `f = 1`: DEAD for all `n ≥ 5`, uniformly in `ℓ*`.**  This is Lemma
  R1-p (§4ax), and it *is* uniform in `ℓ*` — v_task44's row description already
  records `f ≥ 2`.  §2 re-derives it from SIZE-UP as a consistency check
  (`q ≤ (n+5)/6` versus the gap `q ≥ n−3`).
* **Row 2, `f ≥ 2`, `ℓ* ≥ 2`: LIVE.**  This is the whole of row 2.
* **Row 3, every `f ≥ 1`, every `ℓ* ≥ 1`: LIVE.**  In particular `q` prime is
  *not* excluded in row 3, and §2 shows why: there `q ≍ n^{2/3}`, so
  `v_q(n!) = ⌊n/q⌋ ≍ n^{1/3}`, comfortably above the required `10ℓ*`.

---

## 2.  PART A — the effective size lemmas  [PROVEN]

### 2.1  MASTER

From (R1), `c = M/F(q)`.  From (BP-p) and (LEG),
`c = 6f₁ℓ* ≤ 6f₁(n−1)/(N f (p−1))`.  Equating,

> **(MASTER)  `N f (p−1) · n(n−2)  ≤  6 f₁ · F(q)`.**

*Proof.* `M/F(q) ≤ 6f₁(n−1)/(Nf(p−1))` ⟹ `Nf(p−1)·n(n−1)(n−2) ≤ 6f₁(n−1)F(q)`;
cancel `n−1 > 0`. ∎

### 2.2  SIZE-UP

`c ≥ 6f₁L_min` (`L_min = 2` row 2, `1` row 3), so `F(q) = M/c ≤ M/(6f₁L_min)`.
Substituting into MASTER and cancelling `n(n−2)`:

> **(SIZE-UP)  `N f (p−1) ≤ (n−1)/L_min`**, i.e.
> row 2: `f(p−1) ≤ (n−1)/6`;  row 3: `f(p−1) ≤ (n−1)/10`.  ∎

Note this bounds `p` from **above** — a genuinely new direction; every previous
bound in the program bounded `q` from below.

*Consistency check (row 2, `f = 1`).* SIZE-UP reads `q − 1 ≤ (n−1)/6`, i.e.
`q ≤ (n+5)/6`, contradicting the gap `q ≥ f₁(n−3) ≥ n−3` as soon as
`6n−18 > n+5`, i.e. `n ≥ 5`.  Row 2 at `f = 1` is empty for every `n ≥ 5`,
uniformly in `ℓ*`.  ✔ (agrees with Lemma R1-p)

### 2.3  Q-LB — the lower bound on `q`, and the `q > n` crossover

In MASTER use `f₁ ≤ 2`, `p − 1 ≥ p/2 = q^{1/f}/2`, and
`F(q) = q²+q+1 ≤ K q²` with `K ≤ 1.01` (valid since `q ≥ n−3 ≥ 128` in the
relevant range), plus `n(n−2) ≥ 0.999 n²` for `n ≥ 40`:

  `3 f · (q^{1/f}/2) · 0.999 n² ≤ 12 K q²`

> **(Q-LB, row 2)  `q ≥ ( f n² / 8.1 )^{ f/(2f−1) }`.**

**The crossover arithmetic.**  `q > n` ⟺ `(f/(2f−1))(log f + 2 log n − log 8.1) > log n`
⟺ **`log n > f · log(8.1/f)`**.  The right side is maximised over `f ≥ 2` at
`f = 3`, where it equals `2.9798` (computed in `v_task46_sizes_out.txt` STEP 4:
`f=2: 2.7974`, `f=3: 2.9798`, `f=4: 2.8223`, `f=5: 2.4121`, negative from `f ≥ 9`).
Hence

> **Lemma Q  [PROVEN].**  In row 2, for every `n ≥ 20`, every `f ≥ 2` and every
> `ℓ* ≥ 2`: `q > n`.

*(The task anticipated a crossover near `3·10¹⁴`, from `q² ≥ n²ln n/33.24`.
That estimate loses the factor `f` and the `p−1` in (BP-p).  Feeding the
`p`-part filter into MASTER directly instead of through `(SZ′)` moves the
crossover to `n ≥ 20` — **there is no gap between the crossover and the
`n ≤ 10¹¹` scan; the gap was an artefact of the lossy chain.**)*

**But Lemma Q does not kill.**  The kill would need `p > n` so that
`v_p(n!) = 0` contradicts `p ∣ |S*| ∣ n!/2`.  With `f ≥ 2`, `q = p^f > n`
gives only `p > n^{1/f}`.  Concretely for `f = 2`, Q-LB gives
`p = √q ≥ 0.628 n^{2/3}` — large, but far below `n`, and
`v_p(n!) = ⌊n/p⌋ ≍ n^{1/3}` is ample for `6ℓ*`.  The instant kill is available
**only at `f = 1`, which is exactly the sub-row already dead in row 2**.

### 2.4  Consequences: `c` is small, and `M` is smooth

From `c = M/F(q) ≤ n³/q²` and Q-LB (`v_task46_sizes_out.txt` STEP 4):

| `f` | `q ≥` | `c ≤` |
|---|---|---|
| 2 | `0.394 n^{4/3}` | `6.46 n^{1/3}` |
| 3 | `0.551 n^{6/5}` | `3.29 n^{3/5}` |
| 4 | `0.668 n^{8/7}` | `2.24 n^{5/7}` |
| `f` | `(f n²/8.1)^{f/(2f−1)}` | `(8.1/f)^{2f/(2f−1)} n^{(2f−3)/(2f−1)}` |

A sharper route for `f = 2` (used in §3): `c ≤ f₁(n−1)/(p−1) ≤ 2(n−1)/(p−1)`
with `p ≥ 0.628 n^{2/3}` gives **`c ≤ 3.19 n^{1/3}`** (asymptotically `2/0.628`).
Compare v_task45's `(SZ′) c < 2.77 n/ln(n−3)`: this is a polynomial-order
improvement on the whole `f = 2` sub-row.

> **Lemma SM  [PROVEN].**  Let (R1) hold.  Then every prime `r ∣ M` with
> `r ≠ e` satisfies `r < 6f₁n/c + 1` **or** `r ≤ c`.
>
> *Proof.*  Corollary BP-1 (v_task45): `r ∣ |S*|` ⟹ `ℓ* ≤ v_r(n!) < n/(r−1)`
> ⟹ `r < n/ℓ* + 1 = 6f₁n/c + 1`.  `Φ_e(q)` divides `|S*|·e` (it divides
> `q^e−1`, only `gcd(e,q−1)` is lost to the centre), so every prime `r ≠ e`
> dividing `Φ_e(q)` obeys the same.  If instead `r ≥ 6f₁n/c + 1` then
> `v_r(Φ_e(q)) = 0`, so by (R1) `r^{v_r(M)} ∣ c`, whence `r ≤ c`. ∎
>
> **Corollary (row 2, `f = 2`).**  `c ≤ 3.19 n^{1/3}` gives
> `6f₁n/c ≥ 6n/c ≥ 1.88 n^{2/3} > c`, so **`n`, `n−1` and `n−2` are all
> `1.88 n^{2/3}`-smooth** (the script's conservative table prints
> `0.92 n^{2/3}` from the weaker `c ≤ 6.46 n^{1/3}`; either suffices).

Heuristically this alone has density `≈ (1 − ln(3/2))³ ≈ 0.21`; stacked on
Theorem W's `(log n)^{−3/2}` it is another constant-factor squeeze, not a kill.

### 2.5  Row 3: the same machinery gives the *opposite* sign

With `N = 10`, `deg F = 4`, `F(q) ≤ 1.3 q⁴`, `L_min = 1`, MASTER gives
`q^{4−1/f} ≥ f n(n−2)/3.13`, i.e.

  `f = 1: q ≥ 0.684 n^{2/3}`;  `f = 2: q ≥ 0.880 n^{4/7}`;  `f ≥ 3: q ≍ n^{2f/(4f−1)}`,

**exponent always `< 1`**.  Together with SIZE-UP (`10f(p−1) ≤ n−1`) the two
bounds are compatible for every `n > 314` (at `f = 1`: `0.684 n^{2/3} < n/10`
⟺ `n > 314`).  So in row 3, `q < n` always, `p ≤ q < n`, and **no `p ∤ n!`
contradiction exists at any `f`, including `f = 1`.**  The `q ≍ n^{2/3}`,
`c ≍ n^{1/3}` regime is internally consistent; this is why row 3's `f = 1`
sub-row survives while row 2's does not.

---

## 3.  PART B — the quantitative feasibility audit: the uniform bound is FALSE

Row 2 in Weierstrass form (v_task44): `E_c : Y² = X³ − 16c²X − 48c⁴` with
`X = 4ck = 4c(n−1)`, `Y = 4c²(2q+1)`.

**The task's structural observation is correct and is honoured here.**  The
solution is *not* a generic integral point of `E_c`: it satisfies the
divisibilities `4c ∣ X`, `4c² ∣ Y`, `Y/(4c²)` odd — equivalently it is an
integral point of the *original* curve

  `C_c : k³ − k = c(q²+q+1)`   (`X = 4ck`, `Y = 4c²(2q+1)`;
   the task's substitution `V² = 4c(U³−U) − 3c²` is the same locus).

The audit below is therefore run **on `C_c`, not on `E_c`** — i.e. on the
divisible sublocus only.  This matters: at `c = 36` the large integral point of
`E₃₆` (`X = 20628868`) does **not** satisfy `4c ∣ X`, so `c = 36` is *not* a
counterexample and is excluded.  Restricting to `C_c` is exactly the
strengthening the task asked for, and the route still fails.

A uniform-in-`c` effective bound closes the row for all `n ≥ N₀` iff there is
`B(c)` with

* **(i) correctness**: `log|X(P)| ≤ B(c)` for *every* integral point `P` of `C_c`;
* **(ii) strength**: `B(c) < log(4c(n−1))` for every admissible `(c,n)`, `n ≥ N₀`.

For (ii) only the **smallest admissible `n` at a given `c`** matters.  Two
proven lower bounds on `n` in terms of `c`:

* **(n1)** `ℓ* < M/(6f₁³(n−3)²) < 1.13 n/6` for `n ≥ 40` (v_task44 §2.2, from the
  gap), so `c = 6f₁ℓ* < 1.13 f₁ n ≤ 2.26 n`, i.e. **`n > c/2.26`** — valid for
  every `f ≥ 2`;
* **(n2)** in the `f = 2` sub-row, `c ≤ 3.19 n^{1/3}` (§2.4), i.e. `n > c³/32.5`.

Since the row permits every `f ≥ 2`, the binding requirement is the weaker one:

  **(THRESHOLD-1)  `B(c) < log(4c · c/2) = 2 log c + 0.693`**

(using `n > c/2`, which is *more generous* than (n1)'s `c/2.26`; the honest
threshold `2 log c + 0.571` is smaller, so the verdicts below are conservative),
and, if one restricts to `f = 2`,

  **(THRESHOLD-2)  `B(c) < log(4c · c³/32.5) = 4 log c − 2.093`.**

`v_task46_ec.sage` computes, for every admissible `c ≤ 216` (`c ∈ 6Z`; `c = 222`
is where the rank computation stops terminating in a sane time), the
complete set of integral points of `E_c` (Sage `integral_points()`; rank by
2-descent, exhaustive elliptic-log search), filters it by the divisibility to
obtain the integral points of `C_c`, and **verifies each surviving `(k,q)` by
direct substitution into `k³−k = c(q²+q+1)`**.  Excerpt of
`v_task46_ec_out.txt`:

```
c     log c    #C_c-pts  max log|4ck|  witness (k,q)     THRESH-1  verdict1     THRESH-2  verdict2
6     1.792    2          3.8712       (2,0)              4.277    ok            5.074    ok
24    3.178    6          7.1293       (13,9)             7.049    IMPOSSIBLE   10.619    ok
30    3.401    6         12.3854       (1994,16256)       7.496    IMPOSSIBLE   11.512    IMPOSSIBLE
48    3.871    2          7.2034       (7,2)              8.435    ok          13.392    ok
60    4.094    4          8.4764       (20,11)            8.882    ok          14.284    ok
72    4.277    6          9.2739       (37,26)            9.246    IMPOSSIBLE  15.014    ok
78    4.357    2          9.3806       (38,26)            9.407    ok          15.334    ok
90    4.500    2         10.7839       (134,163)          9.693    IMPOSSIBLE  15.906    ok
102   4.625    4         12.5065       (662,1686)         9.943    IMPOSSIBLE  16.407    ok
120   4.787    6         11.7306       (259,380)         10.274    IMPOSSIBLE  16.636    ok
168   5.124    6         11.5007       (147,137)         10.941    IMPOSSIBLE  17.404    ok
```

(the remaining `c ≤ 216` have no integral point on `C_c` at all, or one too
small to matter).  **Totals: 7 of the 36 multipliers `c ≤ 216` violate
THRESHOLD-1; `c = 30` violates even the much laxer THRESHOLD-2.**

> **Theorem U (negative)  [PROVEN].**  There is no function `B(c)` satisfying
> (i) and (ii).
>
> *Witness, fully human-checkable.*  `c = 30` (`f₁ = 1`, `ℓ* = 5`) and
>
>   `1994³ − 1994 = 7928213790 = 30·264273793 = 30·(16256² + 16256 + 1)`.
>
> This is an integral point of `C₃₀` with `X = 4·30·1994 = 239280`,
> `log X = 12.3854`.  Correctness (i) forces `B(30) ≥ 12.3854`.  Strength (ii)
> requires `B(30) < 2 log 30 + log 2 = 7.4955` (row 2, all `f ≥ 2`), or, if one
> restricts to the `f = 2` sub-row, `B(30) < 4 log 30 − 2.093 = 11.5118`.
> **Both fail.** ∎
>
> `q = 16256 = 2⁷·127` is not a prime power, so this point is not an R1
> solution — *which is exactly the point*: an effective height bound cannot see
> the prime-power condition, so it must bound this point too, and doing so
> already makes it too weak.

The point is worth stating plainly, because it changes the character of the
obstruction recorded in v_task45 and §4az:

> The uniform effective bound does not fail because David-type constants are
> too weak.  **It fails because the statement it would have to prove is false.**
> `E_c` really does carry integral points bigger than any row-2 solution point
> could be.  The row-2 solution point, if it exists, is *not* an extremal point
> of `E_c` in any sense; it is an unremarkable one.

Two corroborating checks (`v_task46_ec_out.txt` PART 3):

* **Lang-type.**  `log|Δ(E_c)| = log|16(62208c⁸ − 16384c⁶)| ≈ 8 log c + 13.8`,
  while the solution point has `h(x) = log(4c(n−1)) ≥ 2 log c`.  The ratio
  `ĥ(P_sol)/log|Δ|` is bounded below by an absolute constant of the same order
  as the values `0.04 – 0.36` realised by the genuine integral points.  Lang's
  conjecture, even granted, is satisfied by the solution point with room to
  spare.
* **Hall-type.**  `|Y² − X³| = |16c²X + 48c⁴| ≍ c³ n ≍ X²·(stuff)` — of order
  `X²`, not `X^{1/2}`.  The point is nowhere near a Hall near-miss, so the
  ABC/Hall circle is mute as well.

**Row 3 by analogy.**  The same two-line argument applies verbatim at the level
of *any* height bound `B(c)` for points on the genus-3 quartic `C_c`: (n1)
gives `n > c/2.26` for row 3 too, so the solution point has height `≍ 2 log c`,
which is the generic scale for points on a curve with coefficients of size
`c`.  No effective bound can be that small and correct.  (Row 3 is worse still:
by v_task44 §2.4 the Jacobians are absolutely simple, so no such bound is even
computable member-by-member.)

---

## 4.  PART C — the factorisation route, worked out and honestly assessed

### 4.1  Lemma F  [PROVEN, classical]

> For `e` prime and `f ≥ 1`,
> `Φ_e(p^f) = (p^{ef}−1)/(p^f−1) = ∏_{d ∣ ef, d ∤ f} Φ_d(p)`.
> If `e ∤ f` the index set is `{ed : d ∣ f}` (so `τ(f)` factors); if
> `e ∣ f`, write `f = e^a f'` with `e ∤ f'`, and it is `{e^{a+1}d : d ∣ f'}`
> (so `τ(f')` factors).  The factors are pairwise coprime except that `e` may
> divide exactly one of them, to the first power only (Lemma Φ (F3)).
> `Φ_d(p) ≈ p^{φ(d)}`.

*Proof.* `x^{ef}−1 = ∏_{d∣ef}Φ_d(x)`, `x^f−1 = ∏_{d∣f}Φ_d(x)`; divide.
Coprimality: `gcd(Φ_a(p), Φ_b(p)) > 1` forces `a/b` to be a power of a prime
`r` and then `r ∣ Φ_a(p)` with `v_r ≤ 1`. ∎

So for `f ≥ 2` the right-hand side of (R1) is **never** irreducible.

### 4.2  The resulting divisor system, `e = 3`, `f = 2`

`Φ₃(p²) = Φ₃(p)·Φ₆(p) = A₂·A₁` with `A₂ = p²+p+1`, `A₁ = p²−p+1`,
`gcd(A₁,A₂) = 1` (their difference is `2p`, both are odd, and `p²±p+1 ≡ 1 mod p`).
Both are **odd** (Lemma Φ (F1)).  By §2.4, `A_i ≈ q ≥ 0.394 n^{4/3} > n` for
`n ≥ 20`, so:

> **Lemma DS  [PROVEN].**  In the `f = 2` sub-row of row 2, with
> `B₁ = n, B₂ = n−1, B₃ = n−2`, put `d_j := gcd(A₁,B_j)`, `e_j := gcd(A₂,B_j)`.
> Because `A₁,A₂` are odd and coprime, and `gcd(B_i,B_j) ∣ 2`:
> `A₁ = d₁d₂d₃`, `A₂ = e₁e₂e₃`, `gcd(d_j,e_j) = 1`, `d_je_j ∣ B_j`,
> and `g_j := B_j/(d_je_j)` satisfies `g₁g₂g₃ = c ≤ 3.19 n^{1/3}`.
> Since `A_i > n ≥ B_j`, **each of `A₁, A₂` straddles at least two blocks**:
> no `A_i` divides a single one of `n, n−1, n−2`.  Moreover
> `A₂ − A₁ = 2p ≍ n^{2/3}` and `A₁A₂ = M/c`.

This is a very rigid system.  It is nevertheless **not contradictory**: the
per-block splittings `B_j = d_je_jg_j` are three free coprime factorisations of
three consecutive integers with a tiny cofactor product, and nothing in the
sizes (`d_je_j ≥ B_j/c`, `A₁ ≈ A₂ ≈ √(M/c)`) obstructs them.  The rigidity is
precisely a restatement of "`M/c` is `Φ₃` of a perfect square", i.e. of the
original problem; the factorisation buys structure, not a contradiction.

The same holds for `f ≥ 3` (`τ(f)` factors of sizes `p^{φ(3d)}`) and for row 3
(`Φ₅(p^f) = ∏_{d∣f}Φ_{5d}(p)`).  In row 3 with `f = 1` — the sub-row with the
largest heuristic weight — **there is no factorisation at all**, so this route
cannot even be attempted where it is most needed.

### 4.3  Why the "more factors ⟹ easier" intuition fails here

Splitting `F(q)` would help if the factors had to land in *separate* blocks of
`M`, forcing a Pillai/Størmer-type gap contradiction.  They do not: by Lemma DS
each factor is spread across ≥ 2 blocks, and the blocks are large enough
(`≈ n` each, against factors `≈ n^{4/3}`) to absorb arbitrary coprime splittings.
The mechanism that *does* use the perfect-power condition is the curve — and
§3 shows the curve cannot be pushed.

---

## 5.  Honest gap list

| claim | status |
|---|---|
| (LEG), (BP-p) | **[PROVEN]** (Legendre; Lemma BP, v_task45) |
| MASTER, SIZE-UP | **[PROVEN]**, new; two-line derivations, no computation |
| Row 2 `f = 1` empty for `n ≥ 5`, uniformly in `ℓ*` | **[PROVEN]** (= Lemma R1-p, re-derived) |
| Q-LB `q ≥ (fn²/8.1)^{f/(2f−1)}` | **[PROVEN]**, new; constants `K ≤ 1.01` valid for `q ≥ 128`, `n(n−2) ≥ 0.999n²` for `n ≥ 40` — both hold in the relevant range, but the lemma as stated is asserted only for **`n ≥ 40`** |
| Lemma Q (`q > n` in row 2, all `f ≥ 2`, all `ℓ*`) | **[PROVEN] for `n ≥ 20`** (and `n ≥ 40` if one insists on the Q-LB constants above; the range `20 ≤ n < 40` is inside every existing scan) |
| Row 3: `q < n` at every `f`; `f = 1` live | **[PROVEN]**, new |
| `c ≤ 3.19 n^{1/3}` (`f = 2`), `c ≤ (8.1/f)^{2f/(2f−1)}n^{(2f−3)/(2f−1)}` | **[PROVEN]**, new |
| Lemma SM (`n,n−1,n−2` are `1.88n^{2/3}`-smooth in the `f=2` sub-row) | **[PROVEN]**, new |
| Lemma F, Lemma DS | **[PROVEN]** (F classical; DS new) |
| **Theorem U (no uniform effective bound exists)** | **[PROVEN]**, and — unusually for this file — with **no computational input at all**. The witness `1994³−1994 = 30(16256²+16256+1)` is a one-line integer identity; the thresholds are `2 log 30 + log 2` and `4 log 30 − 2.093`. The table over `c ≤ 216` (which *does* rest on Sage's `integral_points()`) is corroboration only. **A referee should be handed the identity, not the table.** |
| The audit respects the divisibility structure the task flagged | **yes** — it is run on `C_c` (`4c ∣ X`, `4c² ∣ Y`), not on `E_c`. This is not cosmetic: `c = 36`'s large `E`-point fails the divisibility and was discarded; the conclusion survives anyway |
| The instant kill `q > n ⟹ p ∤ n!` closing row 2 | **REFUTED** — works only at `f = 1`; see §2.3 |
| Rows 2 and 3 | **OPEN**, unchanged; empty for `n ≤ 10¹¹` (v_task45) |

**Not claimed anywhere above:** that `C_c` has integral points exceeding
THRESHOLD-1 for *every* `c` (most do not; many `C_c` have no integral point at all).
Theorem U does not need that — a single `c` at which (i) and (ii) conflict
already refutes the existence of a uniform `B`.  What a determined optimist
could still ask for is a bound `B(c)` valid only on the *arithmetically
admissible* sub-locus (`c = 6f₁ℓ*` with `ℓ*` realised by an actual socle
configuration).  That locus is not known to be thin, and no mechanism is
visible for making the bound depend on it; this is recorded as a
non-suggestion, not an open route.

---

## 6.  Effect on Theorem AT

None on the range: unchanged at `9 ≤ n ≤ 10¹¹`, inputs (H1), (H2) and the two
`ℓ*`-families.  The change is to the **route inventory**: v_task45 left two
options for closing rows 2–3, (i) a uniform-in-`c` effective integral-points
theorem, and (ii) a new group-theoretic invariant.  §3 removes (i)
**permanently**.  Option (ii), the PSN-A / PSN-LIE-q route of §4ax, is now the
only surviving candidate, and the new size lemmas of §2 sharpen the target it
must hit: in the dominant sub-row (`row 2, f = 2`) the configuration is pinned
to `q ≥ 0.394 n^{4/3}`, `p ≥ 0.628 n^{2/3}`, `c ≤ 3.19 n^{1/3}`,
`ℓ* ≤ 0.53 n^{1/3}`, with `n, n−1, n−2` all `1.88 n^{2/3}`-smooth.
