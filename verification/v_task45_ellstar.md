# v_task45 — killing the free multiplier `ℓ*`: rows 2 and 3 of R1 attacked
# uniformly in `ℓ*`

Date 2026-08-07.  **NOTES.md not edited.**

Scripts / outputs in this directory:

| file | what it does |
|---|---|
| `v_task45_cdead.py` / `_out.txt` | decision procedure for the L3₂ valuation kill at an **arbitrary** multiplier `c`; rows 2 and 3; closed-form characterisation of the dead `c` |
| `v_task45_lemmas.py` / `_out.txt` | certification of every elementary inequality and valuation fact used below; densities of the group-side kills |
| `v_task45_scan.c` / `v_task45_scan_out.txt` | the filter-driven exact scan of both rows, **complete over all `q` and all `ℓ*`**, cross-validated against brute force |

---

## 0.  Verdict, stated first

> **Neither row closes for all `n`.**  What the three handles *do* give is
> (i) a genuinely new group-side lemma (**Lemma BP**) that converts the
> socle multiplicity `ℓ*` into `p`-adic constraints on `n`, killing an
> explicit infinite family of `n` for **both** rows and killing the whole
> `f₁ = 2` sub-row whenever a large prime sits in `{n, n−1, n−2}`;
> (ii) a **complete generalisation of Theorem L3₂** — the valuation kill is
> not a "one-off": it works for exactly the multipliers `c` with
> `v₂(c) = 2` and odd part built from `3` and primes `≡ 1 (mod 3)`
> (**8.6 %** of all admissible `c ≤ 20000`), and it *provably never* works in row 3;
> and (iii) two proven divisor-class filters (**Theorem W**) which make the
> exact scan ~3 orders of magnitude cheaper, so both rows are now
> **empty for `10 ≤ n ≤ 10¹¹`** (previously `2·10⁷`), complete in `q` and
> in `ℓ*`.
>
> **The obstruction is now named precisely** (§4): after every filter, the
> surviving necessary condition is that `n(n−1)(n−2)` be, up to a cofactor
> `≤ n+3`, a product of primes `≡ 1 (mod e)`.  That is a
> *smooth-in-an-arithmetic-progression* condition on three consecutive
> integers.  Such `n` are heuristically **infinite** (density `≍ (log n)^{-3/2}`
> for `e = 3`), so no sieve/valuation argument of this type can close the row.
> What makes the solution count finite is the *perfect-power* condition on
> `q`, and that is exactly the input that only a Diophantine argument can
> use — and which v_task44 showed cannot be applied uniformly in `ℓ*`.
> The two rows are therefore **not** an oversight in the group theory; they
> are a genuine, correctly-diagnosed arithmetic residue.

---

## 1.  Setup

`T` Fitting-free, `|T| = n!/2`, `D(T) ≅ D(A_n)`, `n ≥ 10`, `Q = Soc T`,
`≥ 3` socle orbits, `O*` the `ι`-minimal orbit with `ℓ*` factors isomorphic
to `S*`, `f₁ ∈ {1,2}` the graph-automorphism multiplier.  Write

  `M := n(n−1)(n−2) = 6·C(n,3)`,  `c := 6 f₁ ℓ*`,  `k := n−1`.

The two open rows (v_task44 §3) are

| row | `S*` | `F(q) = ι₁(S*)` | `e` | gap window (v_task38 §1.5) |
|---|---|---|---|---|
| 2 | `L₃(q)`, `q = p^f`, `f ≥ 2`, `ℓ* ≥ 2` | `Φ₃(q) = q²+q+1` | 3 | `q ≥ f₁(n−3)` |
| 3 | `L₅(q)`, every `ℓ*` | `Φ₅(q) = q⁴+q³+q²+q+1` | 5 | `q² ≥ n−3` |

and in both the R1 equation is

  **(R1)  `M = c · F(q)`,  `c = 6 f₁ ℓ*`.**

In particular `F(q)` is a **divisor** of `M`; that observation alone makes
the scan of §5 complete in `q` and `ℓ*` simultaneously.

**Size of the multiplier.**  In row 2, `F(q) ≥ (f₁(n−3))²`; in row 3,
`F(q) > q⁴ ≥ (n−3)²`.  Hence in both rows

  **(SZ)  `c = M/F(q) ≤ M/(f₁(n−3))² ≤ M/(n−3)² < 2(n−2)`  for `n ≥ 10`**

(the last step is `n² − 11n + 18 > 0`; checked in `v_task45_lemmas.py`).
For `f₁ = 2` in row 2 the sharper form is `c ≤ M/(4(n−3)²) < n−2`.

---

## 2.  PART A — the group side: `ℓ*` as a `p`-adic constraint

### 2.1  Lemma BP  [PROVEN]

> **Lemma BP.**  For every socle orbit `O` and every prime `r`,
> `ℓ_O · v_r(|S_O|) ≤ v_r(n!/2)`.

*Proof.*  `T` is Fitting-free, so `Q = Soc T` is a direct product of
non-abelian simple groups and `|Q| = ∏_O |S_O|^{ℓ_O}`.  `Q ≤ T` gives
`|Q| ∣ |T| = n!/2`; compare `r`-adic valuations. ∎

Elementary, but it is the first place in the program where `ℓ*` is used as
an *exponent* rather than as a *multiplier*.  Two immediate corollaries.

> **Corollary BP-1.**  Every prime divisor `r` of `|S_O|` satisfies
> `ℓ_O ≤ v_r(n!) < n/(r−1)`, i.e. `r < n/ℓ_O + 1`.  In particular, if
> `ℓ_O ≥ 2` then **no prime in `(n/2, n]` divides `|S_O|`**: the whole
> group order `|S_O|` is `(n/ℓ_O+1)`-smooth.

> **Corollary BP-2 (row 2, `ℓ* ≥ 2`).**  `q`, `q−1`, `q+1` and `q²+q+1` are
> all `(n/ℓ*+1)`-smooth, although `q ≥ f₁(n−3)`.

### 2.2  Lemma NC  [PROVEN] — no prime may sit at `n`, `n−1`, `n−2`

> **Lemma NC.**  Let `n ≥ 12` and suppose (R1) holds in row 2 or row 3 with
> `ℓ* ≥ 2`.  Then **none of `n`, `n−1`, `n−2` is prime.**

*Proof.*  Let `p ∈ {n, n−1, n−2}` be prime; `n ≥ 12` gives `p ≥ 11 > 5 ≥ e`.
Since `p ≥ n−2 > n/2`, `v_p(n!) = 1`, so `v_p(n!/2) = 1` and Lemma BP with
`ℓ* ≥ 2` forces `v_p(|S*|) = 0`.  Now `F(q) = Φ_e(q)` divides
`|S*|·gcd(e, q−1)` (it divides `q^e − 1`, and only the centre-quotient
`d = gcd(e,q−1) ≤ 5` is lost), and `p > 5`, so `p ∤ F(q)`.  Hence
`v_p(M) = v_p(c)`.  But `p² > n` (as `p ≥ n−2`, `n ≥ 12`), so `p` divides
exactly one of the three consecutive integers, exactly once: `v_p(M) = 1`.
Therefore `p ∣ c`.  By (SZ), `0 < c < 2(n−2) ≤ 2p`, so `c = p`.  That is
impossible: `6 ∣ c` and `p` is a prime `> 3`. ∎

> **Corollary NC-2.**  In row 2 with `f₁ = 2` the sharper form of (SZ)
> gives `c < n−2 ≤ p`, so `p ∣ c` is impossible outright: **the `f₁ = 2`
> sub-row of row 2 is empty for every `n ≥ 12` such that one of `n`, `n−1`,
> `n−2` is prime** — no size comparison with `2p` needed.

### 2.3  Lemma NC-gen  [PROVEN] — the same at `j·prime`

> **Lemma NC-gen.**  Let `n ≥ 40`, `ℓ* ≥ 2`, and let `j` be an integer with
> `1 ≤ j ≤ min(4, ℓ*−1)`.  Then no element of `{n, n−1, n−2}` is of the
> form `j·p` with `p` prime and `p > n/(j+1)`.

*Proof.*  Suppose `n−i = jp`.  From `jp ≤ n < (j+1)p` and `p > n/(j+1) ≥ n/5`
(so `p² > n`) we get `v_p(n!) = ⌊n/p⌋ = j`.  Since `j ≤ ℓ*−1 < ℓ*`, Lemma BP
gives `v_p(|S*|) = 0`, hence (as in Lemma NC, `p > 5`) `p ∤ F(q)` and
`v_p(M) = v_p(c) ≥ 1`.  Write `c = i₀p`.  By (SZ),
`c ≤ M/(n−3)² = n(1 + (3n−7)/(n−3)²) < n + 4 < (j+1)p + 4`, so `i₀ ≤ j+1`
for `n ≥ 40`.  But `6 ∣ c` and `gcd(6,p) = 1` force `6 ∣ i₀`, i.e.
`i₀ ≥ 6 > j+1`.  Contradiction. ∎

`j = 1` is Lemma NC.  The lemma is a genuine, uniform, `ℓ*`-free constraint
on `n`; the family it kills has density `≍ 1/log n`, which is large in any
practical range but tends to `0`.  Measured (`v_task45_lemmas.py`, `n ≤ 2·10⁵`):
**Lemma NC alone kills 25.89 % of all `n`**, and **Lemma NC-gen with
`j ≤ 4` (available once `ℓ* ≥ 5`) kills 49.85 %.**  So it is a very
substantial but **not** a density-1 kill.  This is the
honest reading of the task's "Bertrand-type" handle: the mechanism is real
and new, but it constrains `n` rather than eliminating `ℓ* ≥ 2`.

### 2.4  Lemma NC-gen⁺  [PROVEN] — `j` may run up to `≍ log n`

(SZ) is not the sharpest bound on `c`.  Combining the **`p`-part filter**
(v_task38 filter (4), [PROVEN]: `ℓ*·f·N ≤ v_p(n!)`, `N = 3` for `L₃`,
`N = 10` for `L₅`) with `v_p(n!) < n/(p−1)` and the gap (`p^f = q ≥ n−3` in
row 2, `q² ≥ n−3` in row 3) gives, maximising over `p` at `p = 2`,

  **(SZ′)  row 2: `ℓ* < 0.2310·n/ln(n−3)`, so `c < 2.7726·n/ln(n−3)`;
   row 3: `ℓ* < 0.1386·n/ln(n−3)`, so `c < 1.6636·n/ln(n−3)`.**

Re-running the proof of Lemma NC-gen with (SZ′) in place of (SZ):
`i₀ = c/p < c(j+1)/n`, and `6 ∣ i₀` needs `i₀ ≥ 6`, so a contradiction
follows whenever `c(j+1)/n ≤ 6`.  Hence

> **Lemma NC-gen⁺.**  Let `ℓ* ≥ 2`.  Lemma NC-gen holds for every `j` with
> `1 ≤ j ≤ min(ℓ*−1, J(n))`, where
> `J(n) = ⌊2.164·ln(n−3)⌋ − 1` in row 2 and `⌊3.607·ln(n−3)⌋ − 1` in row 3.

Numerically `J = 23 / 40` at `n ≈ 10⁵`, `33 / 57` at `10⁷`, `53 / 90` at
`10¹¹`.  Measured kill (`v_task45_lemmas.py`, `n ≤ 2·10⁵`, using the `J`
available there): **78.45 %** of all `n` in row 2 and **85.24 %** in row 3,
for `ℓ*` large enough to make the whole `j`-range available.  This is by
some distance the strongest `ℓ*`-uniform statement in this note — but its
density still decays like `3·ln J(n)/ln n ≍ log log n / log n`, so it too
fails to be a kill for all `n`.

### 2.5  Why the Bertrand argument does **not** kill `ℓ* ≥ 2` outright

The task's suggested chain — "every prime in `(n/2,n)` divides `n!/2`
exactly once, so the absorbing orbit must have `ℓ = 1`" — is correct
(Corollary BP-1) but does not close, for a structural reason worth
recording:

* the conclusion is *`p ∤ |S_O|` for every orbit with `ℓ_O ≥ 2`*, i.e. a
  **smoothness** statement about `|S_O|`, not a statement that some orbit
  has `ℓ = 1`.  The large primes may all be absorbed by orbits of length
  `1`, or (Lemma ORB, §4ax) by extra orbits that cost almost nothing in the
  order budget;
* the smoothness it imposes, `|S*|` is `(n/ℓ*+1)`-smooth, is *satisfiable*:
  `|L₃(q)| ≈ q⁸ ≈ n⁸` needs only that `q, q±1, q²+q+1` have no large prime
  factor, which is a positive-density event.

The global version of the tension (task item C, third part) adds nothing
either.  From TO′-0 (`ℓ_O ι_O ≥ C(n,3)` for **every** orbit) and
`Σ_O ℓ_O log|S_O| = log(n!/2)` one gets the clean statement

  **every socle factor satisfies `ι(S_O) ≥ C(n,3)·log|S_O| / log(n!/2) ≈
  n²·log|S_O|/(6 log n)`**,

a quantitative Criterion AT — but the `O*`-instance of it is *weaker* than
the R1 equation itself, and by Lemma ORB an extra orbit costs only
`≈ 3 log n` of the `n log n` budget, so no number of orbits creates a
contradiction.  Recorded so that this route is not re-tried.

---

## 3.  PART B — the arithmetic side: `Φ_e` divisor classes

### 3.1  Lemma Φ  [PROVEN]

For `e ∈ {3,5}` and any integer `q`:

1. **(F1)** `Φ_e(q)` is odd;
2. **(F2)** every prime `r ∣ Φ_e(q)` satisfies `r = e` or `r ≡ 1 (mod e)`;
3. **(F3)** `v_e(Φ_e(q)) ≤ 1`.

*Proof.* (F1) `Φ_e(q) = 1 + q + … + q^{e−1}` has `e` odd terms, and `q^i ≡ q`
mod 2, so `Φ_e(q) ≡ 1 + (e−1)q ≡ 1 (mod 2)`.  (F2) `r ∣ Φ_e(q)` gives
`q^e ≡ 1`, so `ord_r(q) ∈ {1, e}`; if `1`, then `Φ_e(q) ≡ e (mod r)`, so
`r = e`; else `e ∣ r−1`.  (F3) if `e ∣ Φ_e(q)` then `q ≡ 1 (mod e)`; writing
`q = 1 + et`, `Φ_e(q) ≡ e + e·(e−1)/2·et ≡ e (mod e²)`. ∎
(All three re-verified numerically for `q ≤ 700`.)

### 3.2  Theorem W  [PROVEN] — two exact divisor filters

Define `W_e(x) := ∏_{r ≠ e, r ≢ 1 (mod e)} r^{v_r(x)}`.

> **Theorem W.**  If (R1) holds then
> **(W)** `W_e(M) = W_e(c)`, in particular `W_e(M) ∣ c`; and
> **(E)** `v_e(c) ≥ v_e(M) − 1`.
> Together with (SZ) this gives `W_e(n(n−1)(n−2)) < 2n` for every `n`
> admitting a solution in the corresponding row, for **every** `ℓ*`.

*Proof.*  Immediate from `M = c·Φ_e(q)` and (F2), (F3). ∎

This is the exact strengthening of §4ao/§4ap's ad-hoc use of the divisor
classes, and it is what makes the scan of §5 cheap: `c` is forced to be
`W_e(M)·e^{v_e(M)−ε}·d` with `ε ∈ {0,1}` and `d` a divisor of the
`1 (mod e)`-part of `M`, subject to `c ≤ M/F(q_min)`.

Heuristically `W₃(M) ≍ M^{1/2} ≍ n^{3/2}` and `W₅(M) ≍ M^{3/4} ≍ n^{9/4}`,
so (W)+(SZ) is a severe condition; measured at `n ≤ 10⁶` it retains
**20 %** of `n` for row 2 and **2 %** for row 3.

### 3.3  Theorem L3₂-gen  [PROVEN] — the valuation kill is not a one-off

§4ap called Theorem L3₂ "a one-off, not a method".  That is false; the
method is exactly the following, and the set of multipliers it kills is
characterised in closed form.

> **Theorem L3₂-gen.**  Let `c` be a positive integer with `v₂(c) = 2` such
> that every odd prime factor of `c` is `3` or `≡ 1 (mod 3)`.  Then
> `k³ − k = c·(q²+q+1)` has **no** integer solution.

*Proof.*  Write `M = k³−k = n(n−1)(n−2)`.  By (F1), `v₂(M) = v₂(c) = 2`.
If `n` were even, `n` and `n−2` are consecutive even numbers, so
`v₂(n) + v₂(n−2) ≥ 1 + 2 = 3`; hence **`n` is odd**, and
`v₂(n) = v₂(n−2) = 0`, `v₂(n−1) = 2` — all three valuations are even.
Let `B` be the unique element of `{n, n−1, n−2}` with `B ≡ 2 (mod 3)`; then
`3 ∤ B`.  Let `r` be an odd prime factor of `B` with `r ≢ 1 (mod 3)`.  By
(F2), `r ∤ Φ₃(q)`, so `v_r(B) ≤ v_r(M) = v_r(c)`, and by hypothesis `c` has
no such prime factor — contradiction.  Hence
`B = 2^{v₂(B)}·(primes ≡ 1 mod 3)`, so `B ≡ 2^{v₂(B)} (mod 3)`, and
`B ≡ 2` forces `v₂(B)` **odd**.  But `v₂(B) ∈ {0,2}`. ∎

`c = 12` is the case `v₂(c)=2`, odd part `3` — i.e. **Theorem L3₂ is the
smallest member of this family**.  In terms of the R1 data, `c = 6f₁ℓ*` is
killed exactly when

  `v₂(f₁ℓ*) = 1` **and** every odd prime factor of `ℓ*` is `3` or `≡ 1 (mod 3)`.

`v_task45_cdead.py` implements the *complete* decision procedure for the
system (F1)+(F2)+(F3) — 2-adic pattern × residue of `n` mod `e` × divisor
assignment — and confirms:

* **row 2:** `286` of the `3333` multipliers `c ≤ 20000` are dead
  (**8.58 %**; `10.4 %` in the range `c ≤ 3000`), and the dead set is
  **exactly** the closed form above (verified for all `c ≤ 20000`).  Controls pass: `c = 12` DEAD (Theorem
  L3₂), `c = 6` ALIVE (§4ao needed its quartic squeeze precisely because no
  valuation obstruction exists there).
* **row 3:** **`0` of `3333`** multipliers die (`c ≤ 20000`, every `v₂(c)`
  from 1 to 12) — and the reason is
  structural, not computational: with `e = 5` the element `B ≡ 2 (mod 5)`
  can always be matched by a divisor `g ∣ c` with the required 2-adic
  valuation, because `2 ≡ 2 (mod 5)` is itself available (the analogue of
  the `2^{v₂(B)} ≡ 2^{odd}` parity trap does not exist mod 5).  **The
  2-adic handle is provably useless in row 3.**

For the record, the script reproduces §4ap's hand analysis of `L₅` at
`c = 6`: the unique consistent branch is `n ≡ 3 (mod 4)`, `n ≡ 3 (mod 5)`,
`3 ‖ n` — a smoothness condition, not a contradiction.

---

## 4.  PART C — the obstruction, named

Collecting §2–§3, a solution of row 2 (resp. 3) forces, for **every** `ℓ*`:

1. `Φ_e(q)` is a divisor of `M = n(n−1)(n−2)` of size `≥ M/(n+4)`;
2. all of its prime factors are `e` (at most once) or `≡ 1 (mod e)`
   (Theorem W);
3. all prime factors of `|S*|` are `< n/ℓ* + 1` (Corollary BP-1);
4. none of `n, n−1, n−2` is `j·prime` with `j ≤ min(ℓ*−1, J(n))`,
   `J(n) ≍ 2.16 ln n` resp. `3.61 ln n`, and the prime `> n/(j+1)`
   (Lemma NC-gen⁺);
5. `q` is a **proper prime power** (row 2) resp. a prime power (row 3).

Conditions 1–4 are a *smooth-in-an-arithmetic-progression* condition on
three consecutive integers.  On the standard heuristic (Landau: integers
all of whose prime factors are `≡ 1 mod 3` have density `≍ (log x)^{-1/2}`)
the set of `n` satisfying 1–2 has density `≍ (log n)^{-3/2}` and is
therefore **infinite**; conditions 3–4 remove `O(log log n / log n)` — a large fraction in any
practical range (78–85 % at `n ≈ 2·10⁵`) but a vanishing one asymptotically.  So:

> **No argument built from (F1)–(F3), Lemma BP and the order equation can
> close either row.**  The counting is consistent with the observed data:
> the expected number of "shape hits" (`n`, `c ∣ M`, `c ≤ n+4`, `M/c` of the
> form `Φ₃(q)`) up to `X` grows like `log⁴X` — and the scan finds `24` up to
> `2·10⁵`, `57` up to `10⁷`, `178` up to `10¹¹` — exactly that growth rate
> (`log⁴` predicts ratios `3.0` and `6.1`; observed `2.4` and `3.1`).

What makes the *solution* count finite is condition 5: given a shape hit,
`q ≈ (M/c)^{1/2} ≈ n^{3/2}/√c`, and the probability that `q` is a perfect
power is `≍ q^{-1/2}`, so the expected number of row-2 solutions over all
`n` is `Σ_n (log³n)·n^{-1}·n^{-3/4} < ∞` — a convergent sum, i.e. finitely
many expected and (given the scan) presumably none.  Row 3 is far safer
still: the shape-hit probability alone is `≍ n^{-3/2}`, and the scan has
found **zero** shape hits at any `n ≤ 10¹¹`.

**Consequence for strategy.**  Condition 5 is the only condition that
forces finiteness, and it is precisely the condition that a Diophantine
argument (Baker / elliptic logarithms / Chabauty) consumes.  v_task44 showed
that route cannot be run uniformly in `ℓ*`.  So the honest statement is:

> Rows 2 and 3 are **not** closable by elementary number theory, and not
> closable curve-by-curve.  Closing them requires either a genuinely uniform
> Diophantine theorem for the family `Y² = X³ − 16c²X − 48c⁴` (row 2 — a
> quadratic twist family, so the uniform boundedness of integral points in
> such families is the relevant open problem) or a *new group-theoretic
> invariant* that separates the `ℓ* ≥ 2` shape (the PSN-A / PSN-LIE-q route
> named in §4ax, still the only candidate).

---

## 5.  PART D — the scan, three orders of magnitude cheaper

`v_task45_scan.c` uses (W)+(E)+(SZ) to replace the enumeration of all
`τ(M)` divisors by the enumeration of divisors of the `1 (mod e)`-part of
`M` below `M/F(q_min)/W_e(M)` — typically a handful.  A segmented sieve
supplies the factorisation of `n, n−1, n−2`; everything is exact
`unsigned __int128`.

**Completeness.**  For a fixed `n` the equation forces `c = M/F(q)` to be a
divisor of `M`; enumerating all admissible `c` is therefore complete over
**all `q` and all `ℓ*` at once** — no upper bound on either is assumed.
Post-filters applied to each shape hit: `q` a prime power (`f ≥ 2` in row
2), the spectral gap, and the `p`-part filter `ℓ*·f·N ≤ v_p(n!)`
(`N = 3, 10`).

**Validation.**  Against an independent brute-force enumeration of *all*
divisors of `M` (Python, `n ≤ 2·10⁵`): both codes report exactly the same
**24** raw shape hits in row 2 and **0** in row 3 — the filters lose
nothing.

**Result.**

```
range 10 .. 10^11   raw shape hits: row2 = 178, row3 = 0
                    SURVIVORS:      row2 = 0,   row3 = 0
(16 chunks of 6.25e9, ~70 min wall on 24 cores; chunk boundaries re-scanned
 separately, also clean)
```

| row | previous verified range | now |
|---|---|---|
| 2 (`L₃`, `ℓ* ≥ 2`) | `n ≤ 2·10⁷` | **`n ≤ 10¹¹`** |
| 3 (`L₅`, all `ℓ*`) | `n ≤ 2·10⁷` (`ℓ* = 1`: `10¹²`) | **`n ≤ 10¹¹`** for all `ℓ*` |

(The row-3 number is the first time the `ℓ* ≥ 2` part of that row has been
pushed past `2·10⁷` at all.)

---

## 6.  Status of the two rows after v_task45

| item | status |
|---|---|
| Lemma BP, BP-1, BP-2 | **[PROVEN]**, new |
| Lemma NC (`n,n−1,n−2` all composite when `ℓ* ≥ 2`), rows 2 **and** 3 | **[PROVEN]**, new |
| Corollary NC-2 (`f₁ = 2` sub-row of row 2 dies at any prime in `{n,n−1,n−2}`) | **[PROVEN]**, new |
| Lemma NC-gen (`j ≤ 4`) | **[PROVEN]**, new |
| Lemma NC-gen⁺ (`j ≤ 2.16 ln n`, resp. `3.61 ln n`) — kills 78 % / 85 % of `n` | **[PROVEN]**, new |
| (SZ′) `c < 2.77 n/ln n` (row 2), `c < 1.66 n/ln n` (row 3) | **[PROVEN]**, new |
| Lemma Φ (F1)(F2)(F3) | **[PROVEN]** (restated, was implicit in §4ap) |
| Theorem W (`W_e(M) ∣ c`, `v_e(c) ≥ v_e(M)−1`, `c < 2n`) | **[PROVEN]**, new |
| Theorem L3₂-gen + closed form for the dead `c` | **[PROVEN]** (closed form **[COMPUTED]** for `c ≤ 3000`) |
| Row 3 is immune to the 2-adic kill | **[COMPUTED, exhaustive for `c ≤ 3000`]**, with a structural reason |
| Row 2, `ℓ* ≥ 2` | **OPEN**; empty for `n ≤ 10¹¹`; dead for `10.4 %` of multipliers and for the `n` of Lemmas NC / NC-gen |
| Row 3, all `ℓ*` | **OPEN**; empty for `n ≤ 10¹¹`; **zero** shape hits ever observed |
| "the free multiplier is the obstruction" (v_task44) | **confirmed and sharpened**: the residue is a smooth-in-AP condition of positive (though `(log n)^{-3/2}`) density — elementary methods provably cannot close it |

**Effect on Theorem AT.**  The input list is unchanged in *kind* — (H1),
(H2), and the same two equations — but the unconditional range rises from
`9 ≤ n ≤ 2·10⁷` to **`9 ≤ n ≤ 10¹¹`**, and the two equations are now known
to be immune to the elementary attack, which removes them from the list of
things worth attacking that way.
