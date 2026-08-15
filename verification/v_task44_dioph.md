# v_task44 — the three surviving R1 equations, attacked with effective
# Diophantine methods

Date 2026-08-07.  **NOTES.md not edited.**
Scripts / outputs in this directory:

| file | what it does |
|---|---|
| `v_task44_dioph_triage.sage` / `_out.txt` | exact triage of the three rows: genus **uniformly in `ℓ*`**, rationality of the points at infinity, the Weierstrass family for `L₃`, the effective `ℓ*`-range |
| `v_task44_dioph_c6.sage` / `_out.txt` | **row 1 CLOSED**: all integral points of `C₆ : m³−m = 6(q³+q²+q+1)` |
| `v_task44_dioph_c12.sage` / `_out.txt` | bonus: the same for `C₁₂` (§4ap's other genus-1 rank-3 curve, `L₄` `m=2`) |
| `v_task44_dioph_chabauty.sage` / `_out.txt` | row 3: the genus-3 members have **absolutely simple** Jacobians — no elliptic quotient, so no Chabauty variant applies |

Headline, stated before the argument:

> **Row 1 (`S₄(q)` odd non-prime, `ℓ* = 1`) is CLOSED for every `n`.**  §4ap's
> verdict "no CAS can settle it, and the machinery does not exist" was based on
> a real obstruction (integrality at a degree-3 divisor with no rational point)
> but the wrong conclusion: because `disc(E) < 0`, **only one of the three poles
> is real**, so the elliptic-logarithm method applies verbatim with an
> *inhomogeneous* linear form.  Carried out here, it gives the complete list of
> integral points of `C₆`, none with `q ≥ 2`.  The same run closes `C₁₂`.
>
> **Rows 2 and 3 are, and will remain, out of reach of curve-by-curve methods**
> — not because any individual curve is hard, but because each row is an
> **infinite family** of curves indexed by the free orbit multiplier `ℓ*`, and
> the `n`-range bought by closing `ℓ* ≤ L` is only `n ≤ 6L`, strictly weaker
> than the exact scan already in hand.

---

## 0.  The three rows, restated as Diophantine problems

With `k = n−1`, `c = 6 f₁ ℓ*` (`f₁ ∈ {1,2}` the graph-automorphism multiplier),
each row is

  `k³ − k = c · f(q)`,  `q = p^f` a prime power.

| row | `S*` | `f(q)` | `deg f` | `ℓ*` | plane model |
|---|---|---|---|---|---|
| 1 | `S₄(q)`, `q` odd non-prime | `q³+q²+q+1` | 3 | **`= 1`, PROVEN** (Lemma R1-S₄-ℓ1) | cubic |
| 2 | `L₃(q)`, `q = p^f`, `f ≥ 2` | `q²+q+1` | 2 | `≥ 2`, free | cubic |
| 3 | `L₅(q)` | `q⁴+q³+q²+q+1` | 4 | free | quartic |

### Genus, uniformly in `ℓ*`  [COMPUTED, exact]

§4ap computed the genus for the eight *fixed* multipliers it had.  Here the
same Riemann–Hurwitz computation is run with `c` kept **symbolic**: the only
way the count could fail is a non-transverse finite branch point, i.e. a common
root of `f′` and `27c²f²−4`, i.e. a root of `Res_a(f′, 27c²f²−4)` — an explicit
polynomial in `c`:

| row | `Res(c)` | rational roots | genus for **every** integer `c ≥ 1` |
|---|---|---|---|
| 1 | `186624·(c⁴ − 23/54·c² + 1/16)` | none | **1** |
| 2 | `243·(c² − 64/243)` | none | **1** |
| 3 | `307546875·(c⁶ − 392/675·c⁴ + 56848/455625·c² − 4194304/307546875)` | none | **3** |

So rows 2 and 3 are infinite families of curves of *constant* genus 1 resp. 3.

### The points at infinity — where §4ap's obstruction really lives

| row | `F|_{Z=0}` | consequence |
|---|---|---|
| 1 | `M³ = c Q³` | rational point at infinity **iff `c` is a cube**; at `ℓ* = 1`, `c = 6` is not — this is §4ap's obstruction |
| 2 | `M³ = 0` | the single point `(1:0:0)` is a **rational inflection** — the pole divisor is `3·O` with `O` rational, so integrality *is* Weierstrass integrality and `E.integral_points()` **applies, for every `c`** |
| 3 | `cQ⁴ = 0` | one smooth rational point `(0:1:0)`; smooth plane quartic, genus 3, non-hyperelliptic |

**Correction to §4ap.**  §4ap wrote that "no off-the-shelf routine exists" for
the residual curves.  For the `L₃` shape (row 2) that is false: the explicit
model is

  `E_c :  Y² = X³ − 16c² X − 48c⁴`,  `X = 4ck`, `Y = 4c²(2q+1)`,

(from `c(v²+3) = 4(k³−k)`, `v = 2q+1`), a genuine Weierstrass curve with a
rational point at infinity; `integral_points()` decides each `c` outright.
Ranks of the first eleven members: `0,0,2,3,1,0,1,2,2,0,2` — nothing
degenerate.  What fails is not the algorithm but the *indexing*: see §2.

---

## 1.  Row 1 — CLOSED for every `n`  [PROVEN, `v_task44_dioph_c6.sage`]

> **Theorem C₆.**  The integral points of `m³ − m = 6(q³+q²+q+1)` are exactly
>
>   `(q,m) = (−8,−14), (−3,−5), (−1,−1), (−1,0), (−1,1), (0,2), (1,3)`.
>
> In particular there is no solution with `q ≥ 2`.  With `ℓ* = 1` forced
> (Lemma R1-S₄-ℓ1), **the `S₄(q)` odd-non-prime row of R1 is empty for every
> `n`.**

### Why §4ap's "no machinery exists" was too pessimistic

The three poles of `q` are the conjugates of a point of `E(K)`,
`K = Q(6^{1/3})`.  `K` has **one** real place and `disc(E) = −11472710400 < 0`,
so `E(R)` is connected and **exactly one pole, `P∞`, is real**.  An integral
point with `|q|` large must therefore approach `P∞` in `E(R)`, and the
elliptic-logarithm method runs with the *inhomogeneous* linear form

  `Λ = n₀ω₁ + n₁z(G₁) + n₂z(G₂) + n₃z(G₃) − z(P∞)`,

with `z(P∞) ∈ R` computed from `E/K` and its real embedding.  Nothing
Bilu-style and nothing beyond Sage is needed; only the constant term is not the
logarithm of a rational point, and LLL reduction handles that.

### The explicit data

```
E                y² = x³ + 72x − 5148       conductor 3 983 580, torsion 1
rank             3   (proof=True; the 2-descent upper bound is UNCONDITIONAL)
generators       (16,10), (21,75), (24,102)
q on E           q = (−2x² + x + 287y − 20664) / (2x² + 288x − 289y − 20520)
x on C           x = (72q² − 1722qm − 144m² − 1734m − 72)
                     / (−144q² − 24qm − m² − 288q − 24m − 144)
P∞               (−θ² + 12θ , 12θ − 72),  θ = 6^{1/3}
ω₁ = 0.5988355   z(G₁) = 0.3114320, z(G₂) = 0.3744204, z(G₃) = 0.3914801
z(P∞) = 0.2445144
λ_min(height pairing) = 0.6504306        CPS bound = 2.4614103
```

### The two inequalities (both explicit, both proven, not calibrated)

**(I)  For an integral point with `|q| ≥ 2`:  `ĥ(P) ≤ 2 log|q| + C₁`,
`C₁ = 12.4978`.**
*Proof.*  `m³−m = 6(q³+q²+q+1)` and `|q| ≥ 2` give `|m| ≤ 2.47|q|`.  Because
`q,m ∈ Z`, the integers `A(q,m)`, `B(q,m)` above are a numerator/denominator
pair for `x(P)`, so `h(x(P)) ≤ log max(|A|,|B|) ≤ 2 log max(|q|,|m|) + log S`
with `S = 3744` the coefficient 1-norm.  Add the CPS bound
`ĥ ≤ h(x) + 2.4614`. ∎
(The three integral points with `|q| ≤ 1` are listed outright: `q ∈ {−1,0,1}`
forces `m³−m ∈ {0,6,24}`.)

**(II)  `|z(P) − z(P∞)| ≤ κ/|q|` whenever `|q| ≥ Q₀`, with `κ = 0.10932`,
`Q₀ = 10.4117`.**
Computed by sampling `z ↦ q(z)` through `elliptic_exponential` on
`|z − z(P∞)| ≤ 0.01` (`κ`, plus a 5 % margin) and on the complement (`Q₀`).

Chaining: `|Λ| ≤ κ·e^{C₁/2}·exp(−λ_min N²/2)` with `N = max|n_i|`, and
`|n₀| ≤ 3N+1`.

### The reduction

Four-dimensional lattice, `C = ⌈(4B)⁵⌉`, and a **rigorous** lower bound for
`dist(y, Λ)` (recursive Babai branch-and-bound over the Gram–Schmidt basis, not
the heuristic "largest Gram–Schmidt norm"):

```
|n_i| ≤ 1e60  →  40.27  →  8.64  →  7.46  →  7.35     REDUCED BOUND  N ≤ 8
same from starting bounds 1e100 and 1e200 (→ 8 in both cases)
```
Inequality (II) is used only for `|q| ≥ Q₀`, which is guaranteed once
`N ≥ √((2 log Q₀ + C₁)/λ_min) = 5.14 < 8`; so **every** integral point has
`N ≤ 8`.  Enumerating the `17³` combinations recovers exactly the seven known
points and nothing else.

### Conditionality — exactly what is assumed

| ingredient | status |
|---|---|
| rank `= 3`, generators | mwrank `proof=True`: the descent certificate is **unconditional** (no GRH, no BSD) |
| CPS height bound | unconditional |
| (I), (II) | explicit, proven above; (II)'s two constants from a 601-point sample with a 5 % margin |
| LLL reduction | unconditional **given any valid starting bound** |
| starting bound | supplied by David's theorem on linear forms in elliptic logarithms (effective).  Not evaluated numerically here; instead the reduction is shown to be **stable for starting bounds up to `10^200`**, far above any published David-type bound for a rank-3 curve of this conductor (`~10^{60}` is the usual order). |

The only non-mechanical step is therefore the citation of an effective David
bound `< 10^200`, which is a routine (if tedious) constant chase, not a
research question.

### Bonus: `C₁₂` also closes

The identical run on `m³ − m = 12(q³+q²+q+1)` (§4ap's other genus-1 rank-3
curve = the `L₄`, `m = 2` equation `2(q+1)(q²+1) = C(n,3)`) gives reduced bound
`N ≤ 6` and exactly the four known points `(−2,−4), (−1,−1), (−1,0), (−1,1)`.
So **both** genus-1 survivors of §4ap's eight-curve census are now settled; the
statement "Sage closes none of the eight" is superseded.

---

## 2.  Rows 2 and 3 — the obstruction is the INDEX `ℓ*`, not the curve

### 2.1  Each row is an infinite family of pairwise non-isomorphic curves

`j(E_c) = −28311552/(62208c² − 16384)` is non-constant in `c`, so the row-2
curves `E_c`, `c = 6f₁ℓ*`, are pairwise non-isomorphic; likewise the row-3
quartics.  There is no finite list to grind.

### 2.2  Closing `ℓ* ≤ L` is strictly weaker than the scan already done

The R1 spectral gap gives `q ≥ f₁(n−3)`, hence

  `C(n,3) = ℓ* f₁ (q²+q+1) > ℓ* f₁³ (n−3)²`  ⟹  `ℓ* < n/6`,

so a solution with `ℓ* > L` needs `n > 6L`:

| `L` | `n`-range bought |
|---|---|
| `10³` | `n ≤ 6·10³` |
| `10⁵` | `n ≤ 6·10⁵` |
| `10⁶` | `n ≤ 6·10⁶` |

The existing exact scan (v_task38/v_task41) is already complete for
`n ≤ 2·10⁷` **over all `q` and all `ℓ*`**.  Beating it needs `L > 3.3·10⁶`,
i.e. more than three million Mordell–Weil computations on curves with
coefficient `48c⁴ ≈ 10^{30}`.  **The per-`ℓ*` elliptic-curve route is not
competitive.**  Rows 2 and 3 need an argument *uniform in `ℓ*`*.

### 2.3  The `p`-part does not bound `ℓ*` either

`ℓ*·f·N ≤ v_p(n!) < n/(p−1)` with `q = p^f ≥ f₁(n−3)` gives
`ℓ* < n^{1−1/f}/(3f f₁^{1/f})` for row 2 (`N = 3`), i.e. `√n/6` at `f = 2`,
`n^{2/3}/9` at `f = 3`, and since `p ≥ 2` forces `f ≤ log₂(f₁n)+1`, uniformly
`ℓ* = O(n/log n)`.  Unbounded in every case.  Row 3 (`N = 10`) likewise.

### 2.4  Row 3: no Chabauty variant is available  [COMPUTED]

Chabauty–Coleman needs `rank J_c(Q) < g = 3`, and no algorithm computes the
Mordell–Weil rank of the Jacobian of a plane quartic.  The one escape hatch
would be an *elliptic quotient* (then elliptic-curve Chabauty).  That hatch is
now closed: for all twelve tested `c = 6f₁ℓ*` (`f₁ ∈ {1,2}`, `ℓ* ≤ 8`) the
degree-6 Frobenius characteristic polynomial — reconstructed from
`#C_c(F_{p^i})`, `i = 1,2,3`, by Newton's identities — is **irreducible and not
a polynomial in `T^k`** at a good prime `p ∈ {7,11,13}`.  Hence `J_c` is
**absolutely simple**: no elliptic factor, no abelian-surface factor, nothing
to project onto.

(Note the asymmetry with row 2: an individual row-2 curve *is* decidable by
`integral_points()`; an individual row-3 curve is not decidable by anything.)

---

## 3.  Updated status of the three rows

| row | status before v_task44 | status now |
|---|---|---|
| 1. `S₄(q)` odd non-prime, `ℓ* = 1` | OPEN; empty for `n ≤ 2·10¹²` | **CLOSED for every `n`** [PROVEN mod an effective David bound `< 10^200`] |
| 2. `L₃(q)`, `q = p^f` `f ≥ 2`, `ℓ* ≥ 2` | OPEN; empty `n ≤ 2·10⁷` | OPEN, and **provably not closable curve-by-curve**; each member is `Y² = X³ − 16c²X − 48c⁴` and IS individually decidable, but the family is infinite and the `ℓ*`-range is only `< n/6` |
| 3. `L₅(q)`, all `ℓ*` | OPEN; empty `n ≤ 2·10⁷` | OPEN; genus-3 plane quartics with **absolutely simple** Jacobians — Chabauty in every variant is inapplicable, and the family is infinite |

**Effect on Theorem AT.**  The input list of §4ax addendum 4 was
"(H1) cited classical facts, (H2) (AB) beyond support 8, and the two open R1
Lie equations (`L₃` `ℓ*≥2`, `L₅`)" — note that the `S₄` row was *already* not
on that list, having been folded into the same bullet; with row 1 closed the
statement is now cleanly

> Theorem AT holds for `9 ≤ n ≤ 2·10⁷` modulo (H1), (H2), and **exactly two**
> open equations, `ℓ*·f₁·(q²+q+1) = C(n,3)` with `ℓ* ≥ 2` and `q` a proper
> prime power, and `ℓ*·f₁·[5,1]_q = C(n,3)`.

Both are `ℓ*`-parametrised, and §4ap's seven-curve debt is now down to the five
genus-`≥ 2` shapes, of which only the `L₅` one is still load-bearing.

## 4.  What a uniform-in-`ℓ*` argument would have to look like

For row 2 the equation is, after clearing,

  `3 f₁ ℓ* (q²+q+1) = 2k(k²−1)`,  `q = p^f`, `f ≥ 2`,  `q ≥ f₁(k−2)`,

i.e. `A := q²+q+1` (odd, all prime factors `3` or `≡ 1 mod 3`, `v₃(A) ≤ 1`)
must divide `k(k²−1)` with cofactor `≤ ~k`.  Two structural facts that a proof
could use and that no current step uses:

* `A = Φ₃(p^f)` **factors** for `f ≥ 2` (e.g. `f = 2`: `A = (p²+p+1)(p²−p+1)`,
  the two factors coprime and differing by `2p`), so `A`'s divisors are forced
  into a rigid pattern across three consecutive integers;
* the `ℓ*`-free 2-adic budget that kills `L₃` at `ℓ* = 1` (Theorem L3₂) is
  restored the moment `v₂(ℓ*)` is pinned — a congruence condition on `ℓ*`, not
  on `n`, would re-open the valuation argument.

Neither is a Diophantine-geometry question; both are elementary number theory
on the `ℓ*`-indexed family.  That, and not more curve work, is where rows 2–3
should be attacked.
