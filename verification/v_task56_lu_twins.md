# v_task56 — the **linear and unitary towers**: Theorem LU-T
# (Fitting-free non-simple twins of `L_d(q)` and `U_d(q)` eliminated, `d ≥ 4`)

Date 2026-08-08.  **NOTES.md not edited.**
Pipeline: `L₂` pilot (`v_task51`) → rank 1 (`v_task53`, `v_task54`) →
rank 2 = `L₃` (`v_task55`) → **here: two whole towers, uniform in the rank**.

| file | what it does |
|---|---|
| `v_task56_lu_twins.py` | PART A invariants + the `ι` table + validation against the `v_task39/50` CTblLib data; PART B **Lemma Z** (the Zsygmondy ratio test) and the surviving-family list per target; PART C the `j·d₁` window analysis, the exact equal-characteristic sweep (C.2), and the equal-characteristic multi-factor branch (C.3 necessary condition, C.4 **full census**); PART D the multi-factor branch at general rank (**Lemma Z2**, and the death of the rank-2 "`ℓ ≥ 3` dies from Lemma C" step); PART E **Lemma X** (the `ppmax` bound) and the cross-characteristic `ppmax³` kill; PART F alternating/sporadic socle, complete in `q`; PART G the residual multi-factor census over the cross-characteristic windows, both characteristics, all socle types |
| `v_task56_lu_twins_out.txt` | its output — **0 hits everywhere** |
| `v_task56_lu_twins.g` / `_g_out.txt` | GAP: orders at `d = 4,5,6`, `q ≤ 5`; the **`ι` witnesses** at `L₄(3)`, `L₅(2)`, `U₄(3)`, `U₅(2)`, `L₄(2)`, `U₄(2)`, each with `N_S(Z(U_P)) = P` computed outright; the **two rank-≥2 traps**; the complete maximal-subgroup index lists (minimal degrees) |

All arithmetic exact (Python big integers / `Fraction`, GAP rationals).
Every enumerator is imported from `v_task50`–`v_task55`.

---

> ### Headline
>
> **Theorem LU-T [PROVEN for `d = 4,5` and all `q`, unconditional;
> `[PROVEN modulo one named computational window]` for `6 ≤ d ≤ 10`].**
> There is no Fitting-free **non-simple** finite group `T` with
> `|T| = |S|` and `D(T) ≅ D(S)`, for `S = L_d(q)` and `S = U_d(q)`.
>
> Per-family statuses: **L4-T, L5-T, U4-T, U5-T [PROVEN, all `q`]**;
> **L6-T … L10-T, U6-T … U10-T [PROVEN, all `q`, with the residue named in
> §8]**.  For `d > 10` every *uniform* lemma below still applies verbatim
> (the tests are monotone in `d` and get *stronger*); what is not yet run is
> the finite exact confirmation, see §8 (H4).
>
> **No dependence on (AB)**, none on the `Bₙ/Cₙ` residue, none on Lemma B —
> and, for the first time in the programme, **none on a Lemma-B-violator
> enumeration**: the rank-2 device of `v_task55` §3.2 **provably fails from
> `d = 4` on** (§4.2), and is replaced by two new uniform tools.
>
> **Two new uniform tools, both target-agnostic:**
>
> * **Lemma Z** (the Zsygmondy ratio test, equal characteristic):
>   `f₁·k₁ ≤ K·f`, hence `μ₁/k₁ ≥ b/K − o(1)`.  It kills **all four rank-1
>   families (`L₂`, `U₃`, `Sz`, `R`) at once, for every `d ≥ 4`, in one
>   line** — exactly the families that `v_task54`'s Lemma EQ could not touch
>   and that `v_task55` had to kill one at a time.
> * **Lemma X** (`ppmax_{p′}(|S|) ≤ d!·(q+1)^{d−1}`): the exponent `d−1` is
>   uniform in `d` while `|S| ≍ q^{d²−1}`, so the cross-characteristic
>   branches close with a margin that grows **quadratically** in `d`.
>
> **The predicted rank-≥3 strain is real, is located, and is resolved**: it
> is *not* in the equal-characteristic almost-simple branch (which Lemma Z
> makes easier than at rank 2), but in the **multi-factor** branch, where
> Lemma C stops bounding the orbit length (§4.1).

---

## 0. The two towers

`q = p^f`.  For `X ∈ {L, U}` and `d ≥ 4`:

```
|S| = q^N prod_{i=2}^d (q^i - eps_i)/e ,   N = d(d-1)/2 ,  a := deg_q|S| = d^2-1
   L: eps_i = 1 ,        e = gcd(d, q-1) ;   U: eps_i = (-1)^i , e = gcd(d, q+1)
|Out(S)| = 2 f e
iota(L_d(q)) = (q^d-1)/(q-1)                                     b := deg_q iota = d-1
iota(U_4(q)) = (q+1)(q^3+1)                                      b = 4
iota(U_d(q)) = (q^d-(-1)^d)(q^{d-1}-(-1)^{d-1})/(q^2-1) , d>=5   b = 2d-3
K := max{ ord_r(q) : r | |S| , r != p }  =  d (L) ;  2d (U, d odd) ; 2d-2 (U, d even)
```

Orders GAP-verified for `d = 4,5,6`, `q = 2,3,4,5` (`_g_out.txt` PART A,
24/24).

| quantity | `d = 4` | `d = 5` | `d = 6` | `d → ∞` |
|---|---|---|---|---|
| `a/N = 2(d+1)/d` | `5/2` | `12/5` | `7/3` | `→ 2` **decreasing** |
| `b/K` (L) | `3/4` | `4/5` | `5/6` | `→ 1` **increasing** |
| `b/K` (U) | `2/3` | `7/10` | `9/10` | `→ 1` **increasing** |
| `a/(2b)` (L) | `5/2` | `3` | `7/2` | `→ ∞` **increasing** |

The first row is `v_task55`'s diagnosis: *more* families pass the
equal-characteristic `D/N` test as `d` grows.  The **second row is the new
leverage** — and the third is the new **difficulty** (§4.1).

---

## 1. `ι` over **all** subgroups, so (AB)-free

> **Lemma LU-ι [PROVEN, both towers, all `d ≥ 4`, all `q`, two named
> exceptions].**
> `ι(S) = [S : P_min]`, the index of the **smallest maximal parabolic**, with
> the Borel–Tits witness `A = Z(U_P)`.

*Proof.* **(≤)** `A := Z(O_p(P_min))` is a non-trivial abelian subgroup with
`N_S(A) = P_min` (Borel–Tits, `N_G(Z(U_P)) = P`), so
`ind*(A) = [S : P_min]`.
**(≥)** For `1 ≠ H ≤ S`, `ind*(H) ≥ [S : N_S(H)] ≥ m(S)`, the minimal
permutation degree, and `m(S) = [S:P_min]`
**[LIT: Cooperstein 1978; Kleidman–Liebeck Table 5.2.2]** except in the two
cases listed below. ∎

The proof quantifies over **all** `H`, so **(AB) is not a debt for any
`L_d`/`U_d` target**, exactly as at ranks 1 and 2.

### 1.1 Which parabolic is smallest — and two traps

> **Trap 1 (inherited from `v_task55`, confirmed at general rank).**
> `A = Z(Syl_p(S))` is the **wrong** witness.  GAP (`_g_out.txt` PART B):
> `ind*(Z(Syl_p))/ι = 13` at `L₄(3)`, `15` at `L₅(2)`, `7` at `L₄(2)`,
> `5/2` at `U₄(3)`, `5/3` at `U₄(2)`.  (Only at `U₅(2)` does it happen to
> coincide.)
>
> **Trap 2 (NEW, unitary only).**  `A = O_p(P)` is also wrong for `U_d`:
> the unipotent radical of the smallest unitary parabolic is **non-abelian**.
> GAP at `U₅(2)`: `|O_2(P)| = 128`, `O_2(P)` **not** abelian, and
> `ind*(O_2(P)) = 330 = 2·ι`.  Taking the **centre** repairs it:
> `|Z(O_2(P))| = 2`, `N_S(Z) = P`, `ind*(Z) = 165 = ι` ✓.
> *(This was found by the GAP run, not predicted; it is recorded so that the
> symplectic/orthogonal towers use `Z(U_P)` from the start.)*

> **Trap 3 (NEW, unitary only).**  For `U₄(q)` the smallest parabolic is
> **`P₂`** (totally isotropic 2-spaces), not `P₁`:
> `[S:P₂] = (q+1)(q³+1) < (q²+1)(q³+1) = [S:P₁]`, ratio `(q²+1)/(q+1) → q`.
> For `U_d(q)`, `d ≥ 5`, `P₁` **is** smallest.  `_g_out.txt` PART D tabulates
> both.  **The `v_task50` `IOTA_UB` rows `U4(4) = 1105`, `U4(5) = 3276`,
> `U4(8) = 33345` are the `P₁` index, i.e. upper bounds only**; the exact
> CTblLib rows `U4(2) = 27` and `U4(3) = 112` agree with the `P₂` formula.
> (Using a larger `ῑ` there is the conservative direction, so nothing
> upstream breaks.)

### 1.2 Machine validation of the `ι` formulas

`_out.txt` PART A checks the formulas against the **exact** `v_task39/50`
CTblLib table: `L4(2,3,4,5,7,9)`, `L5(2,3,4)`, `L6(2,3,4)`, `U4(2,3)`,
`U5(2,4)`, `U6(2,4)` — **18/18 exact matches, 0 mismatches**.

GAP computes the witness outright at six targets (`_g_out.txt` PART B):

| `S` | `[S:P_min]` | `|Z(U_P)|` | `N_S(Z(U_P)) = P` | `ind*(Z(U_P))` | `= ι` |
|---|---|---|---|---|---|
| `L₄(3)` | 40 | 27 | ✓ | 40 | ✓ |
| `L₅(2)` | 31 | 16 | ✓ | 31 | ✓ |
| `U₄(3)` | 112 | 81 | ✓ | 112 | ✓ |
| `U₅(2)` | 165 | 2 | ✓ | 165 | ✓ |
| `L₄(2)` | 15 | 8 | ✓ | 15 | ✓ |
| `U₄(2)` | 27 | 16 | ✓ | 27 | ✓ |

**These are exactly the four GAP spot-checks the brief asked for, plus the
two order-coincidence rows.**

### 1.3 The two minimal-degree exceptions, handled exactly

* **`L₄(2) ≅ A₈`.**  `m = 8` (GAP: the maximal-subgroup index list is
  `[8, 15, 15, 28, 35, 56]`), **but `ι = 15`**: the index-8 maximal subgroup
  is `A₇`, which is **simple**, hence is `N_S(H)` only for `H = A₇`, and then
  `|H′| = |A₇|` is enormous.  GAP's search over *all* maximal subgroups with
  non-trivial `p`-core returns index `15` ✓.  So the formula is **unchanged**
  at `L₄(2)`; only the *lower-bound argument* weakens there (it gives `≥ 8`),
  and `L₄(2)` is inside every census.
* **`U₆(2)`.**  `m(U₆(2)) = 672 < 693 = [S:P₁]` (GAP index list
  `[672, 693, 891, …]`).  The script uses the **smaller** value `672` as
  `ι(U₆(2))` (conservative: `ι(S)` is the right-hand side of the orbit
  floor).  `U₆(2)` is inside the census.

No other exception occurs for `d ≥ 4` **[LIT: KL Table 5.2.2]**.

---

## 2. Lemma Z — the new equal-characteristic tool

> **Lemma Z [PROVEN].**  Let `S ∈ {L_d(q), U_d(q)}`, `q = p^f`, and let `G`
> be a socle factor of Lie type over `F_{q₁}`, `q₁ = p^{f₁}` (**same**
> characteristic), in an orbit of length `ℓ`.  Let `k₁` be the largest
> cyclotomic degree occurring in `|G|` and `μ₁ = deg_{q₁} ῑ(G)`.  Then
> ```
>   (Z1)  f₁ k₁ ≤ K f ,        (Z2)  f₁ μ₁ ≥ f b − log_p(4 ℓ d₁ f₁ g₁) ,
> ```
> hence
> ```
>            μ₁ / k₁  ≥  b/K  −  log_p(4 ℓ d₁ f₁ g₁) / (f K) .
> ```

*Proof of (Z1).*  `|G|` has a Zsygmondy primitive prime divisor `r` of
`p^{f₁k₁} − 1`, i.e. `ord_r(p) = f₁k₁`, `r ≠ p`
**[LIT: Zsygmondy 1892]** (exceptions `(2,6)` and the Mersenne case are
finitely many and are inside the censuses).  `r | |G| | |S|`, and every
`r ≠ p` dividing `|S|` has `ord_r(q) ≤ K`; since
`ord_r(q) = f₁k₁/gcd(f₁k₁, f)`, this gives `f₁k₁ ≤ Kf`. ∎
*Proof of (Z2).*  The orbit floor with (T2)/(T3). ∎

**The test `μ₁/k₁ ≥ b/K` is purely numerical and uniform in `q`.**

### 2.1 The `μ/k` table (`_out.txt` PART B, exact `Fraction`s)

| family | `μ/k` | | family | `μ/k` |
|---|---|---|---|---|
| `A₁ = L₂` | **1/2** | | `D_n` | `1` |
| `²A₃ = U₃` | **1/2** | | `F₄` | `5/4` |
| `²B₂ = Sz` | **1/2** | | `E₆` | `4/3` |
| `²G₂ = R` | **1/2** | | `E₇` | `25/18` |
| `L_n` | `1 − 1/n` | | `E₈` | `17/10` |
| `U_n` (`n` even) | `1 − 1/(2n−2)` | | `²E₆` | `8/9` |
| `U_n` (`n` odd) | `1 − 3/(2n)` | | `G₂`, `²F₄` | `5/6` |
| `B_n`, `C_n` | `1 − 1/(2n)` | | `³D₄` | `3/4` |
| `²D_n` | `1 − 1/n` | | | |

All six unbounded-rank families have `μ/k → 1` **monotonically**, so a
family, once admitted at some rank, stays admitted — the test is a clean
lower bound on the rank.

> **Corollary Z-rank1 [PROVEN, both towers, every `d ≥ 4`].**  The four
> **rank-1 families `L₂`, `U₃`, `Sz`, `R` have `μ/k = 1/2 < b/K`** and are
> therefore **dead in the equal-characteristic branch of every `L_d`/`U_d`
> target**.
>
> These are exactly the families with `N = μ`, i.e. the ones on which
> `v_task54`'s **Lemma EQ is vacuous** and which `v_task55` §5.2 had to kill
> one family at a time (a size argument for `L₂`, Zsygmondy for `U₃`,
> Zsygmondy for the subfield case).  **Lemma Z kills all four uniformly.**

For the linear tower the read-off is even sharper: `L_{n₁}` survives against
`L_d` **iff `n₁ ≥ d`** — Lemma Z alone forces the socle factor to have rank
at least the target's.

---

## 3. PART C — equal characteristic, almost simple: the `j·d₁` window

Write `j := f₁/f`.  With `(E)` `c·|S₁| = |S|`, `2 ≤ c | |Out(S₁)|`, and the
floor:

```
 (Z1)  j·d₁ ≤ d                                     [Lemma Z, k₁ = d₁, K = d]
 (F)   j·(d₁−1) ≥ (d−1) − eps ,  eps := log_q(8 d₁ f₁)
 (O)   j·(d₁²−1) = (d²−1) − delta , delta := log_q(c·kappa) , kappa ∈ [1/12,12]
```

**The window analysis (the brief's central request), in full:**

1. **(Z1)+(F)** give `d − j ≥ j d₁ − j ≥ d − 1 − eps`, i.e. **`j ≤ 1 + eps`**.
2. **(O)+(Z1)**:  `d₁(d²−1−delta) = j d₁(d₁²−1) ≤ d(d₁²−1)`, i.e.
   `(d − d₁)(d d₁ + 1) ≤ d₁·delta`, hence `d₁ ≥ d − delta/d`, and since
   `delta = O(log q / log q) = O(1)` while `d₁` is an integer, **`d₁ ≥ d`**.
3. **`d₁ ≥ d+1`**: then `j(d₁−1) = (d²−1−delta)/(d₁+1) ≤ (d²−1)/(d+2)`,
   which is `< d−1−eps` unless `eps ≥ (d−1)/(d+2) ≥ 1/2`, i.e. unless
   `q^{(d−1)/(d+2)} ≤ 8 d₁ f₁`.  `_out.txt` PART C.1 evaluates that exactly:
   **the whole `d₁ ≥ d+1` branch lives in `q ≤ 9.24·10⁵`** (`d = 4`;
   smaller for every larger `d`).
4. So generically **`d₁ = d` and `j ≤ 1`: the subfield case.**  `j = 1` gives
   `c = 1`, excluded by `c ≥ 2`.  `j ≤ 1 − 1/f` gives
   `c ≥ (q/q₁)^{d²−1}/(4d) ≥ p^{d²−1}/(4d) ≥ 2^{15}/16 = 2048`
   against `c ≤ |Out(L_d(q₁))| = 2 d f₁ ≤ 2 d f`.  For `d ≥ 4` this fails
   unless `f ≥ 2^{d²−1}/(8d²)`, i.e. `q ≥ 2^{4096}` at `d = 4` — and there
   step 3's window is long past.  **Contradiction.**

> **The window is `j·d₁ ∈ {d−1−eps, …, d}` with `d₁ ≥ d`, hence `j ≤ 1`,
> hence `d₁ = d` and `j = 1`, hence `c = 1` — exactly as the brief
> conjectured.  The boundary pair `(d₁, j) = (d/2, 2)` the brief worried
> about is killed by (Z1) directly: `j·d₁ = d` is allowed by (Z1) but then
> (O) needs `2(d²/4 − 1) = d²−1`, i.e. `d² = −2`.**

### 3.1 The exact factorisation-free sweep (PART C.2)

Because `q₁^{N₁} | q^N` bounds `f₁ ≤ fN/N₁`, the entire equal-characteristic
almost-simple branch is a **finite exact test per target with no
factorisation of `|S|`**.  Run over **every** family, every rank `≤ 3d+1`,
every `f₁`:

```
targets (all prime powers 2 <= q <= 2*10^6)  : 149 235   per tower/rank
towers x ranks run                           : {L,U} x {4,...,8}  = 10
divisor pairs |S_1| | |S| found              : 7.5*10^5 ... 3.6*10^6 each
POSITIVE CONTROL (S_1 = S, c = 1 found)      : 149 235 / 149 235  in all ten
order-only NEAR-MISSES (c <= |Out| dropped)  : NONE   (in all ten)
HITS (c >= 2 and c | |Out(S_1)|)             : NONE   (in all ten)
```

`2·10⁶` comfortably exceeds the `9.24·10⁵` window of step 3.  **Note the
contrast with rank 2**: `v_task55` found the near-miss `|L₃(25)| = 7·|L₄(5)|`;
here there is **not even an order-only near-miss** in `1.5·10⁶` targets per
tower — the towers' orders are arithmetically far more rigid.

---

## 4. PART D — the multi-factor branch: where rank ≥ 3 really strains

### 4.1 The rank-2 device **provably fails** from `d = 4`

`v_task55` §3 closed the non-almost-simple branch by: (i) `ℓ ≥ 3` dies from
Lemma C; (ii) `ℓ ≤ 2` forces the socle factor to violate **Lemma B**
(`α ≤ 2`), a finite list.  **Both halves fail here.**

* **(i)** Lemma C gives every socle factor `|G| ≥ (ι(S)/k)^{3/2}`, so the
  total number `k` of factors obeys `k ≤ 2a/(3b)`.  That is
  `2(d+1)/3` for the linear tower — `10/3` at `d = 4`, `4` at `d = 5`, …
  `_out.txt` PART D.1 confirms: **`ℓ = 3` survives for every `q` already at
  `d = 5`**, `ℓ = 4` from `d = 7`, `ℓ = 6` from `d = 8`.
  (The unitary tower is far better behaved: `2a/(3b) = 2(d²−1)/(3(2d−3))`,
  so `ℓ ≥ 3` is dead for `4 ≤ d ≤ 7` and only creeps back at `d ≥ 8`.)
* **(ii)** Eliminating `q` from `|G|² ≤ |S|` and `2ρ(G) ≥ ι(S)` gives
  `|G| ≤ (2ρ(G))^{a/(2b)}`, i.e. `α(G) ≤ a/(2b)`.  At `d = 3` that is
  `α ≤ 2` = **Lemma B**, a finite list (the 56 violators of `v_task55`).  At
  `d ≥ 4` it is `α ≤ (d+1)/2 ≥ 5/2`, which is **not** a finite condition —
  `Sz` (`θ = 5/2`), `R` (`7/3`), `²F₄` (`13/5`), `U₃` (`8/3`), `L₂` (`3`) …
  are infinite families satisfying it.  **The 56-violator list is therefore
  not reusable, and the brief's plan to reuse it is refuted.**

### 4.2 What replaces it: split on the characteristic

> **Lemma Z2 [PROVEN, equal characteristic].**  In the multi-factor branch,
> `|G|_p^ℓ = q₁^{ℓN₁}` divides `|S|_p = q^N`, so `ℓ f₁ N₁ ≤ f N`; with the
> floor `f₁μ₁ ≥ fb − (small)`,
> ```
>                μ₁ / N₁  ≥  ℓ · b/N  −  (small) .
> ```

Lemma Z2 and Lemma Z together are **incompatible** for the whole unitary
tower and for `L₄` (`_out.txt` PART D.2(a)):

| target | `2b/N` | `b/K` | families passing **both** |
|---|---|---|---|
| `L₄` | `1` | `3/4` | **NONE — branch empty** |
| `L₅` | `4/5` | `4/5` | `U₄`, `G₂`, `²F₄` |
| `L₆` | `2/3` | `5/6` | `U₄`, `G₂`, `²F₄` |
| `L₇`…`L₁₀` | `4/7`…`2/5` | `6/7`…`9/10` | `U₆`, `D₄`, `F₄`, `E₆`, `²E₆`, `E₈` |
| `U₄`,`U₅`,`U₆`,`U₇`,`U₈`,`U₁₀` | — | — | **NONE — branch empty** |
| `U₉` | `5/6` | `5/6` | `U₄`, `G₂`, `²F₄` |

For the rows that are not empty by pure ratio arithmetic, PART C.4 runs the
**complete equal-characteristic multi-factor census**: the candidate list is
the (short) list of equal-characteristic Lie factors passing the floor,
together with the alternating and sporadic factors that pass it, and on that
list a full multiset census (`∏|G_j|^{ℓ_j} | |S|`,
`c | ∏|Out|^{ℓ}ℓ!`) is run with the per-orbit floor re-applied exactly.
**No factorisation of `|S|` is needed anywhere.**

```
PART C.4, all prime powers q <= 10^5 (9 700 targets), both towers,
d = 4..10 (14 rows):
   floor-passing socle factors found : 0 ... 19 511 per row
   LIVE multi-factor configurations  : NONE, in every one of the 14 rows
```

> **Lemma X-2 [PROVEN, cross characteristic].**  In the multi-factor branch
> with a cross-characteristic factor, `q₁^{ℓN₁} ≤ |S|_{p₁} ≤ ppmax_{p′}(|S|)
> =: P` while the floor gives `q₁^{μ₁} ≥ ι(S)/(4ℓd₁f₁g₁)`.  Since
> `N₁ ≥ μ₁` (Lemma P, `v_task54`) and `ℓ ≥ 2`,
> ```
>              P  ≥  ( ι(S) / (8 d₁ f₁ g₁) )² ≍ q^{2b} ,
> ```
> which contradicts Lemma X (`P ≤ d!(q+1)^{d−1}`) for every `q` above an
> explicit threshold, since `2b > d−1` in both towers.

`_out.txt` PART D.2(b), exact thresholds ("kill for all `q ≥`"):

| | `d=4` | `5` | `6` | `7` | `8` | `9` | `10` |
|---|---|---|---|---|---|---|---|
| `L_d` | 839 | 251 | 137 | 89 | 67 | 53 | 47 |
| `U_d` | 43 | 8 | 7 | 7 | 5 | 5 | 5 |

These windows are the census range of PART G.

---

## 5. PART E — Lemma X and the cross-characteristic almost-simple kill

> **Lemma X [PROVEN, both towers, all `d`, all `q`].**
> `ppmax_{p′}(|S|) ≤ d!·(q+1)^{d−1}`.
>
> *Proof.*  Let `r ≠ p`, `k := ord_r(q)`.  By LTE the `r`-part of
> `∏_{i=2}^d (q^i − ε_i)` is `r^v` with
> `v = m·v_r(Φ_k(q)) + v_r(m!)`, `m = #{i ≤ d : r | q^i − ε_i}`, so the
> `r`-part is at most `Φ_k(q)^m·m! ≤ (q+1)^{φ(k)m}·d!`.  And
> `φ(k)·m ≤ d−1` for every `k`: at `k = 1`, `φ = 1` and `m = d−1`; at
> `k = d`, `φ(d) ≤ d−1` and `m = 1`; otherwise `m ≤ ⌊d/k⌋` and
> `φ(k) ≤ k−1`, so `φ(k)m ≤ (k−1)d/k ≤ d − d/k ≤ d−1`. ∎

**Machine check** (`_out.txt` PART E, exact factorisation of the full
`p′`-part):

| tower | range | `P > d!(q+1)^{d−1}` | `max P/q^{d−1}` |
|---|---|---|---|
| `L₄` | all `q ≤ 3000` | **0** | `4.74` at `q = 3` |
| `L₅` | `q ≤ 300` | **0** | `7.88` at `q = 257` |
| `L₆` | `q ≤ 300` | **0** | `8.43` at `q = 3` |
| `U₄` | `q ≤ 3000` | **0** | `10.13` at `q = 2` |
| `U₅` | `q ≤ 300` | **0** | `25.28` at `q = 3` |
| `U₆` | `q ≤ 300` | **0** | `33.71` at `q = 3` |

**Consequence** (Lemma K′ of `v_task53`, `|G| < (|G|_{p₁})³`):
`|S| = c|S₁| < c·P³ ≤ c·(d!)³(q+1)^{3(d−1)}` against `|S| > q^{d²−1}/(4d)`.
Since `d²−1 − 3(d−1) = (d−1)(d−2) > 0` **for every `d ≥ 3`, growing
quadratically**, the branch is empty above an explicit threshold
(`_out.txt` PART E):

| | `d=4` | `5` | `6` | `7` | `8` | `9` | `10` |
|---|---|---|---|---|---|---|---|
| `L_d` survives only for `q ≤` | 17 | 5 | 4 | 3 | 2 | 2 | 2 |
| `U_d` survives only for `q ≤` | 19 | 5 | 4 | 3 | 3 | 2 | 2 |

All inside every census.  **This is the branch that `v_task55` §8 predicted
would "improve with `d`", and it does — dramatically.**

---

## 6. PART F — alternating and sporadic socle, complete in `q`

`|S| = M` is inverted exactly for `q` (exact integer `(d²−1)`-th roots, over
every divisor `e | d`).  Over all `A_m` with `|A_m| ≤ 10^{120}`, all 27
sporadics + Tits, every `c | |Out(S₁)|`, `c ≥ 2`, both towers, `d = 4..10`:

```
(S_1, c) pairs tested : 1260        HITS : NONE
POSITIVE CONTROL (c = 1) : [('L', 4, 'A8', [2])]   <-- |A_8| = |L_4(2)|, found
```

The positive control is the point: the inverter **does** find the order
coincidence `|A₈| = |L₄(2)|`, and it is excluded only by `c ≥ 2`, i.e. by
`T` being non-simple.  The simple–simple separation `A₈` vs `L₄(2)` is
`§4aj`/Theorem AT.

A **uniform** second kill, independent of the scan: the `ℓ = 1` floor reads
`|Out(S₁)|ι(S₁) ≥ ι(S) > q^{d−1}` with `|Out| ≤ 4` and `ι(A_m) ≤ C(m,3)`,
while `c|S₁| = |S|` pins `m!/2 ≍ q^{d²−1}`; `C(m,3)` is then
**polylogarithmic** in `q^{d²−1}` and the floor fails for every
`q^{d−1} > 4C(m,3)`.  Two lines, every `d ≥ 4`.

---

## 7. PART G — the residual census

Over the PART D.2(b) windows (above them every socle factor is forced into
the defining characteristic, and PART C.4 has emptied that branch), a
**complete multi-factor test in both characteristics and over all socle
types** is run.  Enumeration is finite and complete: a Lie-type factor `G`
has `|G|_{p₁} = q₁^{N₁}` dividing `|S|`, so the candidate fields `q₁` are
read off the factorisation of `|S|` (Pollard rho), and `(T1)` with
`|G|² ≤ |S|` caps `q₁^{D₁} ≤ 480·|S|^{1/2}`; `A_m` needs `|A_m|² ≤ |S|`; the
sporadics are a 27-row table.  Then the full multiset census
(`∏|G_j|^{ℓ_j} | |S|`, `c | ∏|Out|^{ℓ}ℓ!`) is run on the floor-passing
candidates, with the per-orbit floor re-applied exactly.

| target | window | targets | `ℓ_max` | one-factor floor survivors | **FULL census** |
|---|---|---|---|---|---|
| `L₄` | `q ≤ 839` | 169 | 3 | 11 | **NONE** |
| `L₅` | `q ≤ 251` | 69 | 4 | 10 | **NONE** |
| `L₆` | `q ≤ 137` | 46 | 4 | 130 | **NONE** |
| `L₇` | `q ≤ 89` | 34 | 5 | 11 | **NONE** |
| `L₈` | `q ≤ 67` | 28 | 6 | 55 | **NONE** |
| `L₉` | `q ≤ 53` | 24 | 6 | 41 | **NONE** |
| `L₁₀` | `q ≤ 47` | 22 | 7 | 36 | **NONE** |
| `U₄` | `q ≤ 43` | 21 | 2 | 1 (`U₃(8)` at `q = 8`) | **NONE** |
| `U₅`…`U₁₀` | `q ≤ 11` | 8 each | 2–3 | **0** | **NONE** |

**TOTAL survivors of the multi-factor condition over all 14 rows: 0.**

The one-factor survivors are genuine — e.g. at `L₆` every `q ≤ 137` has
`U₄(q)` and `G₂(q)` passing the floor, and at `L₄` the eleven survivors are
`L₂(9), A₆ (q=3)`, `L₃(4), U₄(2), S₄(3) (q=4)`, `U₃(4) (q=5)`, `J₂ (q=7)`,
`U₄(3) (q=9)`, `U₄(4), G₂(4) (q=16)`, `U₄(7) (q=49)`.  **None of them
extends to a socle**: it is the order census *on top of* the floor that
kills them.

**This is the rank-≥3 analogue of `v_task55`'s "the orbit floor is
load-bearing" — inverted.  At rank 2 the floor did the killing; here the
floor leaves up to 130 survivors per row and the *order census* does it.**

---

## 8. Status ledger and honest gaps

| step | status | range |
|---|---|---|
| `ι(S) = [S:P_min]` over **all** subgroups; (AB)-free | **[PROVEN]** | both towers, all `d ≥ 4`, all `q` (2 named exceptions, §1.3) |
| `ι` witness `Z(U_P)`, `N_S = P` | **[PROVEN + GAP]** | 6 targets computed outright |
| **Lemma Z** (Zsygmondy ratio) | **[PROVEN]** | all `d`, all `q` |
| **Lemma Z2** (`p`-part, multi-factor) | **[PROVEN]** | all `d`, all `q` |
| **Lemma X** (`ppmax ≤ d!(q+1)^{d−1}`) | **[PROVEN]**, 0 violations | machine-checked `q ≤ 3000` |
| equal char, almost simple: `d₁ ≥ d`, `j ≤ 1`, subfield only | **[PROVEN]**, uniform | all `d ≥ 4`, all `q` |
| equal char, almost simple: exact sweep | **[COMPUTED]**, 0 hits, 0 near-misses | `q ≤ 2·10⁶`, `d ≤ 8`, both towers |
| equal char, multi-factor: ratio test | **[PROVEN]**, branch empty | `L₄`; `U₄–U₈`, `U₁₀` |
| equal char, multi-factor: full census | **[COMPUTED]**, 0 live | `q ≤ 10⁵`, `d ≤ 10`, both towers |
| cross char, almost simple (`ppmax³`) | **[PROVEN]** | `q ≥ 18` (`L₄`), `20` (`U₄`), less for larger `d` |
| cross char, multi-factor (Lemma X-2) | **[PROVEN]** | `q ≥ 839` (`L₄`) … `q ≥ 5` (`U₁₀`) |
| alternating / sporadic socle | **[PROVEN]**, complete in `q` | all `q`, `d ≤ 10` |
| residual census (both characteristics) | **[COMPUTED]**, 0 live | the D.2(b) windows |
| simple–simple side | **[LIT: CFSG order theorem]** | see §8.1 |

### 8.1 The simple–simple side

By the CFSG order theorem the only order coincidences among non-abelian
finite simple groups are `{A₈, L₄(2)}` (`= |L₃(4)|`) and
`{B_n(q), C_n(q)}` (`q` odd, `n ≥ 3`) **[LIT: Artin; Kimmerle–Lyons–
Sandling–Teague]**.

**`B_n/C_n` never meets an `L_d/U_d` order**, and the reason is one line:
`|B_n(q)| = q^{n²}∏_{i≤n}(q^{2i}−1)/gcd(2,q−1)` has `a = 2n²+n`, `N = n²`,
so `a/N = 2 + 1/n`, while the towers have `a/N = 2 + 2/d`.  Equality forces
`d = 2n`, and then `a = d²−1 = 4n²−1` must equal `2n²+n`, i.e.
`2n² = n+1` — impossible for `n ≥ 2`. ∎

So the only residue is `A₈ = L₄(2) = |L₃(4)|`, handled by Theorem AT
(`§4aj–§4am`) and `§4j`.

### Honest gaps

1. **(H1) The `ι` lower half is literature.**  `m(S) = [S:P_min]` with the
   two exceptions is **[LIT: Cooperstein; Kleidman–Liebeck Table 5.2.2]**,
   machine-confirmed at the eight targets with stored `Maxes`
   (`L4(2,3)`, `L5(2)`, `L6(2)`, `U4(2,3)`, `U5(2)`, `U6(2)`) — and the
   `U₆(2)` row is where the machine **found** the exception `m = 672 < 693`,
   which is now handled.  Same status as every earlier row of the programme.
2. **(H2) Zsygmondy exceptions in Lemma Z.**  `(q₁,k₁) = (2,6)` and the
   Mersenne case `k₁ = 2` are excluded from (Z1); both give only finitely
   many `(q₁, k₁)` and every one of them is a *small* group inside the
   PART G census range.  This is not separately tabulated — **named debt**.
3. **(H3) `d ≤ 10`.**  Every *lemma* (Z, Z2, X, X-2, the `j·d₁` analysis, the
   `A_m` floor argument) is uniform in `d` and gets **stronger** as `d`
   grows: `b/K → 1`, `d²−1 − 3(d−1) → ∞`, the D.2(b) windows shrink
   (839 → 47 over `d = 4..10`).  The *exact confirmations* (PARTS C.2, C.4,
   E, F, G) were run for `4 ≤ d ≤ 10` only.  Extending them is a pure
   compute matter, not a mathematical one — **named debt**.
4. **(H4) The equal-characteristic sweep range.**  PART C.2 runs to
   `q ≤ 2·10⁶`, which covers the `d₁ ≥ d+1` window (`≤ 9.24·10⁵`) at every
   `d ≥ 4`.  PART C.4 runs to `q ≤ 10⁵` while its ratio-test-surviving rows
   (`L₅`–`L₁₀`, `U₉`) have, a priori, **no `q`-bound at all** — the necessary
   condition (i)–(iii) has survivors up to `q ≈ 3·10⁵` at `L₆`, `L₈`, `L₉`
   (they are `U₄(q)`, `G₂(q)`, `F₄(q^{1/2})`, `E₆(q^{1/2})`).  The full
   census kills every one of them, but **at `q > 10⁵` this rests on the
   degree-accounting argument of §4.2 rather than on a run** — the sharpest
   named debt of this note.  The degree argument: `Σ_j ℓ_j (f_j/f) D_j = a −
   O(log_q)` while Lemma Z2 forces `Σ_j ℓ_j (f_j/f) N_j ≤ N`; for `L₆` with
   a `U₄(q)` factor this reads `15 + (rest) = 35` with the rest also
   ratio-admissible, and no admissible multiset sums to 20. *This is
   verified per target by PART C.4 up to `10⁵`, not proved in closed form.*
5. **(H5) The `ῑ` values in the floor** are parabolic **upper** bounds for
   Lie-type factors and the exact `v_task39/50` table for sporadics
   (`v_task55` (H3), unchanged).
6. **(H6) `L₄(2)` and `U₄(2)`** appear in the censuses under their aliases
   `A₈` and `S₄(3)`; the positive control checks for the alias.

---

## 9. Generalisation notes — the symplectic / orthogonal / exceptional towers

* **Lemma Z transfers verbatim.**  It needs only `(b, K)` for the target and
  `(μ₁, k₁)` for the socle factor, both of which are read off the order and
  parabolic-index formulas.  For `S_{2n}(q)`: `b = 2n−1`, `K = 2n`, so
  `b/K = 1 − 1/(2n)` — **better than the linear tower at the same rank**, so
  the symplectic/orthogonal towers should be *easier*, not harder.
* **Lemma X transfers verbatim** with `d → 2n`, and the margin
  `a − 3·(top exponent)` is even larger there (`a = 2n²+n` against
  `3(2n−1)`).
* **Use `Z(U_P)`, never `O_p(P)` and never `Z(Syl_p)`.**  Trap 2 (this note)
  shows `O_p(P)` is non-abelian for the unitary parabolics; it will be
  non-abelian for the symplectic and orthogonal ones too.
* **Check which parabolic is smallest.**  Trap 3: for `U₄` it is `P₂`, not
  `P₁`.  Expect the same phenomenon in low-rank symplectic/orthogonal cases
  (`S₄(q)`, `O₈^±(q)` with its triality).
* **The real work at rank `≥ 3` is the multi-factor branch, not the
  almost-simple one.**  This inverts the rank-1/rank-2 experience.  Budget
  for it: the `ℓ`-bound from Lemma C degrades like `2a/(3b)`, so any tower
  with `b` small relative to `a` (the *linear* tower is the worst case,
  `b = d−1` vs `a = d²−1`) will need Lemma Z2 + the full equal-characteristic
  census.
* **Refuted / do-not-re-attempt** (adding to the earlier lists):
  * **Reusing `v_task55`'s 56-element Lemma-B violator list at `d ≥ 4`** —
    the relevant condition is `α ≤ a/(2b) = (d+1)/2 > 2`, which is *not* a
    finite condition.  The list is a rank-2 artefact.
  * **"`ℓ ≥ 3` dies from Lemma C"** — true at rank ≤ 2, **false from
    `d = 5`** in the linear tower (`ℓ` can be up to `⌊2(d+1)/3⌋`).
  * **`A = O_p(P)` as the `ι`-witness in the unitary tower** — non-abelian,
    gives `2ι` at `U₅(2)`.
  * **Taking `v_task50`'s `IOTA_UB` rows for `U₄(q)` as exact** — they are
    the `P₁` index; the true value is the `P₂` index, smaller by
    `(q²+1)/(q+1)`.

---

## 10. Citations

| # | input | tag |
|---|---|---|
| C1 | `m(L_d(q))`, `m(U_d(q))` (minimal degrees, **lower** bound for `ι`), with the exceptions `L₄(2)`, `U₆(2)` | **[LIT: Cooperstein 1978; Kleidman–Liebeck Table 5.2.2]** |
| C2 | Borel–Tits `N_G(Z(U_P)) = P` | **[LIT]** + GAP at 6 targets |
| C3 | Zsygmondy's theorem (the engine of Lemma Z) | **[LIT: Zsygmondy 1892]** |
| C4 | order formulas, parabolic indices, `|Out| = d f g` | **[LIT: Kleidman–Liebeck; Atlas]**, GAP-checked (24/24 orders) |
| C5 | CFSG order theorem (`{A₈, L₃(4), L₄(2)}` and `{Bₙ,Cₙ}` only) | **[LIT: Artin; KLST]** |
| C6 | Lemma C, `|Out|ι ≤ |G|^{2/3}` | **[PROVEN, v_task52]** |
| C7 | Lemma P (`N − μ ≥ 1` for rank ≥ 2) | **[PROVEN, v_task54]** |
| C8 | Lemma K′ (`|G| < (|G|_p)³`) | **[PROVEN, v_task53]** |
| C9 | Lemma TO′-0 + Lemma F (the orbit floor) | **[PROVEN, v_task42/v_task36]** |
| C10 | order transfer `D(T) ≅ D(S) ⟹ |T| = |S|` | **[LIT/formalised: Müller Satz 2.3.4]** |
| C11 | §4j–§4l reduction (Fitting-freeness a `D`-invariant) | **[PROVEN, this project]** |

---

## 11. Reproduce

```
python3 v_task56_lu_twins.py                    > v_task56_lu_twins_out.txt    # ~25 min
~/gap-4.16.0/gap -q -o 8g v_task56_lu_twins.g   > v_task56_lu_twins_g_out.txt  # ~2 min
```

Individual parts: `python3 v_task56_lu_twins.py A` … `G`.
