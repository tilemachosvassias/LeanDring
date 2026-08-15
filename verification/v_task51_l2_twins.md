# v_task51 — Fitting-free **non-simple** twins of `L₂(q) = PSL(2,q)`
# eliminated; the PILOT for the Lie targets

Date 2026-08-08.  **NOTES.md not edited.**

| file | what it does |
|---|---|
| `v_task51_l2_twins.py` | Phase-1 order census + Phase-2 orbit floor for **every** prime power `4 ≤ q ≤ 10⁶`; plus the targeted scans of the two residual single-orbit branches (`--l2sub`) and the sweep verifying the two uniform inequalities (`--lemC`) |
| `v_task51_l2_twins_out.txt` | the main census run, `q ≤ 10⁶` (78 732 targets) |
| `v_task51_l2_subcases_out.txt` | branches (E1)–(E4): `L₂(q₁)`-socle, alternating socle, sporadic socle, `ℓ = 1, 2` |
| `v_task51_lemmaBC_out.txt` | Lemma B / **Lemma C** verified over 1 286 simple groups |
| `v_task51_l2_twins.g` / `_g_out.txt` | GAP: **exact** `ind*` spectrum of `L₂(q)` over *all* subgroups (16 values of `q`), `mult₁(L₂(q))` for 21 values of `q`, and `(K)` for `q ≤ 2000` |

The CFSG simple-order enumerator and the multiset census are **imported** from
`v_task50_sporadic_twins.py`, so there is one implementation, already exercised
on 27 independent targets.

> **Headline.**
> **Theorem L2-T.**  Let `q ≥ 4` be a prime power and `S = L₂(q)`.  There is no
> Fitting-free **non-simple** finite group `T` with `|T| = |S|` and
> `D(T) ≅ D(S)`.  Combined with the (classical) uniqueness of `|L₂(q)|` among
> simple orders: **`L₂(q)` is `D`-rigid among all finite groups, for every
> `q ≥ 4`.**
>
> Status: the reduction to **two** single-orbit branches is **[PROVEN,
> uniform in `q`]** and rests on one inequality, **Lemma C**, which is
> `[COMPUTED over 1286 simple groups + asymptotic per family]`, not yet
> `[PROVEN]`.  The two residual branches are `[COMPUTED]` empty: the full
> census for all `q ≤ 10⁶`, and the targeted branch scans far beyond that.
> The `q ≥ 4` claim is therefore **conditional on Lemma C and on the residual
> branches beyond the scanned range** — see §7, which states both debts
> without softening them.
>
> **No dependence on the `Bₙ/Cₙ` residue** (§2), and — unlike the `A_n` and
> sporadic rows — **no dependence on the (AB) hypothesis** (§1.1).

---

## 0. Notation

Notation of `v_task34_transport.md` §0 / `v_task50_sporadic_twins.md` §0.
`T` Fitting-free, `Q = Soc T = ∏_i S_i^{ℓ_i}`, `K` the kernel of the action on
the socle factors, `Ā_i` the induced group, orbits `O` of lengths `ℓ_O`,
`c := [T : Soc T]`,

  `ind*(H) := [G:N_G(H)]·|H′|`, `ι(G) := min_{1≠H≤G} ind*(H) = |G|/κ(G)`,
  `I(G) :=` the set of `ind*` values.

`q = p^f`, `d := gcd(2, q−1)`, `N := |L₂(q)| = q(q²−1)/d`.

---

## 1. The target's invariants, uniform in `q`

The subgroup structure of `L₂(q)` is **Dickson's theorem** [LIT: Dickson 1901;
Huppert I.8.27]: every subgroup of `L₂(q)` is

* elementary-abelian-by-cyclic (a subgroup of a Borel `B = E_q : C_{(q−1)/d}`),
* cyclic of order dividing `(q±1)/d`, or dihedral of order dividing
  `2(q±1)/d`,
* `A₄`, `S₄` (the latter only if `q ≡ ±1 mod 8`), `A₅` (only if
  `q ≡ ±1 mod 10` or `p = 5`),
* `PSL₂(q₀)` or `PGL₂(q₀)` for a subfield `F_{q₀} ⊆ F_q`.

Everything in this section is read off that list; **this is the one
`L₂`-specific input of the whole note** (see §6).

### 1.1 `ι(L₂(q))` — and why the target side is (AB)-free

> **Lemma L2-ι [PROVEN].**  For every prime power `q ≥ 4`,
> **`ι(L₂(q)) = q + 1`**, with exactly two exceptions:
> `ι(L₂(5)) = 5` and `ι(L₂(7)) = 7`.

*Proof.*  **(≤)**  Let `U` be the unipotent radical of a Borel `B`.  `U` is
elementary abelian of order `q`, `N_S(U) = B`, `[S:B] = q+1`, and `U′ = 1`, so
`ind*(U) = q+1`.

**(≥)**  Let `1 ≠ H ≤ S`.  If `N_S(H) = S` then `H ⊴ S`, so `H = S` by
simplicity and `ind*(H) = |S′| = |S| > q+1`.  Otherwise `N_S(H)` is proper, so
`[S:N_S(H)] ≥ m(S)`, the minimal index of a proper subgroup, and
`ind*(H) ≥ m(S)`.  By Dickson (equivalently Galois' classical theorem)
`m(L₂(q)) = q+1` for all `q ≥ 4` **except** `q = 5, 7, 9, 11`, where
`m = 5, 7, 6, 11`.

* `q = 5`: `A₄ = N_{A₅}(V₄)` has index 5 and `V₄` is abelian ⟹ `ι = 5`.
* `q = 7`: `S₄ = N_S(V₄)` has index 7 ⟹ `ι = 7`.
* `q = 9, 11`: the subgroups of index `6`, resp. `11`, are `A₅`, which is
  **maximal** and self-normalising; a subgroup `1 ≠ H` with `N_S(H) = A₅`
  would be a proper non-trivial normal subgroup of `A₅` — impossible.  So no
  `ind*` value equals `6` (resp. `11`), the next available index is `q+1`, and
  `ι = q+1 = 10` (resp. `12`). ∎

**Note the shape of the proof: it quantifies over *all* `H`, not only abelian
`H`.**  The `(AB)` hypothesis that stands over Theorem AT (`A_n`) and Theorem
SPT (sporadics) — "`κ` is attained at an abelian subgroup" — is therefore
**not a debt for an `L₂` target**: `ι(L₂(q))` is unconditional.  The reason is
structural: `ind*(H) ≥ [S:N_S(H)] ≥ m(S)` is already sharp for `L₂`, because
the smallest index is realised by a Borel, which *is* a normaliser.

**Independent check** (`v_task51_l2_twins.g` PART A, exhaustive over all
conjugacy classes of subgroups): for
`q = 4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32` the computed `ι` is
`5,5,7,9,10,12,14,17,18,20,24,26,28,30,32,33` — i.e. `q+1` except at `q = 5,7`,
exactly as claimed.

### 1.2 The spectrum `I(L₂(q))`, and an explicit warning

The same GAP run prints the bottom of `I(S)`; e.g.

| `q` | 8 | 13 | 16 | 17 | 25 | 31 |
|---|---|---|---|---|---|---|
| `ι₁` | 9 | 14 | 17 | 18 | 26 | 32 |
| `ι₂` | 28 | 78 | 85 | 102 | 78 | 465 |

**There is no uniform gap `ι₂/ι₁ ≫ 1`** (`ι₂/ι₁ = 1.5` at `q = 9`, `3` at
`q = 25`, `5` at `q = 16`, `≈ q/2` at `q = 31`) — an earlier draft of this note
tried to use a large `ι₂/ι₁` ratio to kill the `ℓ = 2` branch and that route is
**refuted by the data**.  Recorded so it is not re-attempted.  The proof below
uses only `ι₁`.

### 1.3 `mult₁(L₂(q))`

Lemma CT (`v_task41_r1_census.md`) is exactly the `mult₁` statement for this
target: by Dickson the only perfect non-trivial subgroups of `L₂(q)` are the
`A₅`-copies (present iff `q ≡ ±1 mod 10` or `p = 5`) and the subfield subgroups
`L₂(q₀)`, `q₀ = p^{f₀}`, `f₀ | f`, `q₀ > 3`.  Of these the psn ones are the
maximal `A₅`'s and the maximal subfield subgroups, plus `S` itself.  GAP
(`_g_out.txt` PART B, `RepresentativesPerfectSubgroups`, exhaustive):

| `q` | 4 | 5 | 7 | 8 | 9 | 11 | 13 | 16 | 17 | 19 | 23 | 25 | 27 | 29 | 31 | 32 | 37 | 41 | 43 | 49 | 64 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `mult₁` | 1 | 1 | 1 | 1 | 3 | 3 | 1 | 2 | 1 | 3 | 1 | 1 | 1 | 3 | 3 | 1 | 1 | 3 | 1 | 3 | 3 |

`mult₁ ∈ {1,2,3}` throughout, matching Lemma CT (the value 3 is "two `A₅`
classes + `S`", the value 2 at `q = 16` is "one `L₂(4)` class + `S`", the value
3 at `q = 64` is `L₂(4)`, `L₂(8)`, `S`).  **`mult₁` is not used in the proof
below** — it is recorded because it is the invariant that closed the sporadic
pairs, and here it is *too small to separate anything*: `mult₁ ≤ 3` leaves no
room for a comparison argument.  This is a genuine difference between the `L₂`
row and the `A_n`/sporadic rows.

---

## 2. The simple–simple side: free, and `Bₙ/Cₙ`-independent

`|L₂(q)| = q(q²−1)/d` determines `q` (the map `q ↦ q³−q` is strictly
increasing; `q = 4` and `q = 5` give the *same* group `A₅`).  By the CFSG order
theorem the only pairs of non-isomorphic simple groups of equal order are
`{A₈, L₃(4)}` and `{B_n(q), C_n(q)}`, `n ≥ 3`, `q` odd [LIT: Artin;
Kimmerle–Lyons–Sandling–Teague].  Neither involves an `L₂`.  Hence

> **`L₂(q)` is determined among finite simple groups by its order.**

Machine re-confirmation: the census run tests, for **all 78 732** prime powers
`q ≤ 10⁶`, that the enumerator returns exactly **one** simple group of order
`|L₂(q)|` — `positive control ... PASS, all 78732 targets`.  This is also the
control that makes an "empty census" meaningful rather than a false negative.

**Consequence: the `L₂` row of `D`-rigidity does not touch the `Ω₇(q)` vs
`PSp₆(q)` residue that §4l leaves open.**

---

## 3. The two uniform inequalities

Both are stated over *all* non-abelian finite simple `G`, and both are used
only through an **upper bound** `ῑ(G) ≥ ι(G)` (parabolic index for Lie type
via Borel–Tits, `C(m,3)` for `A_m`, the `v_task39`/`v_task50` table for
sporadics) — which is the conservative direction for both.

> **Lemma B.**  `|G| > ι(G)²` for every non-abelian simple `G` except
> `J₁, O′N, J₃`.
> **Lemma C.**  `|Out(G)| · ι(G) ≤ |G|^{2/3}` for every non-abelian simple `G`.

**Status [COMPUTED, `v_task51_lemmaBC_out.txt`]:** verified over **1 286**
simple groups — all Lie types with `q₁ ≤ 4096` and rank `≤ 8`, all `A_m`
(`m ≤ 60`), all 27 sporadics.  Lemma C has **no exceptions**; the tightest row
is `A₆` at ratio `0.790`.  Lemma B fails exactly at `J₁ (α = 1.737)`,
`O′N (1.807)`, `J₃ (1.816)`.

**Asymptotic half [PROVEN per family].**  For `G` of Lie type over `F_{q₁}`
with `Nr` positive roots and rank `r`, `|G| < q₁^{2Nr+r}` and
`|Out(G)| ≤ 6·f₁·gcd(·) ≤ 24 f₁`, while `ι(G) ≤ [G:P] ≍ q₁^{Nr−(\text{level})}`;
the minimum of `log|G|/log ῑ` over the families is `7/3`, attained
asymptotically by the **Ree groups** `²G₂(q₁)` (`|G| ≍ q₁⁷`, `ι = q₁³+1`) —
the extremal family, *not* `L₂` as one might guess, and not `U₃` (`8/3`) or
`Sz` (`5/2`).  The `α`-table in the output file exhibits
`R(27), R(243), R(2187) → 2.3333`.  So Lemma B/C hold for all Lie types with
`q₁` or rank beyond the swept range by the asymptotics; the swept range covers
the rest.

**Honest gap:** neither lemma has a *proof* covering every simple group
uniformly; they are checked-plus-asymptotic.  Lemma C is the one the theorem
depends on.  See §7(G1).

---

## 4. The uniform structure theorem

Standing: `T` Fitting-free, `|T| = N = |L₂(q)|`, `D(T) ≅ D(L₂(q))`, `q ≥ 4`.

**Input 1 — the orbit floor.**  By Lemma TO′-0 (`v_task42_to_prime.md`;
verified *target-agnostic* in `v_task50_sporadic_twins.md` §1.2 — its proof
uses only Lemma TR-1, an exact hypothesis-free identity, and the transfer
`ι(T) = ι(S)` from the conductor multiset) together with Lemma F
(`v_task36_pair_invariants.md`, `ι(K≤Ā) = f(A)·[S_i:N_{S_i}(A)]`,
`f | |Out(S_i)|`):

  **(F)  `ℓ_O · |Out(S_i)| · ι(S_i) ≥ ι(S)`  for every orbit `O`.**

**Input 2 — the `c`-bound.**  `F(T) = 1 ⟹ C_T(Soc T) = 1 ⟹ T ≤ Aut(Soc T)`,
so `c | ∏_i (|Out(S_i)|^{ℓ_i} · ℓ_i!)`.

**Input 3 — Lemma K [PROVEN, elementary].**
*Every prime power dividing `N = |L₂(q)|` is at most `q+1`.*
*Proof.*  `|N|_p = q`.  For odd `r ≠ p`, `r` divides exactly one of `q−1`,
`q+1` (they are coprime for `q` even and have gcd 2 for `q` odd), so
`|N|_r ≤ q+1`.  For `r = 2` and `q` odd, `|N|_2 = |q−1|_2·|q+1|_2/2 =
max(|q−1|_2, |q+1|_2) ≤ q+1` since `min(|q−1|_2,|q+1|_2) = 2`; for `q` even
`|N|_2 = q`. ∎  (Machine check `q ≤ 2000`: no violations, `_g_out.txt` PART C1.)

### 4.1 Step 1 — the size floor

By (F) and **Lemma C**, for every orbit `O` with factor `S_i`:

  `(q+1)/ℓ_O ≤ ι(S) / ℓ_O ≤ |Out(S_i)|·ι(S_i) ≤ |S_i|^{2/3}`,

hence

  **`|S_i| ≥ ((q+1)/ℓ_O)^{3/2}`,  and the orbit contributes
  `|S_i|^{ℓ_O} ≥ ((q+1)/ℓ_O)^{3ℓ_O/2}` to `|Soc T|`.**

The function `ℓ ↦ (3ℓ/2)(log(q+1) − log ℓ)` is `≥ (3/2)log(q+1)` for every
`ℓ ≥ 1` in the admissible range (`ℓ ≤ log N/log 60 ≤ 3log q/log 60`, so
`ℓ log ℓ ≤ (ℓ−1) log(q+1)` holds for all `q ≥ 4`).  Therefore **every orbit
contributes at least `(q+1)^{3/2}`.**

### 4.2 Step 2 — at most ONE socle orbit  [PROVEN, all `q ≥ 4`]

If `T` had `k ≥ 2` socle orbits then
`N ≥ |Soc T| ≥ (q+1)^{3/2·2} = (q+1)³ > q³ ≥ N` — contradiction.
(For the two exceptional targets, `ι(S)³ = 125 > 60 = |L₂(5)|` and
`343 > 168 = |L₂(7)|`, so the same argument applies verbatim.) ∎

*This single line is the whole content of the elimination:* `ι(L₂(q)) = q+1` is
**large** relative to `|L₂(q)| ≍ (q+1)³` — the target sits at the extreme
`ι ≍ |S|^{1/3}` of the `ι`-scale, so a socle factor forced by the floor to have
`ι(S_i) ≳ q` must already be as big as `S` itself.  Two of them do not fit.

### 4.3 Step 3 — the orbit has length `ℓ ≤ 2`  [PROVEN, all `q ≥ 4`]

Soc `T = S₁^ℓ`, one orbit.  From §4.1, `((q+1)/ℓ)^{3ℓ/2} ≤ |S₁|^ℓ ≤ N < q³`,
i.e. `((q+1)/ℓ)^ℓ < q²`.

* `ℓ = 3`: `(q+1)³ < 27q²` ⟹ `q^{1/3} < 3` ⟹ `q < 27`; but then
  `|S₁|³ ≤ N < q³ < 27³` forces `|S₁| < 27 < 60` — impossible.
* `ℓ ≥ 4`: `(q+1)/ℓ < q^{2/ℓ} ≤ q^{1/2}` gives `ℓ > (q+1)/√q > √q`, while
  `60^ℓ ≤ |S₁|^ℓ ≤ N < q³` gives `ℓ < 3 log q/log 60 = 0.733 ln q`.
  `√q < 0.733 ln q` is false for every `q ≥ 4`. ∎

**So `Soc T = S₁` (with `c = N/|S₁| ≥ 2`, `c | |Out(S₁)|`: `T` almost simple)
or `Soc T = S₁ × S₁` (one orbit of length 2, `c` even, `c | 2|Out(S₁)|²`).**

### 4.4 Step 4 — which `S₁` can occur: Lemma K forces rank 1

Let `S₁` be of Lie type over `F_{q₁}`, char `p₁`, with `Nr` positive roots and
rank `r`; then `|S₁|_{p₁} = q₁^{Nr}` and `|S₁| < q₁^{2Nr+r}` (since
`∏(q₁^{d_i}−1) < q₁^{Σd_i} = q₁^{Nr+r}`).

* **`ℓ = 1`.**  Lemma K: `q₁^{Nr} ≤ q+1`.  Also `|S₁| = N/c ≥ N/|Out(S₁)|`.
  Then `N/c ≤ |S₁| < (q₁^{Nr})²·q₁^{r} ≤ (q+1)²q₁^{r}`, so
  `q₁^{r} > N/(c(q+1)²) ≈ q/c`, and dividing into `q₁^{Nr} ≤ q+1`:

    **`q₁^{Nr − r} ≲ c ≤ |Out(S₁)|`.**

* **`ℓ = 2`.**  Lemma K applied to `|S₁|²`: `q₁^{2Nr} ≤ q+1`, and
  `|S₁|² ≥ N/c`.  The same division gives **`q₁^{Nr − r} ≲ √(2c)`**.

For every Lie type **except `A₁`** one has `Nr − r ≥ 1`, and `Nr − r` grows
with the rank (`A_{n−1}`: `(n−1)(n−2)/2`).  Since `|Out(S₁)|` is at most
`≈ 24 f₁ = 24 log_{p₁} q₁`, the displayed inequalities bound `q₁` **and** the
rank absolutely, leaving a finite list of possible `S₁`, all of bounded order
— which then contradicts `|S₁| ≈ N/c ≍ q³` for `q` large, and is covered
exhaustively by the census for small `q`.

`Nr = r` holds **only for `A₁`**, i.e. `S₁ = L₂(q₁)`.  Alternating and
sporadic `S₁` are not covered by the above but have `|Out| ≤ 4`, so they give
*exact* equations `c·|S₁|^ℓ = N` with `c ≤ 4` (resp. `≤ 32`) — a direct check.

### 4.5 Step 5 — the residual branches, scanned

`v_task51_l2_twins.py --l2sub`; exact integer arithmetic, the cube root is a
seed only and every candidate is verified by exact multiplication (positive
controls: `solve_L2_order(60) = [4,5]`, `solve_L2_order(360) = [9]`).

| branch | equation | range scanned | hits |
|---|---|---|---|
| **(E1)** `ℓ = 1`, `Soc T = L₂(q₁)` | `c·q₁(q₁²−1)/d₁ = q(q²−1)/d`, `2 ≤ c ∣ d₁f₁` | `q₁ ≤ 2·10⁷` | **0** |
| **(E2)** `ℓ = 2`, `Soc T = L₂(q₁)²` | `c·(q₁(q₁²−1)/d₁)² = q(q²−1)/d`, `c ∣ 2(d₁f₁)²` | `q₁ ≤ 10⁵` | **0** |
| **(E3)** `Soc T = A_m^ℓ`, `ℓ = 1,2` | `c·(m!/2)^ℓ = \|L₂(q)\|`, `c ∣ 2^ℓ·ℓ!`-bound | `m ≤ 47` (`\|A_m\| ≤ 10⁶⁰`) | **0** |
| **(E4)** `Soc T` sporadic`^ℓ`, `ℓ = 1,2` | `c·\|S₁\|^ℓ = \|L₂(q)\|` | all 27 | **0** |

(E1) tested 1 272 217 `(q₁,c)` pairs and covers `q` up to `≈ 2.5·10⁷`;
(E2) tested 39 232 pairs and covers `q` up to `≈ 10¹⁰`; (E3), (E4)
are complete in `q` (the equation determines `q` from `(m,c)`, resp. `(S₁,c)`).

> **Hygiene note — a bug that was caught and fixed, recorded because it would
> have produced a silent false "no hits".**  The first version of
> `solve_L2_order` seeded the cube root with `n ** (1.0/3.0)`.  At the scales
> of the `ℓ = 2` branch (`|A_m|² ≈ 10¹²⁰`) the float seed is off by `≈ 10²⁴`,
> so the integer correction loop did not terminate and the scan hung rather
> than reporting.  `_icbrt` is now an integer Newton iteration with **no float
> anywhere**, and the script asserts `r³ ≤ n < (r+1)³` at nine test points
> including `10¹²⁰` before running the scan (`_icbrt selftest ... OK` in the
> output file).

**A partial proof of (E1)/(E2) in the equal-characteristic case
[PROVEN].**  Suppose `p₁ = p` in (E1).  Then `q₁·c_p = q` where `c_p = |c|_p`,
and substituting `q = c_p q₁` into `c·q₁(q₁²−1)/d₁ = q(q²−1)/d` gives
`c_{p′}(q₁²−1)/d₁ = (c_p²q₁²−1)/d`.  With `d = d₁` (same characteristic) this
is `(c_{p′} − c_p²)q₁² = c_{p′} − 1`.  If `c_{p′} = c_p²` then `c_{p′} = 1`,
so `c_p = 1`, so `q = q₁` and `c = 1` — excluded.  Otherwise
`q₁² ≤ c_{p′} − 1 < c ≤ d₁f₁ ≤ 2log₂q₁` — impossible.  **So (E1) has no
solution with `p₁ = p`, for any `q`.**

The same substitution in (E2) (`q = c_p q₁²`) gives
`(c_{p′}·d/d₁² − c_p²)q₁⁴ − 2(c_{p′}d/d₁²)q₁² + c_{p′}d/d₁² + 1 = 0`; the
coefficient of `q₁⁴` vanishes only in a case that forces `q₁² < 1`, and
otherwise `q₁² ≤ 2c_{p′} ≤ 4(d₁f₁)²` — **a finite check, covered by the scan**.
The cross-characteristic case `p₁ ≠ p` is the one that is only scanned, in both
branches.

---

## 5. The main census, and the exceptional `q`

`v_task51_l2_twins_out.txt`: for **every** prime power `4 ≤ q ≤ 10⁶`
(78 732 targets), the Phase-1 census of non-simple Fitting-free candidates,
run with the orbit-floor prefilter, is **EMPTY**, and the positive control
passes on every target.

**Robustness (`--raw`, the census run *without* the prefilter).**  Over the
whole range `q ≤ 10⁶` the unfiltered non-simple census contains exactly **one**
solution:

    q = 64 :  Soc = A₅ × L₂(13),  c = 4      (60 · 1092 · 4 = 262080 = |L₂(64)|)

killed by the orbit floor with margin `10 < 65` (`|Out(A₅)|·ι(A₅) = 2·5`).
So over 78 732 targets the *order arithmetic alone* leaves a single candidate,
and the floor removes it.  This is a much sharper picture than the sporadic
row (where `B` had 1225 raw candidates): **the three nearly-coprime blocks
`p^f`, `(q−1)/·`, `(q+1)/·` of `|L₂(q)|`, each of prime-power parts `≤ q+1`
(Lemma K), essentially forbid factorisation into simple orders.**

**The four exceptional isomorphisms.**

| `q` | `S` | how closed |
|---|---|---|
| 4, 5 | `A₅`, `\|S\| = 60` | already `[PROVEN]` in §4l: the only non-solvable group of order 60 is `A₅`.  Re-derived here: census empty, `ι = 5`. |
| 7 | `L₃(2) = L₂(7)`, 168 | `[PROVEN]` §4l (minimal simple order, no room for a semisimple socle).  Census empty; `ι = 7`. |
| 9 | `A₆`, 360 | `[PROVEN]` §4l and §4aj–§4am (alternating row).  Census empty; `ι = 10 = q+1`. |
| 8 | `L₂(8)`, 504 | `[PROVEN]` §4l (`L₂(8)` listed as a minimal simple order).  Census empty; `ι = 9 = q+1`. |

So none of the exceptional isomorphisms needs a new argument; each is closed
twice over, once by §4l's order arithmetic and once by this census.

---

## 6. What generalises to `L_d(q)` / `U_d(q)`, and what is `L₂`-specific

| step | `L₂`-specific? | for a general Lie target `S` |
|---|---|---|
| Dickson's subgroup theorem (§1) | **YES** — this is the only truly `L₂` input | replaced by Aschbacher's classes + Bray–Holt–Roney-Dougal (`d ≤ 12`) / Kleidman–Liebeck; §4y already treats the BHR tables as executable literature |
| `ι(S) = [S:P₁]` = smallest parabolic index, with `Z(U_P)` abelian as witness | **NO** | holds for every Lie type by Borel–Tits; **but** `ι = [S:P₁]` needs `[S:P₁] = m(S)`, i.e. the minimal-index subgroup to be a parabolic — true for `L_d(q)`, `U_d(q)` (`d ≥ 3`) by Cooperstein/Kantor with a short list of exceptions.  So `ι(L_d(q)) = (q^d−1)/(q−1)`, `ι(U_d(q)) = ` the isotropic-point index — **uniform in `q` and `d`** |
| the target being **(AB)-free** (§1.1) | **NO** | the argument is "`ind*(H) ≥ m(S)` and `m(S)` is attained by a normaliser"; it works verbatim whenever the minimal-index subgroup is a parabolic.  So **every Lie target should be (AB)-free** — a real gain over the `A_n` row |
| Lemma K (prime powers `≤ q+1`) | **YES**, in that exact form | generalises to `|S|_r ≤ q^{?}·Φ_k(q)`: for `L_d(q)` every prime power dividing `|S|` is `≤ max(q^{d(d−1)/2}, Φ_k(q))`.  The *ratio* `ppmax/|S|^{1/2}` deteriorates as `d` grows, so Lemma K weakens |
| the orbit floor (F) + Lemma C ⟹ **one orbit** (§4.2) | **NO** as a mechanism, **YES** in its strength | the kill needs `ι(S)^{3/2·k} > |S|`, i.e. `ι(S) > |S|^{2/(3k)}`.  For `L₂`, `ι ≍ |S|^{1/3}` and `k = 2` gives equality-with-room.  For `L_d(q)`, `ι ≍ q^{d−1}` and `|S| ≍ q^{d²−1}`, so `ι ≍ |S|^{1/(d+1)}` — **the margin collapses as `d` grows** and the two-orbit kill fails outright for `d ≥ 3`.  **This is the single most important finding for the programme:** the `L₂` pilot is *easy* precisely because `L₂` is the `ι`-extremal classical family, and the higher-rank targets will need the order census (Lemma K's analogue) to do the work the floor does here |
| Step 4 (`q₁^{Nr−r} ≲ c` ⟹ rank 1) | **NO** | the same computation runs for any target; the conclusion becomes "`S₁` has rank bounded in terms of `|Out|` and the target's `ppmax`" |
| simple–simple side free of `Bₙ/Cₙ` (§2) | **NO for `B_n/C_n` targets** | `L_d(q)` and `U_d(q)` orders are unique among simple orders (Artin/KLST) except `L₄(2) = A₈` vs `L₃(4)`, which §4j already separates.  So `L_d`/`U_d` rows are also `Bₙ/Cₙ`-independent |

**Recommended order for the remaining Lie targets:** `U_3(q)` next (rank 1,
`ι = q³+1 ≍ |S|^{3/8}` — still floor-friendly), then `Sz(q)`, `R(q)` (rank 1,
`ι ≍ |S|^{2/5}`, `|S|^{3/7}` — the *most* floor-friendly families of all), and
only then `L₃(q)`, where the floor stops carrying the argument.

---

## 7. Honest status: what is proven, what is computed, what is open

**Proven, uniform in `q`, no computation:**
Lemma L2-ι (§1.1, **over all subgroups** — the target is (AB)-free);
Lemma K (§4); Step 2 (**at most one socle orbit**, §4.2); Step 3
(**orbit length `≤ 2`**, §4.3) — the last two *modulo Lemma C*;
Step 4's rank reduction (§4.4); the equal-characteristic half of (E1)/(E2)
(§4.5); §2 (simple–simple, from the CFSG order theorem).

**Computed:** the full census for all `4 ≤ q ≤ 10⁶` with positive control on
every target (`v_task51_l2_twins_out.txt`); branches (E1)–(E4)
(`v_task51_l2_subcases_out.txt`); Lemmas B and C over 1 286 simple groups
(`v_task51_lemmaBC_out.txt`); `ι` and `mult₁` in GAP over 16/21 values of `q`
(`v_task51_l2_twins_g_out.txt`).

**Open — the two debts, stated plainly:**

* **(G1) Lemma C is not proven.**  `|Out(G)|·ι(G) ≤ |G|^{2/3}` is checked on
  1 286 groups (tightest ratio `0.790` at `A₆`) and holds asymptotically per
  family, but there is no uniform proof.  Steps 2 and 3 — the entire uniform
  half of the theorem — rest on it.  A proof is not obviously hard (it is a
  statement about minimal parabolic indices against group orders, family by
  family via the standard order formulas plus the `|Out|` tables), but it is
  a page of case analysis that was not written here.  It should be written
  before Theorem L2-T is promoted to `[PROVEN]`, and it is **reusable for
  every Lie target**, so it is worth doing once properly.
* **(G2) The cross-characteristic case of (E1)/(E2) is only scanned.**
  `c·|L₂(q₁)|^ℓ = |L₂(q)|` with `p₁ ≠ p` has no solution for
  `q₁ ≤ 2·10⁷` (`ℓ=1`) / `10⁵` (`ℓ=2`), and the full census independently
  covers all `q ≤ 10⁶`.  A uniform proof would be a Diophantine argument on
  `q³ − q = c(q₁³ − q₁)`-type equations — plausibly elementary (bounded `c`,
  and `q/q₁ → c^{1/3}` forces near-equality of two cubics), but not done.

**Therefore the honest headline is:**

> **Theorem L2-T [PROVEN for all `4 ≤ q ≤ 10⁶`; PROVEN for all `q` modulo
> (G1) and (G2)].**  `L₂(q)` has no Fitting-free non-simple twin, and hence is
> `D`-rigid among all finite groups.

Not `[PROVEN, all q]`.  The gap is named, small, and reusable.

### Citations

| # | input | tag |
|---|---|---|
| C1 | Dickson's subgroup theorem for `L₂(q)` | **[LIT]** |
| C2 | Galois: minimal index of a proper subgroup of `L₂(q)` is `q+1` except `q = 5,7,9,11` | **[LIT]** |
| C3 | CFSG (completeness of the simple-order enumeration) | **[LIT]** |
| C4 | CFSG order theorem: equal-order simple pairs are only `A₈/L₃(4)` and `B_n/C_n` | **[LIT: Artin; KLST]** |
| C5 | Borel–Tits `N_G(Z(U_P)) = P` (the `ι` upper bounds) | **[LIT]** |
| C6 | order transfer `D(T) ≅ D(S) ⟹ |T| = |S|` (Müller Satz 2.3.4) | **[LIT/formalised]** |
| C7 | conductor multiset is a `D`-ring invariant (`conductorMultiplicity_eq_of_ringEquiv`) | **[Lean, kernel-checked]** |
| C8 | Satz 2.3.6 (`|G|` has conductor-multiplicity 1 for `G` Fitting-free) | **[LIT]** |
| C9 | §4j–§4l reduction (order, non-solvability, Fitting-freeness are `D`-invariants) | **[PROVEN, this project]** |
| C10 | Lemma TR-1 / Lemma TO′-0 (target-agnostic, `v_task34`/`v_task42`, re-verified in `v_task50` §1.2) | **[PROVEN]** |
| C11 | Lemma F (`v_task36_pair_invariants.md`) | **[PROVEN]** |
| C12 | Lemma CT (`v_task41_r1_census.md`) — perfect subgroups of `L₂(q)` | **[PROVEN]** |
| **(C)** | Lemma C, `\|Out(G)\|·ι(G) ≤ \|G\|^{2/3}` | **[COMPUTED + asymptotic]** — the load-bearing debt |

---

## 8. Reproduce

```
python3 v_task51_l2_twins.py 1000000 --raw   > v_task51_l2_twins_out.txt      # ~6 min
python3 v_task51_l2_twins.py 20000000 100000 --l2sub \
                                             > v_task51_l2_subcases_out.txt
python3 v_task51_l2_twins.py --lemC          > v_task51_lemmaBC_out.txt       # seconds
~/gap-4.16.0/gap -q -o 4g v_task51_l2_twins.g > v_task51_l2_twins_g_out.txt   # ~3 min
```
All arithmetic is exact Python big-integer / GAP rational.  The only floats
are the display column of the `α`-table in `--lemC` and the cube-root *seed*
in `solve_L2_order`, whose every candidate is verified by exact
multiplication.
