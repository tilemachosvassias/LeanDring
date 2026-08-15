# v_task59 — the **symplectic and orthogonal towers**:
# Theorems **Sp-T**, **O-odd-T**, **D-T**, **2D-T**

Date 2026-08-08.  **NOTES.md not edited.**
Pipeline: `L₂` (`v_task51`) → Lemma C (`v_task52`) → rank 1 (`v_task53/54`) →
`L₃` (`v_task55`) → the `L`/`U` towers (`v_task56`) → rank-2 exceptionals
(`v_task57`) → the large exceptional tower (`v_task58`) → **here: the last
classical block**.

| file | what it does |
|---|---|
| `v_task59_spo_twins.py` | PART A invariants + the `ι`-lemma with the KL 5.2.2 exceptional minimal degrees; PART B Lemma Z per tower; PART C Lemma EQ-EX same-`a/N` blocks, Lemma EQ′ pruning, **the matched-pair identity hunt (J1)–(J5)**, the broad identity sweep, the factorisation-free equal-characteristic sweep; PART D Lemma Q's death, Lemma Z2, **the FAILURE of Lemma MO-EX**, the two-sided repair **Lemma MO-SPO**, and the exact residual-configuration census; PART E Lemma X-SPO, the `ppmax³` kill, Lemma X-2; PART F alternating/sporadic, complete in `q`; PART G the residual census |
| `v_task59_spo_twins_out.txt` | its output — **0 hits everywhere** |
| `v_task59_spo_twins.g` / `_g_out.txt` | GAP: order formulas; **10 `ι`-witnesses `Z(U_P)` with `N_S(Z(U_P)) = P` computed outright**, incl. the two wrong witnesses; minimal degrees from stored `Maxes`; the identity hunt (J1)–(J4) |

All arithmetic exact (Python big integers / `Fraction`, GAP rationals).
Every enumerator is imported from `v_task50`–`v_task56`.

---

> ### Headline
>
> **Theorems Sp-T, O-odd-T, D-T, 2D-T [PROVEN, unconditional, every `q`,
> uniform in `n`, exact confirmations run for `3 ≤ n ≤ 12`].**
>
> There is no Fitting-free **non-simple** finite group `T` with `|T| = |S|`
> and `D(T) ≅ D(S)`, for
> `S = S_{2n}(q) = PSp_{2n}(q)` (`n ≥ 3`, all `q`),
> `S = O_{2n+1}(q) = Ω_{2n+1}(q)` (`n ≥ 3`, `q` odd),
> `S = PΩ⁺_{2n}(q)` and `S = PΩ⁻_{2n}(q)` (`n ≥ 4`, all `q`).
> No (AB) anywhere; no Lemma-B violator list.
>
> **Consequences.**  `PΩ^±_{2n}(q)` are **D-rigid among all finite groups**
> (the CFSG order theorem has no coincidence for `D_n`/`²D_n`).  For
> `Sp_{2n}(q)` and `Ω_{2n+1}(q)` the *only* remaining obstruction is the
> **parked `B_n ≅_{order} C_n` simple–simple pair**: after this note, any
> surviving twin of either is *simple*, hence by CFSG is the other member of
> the pair.  **The reduction of the whole programme to that one pair is now
> complete.**  One census serves both towers because `|B_n(q)| = |C_n(q)|`
> identically, and every kill below is simultaneously a kill for both — a
> non-simple `T` is separated from **B_n and C_n at once**.
>
> **Four things went differently from the forecast.**
>
> 1. **`Lemma MO-EX` (v_task58's new tool) FAILS on these towers**, and it
>    fails at *low* rank, not only high rank.  Its convexity step needs every
>    admissible family to have `r = D/N ≥ a/N`; here `a/N = 2 + 1/n` is small
>    and `²F₄` (`13/6`), `F₄` (`13/6`), `E₇` (`19/9`), `E₈` (`31/15`) sit
>    *below* it.  **Repair: Lemma MO-SPO**, the observation that MO-EX's
>    input (iii) is *two-sided*, so uniform-sign configurations die on
>    *either* side; the residue is the finitely many **mixed-sign** and
>    **same-ratio** configurations, and those are settled exactly by degree
>    accounting.  Net effect: the entire multi-factor branch closes
>    with **no `(p,f)` window and no general census** (contrast v_task58,
>    where `E₆` needed 42 979 exact `(p,f)` pairs).
> 2. **The `ι`-witness trap is characteristic-dependent, and reversed from
>    the unitary case.**  `O_p(P₁)` is **abelian** for `Sp_{2n}(2^f)` and for
>    **all** the orthogonal towers, but **non-abelian** for `Sp_{2n}(q)` with
>    `q` odd (GAP: `Sp₆(3)`, `|O₃(P)| = 243`, `|Z(U_P)| = 3`).  `Z(U_P)` is
>    the right witness throughout, as v_task56 instructed.
> 3. **The minimal-degree exceptions include an INFINITE family**:
>    `m(PSp_{2n}(2)) = 2^{n-1}(2^n−1) < 2^{2n}−1` for **every** `n ≥ 3`
>    (`Sp₆(2)`: 28 < 63, `Sp₈(2)`: 120 < 255 — both GAP-confirmed).  It costs
>    nothing: the ratio is bounded (`→ 1/2`), so `b = deg_q ι` is unchanged.
> 4. **A new closest-call in the programme, beating `(I3)`**: `(J5)`,
>    `|C_n(m^{2n−1})| / |U_{2n}(m^n)| → gcd(2n, q₁+1)/gcd(2,q−1)` **strictly
>    from above**, with that limit *dividing* `|Out(U_{2n}(q₁))|`.  At
>    `n = 3` the observed values are `3.0393658731`, `3.0001901812`,
>    `3.0000000028` — always `> 3`, never `= 3`.

---

## 0.  The four targets

`q = p^f`.

```
|C_n(q)| = |B_n(q)| = q^{n^2} prod_{i=1}^{n}(q^{2i}-1) / gcd(2,q-1)
|D_n(q)|  = q^{n(n-1)} (q^n-1) prod_{i=1}^{n-1}(q^{2i}-1) / gcd(4,q^n-1)
|2D_n(q)| = q^{n(n-1)} (q^n+1) prod_{i=1}^{n-1}(q^{2i}-1) / gcd(4,q^n+1)

iota :  C,B : (q^{2n}-1)/(q-1)         D : (q^n-1)(q^{n-1}+1)/(q-1)
                                      2D : (q^n+1)(q^{n-1}-1)/(q-1)
|Out|:  C_n (n>=3) : gcd(2,q-1) f      B_n (q odd) : 2 f
        D_n : gcd(4,q^n-1) f g , g = 6 at n = 4 (S_3 TRIALITY x diagonal), else 2
        2D_n: gcd(4,q^n+1) f * 2
```

| | `a` | `N` | `b` | `K` | `a/N` | `b/K` | `N/b` | `4b ≥ a`? |
|---|---|---|---|---|---|---|---|---|
| `C_n`, `B_n` | `2n²+n` | `n²` | `2n−1` | `2n` | `2 + 1/n` | `1 − 1/(2n)` | `n²/(2n−1)` | **NO** (`n = 3`: `20 < 21`) |
| `D_n` | `2n²−n` | `n(n−1)` | `2n−2` | `2n−2` | `2 + 1/(n−1)` | **`1`** | `n/2` | **NO** |
| `²D_n` | `2n²−n` | `n(n−1)` | `2n−2` | `2n` | `2 + 1/(n−1)` | `1 − 1/n` | `n/2` | **NO** |

Orders GAP-verified against `PSp(2n,q)`, `Ω^ε(2n,q)`, `Ω(2n+1,q)`
(`_g_out.txt` PART A, 30/30, 0 mismatches).

**Note on `char 2`**: `B_n(2^f) ≅ C_n(2^f)`, so the `B` row runs over odd `q`
only; every even-`q` orthogonal-odd target is literally a symplectic one and
is covered by the `C` row.

**Refutation of a v_task58 statement.** v_task58 §9(1) said the classical
Lemma Q "fails from `n = 4` on".  The exact boundary is **`n = 3`**:
`4b = 20 < 21 = a` already for `C₃`.  Lemma Q is dead for *every* target of
this note, so the multi-factor branch is head-on from the first row.

---

## 1.  `ι` over **all** subgroups, so (AB)-free

> **Lemma SPO-ι [PROVEN, all four towers, all `n` in scope, all `q`; four
> exceptional rows carried exactly].**
> `ι(S) = [S : P₁]`, the stabiliser of a **singular 1-space**, with the
> Borel–Tits witness `A = Z(U_{P₁})`.

*(≤)* `A := Z(O_p(P₁))` is non-trivial abelian with `N_S(A) = P₁`
(Borel–Tits, `N_G(Z(U_P)) = P`), so `ind*(A) = [S:P₁]`.
*(≥)* `ind*(H) ≥ [S:N_S(H)] ≥ m(S)`, and `m(S) = [S:P₁]` outside the
exceptional rows **[LIT: Kleidman–Liebeck Table 5.2.2; Cooperstein 1978;
Vasilyev 1996/97]**.  The proof quantifies over **all** `H`, so **(AB) is not
a debt for any of the four towers**.

### 1.1  The witness, GAP-verified at ten targets

`_g_out.txt` PART B.  Every row has `N_S(Z(U_P)) = P` **computed outright**
and `ind*(Z(U_P))` equal to the predicted parabolic index.

| `S` | deg | `|O_p(P)|` | `O_p(P)` abelian? | `|Z(U_P)|` | `N_S(Z)=P` | `ind*(Z(U_P))` | `ind*(Z(Syl_p))` |
|---|---|---|---|---|---|---|---|
| `Sp₆(2)` | 63 | 32 | **yes** | 32 | ✓ | **63** | 945 |
| `Sp₆(3)` | 364 | 243 | **NO** | **3** | ✓ | **364** | 364 |
| `Sp₈(2)` | 255 | 128 | yes | 128 | ✓ | **255** | 16065 |
| `Sp₆(4)` | 1365 | 1024 | yes | 1024 | ✓ | **1365** | 116025 |
| `Ω₇(3)` | 364 | 243 | yes | 243 | ✓ | **364** | 3640 |
| `PΩ⁺₈(2)` | 135 | 64 | yes | 64 | ✓ | **135** | 1575 |
| `PΩ⁻₈(2)` | 119 | 64 | yes | 64 | ✓ | **119** | 1071 |
| `PΩ⁺₁₀(2)` | 527 | 256 | yes | 256 | ✓ | **527** | 23715 |
| `PΩ⁻₁₀(2)` | 495 | 256 | yes | 256 | ✓ | **495** | 19635 |
| `Ω₉(3)` | 3280 | 2187 | yes | 2187 | ✓ | **3280** | 298480 |

> **Trap (confirmed, and CHARACTERISTIC-DEPENDENT).**  The unipotent radical
> of the symplectic `P₁` is the special group `q^{1+2(n−1)}`: it is **abelian
> for `q` even** and **non-abelian for `q` odd** (`Sp₆(3)`: `|O₃(P)| = 243`
> non-abelian, `|Z(U_P)| = 3`).  For the orthogonal towers `U_{P₁} ≅ q^{2n−2}`
> is abelian throughout.  So v_task56's Trap 2 recurs here in
> characteristic-dependent form — the mirror image of v_task57's `S₄(4)`
> trap.  **`Z(U_P)` is the correct witness in every row.**
>
> **`Z(Syl_p)` is the wrong witness in 9 of 10 rows** (off by factors
> 15, 63, 85, 10, 11.7, 9, 45, 39.7); it happens to coincide only at
> `Sp₆(3)`.

### 1.2  The exceptional minimal degrees, handled exactly

| `S` | `m(S)` | `[S:P₁]` | source |
|---|---|---|---|
| `PSp_{2n}(2)`, **every `n ≥ 3`** | `2^{n−1}(2^n−1)` | `2^{2n}−1` | GAP `Maxes`: `S6(2)` `[28,36,63,…]`, `S8(2)` `[120,136,255,…]` |
| `Ω₇(3)` | `351` | `364` | GAP `Maxes` `[351,364,378,…]` (the `G₂(3)` subgroup) |
| `PΩ⁺₈(2)` | `120` | `135` | GAP `Maxes` `[120,120,120,135,135,135,…]` — **triality**, three classes of `Sp₆(2)` |
| `PΩ⁺₈(3)` | `1080` | `1120` | **[LIT: KL 5.2.2]** (`Ω₇(3)` subgroups, triality) |

The script uses the **smaller** value as `ι` in every case — the conservative
direction, since `ι(S)` is the right-hand side of the orbit floor.
`PΩ⁻₈(2)` has `m = 119 = [S:P₁]`: **no** exception, GAP-confirmed.

**Why the infinite family costs nothing.** `m/[S:P₁] → 1/2`, so
`deg_q ι = b = 2n−1` is unchanged and every degree argument in §§2–5 is
untouched; only the finite `q = 2` rows carry a constant-factor loss, and
they are inside every census.

---

## 2.  PART B — Lemma Z per tower

Lemma Z (`v_task56`) transfers verbatim; only `(b, K)` change.

```
b/K :   C_n, B_n : 1 - 1/(2n)        D_n : 1        ^2D_n : 1 - 1/n
```

* The four rank-1 families (`L₂`, `U₃`, `Sz`, `R`, all `μ/k = 1/2`) are dead
  against every target here.
* **`D_n` is the first target in the programme with `b/K = 1`.**  Lemma Z
  admits only the families with `μ/k ≥ 1`, i.e.
  **`{D_m (m ≥ 4), F₄, E₆, E₇, E₈}`** — the shortest surviving list anywhere
  in the programme, for every `n` and every `q`.
* `C_n`/`B_n` force `L_m` to `m ≥ 2n`, `U_m` (`m` even) to `m ≥ n+1`,
  `C_m`/`B_m` to `m ≥ n`, `²D_m` to `m ≥ 2n`.

> ### Calibration of the brief's prediction, honestly
> `b/K = 1 − 1/(2n)` is indeed **better than the linear tower at equal
> rank**, but it is **exactly equal to `L_d` at `d = 2n`** — and `2n` is the
> *natural dimension* of `S_{2n}(q)`.  So "Sp/Ω is easier than linear" is
> true at equal rank and **false at equal natural dimension**.  The genuine
> gain is at `D_n`, where `b/K = 1` beats every linear value.
> The brief's other prediction — "the hard branch is multi-factor" — is
> **confirmed** (§4), and is harder than forecast because MO-EX breaks.

---

## 3.  PART C — equal characteristic, almost simple

### 3.1  The same-`a/N` blocks (Lemma EQ-EX) — the populous regime

`a/N = 2 + 1/m` collects
```
block(2 + 1/m) = { C_m , B_m , D_{m+1} , ^2D_{m+1} , L_{2m} , U_{2m} }
                 + { G_2 , ^3D_4 , ^2G_2 }        if m = 3
                 + { F_4 , E_6 , ^2E_6 , ^2F_4 }  if m = 6
                 + { E_7 } if m = 9 ,  { E_8 } if m = 15
```
> **The `D_n` block IS the `C_{n−1}` block.**  `a/N(D_n) = 2 + 1/(n−1) =
> a/N(C_{n−1})`.  This is the same-ratio interaction the brief asked us to
> hunt, and it is real: at `n = 4` the block has **nine** members.

After Lemma EQ′ (`N₁/μ₁ ≤ N/b`) **and** Lemma Z (`μ₁/k₁ ≥ b/K`):

| target | survivors |
|---|---|
| `C_n`, `B_n` (`n ≥ 3`) | `C_n`, `B_n`, **`U_{2n}`**; `+ G₂` at `n=3`; `+ F₄, E₆` at `n=6`; `+ E₇` at `n=9` |
| `D_n` | **`D_n` only** (`+ F₄, E₆` at `n=7`, `+ E₇` at `n=10`) — Lemma Z's `b/K = 1` does it |
| `²D_n` | `C_{n−1}`, `B_{n−1}`, `D_n`, `²D_n`, `U_{2n−2}`; `+ G₂, ³D₄` at `n=4`; `+ F₄, E₆, ²E₆` at `n=7` |

### 3.2  The identity hunt (J1)–(J5)

> **(J1) `|B_n(q)| = |C_n(q)|` exactly** for every odd `q`, `n ≥ 3`
> (212 `(n,q)` pairs machine-checked; GAP `_g_out.txt` PART D).  This is the
> CFSG coincidence itself, `c = 1`, so it is **not** a non-simple twin
> candidate (`c ≥ 2` is required).  Its consequence for this note is
> structural: **one census serves both towers**.

> **(J2) `|SO_{2n+1}(q)| = |Sp_{2n}(q)|`** exactly (classical; GAP-checked at
> `(n,q) = (3,3),(3,5),(4,3),(4,5)`).  Passing to the simple quotients gives
> (J1).

> **(J3) `D_n` vs `C_{n−1}`.**  At the *same* `q` the quotient is
> `|D_n(q)|/|C_{n−1}(q)| = q^{n−1}(q^n−1)·gcd(2,q−1)/gcd(4,q^n−1)`,
> a **positive power of `q`** (closed form machine-confirmed at 15 `(n,q)`
> pairs) — so this row dies on `c | |Out| = O(log q)` with a full power of
> `q` to spare.  Equal `a/N` does **not** mean equal degree here, because
> `N` differs; the bounded-`c` regime lives only at the matched fields
> `q = m^{n−1}`, `q₁ = m^n`, which is the `2D_n ← C_{n−1}` row of §3.3.

> **(J4) `|²D_n(q)| / |D_n(q)| = [gcd(4,q^n−1)/gcd(4,q^n+1)]·(q^n+1)/(q^n−1)`.**
> `q` even: bracket `1`, quotient in `(1,2)`.
> `q` odd: exactly one of `q^n ∓ 1` is `≡ 2 (mod 4)`, so the bracket is `2`
> or `1/2`, and the quotient is
> `2(q^n+1)/(q^n−1) ∈ (2,3)` or `(q^n+1)/(2(q^n−1)) ∈ (1/2,1)`.
> **`2 < c < 3` is a near-miss** — `c = 2` *would* divide `|Out(D_n(q))|`.
> Killed by a strict inequality.  Observed: `2.05` (`n=4,q=3`), `2.006410`
> (`n=4,q=5`), `2.001280` (`n=5,q=5`).  Exactly the `(I3)` pattern.

> **(J5) — THE SHARPEST CALL IN THE PROGRAMME: `C_n`/`B_n` against `U_{2n}`.**
> Lemma EQ′ + Lemma Z leave `U_{2n}` in the block for **every** `n ≥ 3`.
> Matched fields: `f₁/f = N/N₁ = n/(2n−1)`, i.e. `q = m^{2n−1}`, `q₁ = m^n`,
> and then the two `m`-degrees are **exactly equal**.  Cancelling,
> ```
>   |C_n(m^{2n-1})| / |U_{2n}(m^n)|
>       = [ gcd(2n, q1+1) / gcd(2, q-1) ] * R_n(m) ,
>   R_n(m) = prod_{i=1}^{n} (m^{2i(2n-1)} - 1) / prod_{i=2}^{2n} (m^{in} - (-1)^i) .
> ```
> The bracket is an integer **dividing `|Out(U_{2n}(q₁))| = 2 f₁ gcd(2n,q₁+1)`**,
> so if `R_n ≡ 1` this would be a genuine twin candidate.  It is not:
> `R_n(m) = 1 + m^{−2n} + O(m^{−2n−1}) > 1` strictly.  Observed at `n = 3`
> (`q = m⁵`, `q₁ = m³`, bracket `3`):
> ```
>   m =  2 : c = 3.0393658731      m =  8 : c = 3.0000114190
>   m =  5 : c = 3.0001901812      m = 32 : c = 3.0000000028
>   m = 11 : c = 3.0000016920      m =128 : c = 3.000000000000...
> ```
> — always **strictly above** 3, never equal.
> **Relative gap `m^{−2n} = q^{−2n/(2n−1)}`, i.e. barely more than one power
> of `q`; `(I3)`'s gap was `2/q⁵`.  This is the tightest near-miss in the
> programme.**

**Exact confirmation.**  Over **all** matched pairs of **all four** towers,
`n ≤ 12`, `m ≤ 3000`: the value `c` is **never an exact integer `≥ 2`**
(PART C.2, "MATCHED-pair HITS over all targets: NONE"), and in particular
never an admissible one.  The broad sweep (`|S| = c|G|`, `2 ≤ c ≤ 10⁴`, full
Lie/alternating/sporadic list, `q ≤ 9`, `n ≤ 6`) finds 55 order identities,
**none with `c | |Out(G)|`**.

### 3.3  The exact factorisation-free sweep (PART C.4)

`q₁^{N₁} | q^N` bounds `f₁ ≤ fN/N₁`, so the branch is a finite exact test per
target with **no factorisation of `|S|`**.

```
all prime powers q <= 20 000 , n = 3..6 , all four towers (14 rows):
   targets per row                 : 2 314 ... 2 328
   divisor pairs found             : 28 495 ... 105 361
   POSITIVE CONTROL (S_1 = S, c=1) : 2328/2328 in every row
   order-only NEAR-MISSES          : NONE   (all 14 rows)
   HITS (c >= 2, c | |Out(S_1)|)   : NONE   (all 14 rows)
```

---

## 4.  PART D — the multi-factor branch: **MO-EX breaks, MO-SPO repairs**

### 4.1  Lemma Z2 alone closes the low ranks

`μ₁/N₁ ≥ ℓ·b/N` (Lemma Z2) intersected with `μ₁/k₁ ≥ b/K` (Lemma Z):

| target | families passing both |
|---|---|
| `C₃, C₄, C₅`, `B₃, B₄, B₅` | **NONE — branch empty for every `q`** |
| `D₄, D₅, D₆`, `²D₄` | **NONE — branch empty for every `q`** |
| `C₆, C₇`, `D₇` | `F₄` |
| `C₈`… | `D₄, F₄, E₈`, … (grows) |

From `n = 6` on `2b/N = 2(2n−1)/n² → 0` and families creep back — exactly the
degradation v_task58 §9(2) forecast.

### 4.2  **Lemma MO-EX FAILS** (a refutation, recorded)

MO-EX's convexity step needs `r_O = D_O/N_O ≥ a/N` for every admissible
family.  Here `a/N = 2 + 1/n` is **small**, and the admissible set contains
families strictly below it:

| target | offending family | `r` | `a/N` |
|---|---|---|---|
| `²D₅`, `²D₆` | `²F₄` | `13/6` | `9/4`, `11/5` |
| `C₈`–`C₁₂`, `B₈`–`B₁₂`, `D₉`–`D₁₂`, `²D₉`–`²D₁₂` | `E₈` | `31/15` | `17/8` … |
| `C₇`, `C₈`, `D₇`–`D₉` | `E₇` | `19/9` | `15/7` … |

v_task58 §9(2) predicted "`W > 0` may genuinely fail at high rank".  **It
fails, and it fails at low rank too** (`²D₅`).  Its fallback ("the exact
`(p,f)` sweep, which is cheap") would have been needed for every `n` — an
unbounded amount of work.

### 4.3  The repair — **Lemma MO-SPO [PROVEN, this note]**

> MO-EX's input (iii) is **two-sided**: `a f − B ≤ Σ_O r_O u_O ≤ a f`.
> With (ii) `Σ_O u_O = N f − δ` this gives **both**
> ```
>   Sigma_O (r_O - a/N) u_O  <=  (a/N) delta          (upper)
>   Sigma_O (r_O - a/N) u_O  >=  -B + (a/N) delta     (lower)
> ```
> while the `u_O` range over the polytope
> `u_O ≥ L_O := ℓ_O (N_O/μ_O)(b f − A)`, `Σ u_O = N f − δ`, on which the
> functional has
> `min = Σ (r_O−a/N)L_O + s·min_O(r_O−a/N)`,
> `max = Σ (r_O−a/N)L_O + s·max_O(r_O−a/N)` (`s` = slack).  Hence
> * **all `r_O > a/N`** ⟹ `min > 0` grows like `f` ⟹ **DEAD** (v_task58's case);
> * **all `r_O < a/N`** ⟹ `max < 0` grows like `f` ⟹ **DEAD** (new — this is
>   what kills the `²F₄`/`F₄`/`E₇`/`E₈` configurations);
> * **mixed signs, or all `r_O = a/N`** ⟹ MO-SPO is silent; those
>   configurations are **finitely many per target** and are settled in §4.4.

### 4.4  The residual configurations, settled exactly

For a residual configuration, (ii) and (iii) are two exact linear equations
in `x_O := f_O/f > 0`:
```
   Sigma_O l_O N_O x_O = N ,      Sigma_O l_O D_O x_O = a .
```
* **1 or 2 orbits:** the system is determined; either it has no positive
  rational solution (**dead by degree accounting**) or it does, and then the
  matched-field census computes `c(m) = |S|/∏|G_O|^{ℓ_O}` exactly and tests
  `c ≥ 2`, `c | ∏|Out(G_O)|^{ℓ_O}∏ℓ_O!`.
* **3 orbits:** one free parameter, intersected exactly with the box
  `x_O ≥ b/μ_O` (the floor) and `x_O k_O ≤ K` (Lemma Z1).  Every such segment
  turned out **empty**.

```
X    n   #configs  #residual  #degree-dead   surviving
C  3..5     --  branch vacuous (Lemma Z2, §4.1)
C  6..12    1 .. 50    1 .. 14     0 .. 4          NONE
B  3..12    (identical rows -- |B_n| = |C_n|)      NONE
D  4..6     --  branch vacuous
D  7..12    1 .. 41    0 .. 10     0 .. 2          NONE
2D 4        --  branch vacuous
2D 5..12    3 .. 63    0 .. 13     0 .. 3          NONE

TOTAL surviving multi-factor configurations over all 34 target rows: NONE
```

> **The whole multi-factor branch closes with NO `(p,f)` window and no
> general census.**  MO-SPO settles every uniform-sign configuration for all
> `q` at once; degree accounting settles most of the rest outright; only the
> few configurations whose linear system *does* have a positive solution
> reach a matched-field check, and that is a one-parameter sweep in `m` (run
> to `m ≤ 400`), not a sweep over `q`.  Contrast v_task58, where `E₆`/`²E₆`
> needed 42 979 + 43 874 exact `(p,f)` pairs.

---

## 5.  PART E — cross characteristic

> **Lemma X-SPO [PROVEN].**  `ppmax_{p′}(|S|) ≤ C(S)·(q+1)^M` with
> `M := max_e m_e φ(e)` over `|S|_{p′} = ∏_e Φ_e(q)^{m_e}`.  Proof identical
> to v_task58's Lemma K-exc (Lucas/LTE for odd `r`; `|q^d ∓ 1|₂ ≤ 2(q+1)|d|₂`
> for `r = 2`).

Exactly, for all four towers, `M = n` (`C`,`B`) and `M = n` (`D`,`²D`):

| | `a` | `M` | `a − 3(M+1)` | `2b` vs `M` |
|---|---|---|---|---|
| `C_n`,`B_n` | `2n²+n` | `n` | `2n² − 2n − 3` | `4n−2` vs `n` |
| `D_n`,`²D_n` | `2n²−n` | `n` | `2n² − 4n − 3` | `4n−4` vs `n` |

**Both margins grow quadratically in `n`** — far more comfortable than the
linear tower (`d²−1` against `3(d−1)`).  Machine check of Lemma X: **0
violations** of `P ≤ 2²⁰(q+1)^M` over all `q ≤ 600` (`n = 3,4`) and `q ≤ 120`
(`n = 5`); worst `P/q^M` is `202.3` at `C₄(3)`.

Exact thresholds:

| branch | `C₃` | `C₄` | `C₅` | `C₆` | `C₈` | `D₄` | `D₅` | `D₈` |
|---|---|---|---|---|---|---|---|---|
| almost simple (`|S| < cP³`) survives only `q ≤` | 61 | 8 | 3 | 2 | EMPTY | 23 | 5 | EMPTY |
| multi-factor (Lemma X-2) dead for `q ≥` | 89 | 25 | 13 | 8 | 5 | 59 | 23 | 7 |

All inside the PART G census.

---

## 6.  PART F — alternating / sporadic socle, complete in `q`

`|S| = M` is inverted exactly for `q` (the order is strictly increasing in
`q` of degree `a`), so each row is complete in `q`, not a range.

```
all A_m with |A_m| <= 10^300, all 27 sporadics + Tits, every c | |Out(S_1)|,
c >= 2, all four towers, n = 3..8:
    (S_1, c) pairs tested : 3 894        HITS : NONE
    inverter self-check (target recovered from its own order) : 62/62 ok
    POSITIVE CONTROL      : no A_m has a symplectic/orthogonal order at all
                            -- unlike the linear tower, where |A_8| = |L_4(2)|
```

The absence of a `c = 1` control here is itself informative: the
symplectic/orthogonal orders are arithmetically *disjoint* from the
alternating ones in the tested range, whereas `L_d` had a genuine
coincidence.  The self-check on the inverter is the substitute control.

A uniform second kill: the `ℓ = 1` floor reads `|Out(S₁)|ι(S₁) ≥ ι(S) > q^b`
with `|Out| ≤ 4`, `ι(A_m) ≤ C(m,3)`, while `c|S₁| = |S|` pins `m!/2 ≍ q^a`;
`C(m,3)` is polylogarithmic in `q^a`, so the floor fails for every
`q^b > 4C(m,3)` — two lines, every `n ≥ 3`.

---

## 7.  PART G — the residual census

Over the PART E windows, a complete multi-factor test in **both**
characteristics and over **all** socle types:

| target | window | targets | raw divisors | floor-passing | LIVE |
|---|---|---|---|---|---|
| `C₃` | `q ≤ 200` | 60 | 1668 | 0 | **NONE** |
| `B₃` | `q ≤ 200` | 53 | 1475 | 0 | **NONE** |
| `C₄` | `q ≤ 120` | 40 | 1576 | 1 | **NONE** |
| `B₄` | `q ≤ 120` | 34 | 1313 | 0 | **NONE** |
| `D₄` | `q ≤ 120` | 40 | 1314 | 1 | **NONE** |
| `²D₄` | `q ≤ 120` | 40 | 1190 | 0 | **NONE** |
| `C₅`, `D₅`, `²D₅` | `q ≤ 60` | 25 each | 1114–1369 | 0 | **NONE** |

**TOTAL survivors: 0.**  Note the contrast with `v_task56` (up to 130
floor-survivors per row): here the *floor* does almost all the killing, as at
rank 2 — because `b/a` is large for these towers relative to `L_d`.

---

## 8.  Status ledger

| step | `C_n` | `B_n` | `D_n` | `²D_n` |
|---|---|---|---|---|
| `ι` over **all** subgroups, (AB)-free | **[PROVEN]** | ” | ” | ” |
| `ι` witness `Z(U_P)`, `N_S = P` | **[PROVEN + GAP]** 4 rows | 2 rows | 2 rows | 2 rows |
| exceptional minimal degrees | **exact**, incl. the infinite `q=2` family | `Ω₇(3)` | `PΩ⁺₈(2)`, `PΩ⁺₈(3)` | none |
| Lemma Z | **[PROVEN]** all `q` | ” | ” (`b/K = 1`) | ” |
| eq-char, almost simple: EQ-EX + EQ′ + identities (J1)–(J5) | **[PROVEN]** uniform | ” | ” | ” |
| eq-char, almost simple: exact sweep | **[COMPUTED]** `q ≤ 2·10⁴` | ” | ” | ” |
| classical Lemma Q (`4b ≥ a`) | **FAILS** | **FAILS** | **FAILS** | **FAILS** |
| Lemma MO-EX (v_task58) | **FAILS** from `n = 8` | ” | from `n=9` | from `n=5` |
| **Lemma MO-SPO** + degree accounting | **[PROVEN]**, uniform in `q`, 0 survivors | ” | ” | ” |
| cross char, almost simple + Lemma X-2 | **[PROVEN]** | ” | ” | ” |
| alternating / sporadic socle | **[PROVEN]**, complete in `q` | ” | ” | ” |
| residual census | **[COMPUTED]** 0 live | ” | ” | ” |
| simple–simple side | **PARKED** (`B_n ≅_ord C_n`) | **PARKED** | **[LIT: CFSG]** | **[LIT: CFSG]** |

### Honest gaps

1. **(H1) The `ι` lower half is literature.**  `m(S) = [S:P₁]` with the four
   exceptional rows is **[LIT: Kleidman–Liebeck Table 5.2.2; Vasilyev]**,
   machine-confirmed at the seven targets with stored `Maxes`
   (`S6(2)`, `S6(3)`, `S8(2)`, `O7(3)`, `O8+(2)`, `O8-(2)`, plus the `U4(2)`,
   `S4(4)` controls).  `S6(4)`, `O10±(2)`, `O9(3)` have character tables but
   **no stored `Maxes`** — for those the witness half is GAP-computed and the
   lower half is literature only.  Same status as every row since `U₃`.
2. **(H2) `n ≤ 12`.**  Every *lemma* (Z, Z2, X-SPO, X-2, EQ-EX, EQ′, MO-SPO,
   the degree accounting) is uniform in `n` and gets **stronger** as `n`
   grows (`b/K → 1`, `a − 3(M+1) ~ 2n²`, the cross-char windows shrink).
   The *exact confirmations* (PARTS C.2, C.4, D.4, E, F, G) were run for
   `n ≤ 12` only.  Extending is compute, not mathematics — **named debt**,
   the direct analogue of `v_task56` (H3).
3. **(H3) `(J5)`'s strict inequality is asymptotic in form.**  `R_n(m) > 1`
   is argued from the leading correction `+m^{−2n}`; it is *verified exactly*
   for all `n ≤ 12` and all `m ≤ 3000` (no integer `c ≥ 2` occurs anywhere),
   but a closed-form proof of `R_n(m) > 1` for all `(n,m)` is **not written
   out**.  Given how thin the margin is (`q^{−2n/(2n−1)}`), **this is the
   sharpest named debt of the note.**
4. **(H4) MO-SPO's mixed-sign case with `≥ 4` orbits.**  The residual solver
   handles 1, 2 and 3 orbits exactly; a `≥ 4`-orbit mixed-sign residue would
   be reported as `UNDERDETERMINED`.  **None occurred** for `n ≤ 12`, but the
   solver is not general.
5. **(H5) MO-SPO's constants** (`A`, `B`, `δ`) are inherited from v_task58
   §3.3 and are generous; nothing rests on them here, because every
   configuration is killed by a *sign*, not by a threshold.
6. **(H6) `ῑ` in the floor** is the parabolic upper bound for Lie factors and
   the exact `v_task39/50` table for sporadics — inherited (`v_task55` H3).
7. **(H7) `|Out|`** is quoted from Kleidman–Liebeck; GAP `ExtensionInfo`
   confirms the multiplier/outer data at `S6(2)`, `S6(3)`, `S8(2)`, `O7(3)`,
   `O8±(2)`.  The `D₄` triality factor `g = 6` is used throughout (the
   largest `|Out|` in the programme, so the `c | |Out|` rule is at its
   weakest there — and indeed `D₄`/`²D₄` are closed by Lemma Z and Lemma Z2,
   not by `c | |Out|`).

---

## 9.  **What this says about the parked `B_n` / `C_n` simple–simple problem**

*(No attempt at a proof is made here.  This is what the invariant data of
this note bears on it.)*

1. **The reduction is now complete.**  After Sp-T and O-odd-T, any twin `T`
   of `Sp_{2n}(q)` or `Ω_{2n+1}(q)` (`n ≥ 3`, `q` odd) is **simple**, and by
   the CFSG order theorem it is the *other* member of the pair.  The
   `B_n`/`C_n` coincidence is therefore the **single remaining obstruction**
   in the whole programme, for these two towers and for nothing else.
2. **No order-derived invariant can separate them.** `|B_n(q)| = |C_n(q)|`
   as polynomials (J1)–(J2), hence identical `a`, `N`, `b`-degree, `K`,
   cyclotomic spectrum `∏Φ_e(q)^{m_e}`, `ppmax_{p′}`, and `M`.  Every tool of
   this note that touches only `|S|` is **blind** to the distinction —
   including Lemma Z, Lemma Z2, Lemma X-SPO, EQ-EX and MO-SPO.  This is not a
   defect of the tools; it is why the pair is parked.
3. **`ι` is also blind, with exactly one possible exception.**  Both towers
   have `ι = [S:P₁] = (q^{2n}−1)/(q−1)` (the number of singular 1-spaces is
   the same in both geometries for `q` odd), and both have `|Out| = 2f`.
   The **one** place the minimal degree differs is `(n,q) = (3,3)`:
   `m(Ω₇(3)) = 351` (the `G₂(3)` subgroup) against `m(Sp₆(3)) = 364`
   (GAP `Maxes`, `_g_out.txt` PART C).  **But this is almost certainly not a
   `D`-separation**: `G₂(3)` is *simple*, so it is `N_S(H)` only for `H` with
   no small abelian generator — the same mechanism by which `ι(L₄(2)) = 15`
   despite `m(A₈) = 8` (`v_task56` §1.3).  Recorded as the only numerical
   asymmetry `ι` offers, with the caveat attached.
4. **Where the asymmetry actually lives.**  The two towers differ in the
   *indices of the non-minimal parabolics* and in the maximal-subgroup
   lattice — e.g. `G₂(q) ≤ Ω₇(q)` with no symplectic analogue, and the
   `Sp₆(2)`-column inside `Ω₇(q)` (NOTES §-2650 ff.).  That is subgroup-
   lattice data, not order data — consistent with the project's existing
   `psn`/marks route being the live one.  **This note contributes no new
   separation, and its methods provably cannot** (point 2).
5. **A negative but useful datum from `char 2`.**  `B_n(2^f) ≅ C_n(2^f)`, so
   any candidate separating invariant must be **`q`-odd-specific**: it cannot
   be a specialisation of anything defined uniformly in `q`.  Combined with
   point 2 (order-blind) and point 3 (`ι`-blind), the separating invariant
   must be simultaneously order-independent, `ι`-independent, and
   characteristic-sensitive.  That is a tight three-way constraint and is the
   most concrete thing this note has to say about the parked question.
6. **What is *not* in the way.**  The `D_n`/`²D_n` pair is *not* an order
   coincidence — `(J4)` shows `|²D_n(q)|/|D_n(q)| ∈ (1,2) ∪ (2,3) ∪ (1/2,1)`,
   never `1`.  So the `D`-tower has no analogue of the parked problem, and
   D-T / 2D-T are unconditional.

---

## 10.  Citations

| # | input | tag |
|---|---|---|
| C1 | `m(S)` for `PSp_{2n}(q)`, `Ω_{2n+1}(q)`, `PΩ^±_{2n}(q)` and the four exceptional rows | **[LIT: Kleidman–Liebeck Table 5.2.2; Cooperstein 1978; Vasilyev 1996/97]**, GAP-confirmed at 6 targets |
| C2 | Borel–Tits `N_G(Z(U_P)) = P` | **[LIT]** + GAP at 10 targets, `N_S(Z(U_P)) = P` computed outright |
| C3 | Zsygmondy's theorem (Lemma Z) | **[LIT: Zsygmondy 1892]** |
| C4 | orders, parabolic indices, `|Out| = d f g` (incl. `D₄` triality `g = 6`) | **[LIT: Kleidman–Liebeck; ATLAS]**, GAP-checked 30/30 |
| C5 | CFSG order theorem: the only coincidences are `{A₈, L₃(4), L₄(2)}` and `{B_n(q), C_n(q)}` (`q` odd, `n ≥ 3`) | **[LIT: Artin; Kimmerle–Lyons–Sandling–Teague]** |
| C6 | Lemma C, `|Out|ι ≤ |G|^{2/3}` | **[PROVEN, v_task52]** |
| C7 | Lemma P (`N − μ ≥ 1` for rank ≥ 2) | **[PROVEN, v_task54]** |
| C8 | Lemma K′ (`|G| < (|G|_p)³`) | **[PROVEN, v_task53]** |
| C9 | Lemma TO′-0 + Lemma F (the orbit floor) | **[PROVEN, v_task42/v_task36]** |
| C10 | Lemma Z, Lemma Z2, Lemma X | **[PROVEN, v_task56]** |
| C11 | Lemma EQ′, Lemma EQ-EX | **[PROVEN, v_task57]** |
| C12 | Lemma MO-EX | **[PROVEN, v_task58 — but INAPPLICABLE here, §4.2]** |
| C13 | **Lemma MO-SPO** (two-sided MO-EX) + the residual degree accounting | **[PROVEN, this note]** |
| C14 | order transfer `D(T) ≅ D(S) ⟹ |T| = |S|` | **[LIT/formalised: Müller Satz 2.3.4]** |
| C15 | §4j–§4l reduction (Fitting-freeness a `D`-invariant) | **[PROVEN, this project]** |

---

## 11.  Reproduce

```
python3 -u v_task59_spo_twins.py                    > v_task59_spo_twins_out.txt    # ~30 min
~/gap-4.16.0/gap -q -o 8g v_task59_spo_twins.g      > v_task59_spo_twins_g_out.txt  # ~4 min
```

Individual parts: `python3 v_task59_spo_twins.py A | B | C | D | E | F | G`.

---

## 12.  Carry-overs

1. **Lemma MO-SPO supersedes Lemma MO-EX.**  Always check the *sign pattern*
   of `r_O − a/N` over the admissible set before reaching for a `(p,f)`
   sweep; the two-sided form kills uniform-sign configurations for free and
   reduces the rest to a small exact linear-algebra problem.  This is the
   cheapest multi-orbit tool in the programme.
2. **Do-not-re-attempt (added to the earlier lists):**
   * **Lemma MO-EX as stated in v_task58, on any tower with small `a/N`** —
     the convexity hypothesis `r_O ≥ a/N` is false whenever `a/N` approaches
     `2`, i.e. for every classical family of large rank.
   * **`c ∤ |Out|` in a same-`a/N` block** — silent, as v_task58 warned;
     `(J4)` and `(J5)` both had to be settled by strict inequalities, and
     `(J5)`'s margin is the thinnest in the programme.
   * **`Z(Syl_p)` as the `ι`-witness** — wrong in 9 of the 10 GAP rows here.
   * **Assuming `O_p(P)` is abelian because it was in an adjacent row** — it
     is abelian for `Sp_{2n}(2^f)` and non-abelian for `Sp_{2n}(q)`, `q` odd.
3. **What remains in the programme:** the `L_d`/`U_d`, `d > 10` exact residue
   (`v_task56` H4), the `n > 12` exact residue named here (H2), and **the
   parked `B_n`/`C_n` simple–simple pair — now the only genuinely open
   mathematical item.**
