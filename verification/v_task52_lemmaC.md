# v_task52 — **Lemma C proven**, **(G2) closed**, and
# **Theorem L2-T unconditional**

Date 2026-08-08.  **NOTES.md not edited.**

| file | what it does |
|---|---|
| `v_task52_lemmaC.py` | the machine half of the proof: degree table + (T1)/(T2) checks (PART 1), the **finite window** where the sufficient condition (★) fails, checked exactly (PART 2), alternating (PART 3), sporadic (PART 4), and the three residual-branch windows of (G2) (PART 5) |
| `v_task52_lemmaC_out.txt` | its output — **TOTAL violations: 0** |
| `v_task52_lemmaC.g` / `_g_out.txt` | GAP: **exact** `ι` and `|Out|` for the 13 tightest rows, and Borel–Tits witnesses `ind*(Z(U_P)) ≤ ῑ` for the 6 window groups whose subgroup lattice is out of reach |

All arithmetic is exact integer arithmetic; Lemma C is always tested in the
cube-cleared form `(|Out|·ῑ)³ ≤ |G|²`, never with a root or a float.

> **Headline.**
> **Lemma C [PROVEN].** For every non-abelian finite simple `G`,
> `|Out(G)| · ι(G) ≤ |G|^{2/3}`, **with no exceptions**.
> The bound is tight only at `A₆ ≅ L₂(9)` (ratio `0.790`) and `L₂(5)`
> (`0.783`); the asymptotically extremal family is the Ree groups `²G₂(q₁)`
> (exponent `α = log|G|/log ι = 7/3`, i.e. `ι ≍ |G|^{3/7} < |G|^{2/3}`).
>
> **(G2) closed.**  The cross-characteristic residual branches (E1)/(E2) of
> `v_task51`, and the alternating branch (E3), are reduced **by proof** to
> explicit finite windows (`q ≤ 600`, `q ≤ 839`, `m ≤ 15`), all strictly
> inside the ranges already exhausted with 0 hits.
>
> **Theorem L2-T [PROVEN, all `q ≥ 4`, unconditional].**  `L₂(q)` has no
> Fitting-free non-simple twin; combined with §2 of `v_task51`,
> **`L₂(q)` is `D`-rigid among all finite groups for every prime power
> `q ≥ 4`.**  No dependence on (AB), none on the `Bₙ/Cₙ` residue.

---

## 1. Lemma C — statement, and what the chain actually needs

`ι(G) := min_{1≠H≤G} [G:N_G(H)]·|H′|`.  Steps 2–3 of `v_task51` use Lemma C
**only** through

  `(q+1)/ℓ_O ≤ |Out(S_i)|·ι(S_i) ≤ |S_i|^{2/3}`  (§4.1 of `v_task51`),

i.e. only in the direction "`ι` small ⟹ `|S_i|` large".  Consequently every
`ι` below may be replaced by any **upper bound** `ῑ ≥ ι`, and every `|Out|` by
any **upper bound** — both are the conservative direction, and both are used
that way throughout.  The exponent `2/3` is exactly what Step 2 needs
(`ι(S)^{3k/2} > |S|` for `k = 2` requires `ι(S) > |S|^{1/3}`, which for the
target `L₂(q)` is `q+1 > (q³−q)^{1/3}` ✓); nothing weaker suffices, and
nothing stronger is needed.

**Upper bounds used.**

* **alternating**: `H = ⟨(123)⟩` is abelian with
  `N_{A_m}(H) = (S₃ × S_{m−3}) ∩ A_m`, so `ι(A_m) ≤ C(m,3)` for all `m ≥ 5`
  (this is an equality for `m ≥ 9`, §4as, but only "≤" is used).  Exact
  values are needed at `m = 5, 6` (`ι = 5, 10`), where `C(m,3)` is too weak.
  `|Out(A_m)| ≤ 2`, `= 4` for `m = 6`.
* **Lie type**: `Z(U_P)` is a non-trivial abelian subgroup with
  `N_G(Z(U_P)) = P` (Borel–Tits), so `ι(G) ≤ [G:P] =: ῑ(G)` for the smallest
  parabolic `P` (the isotropic-point stabiliser; for the rank-1 families
  `A₁, ²A₂, ²B₂, ²G₂` this is the Borel and `ῑ = q+1, q³+1, q²+1, q³+1`).
  These indices are the classical formulas [LIT: Kleidman–Liebeck; Vasilyev];
  **no minimality claim is used** — only that they are *some* `ind*` value.
* **sporadic**: the exact `ι` table of `v_task39`/`v_task50` (27 rows).

---

## 2. Proof of Lemma C for the groups of Lie type

Let `G` be simple of Lie type over `F_{q₁}`, `q₁ = p₁^{f₁}`, written
`|G| = q₁^{N} ∏_{i=1}^{r} (q₁^{d_i} − ε_i)/d`, `ε_i ∈ {±1}`, `d_i ≥ 2`, and
put

  `D := deg_{q₁}|G| = N + Σ d_i`,  `μ := deg_{q₁} ῑ`,  **`e := 2D − 3μ`.**

**(T1)** `|G| ≥ q₁^{D}/(12 d)`.
*Proof.* `∏(q₁^{d_i} − ε_i) ≥ ∏(q₁^{d_i} − 1) = q₁^{Σd_i}∏(1 − q₁^{−d_i})`,
and each `d_i ≥ 2` occurs at most twice in the multiset of degrees (a repeat
occurs only in `D_n`, `n` even), so
`∏(1−q₁^{−d_i}) ≥ (∏_{k≥1}(1−2^{−k}))² = 0.08337… > 1/12`. ∎
(Machine: PART 1 verifies the equivalent integer inequality
`12·∏terms ≥ q₁^{D−N}` at `q₁ = 2,3,4,5` for every family; the ratio is
increasing in `q₁`, so `q₁ = 2` is extremal.)

**(T2)** `ῑ ≤ 4 q₁^{μ}`.
*Proof.* Every `ῑ` in the table is a product of at most two quotients of the
shape `(q₁^{a} ± 1)/(q₁^{b} − 1)` with `a > b ≥ 0`, and each such quotient is
`< q₁^{a}·(1+q₁^{−a})/(q₁^{b}(1−q₁^{−b})) ≤ 2q₁^{a−b}` for `q₁ ≥ 2`. ∎
(Machine: PART 1, same four values of `q₁`, plus every group of the window.)

**(T3)** `|Out(G)| = d·f₁·g` with `g ≤ 6` (`g = 6` only for `D₄`, `g = 3` for
`³D₄`, `g = 2` for the families with a graph automorphism, else `1`)
[LIT: standard]; the script uses a **≥** bound (e.g. `4` instead of the true
`2` for `S₄(3)`), which is conservative.

**Sufficient condition.**  Substituting (T1)–(T3) into `(|Out|·ῑ)³ ≤ |G|²`:

> **(★)  `9216 · d⁵ · g³ · f₁³ ≤ q₁^{e}` ⟹ Lemma C for `G`.**

**The degree table** (PART 1 of the output; `n` = rank parameter):

| family | `D` | `μ` | `e = 2D−3μ` | `3μ/2D` |
|---|---|---|---|---|
| `A₁ = L₂(q₁)` | 3 | 1 | **3** | 0.500 |
| `L_n(q₁)`, `n≥3` | `n²−1` | `n−1` | `(n−1)(2n−1)` | `3/(2n+2) ≤ 0.375` |
| `U_n(q₁)`, `n≥3` | `n²−1` | `2n−3` | `2n²−6n+7` | `≤ 0.5625` (`n=3`) |
| `S_{2n}(q₁)`, `n≥2` | `2n²+n` | `2n−1` | `4n²−4n+3` | `≤ 0.450` |
| `O_{2n+1}(q₁)`, `n≥3` | `2n²+n` | `2n−1` | `4n²−4n+3` | `≤ 0.357` |
| `O^±_{2n}(q₁)`, `n≥4` | `2n²−n` | `2n−2` | `4n²−8n+6` | `≤ 0.322` |
| `G₂` | 14 | 5 | 13 | 0.536 |
| `³D₄` | 28 | 9 | 29 | 0.482 |
| `F₄` | 52 | 15 | 59 | 0.433 |
| `E₆`, `²E₆` | 78 | 16 | 108 | 0.308 |
| `E₇` | 133 | 25 | 191 | 0.282 |
| `E₈` | 248 | 51 | 343 | 0.308 |
| `Sz(q₁) = ²B₂` | 5 | 2 | **4** | 0.600 |
| `R(q₁) = ²G₂` | 7 | 3 | **5** | **0.643** ← extremal |
| `²F₄(q₁)` | 26 | 10 | 22 | 0.577 |

`e > 0` in **every** family and every rank — this is the asymptotic half, and
it is a finite table because `e` is a quadratic in `n` with positive leading
coefficient in each of the six infinite-rank families.  The worst ratio
`3μ/2D = 9/14` is the Ree family, matching the `α = 7/3` row of
`v_task51_lemmaBC_out.txt`: `α = D/μ = 7/3 ≥ 3/2` is exactly `e ≥ 0`.

**The `f₁`-log absorbed, with the finite range named.**  (★) can fail only if
`9216 d⁵g³f₁³ > q₁^{e} ≥ 2^{e f₁}`, which bounds `f₁` (explicitly: `d ≤ dmax`
is `n` for `A_n/²A_n`, `4` for `D`-types, `2` otherwise), and then bounds
`q₁ ≤ (9216 d⁵g³f₁³)^{1/e}`.  PART 2 enumerates this window family by family
(over **all** ranks: for `n` past the third value the window is already empty
and `e` is increasing, so it stays empty) and checks Lemma C on every member
**exactly**.  Result:

| family | groups in the (★)-window | tightest rows (ratio `|Out|ι/|G|^{2/3}`) |
|---|---|---|
| `A₁` | 30 | `L₂(9) 0.790`, `L₂(5) 0.783`, `L₂(4) 0.652` |
| `L_n`, `n≥3` | 3 | `L₃(2) 0.460`, `L₃(4) 0.340`, `L₃(3) 0.082` |
| `U_n` | 6 | `U₃(5) 0.301`, `U₃(8) 0.296`, `U₃(3) 0.169` |
| `S_{2n}` | 1 | `S₄(3) 0.183` |
| `Sz` | 2 | `Sz(8) 0.206`, `Sz(32) 0.050` |
| all others | **0** | (★) holds outright |

**42 groups in total, 0 failures.**  Together with (★) for everything outside
the window, **Lemma C holds for every simple group of Lie type**, with margin
`≥ 1/0.790 = 1.27` and, off the window, margin `≥ q₁^{e/3}/(21·d^{5/3}g f₁)`
growing polynomially.

GAP independently confirms the two inputs on the tight rows
(`v_task52_lemmaC_g_out.txt`): exact `ι` and exact `|Out|` for
`L₂(4,5,7,8,9,11,13)`, `L₃(2,3,4)` — e.g. `L₃(4)`: `ι = 21`, `|Out| = 12`,
`(12·21)³ = 16 003 008 ≤ 20160² = 406 425 600` — and
`ind*(Z(Syl_p)) ≤ ῑ` for `U₃(3), U₃(5), U₃(8), S₄(3), Sz(8), Sz(32)`.
(Note `S₄(3)`: the `Z(Syl₃)` witness realises the isotropic-point index
`40 = (3⁴−1)/(3−1)`, which is what the script uses; `v_task50`'s CTblLib row
records the smaller **exact** `ι = 27`.  Using the larger value is the
conservative choice.)

## 3. Proof of Lemma C for `A_m` and for the sporadics

**Alternating.**  `(|Out|·ι)³ ≤ (2·C(m,3))³ ≤ 8m⁹/216 = m⁹/27` and
`|G|² = (m!/2)²`, so it suffices that `R(m) := 27(m!/2)²/m⁹ > 1`:

* base `m = 9`: `27·(9!/2)² = 888 852 787 200 > 9⁹ = 387 420 489`;
* step `m ≥ 9`: `R(m+1)/R(m) = (m+1)²(m/(m+1))⁹ ≥ (m+1)²(9/10)⁹ > 1`
  (since `100·9⁹ > 10⁹`).

`m = 5,6,7,8` use `ι ≤ 5, 10, 35, 56` and `|Out| = 2,4,2,2` (the first two are
the exact values — `C(5,3) = 10` and `C(6,3) = 20` are too weak; the last two
are the `C(m,3)` bound, and are already sufficient — the exact values are
`ι(A₇) = 35`, `ι(A₈) = 15`):
ratios `0.652, 0.790, 0.377, 0.151`.  PART 3 verifies `A₅ … A₆₀` exactly:
**0 failures**, tightest `A₆` at `0.790`. ∎

**Sporadic.**  PART 4: the 26 sporadics plus the Tits group with their exact
`ι` (`v_task39`) and exact `|Out|`: **0 failures**, tightest `J₁` at ratio
`0.333`.  In particular the three groups that **fail Lemma B**
(`J₁ α=1.737`, `O′N 1.807`, `J₃ 1.816`) satisfy **Lemma C** comfortably —
Lemma B is a strictly stronger statement (`α > 2` versus `α ≥ 3/2`) and is
**not** used in the `L₂` chain. ∎

**Exception list of Lemma C: empty.**

---

## 4. Closing (G2)

Standing: `T` Fitting-free, `|T| = N = |L₂(q)| = q(q²−1)/d`, one socle orbit
of length `ℓ ≤ 2` (Steps 2–3, now unconditional), `c = [T : Soc T]`.

### 4.1 (E1): `Soc T = L₂(q₁)`, `ℓ = 1`, `p₁ ≠ p` — **[PROVEN]**

Equation `c·q₁(q₁²−1)/d₁ = q(q²−1)/d`, `2 ≤ c ∣ |Out(L₂(q₁))| = d₁f₁`.

**(a) Size.**  `q(q²−1)/d = c q₁(q₁²−1)/d₁ ≤ c q₁³/d₁` gives
`q₁³ ≥ q(q²−1)/(2c)`, hence `q₁ ≥ 0.777·q/c^{1/3}` for `q ≥ 4`; and
`c q₁(q₁²−1) ≤ 2q³` gives `q₁ < 1.11 q`.  So **`q₁ ≍ q`**.

**(b) The `p`-part.**  `|N|_p = q` and `p ∤ q₁`, so
`q = |c|_p · |q₁²−1|_p`.  If `p` is odd it divides exactly one of `q₁∓1`, so
one of them equals `m·p^{a}` with `p^{a} ≥ q/|c|_p` and `p^{f−a} = |c|_p ≤ c`;
writing `P := p^{a} = q/p^{j}`, `p^{j} ≤ c`:

  **`q₁ = m·q/p^{j} ± 1`  for some `m ≥ 1` with `m ≤ p^{j}(q+1)/q`.**

For `p = 2` the same holds with `2^{j+1} ≤ 2c` (because
`min(|q₁−1|₂,|q₁+1|₂) = 2`).

**(c) The `p₁`-part (Lemma K in reverse).**  `|N|_{p₁} = |q²−1|_{p₁}/|d|_{p₁}`
and the left side contributes `q₁·|c|_{p₁}`, so `q₁ ∣ |q²−1|_{p₁}`.  For `p₁`
odd this forces `q₁ ∣ q−1` **or** `q₁ ∣ q+1`; for `p₁ = 2` it forces
`q₁/2 ∣ q−1` or `q₁/2 ∣ q+1`.  Write the divisible block as
`q ∓ 1 = k·q₁` (resp. `k·q₁/2`); by (a), `k ≤ 4(q+1)/q₁ ≤ 6.5·c^{1/3}`.

**(d) Collision.**  Substituting (b) into (c):
`q(p^{j} − km) = ±p^{j}(k+1)`-type identity.  Two cases.

* `km ≠ p^{j}` (resp. `≠ 2p^{j}`): then `q ≤ 2c(k+1)` with
  `c ≤ 2f₁ ≤ 2log₂(2q+2)` and `k ≤ 4(q+1)/q₁`, `q₁³ ≥ q(q²−1)/(2c)`.
  PART 5 evaluates this self-consistent system with exact integers:
  **it fails for every `q > 600`.**
* `km = p^{j}` (resp. `2p^{j}`): then the `±` terms must cancel, forcing
  `k = 1` (resp. `2`), `m = p^{j}`, and hence **`q₁ = q ± 1`**.

**(e) The sub-branch `q₁ = q ± 1`, solved in closed form.**
`q₁ = q+1`: `q₁²−1 = q(q+2)`, so the equation reduces to
`c·d·(q+2) = d₁·(q−1)`; `c·d ≥ 2` and `d₁ ≤ 2` give `2(q+2) ≤ 2(q−1)` —
**impossible**.
`q₁ = q−1`: it reduces to `c·d·(q−2) = d₁·(q+1)`, so `c·d ≤ 3` for `q ≥ 8`.
An exhaustive integer solve (PART 5, `4 ≤ q < 2·10⁵`) returns the **single**
solution `q = 8, q₁ = 7, c = 3` — and `c = 3` does not divide
`|Out(L₂(7))| = 2`, so it is not a Fitting-free configuration
(it *is* cross-characteristic, `7 ≠ 2`; it is killed by the `c`-divisibility,
not by the characteristic).  **Impossible.**

**So (E1) has no cross-characteristic solution with `q > 600`; `q ≤ 600` is
inside the exhaustive census `q ≤ 10⁶` (0 hits).  (E1) is closed.** ∎

### 4.2 (E2): `Soc T = L₂(q₁)²`, `ℓ = 2` — **[PROVEN, by order alone]**

`|L₂(q₁)|² ≤ |L₂(q)| < q³` with `|L₂(q₁)| ≥ q₁(q₁²−1)/2 ≥ (3/8)q₁³` gives
`q₁ ≤ (64q³/9)^{1/6} ≈ 1.30 √q`.  The orbit floor (F) for an orbit of length
`2` reads `2·|Out(L₂(q₁))|·(q₁+1) ≥ q+1`, i.e. `4f₁(q₁+1) ≥ q+1` with
`f₁ ≤ log₂ q₁`.  Combining, `q+1 ≤ 4log₂(1.3√q)(1.3√q+1)` — a
`√q · log q` bound against `q`.  PART 5 evaluates it exactly:
**it fails for every `q > 839`**.  The remaining `q ≤ 839` are inside the
census.  **(E2) is closed** — and indeed dies on order + floor alone, no
`d`-bookkeeping needed. ∎

### 4.3 (E3)/(E4): alternating and sporadic socle

**(E3)** was *not* a finite list as stated in `v_task51` (`m` is unbounded a
priori).  It is made finite here: by **Lemma K** the `2`-part of
`N = |L₂(q)|` is `≤ q+1`, while `Soc T = A_m^ℓ` contributes
`2^{ℓ(v₂(m!)−1)} ≥ 2^{v₂(m!)−1}`, so `2^{v₂(m!)−1} ≤ q+1`; and the orbit
floor gives `q+1 ≤ ℓ·|Out(A_m)|·ι(A_m) ≤ 2·|Out(A_m)|·C(m,3)`.  Hence

  `2^{v₂(m!)−1} ≤ 2|Out(A_m)|·C(m,3)`,

which PART 5 shows **fails for every `m > 15`**.  So `m ≤ 15`, and that range
is exhausted by the `v_task51` scan (`m ≤ 47`, complete in `q` because
`(m,ℓ,c)` determines `|L₂(q)|` hence `q`), with **0 hits**.  ∎

**(E4)** is genuinely finite as it stands: 27 socle types × `ℓ ∈ {1,2}` ×
`c ∣ 2^ℓℓ!`; each triple determines `|L₂(q)|` and hence `q` (the map
`q ↦ q³−q` is injective).  The scan is therefore an exhaustive proof, 0 hits.
∎

---

## 5. Consequence

> **Theorem L2-T [PROVEN, unconditional, all prime powers `q ≥ 4`].**
> There is no Fitting-free **non-simple** finite group `T` with
> `|T| = |L₂(q)|` and `D(T) ≅ D(L₂(q))`.  With `v_task51` §2 (order-uniqueness
> of `L₂(q)` among simple groups, CFSG order theorem):
> **`L₂(q)` is `D`-rigid among all finite groups, for every `q ≥ 4`.**

Chain, with every link now `[PROVEN]`:

| link | status |
|---|---|
| `ι(L₂(q)) = q+1` (`q ≠ 5,7`), over **all** subgroups — (AB)-free | `[PROVEN]` `v_task51` §1.1 |
| Lemma K (prime powers in `\|L₂(q)\|` are `≤ q+1`) | `[PROVEN]` `v_task51` §4 |
| orbit floor (F) = Lemma TO′-0 + Lemma F | `[PROVEN]` `v_task42`/`v_task36` |
| **Lemma C** `\|Out(G)\|ι(G) ≤ \|G\|^{2/3}`, no exceptions | **`[PROVEN]` here, §2–§3** |
| Step 2 (one socle orbit), Step 3 (`ℓ ≤ 2`) | `[PROVEN]` (were conditional on C) |
| Step 4 rank forcing ⟹ `S₁ ∈ {L₂(q₁), A_m, sporadic}` | `[PROVEN]` `v_task51` §4.4 |
| (E1)/(E2) equal characteristic | `[PROVEN]` `v_task51` §4.5 |
| **(E1)/(E2) cross characteristic**, **(E3)**, (E4) | **`[PROVEN]` here, §4** |
| simple–simple side, `Bₙ/Cₙ`-independent | `[PROVEN]` `v_task51` §2 (CFSG) |

**Literature actually invoked** (unchanged from `v_task51` plus one item):
Dickson's subgroup theorem; Galois' minimal index; CFSG order theorem;
Borel–Tits `N_G(Z(U_P)) = P`; **the classical minimal-parabolic index
formulas and the `|Out| = d·f·g` table [LIT: Kleidman–Liebeck; Atlas]** —
the new input of §2, used only as *upper* bounds for `ι` and `|Out|`.

## 6. Residual caveats (small, named)

1. Lemma C's Lie-type half rests on the **order formulas, the parabolic index
   formulas and the `d·f·g` table** being quoted correctly.  They are
   standard, and the 42 window groups plus the 1 286-group sweep of
   `v_task51` (`q₁ ≤ 4096`, rank `≤ 8`) plus the GAP rows of
   `v_task52_lemmaC_g_out.txt` cross-check them at every point where the
   inequality is tight.
2. `(T1)` is proven by an Euler-product estimate valid for all ranks; the
   machine check in PART 1 spot-checks it at `q₁ = 2,3,4,5` and the first six
   ranks of each infinite family.
3. The finite windows of §4 (`q ≤ 600`, `q ≤ 839`, `m ≤ 15`) are covered by
   the `v_task51` census (`q ≤ 10⁶`, `m ≤ 47`), which carries its own
   positive controls.  They are **not** re-run here.

## 7. Reproduce

```
python3 v_task52_lemmaC.py                    > v_task52_lemmaC_out.txt   # ~2 min
~/gap-4.16.0/gap -q -o 4g v_task52_lemmaC.g   > v_task52_lemmaC_g_out.txt # ~1 min
```
