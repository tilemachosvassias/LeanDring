# v_task53 — Fitting-free **non-simple** twins of the remaining RANK-1 Lie
# targets: `U₃(q)`, `Sz(q) = ²B₂(q)`, `R(q) = ²G₂(q)`

Date 2026-08-08.  **NOTES.md not edited.**
Pipeline: the `L₂` pilot of `v_task51_l2_twins.md`, applied per family.

| file | what it does |
|---|---|
| `v_task53_rank1_twins.py` | everything below: `--uniform` (Steps 2–3), `--lemK` (Lemma K analogues), `--rank` (Lemma R + the cross-characteristic kill), `--eqchar` (the equal-characteristic branch, decided **exactly**), `--census FAM LIM` (Phase 1 + Phase 2 per target), `--sub` (the residual `c·|S₁| = |S|` equation + a negative control) |
| `v_task53_rank1_twins_out.txt` | `--uniform`, `--lemK`, `--rank` |
| `v_task53_eqchar_out.txt` | the equal-characteristic branch, all three families |
| `v_task53_census_U3_out.txt` | full census, **all 5 216 prime powers `3 ≤ q ≤ 50 000`**, run `--raw` |
| `v_task53_census_Sz_out.txt` | full census, `q = 2^f`, `f` odd `≤ 101` (50 targets, `q ≤ 2.5·10³⁰`), `--raw` |
| `v_task53_census_Ree_out.txt` | full census, `q = 3^f`, `f` odd `≤ 61` (30 targets, `q ≤ 1.3·10²⁹`), `--raw` |
| `v_task53_sub_out.txt` | the residual `ℓ = 1` equation over 281 331 socle candidates, + the negative control |
| `v_task53_rank1_twins.g` / `_g_out.txt` | GAP: order formulas, the explicit `ι` witness `A = Z(Syl_p(S))`, exact `ι` over **all** subgroups where the lattice is in reach, Lemma K, and the `|U₃(q)| = (q+1)·|R(q)|` coincidence |

The CFSG simple-order enumerator and the multiset census are **imported** from
`v_task50_sporadic_twins.py`; the fast factoriser, `iota_ub_generic` and
`prime_powers_upto` from `v_task51_l2_twins.py`.  One implementation, now
exercised on 27 sporadic + 78 732 `L₂` + 5 296 rank-1 Lie targets.

---

> ### Headline
>
> **Theorem U3-T.**  Let `q ≥ 3` be a prime power, `S = U₃(q)`.
> **Theorem Sz-T.**  Let `q = 2^{2m+1} ≥ 8`, `S = Sz(q)`.
> **Theorem Ree-T.**  Let `q = 3^{2m+1} ≥ 27`, `S = R(q)`.
>
> In each case there is no Fitting-free **non-simple** finite group `T` with
> `|T| = |S|` and `D(T) ≅ D(S)`; combined with the (classical) uniqueness of
> `|S|` among simple orders, **`S` is `D`-rigid among all finite groups**.
>
> Status per family, honestly:
>
> | | uniform reduction | residual branch | census |
> |---|---|---|---|
> | `U₃(q)` | `ℓ = 1` **[PROVEN, all `q ≥ 8`]** (`q = 3,4,7`: census) | equal-char **[COMPUTED, exact, complete in `q₁`, `q ≤ 6.9·10⁶⁶`]**; cross-char Lie **[PROVEN empty for `q ≥ 179`]**; alt/sporadic **[COMPUTED, complete in `q`]** | **EMPTY, all `q ≤ 50 000`**, even *without* the orbit-floor filter |
> | `Sz(q)` | `ℓ = 1` **[PROVEN, all `q`]** | equal-char **[COMPUTED, exact, `q ≤ 2.7·10³⁶`]**; cross-char **[COMPUTED only]** | **EMPTY, all `q ≤ 2.5·10³⁰`**, raw |
> | `R(q)` | `ℓ = 1` **[PROVEN, all `q`]** | equal-char **[COMPUTED, exact, `q ≤ 5.4·10⁵⁷`]**; cross-char Lie **[PROVEN empty for `q ≥ 2187`]**; alt/sporadic **[COMPUTED, complete in `q`]** | **EMPTY, all `q ≤ 1.3·10²⁹`**, raw |
>
> All three rows are **(AB)-free** (§1) and **`Bₙ/Cₙ`-independent** (§2), and
> all three inherit the pilot's debt **(G1) Lemma C** (`v_task52`, currently
> `[COMPUTED]`), which Steps 2–3 use.  Remaining own debts: §7.
>
> **The rank-1 families are markedly easier than `L₂`.**  Where the `L₂` pilot
> got only `ℓ ≤ 2` and had one raw census near-miss (`q = 64`), here the
> uniform argument reaches `ℓ = 1` outright — `T` is *almost simple* — and the
> raw, unfiltered census is empty at **every single target**: the orbit floor
> is never actually needed to kill anything.  This confirms the pilot's
> prediction (`ι ≍ |S|^{3/8}, |S|^{2/5}, |S|^{3/7}` vs `|S|^{1/3}` for `L₂`).

---

## 0. Notation

As `v_task51_l2_twins.md` §0.  `T` Fitting-free, `Q = Soc T = ∏ S_i^{ℓ_i}`,
`c := [T : Soc T]`, orbits `O` of lengths `ℓ_O`;
`ind*(H) := [S:N_S(H)]·|H′|`, `ι(S) := min_{1≠H≤S} ind*(H)`,
`I(S) :=` the `ind*` spectrum, `m(S) :=` the **minimal degree** = smallest
index of a proper subgroup.  `q = p^f`.

Orders (GAP-verified against `PSU(3,q)`, `SuzukiGroup(q)`, `ReeGroup(q)`,
`_g_out.txt` PART A):

```
|U_3(q)| = q^3 (q^2-1)(q^3+1)/e ,  e = gcd(3,q+1)     ~ q^8
|Sz(q)|  = q^2 (q-1)(q^2+1)                           ~ q^5
|R(q)|   = q^3 (q-1)(q^3+1)                           ~ q^7
|Out|    = e·2f  (U_3) ,  f  (Sz) ,  f  (R)
```

---

## 1. The targets' invariants, uniform in `q` — and the (AB)-freeness

> **Lemma U3-ι / Sz-ι / Ree-ι  [PROVEN, over ALL subgroups].**
> `ι(U₃(q)) = q³+1` for every prime power `q ≥ 3`;
> `ι(Sz(q)) = q²+1` for every `q = 2^{2m+1} ≥ 8`;
> `ι(R(q))  = q³+1` for every `q = 3^{2m+1} ≥ 27`.
> **No exceptions in any of the three families.**

*Proof.*

**(≤), the witness.**  Let `P = Syl_p(S)` and `A = Z(P)`.  In all three
families `A` is a **non-trivial elementary abelian** subgroup — of order `q`
in each case — and `N_S(A) = B`, the Borel subgroup (equivalently, the
stabiliser of the isotropic point / of the point of the Suzuki–Ree ovoid);
this is Borel–Tits, `N_S(Z(U_P)) = P`, with `P = B` the unique parabolic of
a rank-1 group.  Hence `A′ = 1` and

```
ind*(A) = [S : B] · 1 = q^3+1   (U_3, R) ,      q^2+1   (Sz).
```

**Machine check** (`_g_out.txt` PART B, direct in GAP: `A := Centre(SylowSubgroup(G,p))`):
`|A| = q`, `IsAbelian(A) = true`, and `ind*(A) = q³+1` resp. `q²+1` for
`U₃(q)`, `q = 3,4,5,7,8,9,11,13,16,17,19,23,25,27` (14 values) and `Sz(q)`,
`q = 8,32,128` — **all `ok? true`**.
**The Ree family is NOT machine-checked here**, and the gap is real: GAP
returns `ReeGroup(q)` as a 7-dimensional *matrix* group (no point set to
stabilise), the `Normalizer` of `Z(Syl₃)` in a group of order `10¹⁰` does not
terminate, and `CharacterTable("R(27)")` has **no stored `Maxes`**.  The Ree
row of Lemma ι therefore rests on the literature (C2, C5) alone.

**(≥), over all `H`.**  Let `1 ≠ H ≤ S`.  If `N_S(H) = S` then `H ⊴ S`, so
`H = S` by simplicity and `ind*(H) = |S| ≫ ι`.  Otherwise `N_S(H)` is a
**proper** subgroup, so `ind*(H) ≥ [S:N_S(H)] ≥ m(S)`, the minimal degree.

* `m(Sz(q)) = q²+1` for every `q` **[LIT: Suzuki 1962]** — the ovoid.
* `m(R(q))  = q³+1` for every `q ≥ 27` **[LIT: Ward 1966; Kleidman]**.
* `m(U₃(q)) = q³+1` for every `q ≥ 3` **except `q = 5`**, where `m = 50`
  (the three classes of `A₇`) **[LIT: Cooperstein 1978; Kleidman–Liebeck
  Table 5.2.2]**.

So (≥) is immediate for `Sz`, `R`, and for `U₃(q)`, `q ≠ 5`.  For
**`U₃(5)`** two extra lines: the maximal subgroups have indices
`50, 126, 175, 525` (`_g_out.txt` PART C2), so a proper subgroup of index in
the open interval `(50, 126)` would have index `< 126/50 < 3` inside a
maximal `A₇` — i.e. index `2` in `A₇`, impossible.  And index exactly `50`
gives `N_S(H) = A₇`, so `1 ≠ H ⊴ A₇` properly — impossible, `A₇` simple.
Hence no `ind*` value lies below `126`, and `ι(U₃(5)) = 126 = q³+1`. ∎

**This proof quantifies over all `H`, not only abelian `H`.**  As in the `L₂`
pilot, the hypothesis **(AB)** that stands over Theorem AT (`Aₙ`) and Theorem
SPT (sporadics) is therefore **not a debt for these three rows**.  The reason
is the same structural one: `ind*(H) ≥ [S:N_S(H)] ≥ m(S)` is *sharp*, because
in a rank-1 group of Lie type the minimal-degree subgroup **is** the Borel,
which **is** a normaliser.  *(Note the contrast with `L₂`, which needed two
genuine exceptions `q = 5, 7`, and `U₃(5)`, which needed the argument above
but produces no exception.)*

**Exact `ι` over the whole subgroup lattice** (`_g_out.txt` PART C, no (AB)
restriction, `ConjugacyClassesSubgroups` — the two cases where the lattice is
in reach):

| `S` | `ι` | claimed | `ι₂` | first six of `I(S)` |
|---|---|---|---|---|
| `U₃(3)` | 28 | `3³+1 = 28` | 63 | `28, 63, 84, 112, 126, 189` |
| `Sz(8)` | 65 | `8²+1 = 65` | 455 | `65, 455, 520, 560, 910, 1456` |

Both agree with the independent Lemma-SP values `28`, `65` already tabulated
in `v_task50`'s `IOTA_UB`.  *(Unlike `L₂`, here `ι₂/ι₁` is `2.25` and `7.0` —
but no uniform gap is claimed and none is used; the pilot's refutation of the
`ι₂/ι₁` route stands.)*

**Minimal degrees from the stored maximal subgroups** (`_g_out.txt` PART C2):

```
U3(3) : [28, 36, 63, 63]                m = 28  = q^3+1
U3(4) : [65, 208, 416, 1600]            m = 65  = q^3+1
U3(5) : [50,50,50, 126, 175,175,175, 525]   m = 50   <-- the exception
U3(7) : [344, 2107, 14749, 16856, 43904]    m = 344 = q^3+1
U3(8) : [513, ...]                      m = 513 = q^3+1
U3(9) : [730, ...]                      m = 730 = q^3+1
U3(11): [1332, ...]                     m = 1332 = q^3+1
Sz(8) : [65, 560, 1456, 2080]           m = 65  = q^2+1
Sz(32): [1025, 198400, 325376, 524800]  m = 1025 = q^2+1
R(27) : no stored Maxes
```

The `U₃(5)` row is exactly the input the argument above needs: the indices
jump `50 → 126`, and `126/50 < 3`, so no proper subgroup has index strictly
between them.

### 1.1 The small-`q` exceptional isomorphisms

| case | status |
|---|---|
| `U₃(2)` | **not simple** (`U₃(2) = 3²:Q₈`); excluded from the target range and from the enumerator (`v_task50` `lie_orders` skips `n = 3, q = 2`) |
| `U₃(3) ≅ G₂(2)′` | a genuine isomorphism, **not** an order coincidence.  `v_task50` `ISO_DROP` deliberately keeps `U₃(3)` as the canonical name (`G₂(q)` is generated only for `q ≥ 3`), so the enumerator returns it exactly once — verified by the positive control at `q = 3` |
| `Sz(2)` | **not simple** (`= 5:4`); `f ≥ 3` in the target range and in the enumerator |
| `²G₂(3)′ ≅ L₂(8)` | outside the target range (`q ≥ 27`); `L₂(8)` is closed independently in §4l and in `v_task51` |
| `U₃(5)` | minimal degree `50 ≠ q³+1`; handled in Lemma U3-ι above, **no exception to `ι`** |

No exceptional isomorphism needs a new argument.

---

## 2. The simple–simple side: free, and `Bₙ/Cₙ`-independent

By the CFSG order theorem the only non-isomorphic finite simple groups of
equal order are `{A₈, L₃(4)}` and `{B_n(q), C_n(q)}` (`n ≥ 3`, `q` odd)
**[LIT: Artin; Kimmerle–Lyons–Sandling–Teague]**.  None of `U₃`, `Sz`, `²G₂`
occurs in either.  Hence

> **Each of `U₃(q)`, `Sz(q)`, `R(q)` is determined among finite simple groups
> by its order** — the simple–simple row is free, and **none of the three
> targets touches the `Ω₇(q)` vs `PSp₆(q)` residue that §4l leaves open**.

**Machine re-confirmation, per target.**  Every census run tests that the
enumerator returns **exactly one** simple group of order `|S|`, *and that its
name is the target's*:

```
U3  : PASS, all 5216 targets   Sz : PASS, all 50 targets   Ree: PASS, all 30 targets
```

This is also the control that makes "empty census" meaningful rather than a
false negative.

**A genuine order relation between two of the targets** (found by the
negative control in `--sub`, §6):

> **Observation.**  For `q = 3^{2m+1}`, `|U₃(q)| = (q+1)·|R(q)|` exactly
> (`e = gcd(3,q+1) = 1` since `3 | q`; the ratio is `(q²−1)/(q−1)`).

So `U₃(q)` and `R(q)` have orders in a *fixed small ratio* over the whole Ree
range.  A hypothetical `T` with `Soc T = R(q)` and `c = q+1` would have
`|T| = |U₃(q)|`.  It dies because `c = q+1` does not divide
`|Out(R(q))| = f = log₃ q`.  Recorded because it is the closest thing to a
near-miss anywhere in this note (GAP check: `_g_out.txt` PART E).

---

## 3. The uniform inputs

**Input 1 — the orbit floor.**  Lemma TO′-0 (`v_task42_to_prime.md`, verified
*target-agnostic* in `v_task50_sporadic_twins.md` §1.2) + Lemma F
(`v_task36_pair_invariants.md`):

```
(F)   ℓ_O · |Out(S_i)| · ι(S_i)  ≥  ι(S)     for every socle orbit O.
```

**Input 2 — the `c`-bound.**  `F(T) = 1 ⟹ T ≤ Aut(Soc T)`, so
`c | ∏_i (|Out(S_i)|^{ℓ_i} · ℓ_i!)`.

**Input 3 — Lemma C**, `|Out(G)|·ι(G) ≤ |G|^{2/3}` for all simple `G`.
`[COMPUTED, 1286 groups + per-family asymptotics; being proven in v_task52]`
— **cited as input; this note's Steps 2–3 inherit its status.**  Combining
with (F):

```
|S_i| ≥ (ι(S)/ℓ_O)^{3/2}   for every orbit O.                      (*)
```

**Input 4 — the Lemma K analogues  [PROVEN, elementary; checked in `--lemK`
and in `_g_out.txt` PART D].**

> `ppmax(N)` = largest prime power dividing `N`; `ppmax_{p′}` = same, over
> primes `≠ p`.
>
> | family | `ppmax(|S|) ≤` | `ppmax_{p′}(|S|) ≤` |
> |---|---|---|
> | `U₃(q)` | `max(q³, 2(q+1)²)` | `2(q+1)²` |
> | `Sz(q)` | `q²+1  ( = ι(S) )` | `q²+1` |
> | `R(q)`  | `q³` | `q²−q+1` |

*Proofs.*
**`U₃`:** `|S| = q³(q−1)(q+1)²(q²−q+1)/e`.  `gcd(q−1,q+1) | 2`;
`q²−q+1 = q(q−1)+1` so `gcd(q−1, q²−q+1) = 1`; `q²−q+1 ≡ 3 mod (q+1)` so
`gcd(q+1, q²−q+1) | 3`, and when `3 | q+1` the `3`-part of `q²−q+1` is
exactly `3`, cancelled by `e = 3`.  So an odd `r ≠ p` has its whole `r`-part
inside one block, `≤ (q+1)²`; for `r = 2`, `q` odd, the `2`-part is
`|q−1|₂·|q+1|₂²` with `min(|q−1|₂,|q+1|₂) = 2`, hence `≤ 2(q+1)²`; the
`p`-part is `q³`.
**`Sz`:** `q−1` and `q²+1` are odd and `gcd(q−1,q²+1) = gcd(q−1,2) = 1`, so
the three blocks `q²`, `q−1`, `q²+1` are **pairwise coprime** and
`ppmax ≤ max(q², q−1, q²+1) = q²+1`.  *(This is the cleanest Lemma K of the
whole programme — as clean as `L₂`'s.)*
**`R`:** `q²−q+1` is odd, `≡ 3 mod (q+1)` but `3 ∤ q²−q+1` (as `3 | q`), and
`≡ 1 mod (q−1)`, so it is coprime to `(q−1)(q+1)`; the `2`-part is
`|q−1|₂|q+1|₂ ≤ 2(q+1)`; the `p`-part is `q³`.  ∎

`--lemK` finds **no violation** over 465 `U₃` targets (`q ≤ 3000`), 20 `Sz`
targets (`q ≤ 2.2·10¹²`), 13 `R` targets (`q ≤ 7.6·10¹²`); the bounds are
**attained** (ratio `1.0000`) at `U₃(3)`, `Sz(2⁴¹)`, `R(27)`, so none is
loose.  GAP cross-check to `q ≤ 3000` / `f ≤ 31` / `f ≤ 21`: no violations.

**Input 5 — Lemma K′  [PROVEN, elementary].**  *Every simple `G` of Lie type
satisfies `|G| < (|G|_p)³`*, `p` the defining characteristic.
*Proof.* Write `|G| = q₁^N·∏_i(q₁^{d_i} − ε_i)/g` with `N` the number of
positive roots and `D := Σ d_i`; then `|G| < q₁^{N+D}` and `D ≤ 2N` for every
type (checked exhaustively over all types of rank `≤ 12` in `--rank`:
*violations: NONE*, with `A₁` extremal at `D = 2N`).  ∎

---

## 4. Steps 2 and 3: at most one orbit, and the orbit has **length 1**

Standing: `T` Fitting-free, `|T| = |S|`, `D(T) ≅ D(S)`.

### 4.1 Step 2 — at most ONE socle orbit  [PROVEN, all `q`, modulo Lemma C]

By (*) with the convexity argument of the pilot (`ℓ ↦ (3ℓ/2)(log ι − log ℓ)`
is `≥ (3/2)log ι` on the admissible range `ℓ ≤ log|S|/log 60`), **every orbit
contributes at least `ι(S)^{3/2}` to `|Soc T|`.**  Two orbits would give
`|S| ≥ ι(S)³`, so it suffices that

```
ι(S)^3 > |S| :     (q^3+1)^3 > q^9 > |U_3(q)| ;
                   (q^2+1)^3 > q^6 > |Sz(q)|  ;
                   (q^3+1)^3 > q^9 > |R(q)|   .
```

All three are trivial (`|U₃(q)| < q⁸ + q⁵`, `|Sz(q)| < q⁵`, `|R(q)| < q⁷`).
`--uniform` verifies them **exactly, as integers**, on 2 327 `U₃` targets
(`q ≤ 20 000`), 30 `Sz` targets (`q ≤ 2.3·10¹⁸`), 20 `R` targets
(`q ≤ 3.6·10¹⁹`): **fails NEVER**, tightest ratios `ι³/|S| = 4.40` (`U₃(4)`),
`9.43` (`Sz(8)`), `757.1` (`R(27)`). ∎

### 4.2 Step 3 — the orbit has LENGTH 1  [PROVEN, all `q`; `U₃`: `q ≥ 8`]

Soc `T = S₁^ℓ`, one orbit; (*) gives `(ι(S)/ℓ)^{3ℓ/2} ≤ |S₁|^ℓ ≤ |S|`.  In
log-`q` terms with `|S| ≍ q^a`, `ι(S) ≍ q^b`, the condition to kill `ℓ` is
`(3ℓ/2)(b − log_q ℓ) > a`; the binding case is `ℓ = 2`, i.e.
`log_q 2 < (3b−a)/3`:

| family | `a` | `b` | `(3b−a)/3` | threshold |
|---|---|---|---|---|
| `U₃` | 8 | 3 | `1/3` | `q ≥ 9` |
| `Sz` | 5 | 2 | `1/3` | `q ≥ 9`, and `q = 8` by exact check |
| `R`  | 7 | 3 | `2/3` | `q ≥ 3`, so **all** `q ≥ 27` |

`ℓ ≥ 3` is far easier (`(9/2)(b − log_q 3) > a` in every family), and `ℓ ≥ 4`
is killed by `ℓ ≤ a·log q/log 60` against `ℓ > q^{...}` exactly as in the
pilot.  `--uniform` checks **every `ℓ` from 2 to `⌊log|S|/log 60⌋`, exactly**:

```
U3  : (iota/l)^{3l/2} > |S| fails only at (q,l) = (3,2), (4,2), (7,2)
Sz  : fails NEVER   ->   l = 1 for every q >= 8
Ree : fails NEVER   ->   l = 1 for every q >= 27
```

The three `U₃` residues `q = 3, 4, 7` are inside the census range, where the
census (even unfiltered) is empty. ∎

> **Consequence [PROVEN, modulo Lemma C].**  `Soc T = S₁` is a **single
> simple group** and `T` is **almost simple**:
> ```
>       c · |S₁| = |S| ,     c ≥ 2 ,     c | |Out(S₁)| .              (E)
> ```
> This is a strictly stronger reduction than the pilot achieved for `L₂`
> (where `ℓ ≤ 2` and an `S₁ × S₁` branch survived).

---

## 5. The residual equation (E), split by characteristic

### 5.1 Equal characteristic  [COMPUTED — but *exact* and *complete in `q₁`*]

If `S₁` is of Lie type over `F_{q₁}` in the **defining** characteristic `p` of
the target, then `|S₁|_p = q₁^N` divides `|S|_p`, so `q₁ = p^{f₁}` with
`f₁ ≤ 3f` (`U₃`, `R`) resp. `2f` (`Sz`).  **This branch needs no
factorisation of `|S|` at all** — only `|S|` itself — so it can be decided
outright, over *all* `f₁` in that range and all Lie types of rank `≤ 6`, at
`q` far beyond anything the census can reach.  `--eqchar`:

| family | targets | `q` up to | `(target, q₁)` pairs | positive control (`c = 1` self-solution found) | **hits** |
|---|---|---|---|---|---|
| `U₃` | 359 (`p ∈ {2,3,5,7,11,13}`, `f ≤ 60`) | `6.9·10⁶⁶` | 32 937 | PASS 359/359 | **0** |
| `Sz` | 60 (`f` odd `≤ 121`) | `2.7·10³⁶` | 7 440 | PASS 60/60 | **0** |
| `R`  | 60 (`f` odd `≤ 121`) | `5.4·10⁵⁷` | 11 160 | PASS 60/60 | **0** |

The positive control is essential and non-trivial: it demands that the same
enumeration **does** find `S₁ = S`, `c = 1`, for every target — so an empty
hit list is a real emptiness and not a broken loop.

*(A uniform proof of this branch is available in outline: Lemma R below gives
`D/N > (a−b_p)/b_p` where `b_p = log_q|S|_p`, i.e. `D/N > 5/3` for `U₃`,
`3/2` for `Sz`, `4/3` for `R` — a finite type list; and for `U₃` the only
surviving type is `A₁`, where substituting `q₁ = q³/c_p` into (E) forces
`q ≲ 36(log₂ q)²`, i.e. `q < 2000`.  We record the mechanism but the full
case analysis was not written out — see §7 (G4).)*

### 5.2 Cross characteristic, `S₁` of Lie type  [PROVEN for `U₃`, `R`]

If `p₁ ≠ p` then `|S₁|_{p₁} ≤ ppmax_{p′}(|S|)`, and by Lemma K′
`|S₁| < (|S₁|_{p₁})³ ≤ ppmax_{p′}³`.  Since `|S₁| = |S|/c` with
`c ≤ |Out(S₁)| ≤ 78·f₁ ≤ 78·log₂ ppmax_{p′}` (using `|Out| = d₁f₁g₁`,
`g₁ ≤ 6`, `d₁ ≤ 13` for rank `≤ 12`), the branch dies as soon as

```
c · ppmax_{p'}^3  <  |S| .
```

| family | `ppmax_{p′} ≲` | `|S| ≍` | verdict |
|---|---|---|---|
| `U₃(q)` | `2(q+1)²` | `q⁸` | `c·8q⁶ < q⁸` ⟸ `q² > 8c ≈ 10³ log q` — **contradiction for all `q ≥ 179`** (exact, `--rank`) |
| `R(q)` | `q²−q+1` | `q⁷` | `c·q⁶ < q⁷` ⟸ `q > c` — **contradiction for all `q ≥ 2187`** (exact, `--rank`) |
| `Sz(q)` | `q²+1` | `q⁵` | `c·q⁶ < q⁵` is **false**: `ppmax_{2′}³ ≍ q⁶ > |S| ≍ q⁵`. **No uniform kill.** |

So for `U₃` only `q < 179` and for `R` only `q ∈ {27, 243}` survive
cross-characteristically — all deep inside the census range.  **`Sz` gets no
uniform cross-characteristic kill**; that branch is `[COMPUTED]` only, and it
is `Sz`'s own honest gap (§7 (G3)).  The reason is structural and worth
naming: `Sz` is the family whose order is *farthest* from a cube of its
`p`-part (`|Sz(q)| ≍ (|S|_2)^{5/2}` vs `|L₂(q)| ≍ (|S|_p)³`), so Lemma K′
leaves the most room.

### 5.3 Lemma R (rank forcing), for the record

Same computation as the pilot's Step 4, in the `(N, D)` bookkeeping:
`q₁^N ≤ ppmax`, `q₁^{N+D} > |S|/c`, hence

```
D/N  >  log( |S| / (c·ppmax) ) / log(ppmax) ,
```

and `D/N → 1` as the rank grows, so the surviving type list is always
**finite**.  `--rank` prints it per family.  Honest assessment: with the
conservative `|Out|` cap this bound is **weak** for these targets — at the top
of the `Sz`/`R` ranges it still leaves ~10–25 types.  Lemma R is a rank
*bound*, not a kill; the work is done by §5.1, §5.2 and the census.  (`L₂`
always survives Lemma R — `D/N = 2` is the maximum — exactly as in the pilot.)

### 5.4 Alternating and sporadic `S₁`, and the direct scan of (E)

`--sub` solves (E) *for `q`* from `(S₁, c)`, by exact integer `k`-th roots
(`_iroot` selftested to the `10²⁰⁰` scale, `k = 3,5,7,8`, **no float
anywhere**; order inverters positive-controlled at seven `(fam,q)` points).
**Each row is therefore complete in `q` — it covers all `q`, not a range.**

```
socle candidates : 281 331   (Lie q1 <= 100 000, rank <= 6;
                              all A_m with |A_m| <= 10^80; all 27 sporadics + Tits)
U3  : 574 745 (S_1,c) pairs tested  ->  0 hits
Sz  : 574 745 (S_1,c) pairs tested  ->  0 hits
Ree : 574 745 (S_1,c) pairs tested  ->  0 hits
```

For alternating (`|Out| ≤ 4`) and sporadic (`|Out| ≤ 2`) `S₁` the candidate
list is **complete**, so those sub-branches are closed for **all `q`**.

**Negative control** (the constraint `c | |Out(S₁)|` dropped, `c ≤ 2000`,
candidates with `q₁ ≤ 2000`, rank `≤ 5`): `U₃` **16** order-only near-misses,
`Sz` **0**, `R` **0**.  The `U₃` list is instructive —

```
U3(3)  = 36·|L3(2)| = 12·|L2(8)|     U3(4)  = 8·|L2(25)| = 1040·|A5|
U3(5)  = 50·|A7| = 350·|A6|          U3(27) = 28·|R(27)| , U3(243) = 244·|R(243)|
```

— *every one* of them is killed by `c ∤ |Out(S₁)|` alone.  This control also
shows the order-inverters fire when a solution exists, so the all-empty main
scan is a tested emptiness.

---

## 6. The censuses

Phase 1 (order census) + Phase 2 (orbit-floor prefilter) per target, run with
`--raw` so that the **unfiltered** census is printed as well.

| family | targets | range | non-simple census | raw (unfiltered) census | positive control |
|---|---|---|---|---|---|
| `U₃(q)` | **5 216** | all prime powers `3 ≤ q ≤ 50 000` | EMPTY, 5216/5216 | **EMPTY** | PASS 5216/5216 |
| `Sz(q)` | **50** | `q = 2^f`, `f` odd `≤ 101`, `q ≤ 2.535·10³⁰` | EMPTY, 50/50 | **EMPTY** | PASS 50/50 |
| `R(q)` | **30** | `q = 3^f`, `f` odd `≤ 61`, `q ≤ 1.272·10²⁹` | EMPTY, 30/30 | **EMPTY** | PASS 30/30 |

**The single most striking datum in this note:** the *raw* census — order
arithmetic and the Fitting-free divisibility `c | ∏(|Out|^{ℓ}ℓ!)` alone, with
**no** orbit floor, **no** Lemma C — is empty at **every one of the 5 296
targets**.  In the `L₂` pilot the raw census produced one survivor
(`q = 64`, `A₅ × L₂(13)`, `c = 4`) that needed the floor.  Here the floor
killed **zero** candidates because there were none to kill.  Consequently:

> **Corollary.**  For every scanned `q`, Theorems U3-T / Sz-T / Ree-T hold
> **independently of Lemma C and of the orbit floor** — i.e. independently of
> debt (G1).  Only the *uniform-in-`q`* half (Steps 2–3, §4) uses Lemma C.

The mechanism is exactly the one the pilot predicted: the three/four nearly
coprime blocks of `|S|` (`q^k`, `q−1`, `q+1`, `q²∓q+1`), each of bounded
prime-power part (Lemma K), leave no room to write `|S|` as
`c·∏|S_i|^{ℓ_i}`.  The `Sz` order is the most rigid of all — three pairwise
**coprime** blocks.

The `Sz` and `R` families are *sparse* (`q = p^{odd}`), which is why the
census reaches `10²⁹`–`10³⁰` rather than `10⁴`–`10⁵`: the algebraic
factorisations
`q²+1 = (q+2^{(f+1)/2}+1)(q−2^{(f+1)/2}+1)` and
`q²−q+1 = (q+3^{(f+1)/2}+1)(q−3^{(f+1)/2}+1)`
are supplied to the factoriser (asserted exact in the script), so no Pollard
rho is needed on the Zsygmondy blocks.

---

## 7. Honest status

### Proven, uniform in `q`, no computation
* Lemma U3-ι, Sz-ι, Ree-ι (§1) — **over all subgroups**, so all three rows
  are **(AB)-free**.  No exceptions in any family (`U₃(5)` handled).
* §2, the simple–simple side (from the CFSG order theorem) — and the
  `Bₙ/Cₙ`-independence.
* Lemma K analogues and Lemma K′ (§3, Inputs 4–5).
* Step 2 (**at most one socle orbit**) and Step 3 (**orbit length 1**, §4) —
  *modulo Lemma C*; `U₃` residue `q ∈ {3,4,7}`.
* §5.2, the cross-characteristic Lie branch: **empty for `U₃(q)`, `q ≥ 179`**
  and **`R(q)`, `q ≥ 2187`** — *not* for `Sz`.
* §5.4, alternating and sporadic socles: **empty for all `q`, all three
  families**.

### Computed
The three censuses (§6, with per-target positive control); the equal-
characteristic branch (§5.1, exact and complete in `q₁`, with positive
control); the residual (E) scan over 281 331 socle candidates with a negative
control (§5.4); `--lemK` and `--rank` sweeps; the GAP spot-checks
(orders at **23** values of `q` across all three families; the explicit `ι`
witness `A = Z(Syl_p)` at **17** values (`U₃` and `Sz` only); the exact
lattice `ι` at **2**; minimal degrees from `Maxes` at **9**; Lemma K to
`q ≤ 3000` / `f ≤ 31` / `f ≤ 21`; the `|U₃(q)| = (q+1)|R(q)|` identity at
`q = 27, 243, 2187`).

### Open — the debts, stated plainly

* **(G1) Lemma C is not proven** — inherited verbatim from the pilot; it is
  `[COMPUTED]` (`v_task52` in progress) and Steps 2–3 rest on it.  **But
  note the Corollary in §6:** on the scanned ranges these three theorems do
  **not** depend on it, because the raw census is already empty.  So (G1)
  affects only the extrapolation to unscanned `q`.
* **(G2) The `Sz` cross-characteristic branch has no uniform proof.**  §5.2
  fails for `Sz` for a structural reason (`|Sz(q)| ≍ (|S|_2)^{5/2}`).  It is
  closed by the census to `q ≤ 2.5·10³⁰` and by `--sub` for all `q` with
  `q₁ ≤ 10⁵`, rank `≤ 6`.  This is `Sz`'s own gap and it is the *only* place
  where `Sz` is weaker than the other two.
* **(G3a) No GAP verification exists for the Ree family's `ι`.**  `ReeGroup`
  is a matrix group, `R(27)` has no stored `Maxes`, and the relevant
  `Normalizer` is out of reach.  Theorem Ree-T's `ι(R(q)) = q³+1` rests
  entirely on Ward's minimal-degree theorem plus Borel–Tits, with no
  independent machine check at any `q`.  The `U₃` and `Sz` rows do have one.
* **(G3) The `--sub` socle range is bounded** (`q₁ ≤ 10⁵`, Lie rank `≤ 6`).
  Larger `S₁` is excluded for `U₃` and `R` by §5.2 + §5.1; for `Sz` it is a
  scanned bound only.
* **(G4) The uniform proof of the equal-characteristic branch (§5.1) is
  sketched, not written.**  The mechanism (Lemma R type list, then the
  order equation forcing `q` bounded) is spelled out for `U₃`; the `Sz` and
  `R` case analyses were not carried out.  The branch is `[COMPUTED]` exactly
  and completely in `q₁` to `q ≤ 6.9·10⁶⁶` / `2.7·10³⁶` / `5.4·10⁵⁷`.

**Therefore the honest headline is:**

> **Theorems U3-T, Sz-T, Ree-T**
> `[PROVEN, unconditionally and independently of Lemma C, for all
> q ≤ 50 000 (U₃), q ≤ 2.5·10³⁰ (Sz), q ≤ 1.3·10²⁹ (R)]`;
> `[PROVEN for all q modulo (G1) Lemma C and the residual branches
> (G2)–(G4)]`.
> `U₃(q)`, `Sz(q)`, `R(q)` are `D`-rigid among all finite groups, on those
> terms.

Not `[PROVEN, all q]` for any of the three.  The gaps are named, and (G1) is
shared with every future Lie target.

---

## 8. Generalisation notes — what changed vs the `L₂` pilot

| step | `L₂` pilot | rank-1 Lie targets (this note) |
|---|---|---|
| target's subgroup theorem | **Dickson** — the pilot's one `L₂`-specific input | **not needed at all.**  Only the *minimal degree* `m(S)` is used, and it is a one-line literature citation per family (Suzuki / Ward / Cooperstein).  The pilot's "Dickson is the only `L₂`-specific input" worry does **not** generalise into a problem |
| `ι` | `q+1`, with **two exceptions** (`q = 5, 7`) | `q³+1`, `q²+1`, `q³+1`, **no exceptions** in any family.  `U₃(5)`'s exceptional minimal degree `50` does *not* become an `ι` exception (§1) |
| (AB)-freeness | gained | **confirmed to generalise**, exactly as the pilot predicted, and by the same proof shape |
| Lemma K | `≤ q+1`, ratio `ppmax/|S|^{1/3} = 1` | `Sz` is *equally* clean (three pairwise coprime blocks, `ppmax ≤ q²+1 = ι`); `U₃`, `R` slightly weaker but still tight (bounds attained) |
| orbit floor strength | `ι ≍ |S|^{1/3}`, enough for `ℓ ≤ 2` | `ι ≍ |S|^{3/8}, |S|^{2/5}, |S|^{3/7}` — enough for **`ℓ = 1`**, i.e. `T` almost simple.  **The pilot's floor-friendliness prediction is confirmed quantitatively** |
| census | one raw near-miss (`q = 64`) needing the floor | **zero** raw candidates anywhere; the floor is never used.  The order census alone carries the whole argument — which is what the pilot said would eventually be needed for `L_d`, `d ≥ 3`, and which turns out to be *already* true here |
| residual branches | `L₂(q₁)` socle with `ℓ = 1, 2`; equal-char proven, cross-char scanned | `ℓ = 1` only; equal-char decided **exactly and completely in `q₁`** by a factorisation-free method (new technique, §5.1 — it should be reused for every Lie target); cross-char **proven empty** for `U₃`, `R`; scanned for `Sz` |
| `Bₙ/Cₙ` residue | independent | independent |
| new obstruction found | — | **`|Sz(q)|` is the farthest of all rank-1 orders from `(|S|_p)³`**, which is exactly why Lemma K′ cannot close its cross-characteristic branch.  Any future family with `|S| ≪ (|S|_p)³` will have the same problem |
| new coincidence found | — | **`|U₃(q)| = (q+1)·|R(q)|` for every `q = 3^{2m+1}`** — the only order relation between target families in the programme so far; killed by the `c | |Out|` constraint |

**Refuted / do-not-re-attempt** (in addition to the pilot's list):
* *the loose "order window" test for the equal-characteristic branch* — an
  earlier version of `--eqchar` bounded `|S₁|` by `q₁^{N+D}` up to a factor
  `55.6` and was completely undecisive (it "survived" even `S₁ = S, c = 2`).
  Use exact orders; they are cheap because `q₁` is determined by `N` and `c_p`.
* *Lemma R as a kill* — with an honest `|Out(S₁)| ≤ 78 f₁` cap it leaves
  10–25 types at the top of the `Sz`/`R` ranges.  It is a rank bound only.

**Recommended next targets.**  `L₃(q)` and `U₄(q)`: the floor now gives
`ι ≍ |S|^{1/4}` resp. `|S|^{≈1/5}`, so Step 2 (one orbit) still passes but
Step 3 will no longer reach `ℓ = 1`, and the raw census will start producing
candidates.  The transferable machinery from this note is (i) the
factorisation-free **equal-characteristic** decision procedure (§5.1) and
(ii) the **`ppmax_{p′}³` cross-characteristic kill** (§5.2), which works
whenever `|S| > c·ppmax_{p′}³` — i.e. whenever the target's order is large
compared with the cube of its largest cross-characteristic prime power.

---

## 9. Citations

| # | input | tag |
|---|---|---|
| C1 | minimal degree `m(Sz(q)) = q²+1` | **[LIT: Suzuki 1962]** |
| C2 | minimal degree `m(²G₂(q)) = q³+1`, `q ≥ 27` | **[LIT: Ward 1966]** |
| C3 | minimal degree `m(U₃(q)) = q³+1`, `q ≥ 3`, `q ≠ 5`; `m(U₃(5)) = 50` | **[LIT: Cooperstein 1978; Kleidman–Liebeck Table 5.2.2]** |
| C4 | maximal subgroups of `U₃(5)` (used only for the `U₃(5)` step) | **[LIT: ATLAS / CTblLib `Maxes`]**, read off in `_g_out.txt` PART C2 |
| C5 | Borel–Tits `N_G(Z(U_P)) = P` (the `ι` witness) | **[LIT]** + GAP-verified directly, `_g_out.txt` PART B |
| C6 | CFSG (completeness of the simple-order enumeration) | **[LIT]** |
| C7 | CFSG order theorem: equal-order simple pairs are only `A₈/L₃(4)`, `Bₙ/Cₙ` | **[LIT: Artin; KLST]** |
| C8 | order transfer `D(T) ≅ D(S) ⟹ |T| = |S|` (Müller Satz 2.3.4) | **[LIT/formalised]** |
| C9 | conductor multiset is a `D`-ring invariant | **[Lean, kernel-checked]** |
| C10 | §4j–§4l reduction (order, non-solvability, Fitting-freeness are `D`-invariants) | **[PROVEN, this project]** |
| C11 | Lemma TR-1 / Lemma TO′-0 (target-agnostic) | **[PROVEN]** |
| C12 | Lemma F (`v_task36_pair_invariants.md`) | **[PROVEN]** |
| **(C)** | **Lemma C**, `|Out(G)|·ι(G) ≤ |G|^{2/3}` (`v_task52`) | **[COMPUTED + asymptotic]** — the shared debt (G1) |

---

## 10. Reproduce

```
python3 v_task53_rank1_twins.py --uniform                      # seconds
python3 v_task53_rank1_twins.py --lemK                         # ~2 min
python3 v_task53_rank1_twins.py --rank                         # ~1 min
python3 v_task53_rank1_twins.py --eqchar 121   > v_task53_eqchar_out.txt      # ~2 min
python3 v_task53_rank1_twins.py --census U3  50000 --raw > v_task53_census_U3_out.txt
python3 v_task53_rank1_twins.py --census Sz    101 --raw > v_task53_census_Sz_out.txt
python3 v_task53_rank1_twins.py --census Ree    61 --raw > v_task53_census_Ree_out.txt
python3 v_task53_rank1_twins.py --sub       100000      > v_task53_sub_out.txt
~/gap-4.16.0/gap -q -o 8g v_task53_rank1_twins.g > v_task53_rank1_twins_g_out.txt
```

All arithmetic is exact Python big-integer / GAP rational.  The only floats
are the display columns of the `--rank` threshold table; every hit, every
census entry and every root is verified by exact multiplication.
