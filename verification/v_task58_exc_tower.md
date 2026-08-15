# v_task58 — the **large exceptional tower**:
# **Theorems F4-T, E6-T, 2E6-T, E7-T, E8-T**

Date 2026-08-08.  **NOTES.md not edited.**
Pipeline: `L₂` (`v_task51`) → Lemma C (`v_task52`) → rank 1 (`v_task53`,
`v_task54`) → `L₃` (`v_task55`) → the rank-2 exceptionals (`v_task57`) →
**this note**, the five targets `F₄(q)`, `E₆(q)`, `²E₆(q)`, `E₇(q)`,
`E₈(q)`, all `q ≥ 2`.

| file | what it does |
|---|---|
| `v_task58_exc_tower.py` | PART 0 the **`E₇`/`E₈` erratum** in the shared `FAM` table; PART 1 invariants, cyclotomic spectra, **Lemma K-exc(tower)**; **PART 2 Lemma MO-EX** (the new multi-orbit lemma) + PART 2B the exact `(p,f)` residual sweep + PART 2C non-defining-characteristic socle factors; PART 3 cross-characteristic `ppmax³`; PART 4 Lemma EQ′ + EQ-EX; PART 4.5 the matched case in closed form; PART 4.6 the non-matched case; PART 4.0 the factorisation-free exact sweep; PART 5 alternating/sporadic + **the `E₈` sporadic-floor arithmetic**; **PART 8 the `13/6`-block identity hunt**; PART 6 the residual census |
| `v_task58_exc_tower_out.txt` | its output (702 lines) |
| `v_task58_exc_tower.g` / `_g_out.txt` | GAP: orders; **all four minimal parabolic indices re-derived as `|S|/(q^{dim U_P}|Levi|(q−1))` at `q ≤ 16`**; `Maxes` of `F₄(2)`; the identities `(I1)`–`(I5)` as exact rationals; the `E₈`/Monster arithmetic; the erratum |

All arithmetic exact (Python big integers / `Fraction`, GAP rationals).
Every enumerator is imported from `v_task50`–`v_task55`.

---

> ### Headline
>
> **Theorems F4-T, E6-T, 2E6-T, E7-T, E8-T [all PROVEN, unconditional,
> every prime power `q ≥ 2`].**
>
> There is no Fitting-free **non-simple** finite group `T` with `|T| = |S|`
> and `D(T) ≅ D(S)` for `S = F₄(q)`, `E₆(q)`, `²E₆(q)`, `E₇(q)`, `E₈(q)`.
> With the CFSG order theorem these five families are **`D`-rigid among all
> finite groups**.  No (AB), no `Bₙ/Cₙ` dependence.
>
> **Three things went differently from the forecast in `v_task57` §10.**
>
> 1. **An erratum, found and fixed.**  The shared `FAM` table carried
>    `ι(E₇(q))` and `ι(E₈(q))` **too small**, with `μ = 25, 51` instead of
>    the correct `μ = 27, 57`.  Corrected at source; Lemma C and every
>    verdict of `v_task52`/`v_task57` are unaffected (re-run and diffed).
> 2. **`v_task57` §10.1 was WRONG: `ℓ ≥ 2` is *not* vacuous.**  Lemma Q's
>    `ℓ ≤ 2` step needs `4b ≥ a`, and `4b < a` for `E₆`, `²E₆`, `E₇`, `E₈`
>    (`64 < 78`, `108 < 133`, `228 < 248`).  The multi-orbit branch is the
>    **hardest part of this note**, not the easiest.
> 3. **The replacement is new and reusable: Lemma MO-EX**, a *convexity*
>    argument on the exponents `D₁/N₁` which needs no violator list, no
>    Lemma B, and is uniform in `q`.  It is exactly the tool the classical
>    tower (`Sp`/`Ω`, `Bₙ`/`Cₙ`) will need.
>
> **The `a/N = 13/6` block did interact, as predicted — but benignly.**
> Nine matched cross-family pairs exist inside `{²F₄, F₄, E₆, ²E₆}`; every
> one of them has `deg_q |S| = deg_q |S₁|` **exactly**, so `c(q)` tends to a
> *constant* and the `c ∤ |Out|` rule of §4bd/§4be/§4bf gives **nothing**.
> Each had to be settled by an exact inequality.  The closest call in the
> whole programme: `|²E₆(q)|/|E₆(q)| → 3⁺`, and `3` divides
> `|Out(E₆(q))| = 6f`.  It dies on `3 < c < 4`.

---

## 0. PART 0 — the `E₇`/`E₈` erratum in the shared `FAM` table

`deg_q [S:P] = dim U_P` for every parabolic, and the minimal maximal
parabolic is the one with the largest Levi:

| `S` | node | Levi | `dim U_P = μ` | `ι(S) = [S:P]` |
|---|---|---|---|---|
| `F₄(q)` | `P₁` | `B₃` | 15 | `(q¹²−1)(q⁴+1)/(q−1)` |
| `E₆(q)` | `P₁` | `D₅` | 16 | `(q⁹−1)(q⁸+q⁴+1)/(q−1)` — `U_P` **abelian** |
| `²E₆(q)` | — | — | 16 | `(q⁹+1)(q⁸+q⁴+1)/(q+1)` |
| `E₇(q)` | `P₇` | `E₆` | **27** | `(q¹⁴−1)(q⁹+1)(q⁵+1)/(q−1)` — `U_P` **abelian** |
| `E₈(q)` | `P₈` | `E₇` | **57** | `(q³⁰−1)(q¹²+1)(q¹⁰+1)(q⁶+1)/(q−1)` |

`v_task52`'s `FAM` had
`ι(E₇) = (q¹⁴−1)(q⁹+1)(q⁵−1)/((q²−1)(q−1))` with `μ = 25`, and `ι(E₈)`
divided by a spurious `(q²−1)(q⁴−1)` with `μ = 51`.  The two wrong values
are smaller by the factors `(q⁵+1)(q²−1)/(q⁵−1)` and `(q²−1)(q⁴−1)`
(GAP `_g_out.txt` PART F: `99/31, 45` at `q = 2`).  A quick sanity check
that fixes the sign of the error: `[E₇:P₇]` must equal `|W(E₇)|/|W(E₆)| = 56`
at `q → 1`; the correct formula gives `14·2·2 = 56`, the old one `70`.

**Fixed at source** in `v_task52_lemmaC.py` (with an `ERRATUM` comment).
Impact, re-run and diffed:

* `v_task52`: only the two `2D−3μ` entries move (`191 → 185`, `343 → 325`);
  both still `> 0`, so **Lemma C is unchanged**.
* `v_task57`: PARTs 4 / 4.5 re-run — the surviving-family lists are
  **byte-identical** (`E₇`, `E₈` are killed by Lemma EQ′ with either value
  of `μ`).  **No verdict moves anywhere.**
* `v_task57` §10's forecast `3b − a = −58, −95` for `E₇`, `E₈` becomes
  `−52, −77`.

All four indices are re-derived independently in GAP at `q = 2,3,4,5,7,8,
9,11,13,16` as `|S|/(q^{dim U_P}·|Levi|_univ·(q−1))`, 40/40 matches
(`_g_out.txt` PART B).

---

## 1. The five targets

`q = p^f`.  `a = deg_q|S| = dim S`, `b = deg_q ι(S) = dim U_P`,
`N = deg_q|S|_p`.

| `S` | `|S|` | `|Out|` | `a` | `b` | `N` | `a/b` | `a/N` | `N/b` | `3b−a` |
|---|---|---|---|---|---|---|---|---|---|
| `F₄(q)` | `q²⁴(q¹²−1)(q⁸−1)(q⁶−1)(q²−1)` | `f` (`2f` if `p=2`) | 52 | 15 | 24 | `52/15` | `13/6` | `8/5` | `−7` |
| `E₆(q)` | `q³⁶(q¹²−1)(q⁹−1)(q⁸−1)(q⁶−1)(q⁵−1)(q²−1)/d`, `d=(3,q−1)` | `2df` | 78 | 16 | 36 | `39/8` | `13/6` | `9/4` | `−30` |
| `²E₆(q)` | same with `q⁹+1, q⁵+1`, `d=(3,q+1)` | `2df` | 78 | 16 | 36 | `39/8` | `13/6` | `9/4` | `−30` |
| `E₇(q)` | `q⁶³(q¹⁸−1)(q¹⁴−1)(q¹²−1)(q¹⁰−1)(q⁸−1)(q⁶−1)(q²−1)/(2,q−1)` | `df` | 133 | **27** | 63 | `133/27` | `19/9` | `7/3` | `−52` |
| `E₈(q)` | `q¹²⁰(q³⁰−1)(q²⁴−1)(q²⁰−1)(q¹⁸−1)(q¹⁴−1)(q¹²−1)(q⁸−1)(q²−1)` | `f` | 248 | **57** | 120 | `248/57` | `31/15` | `40/19` | `−77` |

`3b − a < 0` throughout, so the rank-1 Step 2 (`ι³ > |S|`) fails for all
five and the multi-orbit branch has to be handled head-on.

### 1.1 The `ι`-lemmas — over **all** subgroups, so (AB)-free

> **Lemma F4-ι / E6-ι / 2E6-ι / E7-ι / E8-ι [PROVEN, all `q ≥ 2`,
> no exceptions].**  `ι(S)` is the minimal parabolic index of the table
> above.

*Proof of `(≤)` — the witness.*  Two shapes, exactly as at rank 2:

* **`E₆`, `²E₆`, `E₇`: `A = O_p(P)` is ABELIAN** (the cominuscule nodes:
  the 27-dimensional node of `E₆`, the 56-dimensional node of `E₇`), of
  order `q¹⁶` resp. `q²⁷`, and `N_S(A) = P` by Borel–Tits.  This is the
  `C₂`-Siegel shape of `v_task57`.
* **`F₄`, `E₈`: no cominuscule node exists**, so no parabolic has abelian
  unipotent radical.  Take `A = X_θ = Z(U_{P₁})` resp. `Z(U_{P₈})`, the
  **long-root subgroup** `≅ (F_q,+)`; Borel–Tits gives `N_S(X_θ) = P`, the
  long-root parabolic, and for `F₄` and `E₈` the long-root parabolic **is**
  the minimal one (`P₁` for `F₄`, `P₈` for `E₈`).  This is the
  `G₂`/`³D₄`/`²F₄` shape.

*Proof of `(≥)`.*  `ind*(H) ≥ [S:N_S(H)] ≥ m(S)`, the minimal permutation
degree:

| `S` | `m(S)` | source |
|---|---|---|
| `F₄(q)` | `(q¹²−1)(q⁴+1)/(q−1)` | **[LIT: Vasilyev 1996/97; Kleidman–Liebeck 5.2.2]** |
| `E₆(q)` | `(q¹²−1)(q⁹−1)/((q⁴−1)(q−1))` | **[LIT: Vasilyev]** |
| `²E₆(q)` | `(q¹²−1)(q⁹+1)/((q⁴−1)(q+1))` | **[LIT: Vasilyev]** |
| `E₇(q)` | `(q¹⁴−1)(q⁹+1)(q⁵+1)/(q−1)` | **[LIT: Vasilyev]** |
| `E₈(q)` | `(q³⁰−1)(q¹²+1)(q¹⁰+1)(q⁶+1)/(q−1)` | **[LIT: Vasilyev]** |

> ### The `F₄(2^f)` trap, checked and **absent**
> The brief flagged the `p = 2` special isogeny of `F₄` (the `G₂(3)`-style
> trap, where `Z(Syl_p)` is too big and, worse, a maximal subgroup can have
> index *below* the parabolic index).  Both halves are clean here:
> * the witness is `X_θ`, not `Z(Syl_p)`, so the first half never bites;
> * GAP, `F₄(2)`, stored `Maxes` (14 classes): the smallest indices are
>   `69615, 69615, 69888, 69888, 3132675, …` — so
>   **`m(F₄(2)) = 69615 = (2¹²−1)(2⁴+1)/(2−1)`, the parabolic index exactly**.
>   The runner-up `69888` is `Sp₈(2)`, only `0.4 %` bigger.  No `G₂(4)`-style
>   defect.  (`E₆(2)`, `²E₆(2)`, `F₄(3)` have character tables but no stored
>   `Maxes`; `E₇(2)`, `E₈(2)` have no table.)

The proof quantifies over **all** `H`, so **(AB) is not a debt** for any of
the five targets.

---

## 2. PART 1 — the cyclotomic spectra and Lemma K-exc(tower)

The `p′`-part factors as `∏_e Φ_e(q)^{m_e}`; write
`M := max_e m_e·φ(e)` (the *cyclotomic strain exponent*).  Computed and
cross-checked against `∑ m_e φ(e) = a − N` (5/5 exact):

```
F4    Phi1^4 Phi2^4 Phi3^2 Phi4^2 Phi6^2 Phi8 Phi12                      M = 4
E6    Phi1^6 Phi2^4 Phi3^3 Phi4^2 Phi5 Phi6^2 Phi8 Phi9 Phi12            M = 6
2E6   Phi1^4 Phi2^6 Phi3^2 Phi4^2 Phi6^3 Phi8 Phi10 Phi12 Phi18          M = 6
E7    Phi1^7 Phi2^7 Phi3^3 Phi4^2 Phi5 Phi6^3 Phi7 Phi8 Phi9 Phi10
        Phi12 Phi14 Phi18                                                M = 7
E8    Phi1^8 Phi2^8 Phi3^4 Phi4^4 Phi5^2 Phi6^4 Phi7 Phi8^2 Phi9 Phi10^2
        Phi12^2 Phi14 Phi15 Phi18 Phi20 Phi24 Phi30                      M = 8
```

(The brief's `F₄: Φ₁²Φ₂²Φ₃Φ₄Φ₆Φ₈Φ₁₂` under-counts the multiplicities; the
correct ones are above, and they satisfy the degree identity.)

> **Lemma K-exc(tower) [PROVEN].** `ppmax_{p′}(|S|) ≤ P(q) := C(S)·(q+1)^M`
> with `C(S) = max(C₂, C_odd)`,
> `C₂ = 2^k ∏_terms |d|₂` and `C_odd = max_{r,e} r^{∑_{k≥1} m_{e r^k}}`.
>
> *Proof.* **Odd `r ≠ p`:** with `e = ord_r(q)`, `r | Φ_d(q)` only for
> `d = e` or `d = e r^k`, and in the latter case `r ‖ Φ_d(q)`
> (Lucas / LTE).  So the `r`-part is `≤ Φ_e(q)^{m_e}·r^{s}` with
> `s = ∑_{k≥1} m_{er^k}`; `Φ_e(q) < (q+1)^{φ(e)}` gives the `(q+1)^M`, and
> `e r^k` must itself be a block index, so `r ≤ e_max` and `r^s ≤ C_odd`.
> **`r = 2`, `q` odd:** every factor is `q^d ∓ 1` and
> `|q^d ∓ 1|₂ | |q^{2d}−1|₂ = |q²−1|₂|d|₂ ≤ 2(q+1)|d|₂` because
> `min(|q−1|₂,|q+1|₂) = 2`; multiply over the `k` terms and use `k ≤ M`.
> **`r = 2`, `q` even:** `2 = p`, excluded. ∎

Constants: `C = C₂ = 2048, 8192, 8192, 131072, 4194304` and
`C_odd = 9, 81, 81, 81, 243`.  **0 violations** over all admissible
`q ≤ 200` (`F₄`, `E₆`, `²E₆`), `q ≤ 100` (`E₇`), `q ≤ 60` (`E₈`), with the
`Φ_e(q)` factored individually.

---

## 3. **PART 2 — the multi-orbit branch, and why `v_task57` was wrong**

### 3.1 Lemma Q does not apply

`v_task55`'s Lemma Q reduces "`T` not almost simple" to the 56-element
Lemma-B violator list through the step: `ℓ ≤ 2` gives `|G|² ≤ |S|` and
`2ρ(G) ≥ ι(S)`, hence `|G| ≤ |S|^{1/2} ≤ ι(S)² ≤ 4ρ(G)²` — **which needs
`4b ≥ a`**.

| target | `4b` | `a` | `4b ≥ a` |
|---|---|---|---|
| `L₃` | 8 | 8 | yes (equality) |
| `S₄`, `G₂`, `³D₄`, `²F₄` | 12, 20, 36, 40 | 10, 14, 28, 26 | yes |
| **`F₄`** | **60** | **52** | **yes** |
| **`E₆`, `²E₆`** | **64** | **78** | **NO** |
| **`E₇`** | **108** | **133** | **NO** |
| **`E₈`** | **228** | **248** | **NO** |

So `v_task57` §10.1 ("`ℓ ≥ 2` will be vacuous for the whole `F₄`–`E₈`
tower", read off `q^b ≲ 2ρ_max`) is **false for four of the five targets**.
`ι(S)` is simply too small relative to `|S|` (`b/a = 16/78, 27/133,
57/248 < 1/4`) for the floor to squeeze a socle factor into a finite list.
`L₃`'s equality `4b = a` was the true boundary all along.

### 3.2 The replacement

> **Lemma MO-EX [PROVEN, this note].**  Let `T` be Fitting-free,
> `|T| = |S|`, `D(T) ≅ D(S)`, `T` **not** almost simple, with
> `Soc T = ∏_O G_O^{ℓ_O}` over the socle orbits, and suppose every `G_O` is
> of Lie type in the **defining** characteristic `p` (PART 2C disposes of
> the rest).  Put `r_O := D_O/N_O` and `u_O := ℓ_O N_O f_O`.  Then
>
> * **(i) floor + `p`-part.**  `∑_O ℓ_O (N_O/μ_O) ≤ N/b + E₁`.  Since
>   `N_O/μ_O ≥ 1` in **every** family and `∑_O ℓ_O ≥ 2`, each single family
>   obeys `N_O/μ_O ≤ N/b − 1 + E₁`.
> * **(ii) `p`-part EQUALITY (Lemma EQ-EX).**  `∑_O u_O = N f − δ`,
>   `δ = v_p(c)`.
> * **(iii) order.**  `a f − B ≤ ∑_O r_O u_O ≤ a f`.
>
> Combining (ii) and (iii):
> ```
>        ∑_O ( r_O − a/N ) u_O   ≤   B + (a/N)·δ .           (*)
> ```
> Each `u_O ≥ ℓ_O (N_O/μ_O)(b f − A_O)`, so with
> `W := min_config ∑_O ℓ_O (N_O/μ_O)(r_O − a/N)` over all admissible
> configurations,
> ```
>        W · ( b f − A )  ≤  B + (a/N)·δ ,
> ```
> an explicit threshold in `q`. ∎

The point is **(i)**: `N_O/μ_O ≥ 1` always, so the floor *caps the number
of socle factors* at `N/b` — and `N/b < 3` for all five targets, so there
are **at most two**.  Then (*) is a convexity statement: `a/N` would have
to be a weighted average of the `r_O`, and every admissible family has
`r_O ≥ a/N`.

Exact tables (no `q` anywhere):

| target | `N/b` | cap `= N/b − 1` | `a/N` | admissible families `N₁/μ₁ ≤ cap` | all `r ≥ a/N`? | `W` |
|---|---|---|---|---|---|---|
| `F₄` | `8/5` | `3/5` | `13/6` | **NONE** (`3/5 < 1 = min N/μ`) | — | — |
| `E₆` | `9/4` | `5/4` | `13/6` | `²F₄`(6/5,13/6), `G₂`(6/5,7/3), `L₂`(1,3), `R`(1,7/3), `Sz`(1,5/2), `U₃`(1,8/3), `U₄`(6/5,5/2) | **yes** | `1/6` (`²F₄×R`) |
| `²E₆` | `9/4` | `5/4` | `13/6` | same seven | **yes** | `1/6` |
| `E₇` | `7/3` | `4/3` | `19/9` | the seven `+ ³D₄`(4/3,7/3), `S₄`(4/3,5/2) | **yes** | `13/45` |
| `E₈` | `40/19` | `21/19` | `31/15` | `L₂`, `R`, `Sz`, `U₃` (all `N/μ = 1`) | **yes** | `8/15` (`R²`) |

* **`F₄` dies outright**: the cap `3/5` is below the *global* minimum
  `N/μ = 1`, so **no** family can carry a socle factor.  The multi-orbit
  branch is empty for every `q`, with no threshold and no exceptional list.
  (`F₄` is also the one target where the classical Lemma Q still works —
  two independent kills.)
* For `E₆`/`²E₆` the only **same-ratio** admissible family is `²F₄`
  (`r = 13/6 = a/N` exactly, contributing `0` to `W`), and an
  *all*-same-ratio configuration would need `2·6/5 = 12/5 > 9/4 = N/b`:
  **impossible**.  So at least one factor is strictly above `a/N`, giving
  `W = 1/6 > 0`.
* For `E₇` and `E₈` there is **no** same-ratio admissible family at all.

### 3.3 PART 2B — the exact residual sweep

The explicit constants: `ℓ_O ≤ 2`, `|Out(G_O)| = d_O f_O g_O ≤ 8 f_O`,
`f_O ≤ N f`, `c ≤ 2(8Nf)² = 128(Nf)²`, so

```
   A ≤ log_p(64 N f/κ_ι) ,  B ≤ log_p(2304) ,  δ ≤ log_p(128 (Nf)²) ,
```
and MO-EX closes at `(p,f)` as soon as `W(bf − A) > B + (a/N)δ`.  Closing
is monotone in `p` and in `f`, so the failing set is found exactly by a
binary search in `p` for each `f`.  It is **finite and small**, and each
pair is then swept exactly (every admissible family, every `ℓ_O ≤ 2`, every
`f_O`, with exact order divisibility, exact `c | ∏|Out|^{ℓ}∏ℓ!` and the
exact floor with the tabulated `ι`):

```
F4  : window VACUOUS
E6  : fails for 42979 pairs (p,f), p <= 514939, f <= 26 -- SURVIVORS 0
2E6 : fails for 43874 pairs (p,f), p <= 526483, f <= 27 -- SURVIVORS 0
E7  : fails for    47 pairs (p,f), p <=    127, f <=  8 -- SURVIVORS 0
E8  : fails for     3 pairs (p,f), p <=      3, f <=  2 -- SURVIVORS 0
```

**No factorisation of `|S|` is used anywhere in PART 2B.**

### 3.4 PART 2C — socle factors outside the defining characteristic

* **(a) cross characteristic.**  `|G|_{p₁} ≤ ppmax_{p′}(|S|) =: Q`, so
  `|G| < Q³` (Lemma K′) and `|Out(G)|ι(G) ≤ |G|^{2/3} < Q²` (Lemma C).
  The floor with `ℓ ≤ 2` needs `2Q² ≥ ι(S)`.  Exponents `2M` vs `b` are
  `8:15, 12:16, 12:16, 14:27, 16:57` — dead in every family.  With the
  crude `Q ≤ P(q)` the residue is `q ≤ 11 / 121 / 121 / 7 / 2`; with the
  **exact** `ppmax` it collapses to
  ```
  F4 {2,3}   E6 {2,3,4,5,9}   2E6 {2,3,4,7,8}   E7 {2,3}   E8 {}
  ```
  — censused exactly in PART 6 (below), 0 survivors.
* **(b) alternating.**  `ℓ·2·C(m,3) ≥ ι(S)` forces `m ≳ q^{b/3}` while
  `|G|² ≤ |S|` forces `m log m ≲ (a/2)log q`, i.e. `q^{b/3} ≲ a log q`
  with `b/3 ≥ 5`.  Exact check: **empty for every `q`, all five targets.**
* **(c) sporadic.**  Exact finite check (floor **and** `|G| | |S|`):
  **empty for every `q`, all five targets.**

---

## 4. PARTS 3–4.6 — the almost-simple branch

### 4.1 Cross characteristic (PART 3) — **empty for every `q`**

`|S| < c·P(q)³` with `c ≤ 6 n_max log₂P`.  Exponent margins `a − 3(M+1)`
are `37, 57, 57, 109, 221` — an order of magnitude more comfortable than
`L₃`'s `2`.  With the bound `P(q)` only `F₄(2)` and `²E₆(2)` survive; with
the **exact** `ppmax_{p′}(|S|)` the branch is **empty for every `q` in all
five families**.

### 4.2 Equal characteristic: Lemma EQ′ + Lemma EQ-EX (PART 4)

Both quoted from `v_task57` (target-agnostic, PROVEN).  Intersecting
`N₁/μ₁ ≤ N/b` with `D₁/N₁ = a/N` exactly:

| target | `a/N` | `N/b` | surviving socle families |
|---|---|---|---|
| `F₄` | `13/6` | `8/5` | `F₄(q₁)`, `²F₄(q₁)` |
| `E₆` | `13/6` | `9/4` | `F₄(q₁)`, `E₆(q₁)`, `²E₆(q₁)`, `²F₄(q₁)` |
| `²E₆` | `13/6` | `9/4` | `F₄(q₁)`, `E₆(q₁)`, `²E₆(q₁)`, `²F₄(q₁)` |
| `E₇` | `19/9` | `7/3` | **`E₇(q₁)` only** |
| `E₈` | `31/15` | `40/19` | **`E₈(q₁)` only** |

The **`13/6` block** is `{²F₄, F₄, E₆, ²E₆}` among the exceptional families
and `{L₁₂, U₁₂, S₁₂ = C₆, O₁₃ = B₆, O₁₄⁺ = D₇, O₁₄⁻ = ²D₇}` among the
classical ones — **every classical member is removed by Lemma EQ′**
(`N₁/μ₁ = 6, 3.14, 3.27, 3.27, 3.5, 3.5`, all `> 9/4`).  Likewise the
`19/9` block is `{E₇, L₁₈, U₁₈, S₁₈, O₁₉, O₂₀^±}` and the `31/15` block is
`{E₈, L₃₀, U₃₀, S₃₀, O₃₁, O₃₂^±}`; only the exceptional member survives.

### 4.3 The matched case (PART 4.5) — and why the old rule is useless here

> **Observation [PROVEN].**  If `S` and `G` lie in the same `a/N` block and
> `f₁` is matched (`N₁f₁ = Nf`), then
> `deg_q|S| − deg_q|G| = af − a₁f₁ = (a/N)Nf − (a₁/N₁)N₁f₁ = 0`.

So `c = |S|/|G|` tends to a **constant**.  This is qualitatively different
from every earlier identity in the programme
(`|U₃(q)| = (q+1)|R(q)|`, `|L₃(25)| = 7|L₄(5)|`,
`|S₄(q³)| = ((q²+1)/d)|³D₄(q)|`, `|G₂(q²)| = (q²+q+1)|²F₄(q)|`), where
`c(q)` was a positive **power** of `q` and the rule `c | |Out| = O(log q)`
killed it with a full power of `q` to spare.  **Here that rule gives
nothing** and each pair needs an exact inequality.

| target ← socle | matched `f₁/f` | `c(q)` | verdict |
|---|---|---|---|
| `F₄ ← F₄`, `E₆ ← E₆`, `²E₆ ← ²E₆`, `E₇ ← E₇`, `E₈ ← E₈` | `1` | `≡ 1` | `c ≥ 2` fails |
| `F₄ ← ²F₄` | `2` | — | `f₁ = 2f` even, `²F₄` needs `f₁` **odd**: **0 admissible pairs** |
| `E₆ ← F₄`, `²E₆ ← F₄` | `3/2` | see (I1), (I4) | `c < 1` resp. `< 1` |
| `E₆ ← ²F₄`, `²E₆ ← ²F₄` | `3` | see (I2), (I4) | `c < 8/7 < 2` |
| `E₆ ← ²E₆` | `1` | `< 1` | impossible |
| **`²E₆ ← E₆`** | `1` | see **(I3)** | `3 < c < 4`: **never an integer** |

Machine confirmation over all admissible `q ≤ 4000` (589 target parameters):
**`integer c ≥ 2` : NONE**, in every one of the nine pairs.

### 4.4 The non-matched case (PART 4.6) — Zsygmondy + counting

For a same-ratio pair put `δ = Nf − N₁f₁ ≥ 1`.
**(i) Zsygmondy**: a primitive prime `r` of `p^{Ef}−1` (`E` = the target's
largest degree, `Ef ≥ 12 > 6`) divides `|S|`, hence `|S₁|`, hence
`Ef | m f₁` for some `m` in the socle's degree multiset — pinning `f₁/f` to
a sparse set of rationals.  **(ii) Counting**:
`c = |S|/|S₁| ≥ κ p^{(a/N)δ}` against `c ≤ |Out(S₁)| ≤ 18(N/N₁)f`.
Every non-matched ratio allowed by (i) has `δ/f ≥ 12`, hence
`c ≥ κ·2^{26f}` at worst — **DEAD for all `f ≥ 1`**, in every one of the
13 non-matched rows.

### 4.5 PART 4.0 — the independent factorisation-free sweep

`q₁^{N₁} | q^N` bounds `f₁ ≤ Nf/N₁`, so the whole branch is a finite exact
test per target, over **every** family and rank `≤ 29`:

```
F4  : 5217 targets (q <= 50 000) , 137755 divisor pairs , control 5217/5217
E6  : 3320 targets (q <= 30 000) , 109917 divisor pairs , control 3320/3320
2E6 : 3320 targets (q <= 30 000) , 108275 divisor pairs , control 3320/3320
E7  : 1056 targets (q <=  8 000) ,  60450 divisor pairs , control 1056/1056
E8  :  466 targets (q <=  3 000) ,  46364 divisor pairs , control  466/466
HITS: NONE ;  order-only NEAR-MISSES (c <= |Out| dropped): NONE
```

---

## 5. PART 5 — alternating / sporadic socle, and the `E₈` floor arithmetic

`|S| = M` is inverted exactly for `q`, so each row is **complete in `q`**.
All 27 sporadics + Tits + `A_m` up to `10^300`, every `c | |Out(S₁)|`,
`c ≥ 2`: **177 `(S₁,c)` pairs per target, 0 hits, inverter self-check OK.**

### 5.1 The `E₈` sporadic floor, done honestly

The brief asked whether the Monster can reach the `E₈` floor.  It can:

```
iota(E8(2)) = 293 091 386 578 365 375        ~ 2.93e17
iota(M)     =  97 239 461 142 009 186 000    ~ 9.72e19   >  iota(E8(2))
```

So **the floor (F) alone does NOT exclude the Monster** — the floor is the
wrong test at `E₈`, exactly as the brief warned.  What actually happens:

* at `q = 2`: `|M|² / |E₈(2)| = 1.93·10³³`, so `|G|² ≤ |S|` fails by 33
  orders of magnitude;
* at `q = 3`: `|M|²/|E₈(3)| = 3.5·10⁻¹¹`, so the Monster **passes** both
  the floor and `|G|² ≤ |S|`.  Neither of the two "obvious" tests works;
* what kills it is **divisibility**: `|M| ∤ |E₈(q)|` for any `q`
  (GAP-verified at `q = 2, 3`), and the almost-simple equation
  `c|M| = |S|` with `c | |Out(M)| = 1` is absurd.

The complete sporadic disposal is therefore **PART 2C(c)** (multi-orbit:
exact floor **and** exact divisibility, empty for every `q` and every
target) together with **PART 5** (almost simple: order inversion, empty for
every `q`).  The Monster is also *not* a Lemma-B violator
(`|M| = 8.1·10⁵³ > 4ρ(M)² = 3.8·10⁴⁰`), so it never entered the `v_task55`
list either.

---

## 6. **PART 8 — the `13/6`-block identity hunt**

The nine matched cross-family pairs, `c(q) = |S|/|G|` over all admissible
`(q, q₁)`:

```
  S      G      f1/f    c(q) range                       verdict
  E6     F4     3/2     [0.317068, 0.999998]  (11 pairs) no integer c >= 2
  E6     2F4    3       [0.811013, 0.999939]  ( 4 pairs) no integer c >= 2
  E6     2E6    1       [0.332680, 3.000000]  (24 pairs) no integer c >= 2
  2E6    F4     3/2     [0.953071, 1.000000]  (11 pairs) no integer c >= 2
  2E6    2F4    3       [0.288905, 0.333313]  ( 4 pairs) no integer c >= 2
  2E6    E6     1       [0.333333, 3.005888]  (24 pairs) no integer c >= 2
```

Closed forms, all **[PROVEN]** by cancelling the order polynomials:

> **(I1)**  `|E₆(m²)| / |F₄(m³)| = (m¹⁶−1)(m¹²−1)(m¹⁰−1)(m⁴−1) /
> ( gcd(3,m²−1)·(m³⁶−1)(m⁶−1) )`.
> Both orders have `q`-degree `156` in `m`.  Numerator `< m⁴²`,
> denominator `> m⁴² − m³⁶ − m⁶`, so the quotient is `< (1−m⁻⁶)⁻¹ ≤ 8/7`,
> and in fact `< 1` for every `m ≥ 2`.  **`c < 2`: DEAD.**

> **(I2)**  `|E₆(q)| / |²F₄(q³)| = (q⁹−1)(q⁸−1)(q⁶−1)(q⁵−1)(q²−1) /
> ( gcd(3,q−1)·(q¹⁸+1)(q⁹+1)(q³−1) )`.
> Numerator `< q³⁰`; denominator (at `d = 1`) `> q³⁰ − q²⁷`; so
> `c < (1−q⁻³)⁻¹ ≤ 8/7 < 2`.  **DEAD.**

> **(I3)** — **the closest call in the programme.**
> `|²E₆(q)| / |E₆(q)| = [gcd(3,q−1)/gcd(3,q+1)]·(q⁹+1)(q⁵+1)/((q⁹−1)(q⁵−1))`.
> `3 | q−1` and `3 | q+1` are mutually exclusive, so the bracket is
> `1`, `3` or `1/3`.  In the interesting case `q ≡ 1 (mod 3)` the bracket is
> `3` and, with `A = q⁹−1`, `B = q⁵−1`,
> ```
>        c  =  3 (1 + 2/A)(1 + 2/B)  ,      so      3 < c < 4
> ```
> for every `q ≥ 4` (the smallest `q ≡ 1 mod 3`).
> **`c` is never an integer.**  Observed: `c = 3.005888…` at `q = 4`,
> `3.0000000000…` at `q = 121`.
> **Had `c` been exactly `3`, it would have divided `|Out(E₆(q))| = 6f` and
> produced a genuine twin candidate.**  It is killed by a *strict
> inequality*, not by an arithmetic obstruction — the first time in this
> programme that the `c | |Out|` rule was not the thing that closed a row.
> (The reverse direction `|E₆(q)|/|²E₆(q)| < 1` is impossible outright.)

> **(I4)**  `|²E₆(m²)|/|F₄(m³)|` and `|²E₆(q)|/|²F₄(q³)|`: same shape,
> both `< 2` by the same cancellation.  **DEAD.**

> **(I5)**  `|F₄(q²)| = c·|²F₄(q)|` would need `f₁ = 2f` **even**, but
> `²F₄` exists only for `f₁` **odd**: no admissible pair exists at all.
> Contrast Identity B of `v_task57`, `|G₂(q²)| = (q²+q+1)|²F₄(q)|`, which
> *does* exist precisely because `G₂` and `²F₄` are **not** in the same
> `a/N` block, so their degrees differ and `c` is a polynomial.

**Verdict on the block: four near-identities (`c → 1/d` or `c → 3⁺`) and
not one exact one.**  The block interacted exactly as `v_task57` §10.4
predicted; the interaction is benign, but only because of `(I3)`'s strict
inequality.

> ### The refined `c ∤ |Out|` pattern
> `v_task57` named the rule "exact inter-family order identities
> `|S| = c(q)|G|` with `c(q)` a polynomial always die on `c | |Out|`".
> This note adds the **complementary regime**: inside a single `a/N` block
> the matched pairs have **equal degree**, `c(q) → const`, and the rule is
> *silent*.  The correct general statement is:
> * **different `a/N` blocks ⟹ `c(q)` is a positive power of `q` ⟹ dies on
>   `c | |Out|`;**
> * **same `a/N` block ⟹ `c(q)` is bounded ⟹ must be settled by an exact
>   inequality, and can come arbitrarily close to an admissible integer.**
> The second regime is new here and is a warning label for the classical
> tower, where the blocks are much more populous (`13/6` alone contains
> `L₁₂, U₁₂, S₁₂, O₁₃, O₁₄^±`).

A broad order-coincidence sweep (`|S| = c|G|`, `2 ≤ c ≤ 10⁴`, over the full
Lie/alternating/sporadic list, `q ≤ 9`) turns up **no further identities**;
the only `c = 1` rows are the isomorphism controls.

---

## 7. PART 6 — the residual census

The **only** residue of the entire note is the multi-orbit
cross-characteristic window of PART 2C(a):

| target | residual `q` | RAW survivors | after the orbit floor | positive-control failures |
|---|---|---|---|---|
| `F₄` | `{2, 3}` | 0 | 0 | 0/2 |
| `E₆` | `{2, 3, 4, 5, 9}` | 0 | 0 | 0/5 |
| `²E₆` | `{2, 3, 4, 7, 8}` | 0 | 0 | 0/5 |
| `E₇` | `{2, 3}` | 0 | 0 | 0/2 |
| `E₈` | — | *no census needed* | — | — |

---

## 8. Status ledger

| step | `F₄` | `E₆` | `²E₆` | `E₇` | `E₈` |
|---|---|---|---|---|---|
| `ι` over **all** subgroups, (AB)-free | **[PROVEN]** | ” | ” | ” | ” |
| Lemma K-exc(tower) | **[PROVEN]**, 0 violations | ” | ” | ” | ” |
| rank-1 Step 2 (`ι³ > |S|`) | fails | fails | fails | fails | fails |
| classical Lemma Q (`4b ≥ a`) | **holds** | **FAILS** | **FAILS** | **FAILS** | **FAILS** |
| **Lemma MO-EX** ⟹ almost simple | **[PROVEN]** all `q`, vacuous | **[PROVEN]** all `q` | ” | ” | ” |
| multi-orbit residual sweep | *vacuous* | **[COMPUTED]** 42 979 `(p,f)` | 43 874 | 47 | 3 |
| non-defining-char socle factors | **[PROVEN]** | ” | ” | ” | ” |
| cross characteristic, almost simple | **[PROVEN]** all `q` | ” | ” | ” | ” |
| equal characteristic, uniform | **[PROVEN]** all `q` | ” | ” | ” | ” |
| equal characteristic, exact sweep | `q ≤ 5·10⁴` | `q ≤ 3·10⁴` | `q ≤ 3·10⁴` | `q ≤ 8·10³` | `q ≤ 3·10³` |
| alternating / sporadic socle | **[PROVEN]**, complete in `q` | ” | ” | ” | ” |
| residual census | `q ∈ {2,3}`, 0 | `{2,3,4,5,9}`, 0 | `{2,3,4,7,8}`, 0 | `{2,3}`, 0 | *not needed* |
| simple–simple side | **[LIT: CFSG order theorem]** | ” | ” | ” | ” |

**Every finite window produced by a uniform argument lies strictly inside a
range that has been exhausted exactly.**  Hence Theorems F4-T, E6-T, 2E6-T,
E7-T, E8-T as stated.

### Honest gaps

1. **(H1) The lower half of every `ι` is literature.**  `m(F₄(q))`,
   `m(E₆(q))`, `m(²E₆(q))`, `m(E₇(q))`, `m(E₈(q))` are quoted from
   Vasilyev.  Machine-confirmed only at `F₄(2)` (stored `Maxes`, and the
   confirmation is exact: `m = 69615` = parabolic index).  Same epistemic
   status as every `ι` row since `U₃`.
2. **(H2) `E₆(q)`, `²E₆(q)`, `E₇(q)`, `E₈(q)` have no computational
   verification at any `q`.**  `E₆(2)` and `²E₆(2)` have character tables
   but no stored `Maxes`; `E₇(2)`, `E₈(2)` have no table.  The upper halves
   of the `ι`-lemmas rest on Borel–Tits alone.  Mitigating: the four rows
   are also the most comfortable (margins `≥ 57` in the cross-characteristic
   exponent, `W > 0` with slack in MO-EX).
3. **(H3) Lemma MO-EX's constants.**  `A`, `B`, `δ` are bounded
   generously (`|Out| ≤ 8f_O`, `f_O ≤ Nf`, `c ≤ 128(Nf)²`).  Sharper
   family-specific constants would shrink the `E₆`/`²E₆` residual window
   from `~5·10⁵` to `~5·10³`; the window was swept exactly as it stands, so
   nothing rests on this, but a future note should tighten it before
   applying MO-EX to the classical tower where `b/a` is even smaller.
4. **(H4) `ῑ` in the orbit floor** is the parabolic upper bound for Lie
   factors and the exact `v_task39`/`v_task50` table for sporadics —
   inherited from `v_task55` (H3).
5. **(H5) `|Out|` values** are quoted from Kleidman–Liebeck; the only GAP
   confirmations available are at `F₄(2)`, `E₆(2)`, `²E₆(2)`.
6. **(H6) The `E₇`/`E₈` erratum** was live in `v_task52` and in every
   note that imports `FAM`.  Fixed at source and **every downstream output
   audited**:
   * `v_task52_lemmaC_out.txt` — two `2D−3μ` entries move
     (`191→185`, `343→325`), both still `> 0`; **regenerated**.
   * `v_task54_rank1_gaps_out.txt` — the `E₇`/`E₈` rows of the `D`–`μ`
     table move (`μ = 25,51 → 27,57`; `N−μ = 38,69 → 36,63`) and Lemma W's
     `E₇` threshold moves from `q > 10` to `q > 13`, well inside the
     exhausted scan; **regenerated**, verdicts unchanged.
   * `v_task55`, `v_task57` outputs — no `E₇`/`E₈` occurrence at all;
     `v_task57` PARTs 4/4.5 re-run, surviving-family lists identical.
   * `v_task56` (the `L`/`U` towers) already carries `μ = 27, 57`.
   * `v_task24`–`v_task42` outputs — no `E₇`/`E₈` occurrence.
   No verdict anywhere in the programme moves.

---

## 9. What remains: the final map

Settled so far: `A_n` (`v_task47`–`49`), all 27 sporadics (`v_task50`),
`L₂` (`v_task51`), `U₃`/`Sz`/`R` (`v_task53`/`54`), `L₃` (`v_task55`),
`L_d`/`U_d` for `d ≥ 4` (`v_task56`, with the `d > 10` residue named
there), `S₄`/`G₂`/`³D₄`/`²F₄` (`v_task57`), and `F₄`/`E₆`/`²E₆`/`E₇`/`E₈`
(this note).  **The exceptional tower is complete.**

**What is left is the orthogonal/symplectic block:**

| block | families | the strain point |
|---|---|---|
| `Bₙ`/`Cₙ` | `O_{2n+1}(q)`, `Sp_{2n}(q)`, `n ≥ 3` | `a/N = 2 + 1/n`; and **the parked `Bₙ ≅ Cₙ` order coincidence** — the one place where the CFSG order theorem does *not* separate two simple groups, so the simple–simple side is a genuine open item, not a citation |
| `Dₙ`/`²Dₙ` | `O_{2n}^±(q)`, `n ≥ 4` | `a/N = (2n−1)/(n−1)`; `|Out|` is large (`6` at `D₄`), so `c \| |Out|` is at its weakest |
| residue | `L_d`/`U_d`, `d > 10` | the finite exact confirmation of `v_task56` §8 (H4) |

Four concrete carry-overs from this note:

1. **`4b ≥ a` is the exact boundary for the classical Lemma Q**, and it is
   crossed early: for `L_d`, `4b = 4(d−1)` vs `a = d²−1`, equality at
   `d = 3` and failure from `d = 4` on; for `C_n`, `4b = 4(2n−1)` vs
   `a = 2n²+n`, failure from `n = 4` on (`28 < 36`).  So **Lemma Q is dead
   for `Sp_{2n}`/`Ω_{2n+1}` with `n ≥ 4` and for `Ω^±_{2n}` with `n ≥ 4`**
   (`D₄`: `4·6 = 24 < 28`).
2. **Lemma MO-EX is the replacement**, and its two checks must be redone
   per family: (i) the cap `N/b − 1` admits more and more families as the
   rank grows (`N/b = n²/(2n−1) → n/2` for `C_n`), so the admissible list
   will not stay at nine entries; (ii) the weight
   `W = min ∑ ℓ_O(N_O/μ_O)(D_O/N_O − a/N)` must stay `> 0`.  **`W > 0` may
   genuinely fail at high rank** — `a/N → 2` for `C_n` and `→ 2` for
   `D_n`, while `min D/N` over all families is `2` in the limit too.  If it
   fails, the fallback is the exact `(p,f)` sweep, which is cheap (it ran
   here in seconds for 87 000 pairs).
3. **The bounded-`c` regime of §6 will be common in the classical tower**,
   because the `a/N` blocks there are populous: `13/6` already contains
   `L₁₂, U₁₂, S₁₂, O₁₃, O₁₄^±` alongside the four exceptional members, and
   every same-ratio matched pair inside a block has *equal degree*, hence
   bounded `c`, hence must be settled by an exact inequality.  The `(I3)`
   near-miss (`3 < c < 4` against `c | 6f`) shows how thin the margin can
   be.  **Do not expect `c ∤ |Out|` to close the classical tower.**
4. **`Bₙ` vs `Cₙ` is untouched here** and remains the only simple–simple
   item in the whole programme.

## 10. Citations

| # | input | tag |
|---|---|---|
| C1 | minimal permutation degrees of `F₄`, `E₆`, `²E₆`, `E₇`, `E₈` | **[LIT: Vasilyev 1996/97; Kleidman–Liebeck Table 5.2.2]** |
| C2 | Borel–Tits `N_G(O_p(P)) = P`, `N_G(Z(U_P)) = P`; cominuscule nodes of `E₆`, `E₇` have abelian unipotent radical | **[LIT]** + GAP at `F₄(2)` |
| C3 | Zsygmondy's theorem | **[LIT: Zsygmondy 1892]** |
| C4 | orders, `|Out| = dfg`, parabolic indices, Levi decompositions | **[LIT: Kleidman–Liebeck; ATLAS]**, GAP-checked |
| C5 | maximal subgroups of `F₄(2)` (completeness) | **[LIT: ATLAS / CTblLib `Maxes`]** |
| C6 | CFSG order theorem (`{A₈,L₃(4)}`, `{Bₙ,Cₙ}` `n ≥ 3` only) | **[LIT: Artin; KLST]** |
| C7 | Lemma C `|Out|ι ≤ |G|^{2/3}` | **[PROVEN, v_task52 — re-verified with the corrected `E₇`/`E₈` rows]** |
| C8 | Lemma TO′-0 + Lemma F (the orbit floor) | **[PROVEN, v_task42/v_task36]** |
| C9 | Lemma EQ′, Lemma EQ-EX | **[PROVEN, v_task57]** |
| C10 | order transfer `D(T) ≅ D(S) ⟹ |T| = |S|` | **[LIT/formalised: Müller Satz 2.3.4]** |
| C11 | §4j–§4l reduction (Fitting-freeness a `D`-invariant) | **[PROVEN, this project]** |
| C12 | **Lemma MO-EX** | **[PROVEN, this note]** |

---

## 11. Reproduce

```
python3 -u v_task58_exc_tower.py                    > v_task58_exc_tower_out.txt    # ~5 min
~/gap-4.16.0/gap -q -o 8g v_task58_exc_tower.g      > v_task58_exc_tower_g_out.txt  # ~1 min
```

Individual parts: `python3 v_task58_exc_tower.py 0 | 1 | 2 | 3 | 4 | 45 |
46 | 40 | 5 | 8 | 6`.
