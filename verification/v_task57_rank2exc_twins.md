# v_task57 — the remaining **rank-2 / small-rank exceptional** block:
# **Theorems S4-T, G2-T, 3D4-T, 2F4-T**

Date 2026-08-08.  **NOTES.md not edited.**
Pipeline: `L₂` pilot (`v_task51`) → Lemma C (`v_task52`) → rank 1
(`v_task53`, `v_task54`) → `L₃` (`v_task55`) → **this note**, the four
targets `S₄(q) = PSp₄(q) = C₂(q)`, `G₂(q)`, `³D₄(q)`, `²F₄(q)`.

| file | what it does |
|---|---|
| `v_task57_rank2exc_twins.py` | PART 1 invariants + **Lemma K-exc** + the strain diagnostic; PART 2 **Lemma Q** (reusing the *same* 56-element Lemma-B violator list of `v_task55`); PART 3 the cross-characteristic `ppmax³` kill; PART 4 **Lemma EQ′** + the `D/N` test; **PART 4.5 Lemma EQ-EX** (the `p`-part is an *equality*) and the same-ratio residual families in closed form; **PART 4.6** the Zsygmondy + counting kill of every non-matched `f₁`; PART 4.0 the factorisation-free exact equal-characteristic sweep; PART 5 alternating/sporadic socle, complete in `q`; PART 6 the residual census; **PART 7** the `S₄(3)` defect and the coincidence hunt |
| `v_task57_rank2exc_twins_out.txt` | its output |
| `v_task57_rank2exc_twins.g` / `_g_out.txt` | GAP: orders; the **`S₄(3)` defect** proved over the lattice (`I(S) = {27, 40, 45}`); the `ι` witnesses at `S₄(4,5,7)`, `G₂(3)`, `³D₄(2)`; the `Z(Syl_p)` trap; minimal degrees from stored `Maxes`; the `G₂(3)`/`G₂(4)` exceptional-minimal-degree analysis; the coincidence controls |

All arithmetic exact (Python big integers / `Fraction`, GAP rationals).
Every enumerator is imported from `v_task50`–`v_task55`.

---

> ### Headline
>
> **Theorem S4-T [PROVEN, all prime powers `q ≥ 3`, unconditional].**
> **Theorem G2-T [PROVEN, all prime powers `q ≥ 3`, unconditional].**
> **Theorem 3D4-T [PROVEN, all prime powers `q ≥ 2`, unconditional].**
> **Theorem 2F4-T [PROVEN, all `q = 2^{2m+1} ≥ 8`, unconditional].**
>
> There is no Fitting-free **non-simple** finite group `T` with `|T| = |S|`
> and `D(T) ≅ D(S)`, for `S = S₄(q)`, `G₂(q)`, `³D₄(q)`, `²F₄(q)`.  With the
> CFSG order theorem (order-uniqueness among simple groups; `Bₙ ≠ Cₙ` is a
> rank `≥ 3` issue and does **not** touch `C₂ = B₂`), these four families are
> **`D`-rigid among all finite groups**.
> Excluded degenerate parameters are covered elsewhere: `S₄(2)′ ≅ A₆`
> (§4l/AT), `G₂(2)′ ≅ U₃(3)` (**U3-T**), `²F₄(2)′` = Tits (`v_task50`).
>
> No dependence on **(AB)**, none on the `Bₙ/Cₙ` residue, none on Lemma B
> as a hypothesis.
>
> **Three of the four targets are strictly *easier* than `L₃`.**  For
> `G₂`, `³D₄`, `²F₄` the multi-orbit window of Lemma Q is **empty for every
> `q`**, and for `G₂` and `²F₄` even the rank-1 Step 2 (`ι³ > |S|`) is back.
> `²F₄` needs **no census at all** — like `Sz`, it is census-free.
>
> **Two new inter-family order identities**, both exact for all `q`
> (§7): `|S₄(q³)| = ((q²+1)/gcd(2,q−1))·|³D₄(q)|` and
> `|G₂(q²)| = (q²+q+1)·|²F₄(q)|`.

---

## 0. The four targets

`q = p^f`.  `a := deg_q |S|`, `b := deg_q ι(S)`, `N := deg_q |S|_p`.

| `S` | `|S|` | cyclotomic shape | `ι(S)` | `|Out|` | `a` | `b` | `N` |
|---|---|---|---|---|---|---|---|
| `S₄(q)` | `q⁴(q²−1)(q⁴−1)/d`, `d = gcd(2,q−1)` | `q⁴ Φ₁²Φ₂²Φ₄/d` | `(q+1)(q²+1)` **[q ≥ 4]**, `27` at `q = 3` | `2f` | 10 | 3 | 4 |
| `G₂(q)` | `q⁶(q⁶−1)(q²−1)` | `q⁶ Φ₁²Φ₂²Φ₃Φ₆` | `(q⁶−1)/(q−1)` | `f` (`2f` if `p = 3`) | 14 | 5 | 6 |
| `³D₄(q)` | `q¹²(q⁸+q⁴+1)(q⁶−1)(q²−1)` | `q¹² Φ₁²Φ₂²Φ₃²Φ₆²Φ₁₂` | `(q⁸+q⁴+1)(q+1)` | `3f` | 28 | 9 | 12 |
| `²F₄(q)` | `q¹²(q⁶+1)(q⁴−1)(q³+1)(q−1)` | `q¹² Φ₁²Φ₂²Φ₄²Φ₆Φ₁₂` | `(q⁶+1)(q³+1)(q+1)` | `f` | 26 | 10 | 12 |

Orders GAP-verified against the formulas at `S₄(3,4,5,7,8,9)`,
`G₂(3,4,5)`, `³D₄(2,3)`, `²F₄(2)` (`_g_out.txt` PART A).

Note `B₂ = C₂` as Dynkin diagrams, so `S₄(q) = PSp₄(q) = Ω₅(q)` is a
**single** group: the parked `Bₙ/Cₙ` simple–simple separation is a rank
`≥ 3` question and is not touched here.

---

## 1. The `ι`-lemmas — over **all** subgroups, so (AB)-free

> **Lemma S4-ι [PROVEN, all `q ≥ 3`, one exception, which is exact].**
> `ι(S₄(q)) = (q+1)(q²+1)` for every `q ≥ 4`, and **`ι(S₄(3)) = 27`**.
>
> **Lemma G2-ι [PROVEN, all `q ≥ 3`, no exceptions].**
> `ι(G₂(q)) = (q⁶−1)/(q−1)`.
>
> **Lemma 3D4-ι [PROVEN, all `q`].** `ι(³D₄(q)) = (q⁸+q⁴+1)(q+1)`.
>
> **Lemma 2F4-ι [PROVEN, all `q = 2^{2m+1} ≥ 8`].**
> `ι(²F₄(q)) = (q⁶+1)(q³+1)(q+1)`.

*Proof of `(≤)` — the witness.*  Two shapes occur, and getting the shape
right is the whole content:

* **`C₂` (and only `C₂` among the four): `A = O_p(P)` for the Siegel
  parabolic** — the stabiliser of a totally isotropic 2-space.  Its
  unipotent radical is the group of symmetric `2×2` matrices, **elementary
  abelian of order `q³`**, with `N_S(A) = P` of index `(q+1)(q²+1)`
  (Borel–Tits).
* **`G₂`, `³D₄`, `²F₄`: `A = Z(U_P) = X_θ` the long-root subgroup** of the
  minimal-index maximal parabolic, `A ≅ (F_q,+)` abelian, `N_S(A) = P`
  (Borel–Tits `N_G(Z(U_P)) = P`).  These groups have **no** abelian
  unipotent radical, so the `C₂` witness has no analogue.

*Proof of `(≥)`.*  For `1 ≠ H ≤ S` with `N_S(H) ≠ S`,
`ind*(H) ≥ [S : N_S(H)] ≥ m(S)`, the minimal permutation degree, and

| `S` | `m(S)` | source |
|---|---|---|
| `S₄(q)`, `q ≥ 4` | `(q⁴−1)/(q−1)` | **[LIT: Cooperstein 1978; Kleidman–Liebeck Table 5.2.2]** |
| `S₄(3)` | **27** | the `U₄(2)` isomorphism; GAP |
| `G₂(q)`, `q ≥ 5` | `(q⁶−1)/(q−1)` | **[LIT: Cooperstein; Vasilyev]** |
| `G₂(3)` / `G₂(4)` | **351** / **416** | GAP `Maxes` — *smaller* than the parabolic index |
| `³D₄(q)` | `(q⁸+q⁴+1)(q+1)` | **[LIT: Kleidman 1988, maximal subgroups of `³D₄(q)`]** |
| `²F₄(q)`, `q ≥ 8` | `(q⁶+1)(q³+1)(q+1)` | **[LIT: Malle 1991, maximal subgroups of `²F₄(q)`]** |

The two `G₂` rows where `m(S) < ` witness need the extra step, and it is
clean:

> **The `G₂(3)`/`G₂(4)` refinement [PROVEN].**  `N = N_S(A)` with
> `1 ≠ A` abelian contains a **nontrivial abelian normal subgroup**, so `N`
> is neither simple nor almost simple with simple socle only.
> At `G₂(4)` the only maximal subgroups of index `< 1365` are the two
> classes of `J₂` (index 416) — and `J₂` is **simple**, hence `≠ N_S(A)`.
> Any proper `N ≤ J₂` has `[S:N] ≥ 416·m(J₂) = 416·100 = 41 600 > 1365`.
> Hence `ι(G₂(4)) = 1365`.  Same at `G₂(3)`: the only maximal subgroups of
> index `< 364` are the two classes of `U₃(3).2` (index 351), whose unique
> minimal normal subgroup `U₃(3)` is simple, so again `≠ N_S(A)`, and
> `351·m(U₃(3).2) ≥ 351·28 ≫ 364`.  Hence `ι(G₂(3)) = 364`.
> (Full maximal-index lists in `_g_out.txt` PART E.)

The proof quantifies over **all** `H`, so **(AB) is not a debt** for any of
the four targets.

### 1.1 GAP verification of the witnesses

`_g_out.txt` PARTS C, C2, D, F:

| check | result |
|---|---|
| `S₄(4)`: abelian normal `A ≤ Syl₂`, `|A| = q³` | 2 classes, `[S:N_S(A)] = 85 = (q+1)(q²+1)` ✓ |
| `S₄(5)` | 1 class, `[S:N_S(A)] = 156` ✓ |
| `S₄(7)` | 1 class, `[S:N_S(A)] = 400` ✓ |
| `G₂(3)`: min over abelian normal `A ≤ Syl₃` | `364` ✓ (index set `{364, 1456, 2912}`) |
| `³D₄(2)`: same | `819` ✓ (index set `{819, 2457, 17199, 51597}`) |
| minimal degrees from stored `Maxes` | `S₄(3,4,5) = 27, 85, 156`; `G₂(3,4,5) = 351, 416, 3906`; `³D₄(2) = 819` |

> ### Two `Z(Syl_p)` traps, recorded
> `v_task55` recorded that at rank 2 the witness is not `Z(Syl_p)`.  Here
> the trap appears **twice, in different disguises**:
> * `S₄(4)`: `Z(Syl₂)` has order `16` and `[S:N_S(Z)] = 425 = 5·85` — a
>   factor `q+1` too large.  (At **odd** `q` the trap does *not* bite:
>   `Z(Syl_p)` has order `q` and gives exactly `(q+1)(q²+1)`, GAP-checked at
>   `q = 5, 7`.  So this trap is characteristic-dependent — a new wrinkle.)
> * `G₂(3)`: `Z(Syl₃)` has order **9** (not `q = 3`) because of the special
>   isogeny at `p = 3`, and gives `[S:N_S(Z)] = 1456 = 4·364`.  The correct
>   witness is the **long-root subgroup `X_θ` of order `q = 3` inside**
>   `Z(Syl₃)`.  At `³D₄(2)`, by contrast, `Z(Syl₂)` **is** the long-root
>   group (order 2) and gives `819` directly.

---

## 2. PART 1 — the strain, quantified

| target | `3b − a` | `max ι³/|S|` (scan) | `min ι³/|S|` | rank-1 Step 2 |
|---|---|---|---|---|
| `S₄(q)` | `−1` | `0.811` (`q = 5`) | — | **FAILS for every `q`** |
| `G₂(q)` | `+1` | grows like `q` | `11.36` (`q = 3`) | **HOLDS for every `q`** |
| `³D₄(q)` | `−1` | `2.599` at `q = 2` only | decays like `1/q` | **FAILS for `q ≥ 3`** |
| `²F₄(q)` | `+4` | grows like `q⁴` | `6693` (`q = 8`) | **HOLDS, hugely** |

So only `S₄` and `³D₄` need Lemma Q at all; `G₂` and `²F₄` recover the
rank-1 argument outright (`ι(S)³ > |S| ⟹ one socle orbit of length 1`).
Lemma Q is run for all four anyway, and closes all four.

> **Lemma K-exc [PROVEN, elementary; 0 violations over the full scans].**
> `ppmax_{p′}(|S|) ≤ P(q)` with
> `P = 8(q+1)²` (`S₄`, `G₂`), `72(q²+q+1)²` (`³D₄`), `9(q²+1)²` (`²F₄`).
>
> *Proof.*  An odd `r ≠ p` has `ord_r(q) = e` and so divides `Φ_e(q)` and
> (by Lucas/Zsygmondy) `Φ_{e r^k}(q)` only to the first power; hence its
> `r`-part is at most `(largest block)^{multiplicity} · r_small`, bounded
> by the stated constants.  For `q` odd the `2`-part of `Φ₁²Φ₂²` is
> `(|q−1|₂|q+1|₂)²` with `min(|q−1|₂,|q+1|₂) = 2`, hence `≤ 4(q+1)²`; the
> `Φ₄` block is `≡ 2 (mod 4)`, giving `≤ 8(q+1)²`.  For `q` even and for
> `²F₄` the `2`-part is `|S|_p` and is excluded. ∎
> (0 violations over all admissible `q ≤ 2000` resp. `q ≤ 600`.)

---

## 3. PART 2 — **Lemma Q**: `T` is almost simple

Lemma Q is **target-agnostic** and is quoted verbatim from `v_task55` §3:
if `T` is not almost simple, some socle factor `G` with orbit length `ℓ`
has `|G|^{max(2,ℓ)} ≤ |S|` and `ℓ|Out(G)|ι(G) ≥ ι(S)`; `ℓ ≥ 3` dies from
Lemma C, and `ℓ ≤ 2` forces `|G| ≤ 4ρ(G)²` — i.e. `G` is one of the **56
Lemma-B violators** enumerated (and proven complete: Lie tail `q₁ ≤ 2 709 504`,
rank `≤ 24`) in `v_task55` PART 2b.  **That list is reused, not recomputed.**
`max ρ` over the list is `283 599 225`, attained by `Th`.

Per-target windows (PART 2):

| target | `ℓ ≥ 3` possible only for `q ≤` | `ℓ ≤ 2` window | Lemma-Q threshold |
|---|---|---|---|
| `S₄(q)` | `3` | one violator, `U₃(8)`, window `[25,25]` | **`q > 25`** |
| `G₂(q)` | — | **empty** | **every `q`** |
| `³D₄(q)` | — | **empty** | **every `q`** |
| `²F₄(q)` | — | **empty** | **every `q`** |

> **Why the rank-2 window collapsed.**  `v_task55` §8 predicted it: the
> Lemma-Q window is `ι(S) ≤ 2ρ_max`, i.e. `q^b ≲ 5.7·10⁸`.  For `L₃`, `b = 2`
> gives `q ≤ 23 815`; here `b = 3, 5, 9, 10` gives `q ≤ 830, 56, 8, 6`, and
> the *second* constraint `|G|² ≤ |S|` then empties all but one cell.
> **Rank 2 in the `A₂` sense really was the worst case for Lemma Q.**
> `²F₄` has `b = 10` and `q ≥ 8`, so the window is empty on the exponent
> alone.

**Consequence [PROVEN].**  For `q > 25` (`S₄`) and for **every** `q`
(`G₂`, `³D₄`, `²F₄`),
```
   (E)   c·|S₁| = |S| ,   c ≥ 2 ,   c | |Out(S₁)| ;
   (F)   |Out(S₁)|·ι(S₁) ≥ ι(S) .
```

---

## 4. PART 3 — cross characteristic: the `ppmax³` kill

`|S₁|_{p₁} ≤ ppmax_{p′}(|S|) ≤ P(q)`, Lemma K′ gives `|S₁| < P³`, so
`|S| < c·P³` with `c ≤ 6·n_max(P)·log₂P`.  Exponents: `a` against
`3·deg_q P`, i.e. `10 vs 6`, `14 vs 6`, `28 vs 12`, `26 vs 12` — **margin
`≥ 4` in every family**, so the kill is far more comfortable than for `L₃`
(`8 vs 6`).  Exact evaluation:

```
S4  : survives only for q in {3,4,5,7,8,9,11,13,16,17,19,23,25}
G2  : survives only for q in {3, 4}
3D4 : survives only for q in {2, 3}
2F4 : EMPTY for every q
```

---

## 5. PARTS 4–4.6 — equal characteristic, **uniform for all four targets**

Three lemmas, each strictly stronger than the last.

> **Lemma EQ′ [PROVEN, target-agnostic; the rank-2 generalisation of
> `v_task54`'s Lemma EQ].**  In equal characteristic with (E)+(F),
> ```
>          q₁^{ (b/N)·N₁ − μ₁ }  ≤  4 d₁ f₁ g₁ .
> ```
> *Proof.*  (E) gives `q₁^{N₁} ≤ q^N`; (F) with (T2)/(T3) gives
> `4d₁f₁g₁ q₁^{μ₁} ≥ ι(S) > q^b`.  Eliminate `q`. ∎
>
> So a family dies uniformly as soon as `N₁/μ₁ > N/b`.  (`v_task54`'s
> Lemma EQ is the case `b = N`, i.e. rank 1.)

> **Lemma EQ-EX [PROVEN, target-agnostic].**  `T` almost simple with socle
> `S₁`, `|S| = c|S₁|`.  Comparing `p`-parts is an **equality**:
> ```
>          q₁^{N₁} · c_p  =  q^N ,        c_p := |c|_p ,  c_p | c | |Out(S₁)| .
> ```
> With (T1) this pins `q^{N·D₁/N₁ − a}` inside a polylog band, so **every
> family with `D₁/N₁ ≠ a/N` is killed above an explicit threshold**.

Intersecting the two (PART 4.5) leaves an astonishingly short list:

| target | `a/N` | `N/b` | surviving families |
|---|---|---|---|
| `S₄(q)` | `5/2` | `4/3` | `U₄(q₁)`, `S₄(q₁)`, `Sz(q₁)` |
| `G₂(q)` | `7/3` | `6/5` | `G₂(q₁)`, `R(q₁)` |
| `³D₄(q)` | `7/3` | `4/3` | `G₂(q₁)`, `³D₄(q₁)`, `R(q₁)` |
| `²F₄(q)` | `13/6` | `6/5` | **`²F₄(q₁)` only** |

### 5.1 The matched case `c_p = 1`, in closed form (PART 4.5)

`c_p = 1` forces `q₁^{N₁} = q^N` exactly, i.e. `f₁ = Nf/N₁`, and then
`c = |S|/|S₁|` is a **closed rational function of `q`**:

| pair | `c(q)` | verdict |
|---|---|---|
| `S₄ ← Sz` | `f₁ = 2f` is **even**, but `Sz` needs `f₁` odd | **impossible**, 0 admissible pairs |
| `G₂ ← R`, `³D₄ ← R` | `f₁ = 2f` resp. `4f`, even; `R` needs `f₁` odd | **impossible**, 0 admissible pairs |
| `S₄ ← S₄`, `G₂ ← G₂`, `³D₄ ← ³D₄`, `²F₄ ← ²F₄` | `q₁ = q`, so `c = 1` | excluded by `c ≥ 2` |
| `S₄ ← U₄` (`q = m³`, `q₁ = m²`) | `c = d₁(m⁶−1)²/(2(m⁴−1)(m⁸−1))`; since `(m⁴−1)(m⁸−1) − (m⁶−1)² = −m⁴(m²−1)² < 0`, `1 < c < 441/425 < 2` | **never an integer `≥ 2`** |
| `³D₄ ← G₂` (`q₁ = q²`) | `c = (q⁸+q⁴+1)/((q⁶+1)(q²+1)) < 1` | **`|G₂(q²)| > |³D₄(q)|` always** |

Machine confirmation (`q ≤ 20 000`): `S₄←U₄` 15 pairs, `c ∈ [1+2·10⁻⁹, 441/425]`, no
integer `≥ 2`; `³D₄←G₂` 2328 pairs, `c ∈ [21/25, 1)`; GAP `_g_out.txt`
PART G shows `21/25, 91/100, 273/289, 651/676` at `q = 2,3,4,5`.

### 5.2 The non-matched case, killed by **Zsygmondy + counting** (PART 4.6)

For each pair a Zsygmondy primitive prime `r` of `p^{e f₁} − 1` sits in the
top cyclotomic block of `|S₁|`; `r | |S₁| | |S|`, and the `p′`-part of `|S|`
divides `p^{E f} − 1` for the target's top exponent `E`.  Hence
**`e f₁ | E f`**:

| target ← socle | `e` | `E` | matched `f₁` | non-matched `f₁` |
|---|---|---|---|---|
| `S₄ ← S₄` | 4 (`Φ₄`) | 4 | `f` | `f₁ | f`, `f₁ < f` |
| `S₄ ← U₄` | 6 (`Φ₆`) | 4 | `2f/3` | `3f₁ | 2f`, `3f₁ < 2f` |
| `S₄ ← Sz` | 4 | 4 | (impossible) | — |
| `G₂ ← G₂` | 6 | 6 | `f` | `f₁ | f`, `f₁ < f` |
| `G₂ ← R` | 6 | 6 | `2f` (impossible: `f₁ ≤ f`) | `f₁ | f` |
| `³D₄ ← ³D₄` | 12 (`Φ₁₂`) | 12 | `f` | `f₁ | f` |
| `³D₄ ← G₂` | 6 | 12 | `2f` | `f₁ | 2f`, `f₁ < 2f` |
| `³D₄ ← R` | 6 | 12 | `4f` (impossible: `f₁ ≤ 2f`) | `f₁ | 2f` |
| `²F₄ ← ²F₄` | 12 | 12 | `f` | `f₁ | f` |

Every non-matched `f₁` satisfies `q₁ ≤ q^{(matched)/2}`-ish, so
`c = |S|/|S₁|` is at least a positive power of `q` while `c ≤ |Out(S₁)|` is
`O(log q)`.  Exact check over all `q ≤ 10⁶` (`²F₄`: `q = 2^f`, `f` odd
`≤ 121`):

```
S4  <- S4  : 79001 pairs, c <= |Out| : NONE     S4  <- U4  : 88 , NONE
S4  <- Sz  :    18 pairs,              NONE     G2  <- G2  : 79001 , NONE
G2  <- R   :     9 pairs,              NONE     3D4 <- 3D4 : 79020 , NONE
3D4 <- G2  : 79059 pairs,              NONE     3D4 <- R   :      9 , NONE
2F4 <- 2F4 :   133 pairs,              NONE
```

**Together, §5.1 + §5.2 close the equal-characteristic branch uniformly in
`q` for all four targets.**  (`v_task55` §5.2 had to kill three families by
hand; the `EQ-EX` exact-ratio criterion replaces that with a mechanical
two-line test and is the main reusable gain of this note.)

### 5.3 PART 4.0 — the independent factorisation-free sweep

`q₁^{N₁} | q^N` bounds `f₁ ≤ Nf/N₁`, so the whole branch is a finite exact
test per target with **no factorisation of `|S|`**.  Run over *every*
family, every rank `≤ 29`, every `f₁`:

```
S4  : 18 119 targets (q <= 200 000) , 54 877 divisor pairs , control 18119/18119 , HITS NONE
G2  :  6 147 targets (q <=  60 000) , 31 412 divisor pairs , control  6147/6147  , HITS NONE
3D4 :  2 328 targets (q <=  20 000) , 14 633 divisor pairs , control  2328/2328  , HITS NONE
2F4 :     20 targets (f <= 41 odd)  ,    374 divisor pairs , control    20/20    , HITS NONE
order-only NEAR-MISSES (c <= |Out| dropped) : NONE, in all four families
```

---

## 6. PART 5 — alternating / sporadic socle, complete in `q`

`|S| = M` is inverted exactly for `q` (exact integer `a`-th roots), so each
row is complete in `q`, not a range.  All 27 sporadics + Tits + `A_m` with
`|A_m| ≤ 10^{120}`, every `c | |Out(S₁)|`, `c ≥ 2`: **90 `(S₁,c)` pairs per
target, 0 hits in the target range.**

One hit at an **excluded** parameter, and it is the expected one:
`|S₄(2)| = 2·|A₆|` — the isomorphism `S₄(2) ≅ A₆.2 = Σ₆`, i.e. `S₄(2)′ ≅ A₆`.
`q = 2` is outside the `S₄` target range (`S₄(2)` is not simple), so this is
a *positive control*, not a twin.

---

## 7. PART 7 — the `S₄(3)` defect and the coincidence hunt

### 7.1 The `S₄(3)` defect, handled exactly

`S₄(3) = PSp₄(3) ≅ U₄(2)` — an **isomorphism**, not a twin, so there is no
double-counting question (`c ≥ 2` excludes it automatically).  But its
minimal degree is **27** (the maximal subgroup `2⁴:A₅`), not the parabolic
index `40`.  GAP, over the whole subgroup lattice (`_g_out.txt` PART B,
reproducing `v_task29`/§4at exactly):

```
maximal subgroup indices          : 27, 36, 40, 40, 45
{ [S : N_S(A)] : 1 != A abelian } : { 27, 40, 45 }
witness at 27 : A elementary abelian of order 16, A' = 1, N_G(A) = 2^4:A5
==> iota(S4(3)) = 27  <  40 = (q+1)(q^2+1)
```

**How it is handled here.**  Every inequality in this note uses the
**exact** `ι`, never the closed form; the target table carries
`ι(S₄(3)) = 27` as a hard-coded exception (PART 1 prints the comparison at
`q = 3,4,5,7,8,9,11`).  The defect makes the Lemma-Q and cross-characteristic
windows at `q = 3` *larger*, never smaller — and `q = 3` sits inside the
`S₄` census (`q ≤ 27`) anyway.  So the defect costs nothing.

*(This is the third appearance of the `S₄(3)` defect in the programme —
§4at fitted `ι₂` at prime `q` and got it wrong, `v_task50` recorded it, and
`v_task52` handled it conservatively.  It is now used, not merely
avoided.)*

### 7.2 Two new inter-family order identities

The hunt (`|S| = c·|G|`, `2 ≤ c ≤ 10⁴`, over the full candidate list) turns
up two *families* of identities, both exact for every `q`:

> **Identity A [PROVEN, all `q`].**
> ```
>       | S₄(q³) |  =  ((q²+1)/gcd(2,q−1)) · | ³D₄(q) | .
> ```
> *Proof.* `|S₄(q³)|/|³D₄(q)| = (q¹²−1)/(d(q⁸+q⁴+1)(q²−1)) = (q⁴−1)/(d(q²−1))
> = (q²+1)/d.* ∎
> Observed at `q = 2,3,4,5`: `c = 5, 5, 17, 13`.
> **It dies solely because `c = (q²+1)/d ∤ |Out(³D₄(q))| = 3f`** — indeed
> `c ≍ q²` while `|Out|` is `O(log q)`.

> **Identity B [PROVEN, all `q = 2^{2m+1}`].**
> ```
>       | G₂(q²) |  =  (q² + q + 1) · | ²F₄(q) | .
> ```
> *Proof.* `(q¹²−1)/((q⁶+1)(q³+1)(q−1)) = (q³−1)/(q−1) = q²+q+1.* ∎
> Observed at `q = 8`: `|G₂(64)| = 73·|²F₄(8)|`; and at the excluded `q = 2`,
> `|G₂(4)| = 14·|²F₄(2)′|`.
> **It dies solely because `c = q²+q+1 ∤ |Out(²F₄(q))| = f`.**

These join `|U₃(q)| = (q+1)|R(q)|` (§4bd) and `|L₃(25)| = 7|L₄(5)|` (§4be).
The pattern is now unmistakable and worth naming:

> **The `c ∤ |Out|` pattern.**  Exact inter-family order identities
> `|S| = c(q)|G|` with `c(q)` a *polynomial in `q`* exist in abundance; every
> one of them is killed by the Fitting-free constraint `c | |Out(S₁)|`,
> because `|Out|` is always `O(log q)` while `c(q)` is a positive power of
> `q`.  **`c | |Out(S₁)|` must never be relaxed to `c ≤ |Out(S₁)|`.**
> (Here it is not even close — the margin is a full power of `q`.)

Also recorded from the hunt: `|G₂(4)| = 416·|J₂|` (this is just the
minimal-degree relation, `J₂ < G₂(4)`), `|S₄(8)| = 5·|³D₄(2)|` (Identity A
at `q = 2`), and the isomorphism controls `S₄(2)′ ≅ A₆`, `S₄(3) ≅ U₄(2)`,
`G₂(2)′ ≅ U₃(3)`, `²F₄(2)′ = ` Tits.

---

## 8. PART 6 — the residual census

Residual windows after §§3–6:  `S₄`: `q ≤ 25` (Lemma Q **and** cross-char);
`G₂`: `q ∈ {3,4}`; `³D₄`: `q ∈ {2,3}`; `²F₄`: **none**.
Census run with margin (`S₄`: `q ≤ 27`, `G₂`: `q ≤ 9`, `³D₄`: `q ≤ 4`):

| target | targets | positive-control failures | RAW (Phase 1) survivors | after the orbit floor |
|---|---|---|---|---|
| `S₄` | 14 | 0 | **4** | **0** |
| `G₂` | 6 | 0 | 0 | 0 |
| `³D₄` | 3 | 0 | 0 | 0 |
| `²F₄` | — | — | *no census needed* | — |

The four `S₄` raw survivors, and their death on the floor:

```
q =  4 (iota = 85)   A5 x L2(16)             |Out|iota = 10 , 68
q =  8 (iota = 585)  U3(3) x Sz(8)           |Out|iota = 56 , 195
q =  8 (iota = 585)  L3(2) x A6 x L2(13)     |Out|iota = 14 , 40 , 28
q = 16 (iota = 4369) L2(16) x L2(256)        |Out|iota = 68 , 2056
```

Every factor of every survivor fails `|Out(S_i)|·ι(S_i) ≥ ι(S)`, so all four
die.  As at `L₃`, all survivors are multi-orbit configurations with orbits
of length 1 — exactly the branch Lemma Q handles uniformly, so the census is
a *confirmation* here, not the argument.

---

## 9. Status ledger

| step | `S₄` | `G₂` | `³D₄` | `²F₄` |
|---|---|---|---|---|
| `ι` over **all** subgroups, (AB)-free | **[PROVEN]** (`q=3` exact exception) | **[PROVEN]** (`q=3,4` need the max-subgroup refinement) | **[PROVEN]** | **[PROVEN]** |
| Lemma K-exc | **[PROVEN]**, 0 violations | ” | ” | ” |
| rank-1 Step 2 (`ι³ > |S|`) | fails | **holds** | fails | **holds** |
| Lemma Q ⟹ almost simple | **[PROVEN]** `q > 25` | **[PROVEN]** all `q` | **[PROVEN]** all `q` | **[PROVEN]** all `q` |
| cross characteristic empty | **[PROVEN]** `q ≥ 27` | `q ≥ 5` | `q ≥ 4` | **all `q`** |
| equal characteristic, uniform | **[PROVEN]** all `q` (§5.1+§5.2) | ” | ” | ” |
| equal characteristic, exact sweep | **[COMPUTED]** `q ≤ 2·10⁵` | `q ≤ 6·10⁴` | `q ≤ 2·10⁴` | `f ≤ 41` |
| alternating / sporadic socle | **[PROVEN]**, complete in `q` | ” | ” | ” |
| residual census | **[COMPUTED]** `q ≤ 27`, 0 | `q ≤ 9`, 0 | `q ≤ 4`, 0 | *not needed* |
| simple–simple side | **[LIT: CFSG order theorem]** — no `Bₙ/Cₙ` issue at `n = 2` | ” | ” | ” |

**Every finite window produced by a uniform argument lies strictly inside a
range that has been exhausted exactly.**  Hence Theorems S4-T, G2-T, 3D4-T,
2F4-T as stated in the headline.

### Honest gaps

1. **(H1) The lower half of every `ι` is literature.**  `m(S₄(q))`,
   `m(G₂(q))`, `m(³D₄(q))`, `m(²F₄(q))` are quoted (Cooperstein;
   Kleidman–Liebeck 5.2.2; Kleidman 1988; Malle 1991), machine-confirmed only
   where stored `Maxes` exist (`S₄` `q ≤ 5`, `G₂` `q ≤ 5`, `³D₄(2)`).
   Same epistemic status as the `U₃`/`Sz`/`R`/`L₃` rows.
2. **(H2) `²F₄(q)` has no computational verification at any `q ≥ 8`.**
   `²F₄(8)` has order `2.6·10²³` and no stored `Maxes`, no usable
   representation; the whole `²F₄` row is **structural only**, exactly as
   flagged in the brief.  The `q = 2` data point is the Tits group, which is
   *not* `²F₄(2)` and is excluded.  Mitigating: `²F₄` is also the *most*
   comfortable row (empty Lemma-Q window, empty cross-characteristic branch,
   `ι³/|S| ≥ 6693`), so nothing delicate rests on the missing check.
3. **(H3) The `G₂(3)`/`G₂(4)` refinement uses the stored maximal-subgroup
   lists** as complete.  For `q ≥ 5` no refinement is needed (the literature
   minimal degree equals the parabolic index), but the completeness of the
   `G₂(3)`, `G₂(4)` `Maxes` is a **[LIT/ATLAS]** input.
4. **(H4) `ῑ` in the orbit floor** is the parabolic upper bound for Lie-type
   factors (conservative) and the exact `v_task39`/`v_task50` table for
   sporadics — inherited from `v_task55` (H3).
5. **(H5) The Lemma-B violator enumeration** is inherited wholesale from
   `v_task55` (H2), including its reliance on the `v_task52` surrogates
   (T1)/(T2)/(T3).  Nothing new is assumed here.
6. **(H6) `³D₄(q)` `|Out| = 3f`** and the `²F₄` `|Out| = f` are quoted from
   Kleidman–Liebeck; GAP checks exist only via the ATLAS at `³D₄(2)`.

---

## 10. What remains for the full exceptional tower

The four targets settled here are the ones with `D/μ ≤ 28/9`.  The
remaining exceptional families are `F₄`, `E₆`, `²E₆`, `E₇`, `E₈`, and the
outlook is **good — they get easier, not harder**:

| family | `D` | `μ` | `N` | `a/b = D/μ` | `a/N = D/N` | `N/b` |
|---|---|---|---|---|---|---|
| `F₄(q)` | 52 | 15 | 24 | `52/15 ≈ 3.47` | `13/6` | `8/5` |
| `E₆(q)`, `²E₆(q)` | 78 | 16 | 36 | `39/8 = 4.88` | `13/6` | `9/4` |
| `E₇(q)` | 133 | 25 | 63 | `133/25 = 5.32` | `19/9` | `63/25` |
| `E₈(q)` | 248 | 51 | 120 | `248/51 ≈ 4.86` | `31/15` | `40/17` |

1. **Lemma Q's window shrinks further.**  It is `q^b ≲ 2ρ_max ≈ 5.7·10⁸`
   with `b = μ = 15, 16, 25, 51`: `q ≤ 3, 3, 2, 1`.  Combined with
   `|G|² ≤ |S|` these are certainly empty.  **`ℓ ≥ 2` will be vacuous for
   the whole `F₄`–`E₈` tower.**
2. **Step 2 (`ι³ > |S|`) returns for the big ones**: `3b − a` is
   `−7` (`F₄`), `−30` (`E₆`), `−58` (`E₇`), `−95` (`E₈`) — so *no*, it
   fails badly for all of them, and Lemma Q is genuinely needed. (Only
   `G₂`/`²F₄` were lucky.)  This is not a problem given (1).
3. **Cross characteristic gets more comfortable still**: `deg_q P ≈ 2·(top
   block degree)` is `O(rank)` while `a` is quadratic in the rank, so the
   `a vs 3 deg P` margin grows.
4. **The real work is Lemma EQ-EX's same-ratio list**, and it is short:
   `a/N = 13/6` for `F₄`, `E₆`, `²E₆` — *the same value as `²F₄`* — so the
   `F₄`/`E₆`/`²E₆`/`²F₄` block will interact (and Identity B suggests more
   order identities are waiting inside it).  `E₇` (`19/9`) and `E₈` (`31/15`)
   have ratios shared with essentially nothing.  Intersecting with
   `N₁/μ₁ ≤ N/b` (which is generous for `E₇`, `E₈`) is the one computation
   that has to be redone per family.
5. **`Bₙ/Cₙ` (`n ≥ 3`) remains parked** and is untouched by this note.
   `Dₙ`, `²Dₙ`, `Lₙ`, `Uₙ` for `n ≥ 4`, and `Sp₆`/`O₇`, are the *classical*
   remainder; `v_task55` §8 already identified the equal-characteristic
   family list as the strain point there, and **Lemma EQ-EX is precisely the
   tool that was missing** — it replaces "`D₁/N₁ ≥ a/N`" (a `≥`, which
   admits seven families at `d = 4`) by "`D₁/N₁ = a/N`" (an `=`, which admits
   two or three).  Retro-fitting it to `L₃`/`U₄` would shorten those notes.

---

## 11. Citations

| # | input | tag |
|---|---|---|
| C1 | `m(S₄(q)) = (q⁴−1)/(q−1)` (`q ≥ 4`), `m(G₂(q)) = (q⁶−1)/(q−1)` (`q ≥ 5`) | **[LIT: Cooperstein 1978; Kleidman–Liebeck Table 5.2.2; Vasilyev]** |
| C2 | `m(³D₄(q)) = (q⁸+q⁴+1)(q+1)` | **[LIT: Kleidman 1988]** |
| C3 | `m(²F₄(q)) = (q⁶+1)(q³+1)(q+1)` (`q ≥ 8`) | **[LIT: Malle 1991]** |
| C4 | Borel–Tits `N_G(Z(U_P)) = P`; abelian unipotent radical of the `C₂` Siegel parabolic | **[LIT]** + GAP at `S₄(4,5,7)`, `G₂(3)`, `³D₄(2)` |
| C5 | Zsygmondy's theorem (used at `p^{4f₁}−1`, `p^{6f₁}−1`, `p^{12f₁}−1`) | **[LIT: Zsygmondy 1892]** |
| C6 | orders, `|Out| = d f g`, parabolic indices | **[LIT: Kleidman–Liebeck; ATLAS]**, GAP-checked |
| C7 | maximal subgroups of `G₂(3)`, `G₂(4)`, `³D₄(2)` (completeness) | **[LIT: ATLAS / CTblLib `Maxes`]** |
| C8 | CFSG order theorem (`{A₈, L₃(4)}`, `{Bₙ, Cₙ}` `n ≥ 3` only) | **[LIT: Artin; KLST]** |
| C9 | Lemma C `|Out|ι ≤ |G|^{2/3}` | **[PROVEN, v_task52]** |
| C10 | Lemma TO′-0 + Lemma F (the orbit floor) | **[PROVEN, v_task42/v_task36]** |
| C11 | Lemma Q + the 56 Lemma-B violators | **[PROVEN, v_task55]** |
| C12 | order transfer `D(T) ≅ D(S) ⟹ |T| = |S|` | **[LIT/formalised: Müller Satz 2.3.4]** |
| C13 | §4j–§4l reduction (Fitting-freeness a `D`-invariant) | **[PROVEN, this project]** |

---

## 12. Reproduce

```
python3 -u v_task57_rank2exc_twins.py                    > v_task57_rank2exc_twins_out.txt    # ~40 min
~/gap-4.16.0/gap -q -o 8g v_task57_rank2exc_twins.g      > v_task57_rank2exc_twins_g_out.txt  # ~10 min
```

Individual parts: `python3 v_task57_rank2exc_twins.py 1 | 2 | 3 | 4 | 45 |
46 | 40 | 5 | 6 | 7`.
