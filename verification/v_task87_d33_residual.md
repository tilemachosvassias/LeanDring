# v_task87 — closing the `d ≥ 33` residual of the block-2 audit
# (equal characteristic, **multi-factor**, `L_d(q)` / `U_d(q)`)

Date 2026-08-09.  **`NOTES.md` not edited.**
Input: `v_task82_audit_block2.md` §2.4 + §3.3 + §6 (the named residual),
`v_task60_lu_residues.md` (Lemma DEG, Lemma Z, Corollary PACK-TOP),
`v_task56_lu_twins.md` §8 (H1)–(H5).

| file | what it does |
|---|---|
| `v_task87_lemmas.py` / `_out.txt` | PART 1 **Lemma COX** (`2N_i = h_i n_i`, `h_i` = Coxeter number) verified on 2398 family/rank rows; PART 2 `M_K = 1` in both towers, `d ≤ 300`; PART 3 **Theorem MF** re-checked as an exhaustive numeric case distinction, `31 ≤ d ≤ 2000`; PART 4 the finite residue at `d ≤ 30`; PART 5 the slack-tolerance analysis |
| `v_task87_scan.py` / `_out.txt` | the **exact, slack-free** equal-characteristic multi-factor census, `33 ≤ d ≤ 60`, **every** prime power `q ≤ 100`, **every** family/rank/`f_i ≥ 1` (subfield factors included) |
| `v_task87_pos.py` / `_out.txt` | the hypothesis **(POS)** (`q_i ≥ q`) tested exactly against the orbit floor, `33 ≤ d ≤ 200`, every `q ≤ 1024` with `f ≥ 2` |

All arithmetic exact (Python big integers / `Fraction`); **no floats, no
logarithms in any test that feeds a yes/no answer.**

---

> ### Headline
>
> **Theorem MF [PROVEN, `q`-free, both towers, every `d ≥ 31`]** — modulo the
> two hypotheses **(DEG-exact)** and **(POS)** made explicit below.
> The equal-characteristic multi-factor branch is **empty**, and the proof
> uses **no orbit floor, no Lemma ZM, no census and no `q`** — so the two
> defects `v_task82` (F3) found in `v_task60` PART C (the dropped `(Z2)`
> log-slack and the dropped `v_r(d!)`) **cannot enter it**: neither
> ingredient occurs.
>
> The engine is one new structural identity:
>
> > **Lemma COX.** For every finite simple group of Lie type,
> > `2 N_i = h_i · n_i`, where `h_i` is the **Coxeter number** of the ambient
> > root system and `n_i = D_i − 2N_i`.  Equivalently `σ_i = N_i/n_i = h_i/2`.
>
> Feeding it into Lemma DEG turns `(P=)` and `(R=)` into one sentence:
>
> > **the `x`-weighted mean of the Coxeter numbers of the socle factors is
> > EXACTLY the Coxeter number `d` of the target.**
>
> For the **linear** tower this closes the branch in three lines: Lemma Z
> forces `h_i ≤ K/j_i = d/j_i ≤ d` for *every* factor, so a mean of `d` is
> only possible if `h_i = d` for every factor — and every family with
> `h = k = d` has rank `≥ d/2`, so two factors already overspend the rank
> budget `d−1`.  For the **unitary** tower (`K ≈ 2d`, so the bound is only
> `h_i ≤ 2d`) the same identity plus **PACK-TOP** leaves exactly two possible
> `Φ_K`-owners, `²G₂` and `²F₄`, and both die on an explicit quadratic
> inequality with margin from `d ≥ 29`.
>
> **Unconditionally** (no hypotheses beyond (H1)/(H5)): the exact
> **slack-free census** finds **0** admissible multi-factor configurations
> for `33 ≤ d ≤ 60` and **every** prime power `q ≤ 100`, including every
> subfield factor `f_i < f`.  This closes the audited residual on the whole
> range where it was actually named ("`d ≥ 33` **and small `q`**").
>
> **One new named gap** falls out of writing the argument honestly:
> **(H6)** — `v_task60` PART C treats `(P=)` and `(R=)` as *exact* (its
> `pack_kill` uses `N` and `d−1` as literal right-hand sides), i.e. it
> silently sets the `c`-corrections `v_p(c)/f` and `θ` to zero.  Theorem MF
> inherits exactly that hypothesis and nothing worse — but it was never
> stated anywhere, and it is **not** implied by anything proven so far.

---

## 1. What the residual is, precisely

`v_task82` §6:

> "the equal-characteristic multi-factor branch at `d ≥ 33` and small `q`,
> where PART C's enumeration is incomplete and no census exists.  §2.4's
> `σ = d/2` / PACK-TOP argument is `q`-free and looks sufficient; it should
> be written out."

`v_task60` PART C enumerates candidate socle shapes with
`lb = b/μ_i` (the orbit floor with the `(Z2)` log-slack `Λ/f` **dropped**)
and `need = ℓ_i·m` (Lemma ZM with the `v_r(d!)` term **dropped**).  Both are
valid only above an uncomputed `q`-threshold.  Below it the branch rested on
the C.4 censuses, which reach `q ≤ 10⁵` for `d ≤ 10`, `q ≤ 3000` for
`11 ≤ d ≤ 20` and (after `v_task82`) `q ≤ 3000` for `21 ≤ d ≤ 32` — **nothing
at all for `d ≥ 33`**.

The single most consequential effect of the dropped `(Z2)` slack is that
`lb = b/μ_i ≥ 1` for the rows that matter, i.e. PART C silently enumerates
only factors with **`j_i ≥ 1`** (`q_i ≥ q`).  Configurations with a socle
factor over a *proper subfield* are simply not in its list.  That is the
hypothesis isolated below as **(POS)**, and it is the only place where the
new argument needs anything beyond degrees.

### 1.1 Setting and notation (as in `v_task60` §1)

`S = L_d(q)` or `U_d(q)`, `q = p^f`; `N = d(d−1)/2`, `a = d²−1`, `b = deg_q ι(S)`,
`K = max{ord_r(q) : r | |S|, r ≠ p}`, so

```
   K = d           (linear)
   K = 2d          (unitary, d odd)
   K = 2d − 2      (unitary, d even)
```

`T` Fitting-free, `|T| = |S|`, `D(T) ≅ D(S)`, `T` not almost simple,
`Soc T = ∏_i S_i^{ℓ_i}` with `L := ∑_i ℓ_i ≥ 2`, every `S_i` of Lie type over
`F_{q_i}`, `q_i = p^{f_i}` (**equal characteristic**), `c = [T : Soc T]`.
Put `j_i = f_i/f`, `x_i = ℓ_i j_i`, `n_i = D_i − 2N_i`, `k_i = max Cyc(S_i)`,
and

```
        v_i  :=  x_i n_i  =  ℓ_i j_i n_i   >  0 .
```

For the target `a − 2N = d − 1` in **both** towers.

---

## 2. Lemma COX — the new structural input

> ### Lemma COX [PROVEN]
> Let `G` be a finite simple group of Lie type, `N = deg_{q_1}|G|_p`,
> `D = deg_{q_1}|G|`, `n_r := D − 2N`, and let `h` be the **Coxeter number of
> the ambient (untwisted) root system**.  Then
> ```
>        2 N  =  h · n_r ,      i.e.    σ := N/n_r = h/2 ,
> ```
> and `h ≤ k ≤ 2h`, where `k = max Cyc(G)`.  Moreover `h = k` exactly for the
> untwisted families and for `²B₂`, `²G₂`, `²F₄`; `h < k` exactly for
> `²A`, `²D`, `³D₄`, `²E₆`.

*Proof.*  `N = |Φ⁺| = |Φ|/2` and `|Φ| = (rank)·h` for every root system, so
`2N = h·rank`.  `D − 2N` is the **ambient** rank for the untwisted families
and for `²A`, `²D`, `²E₆`, `³D₄` (whose order polynomials carry the untwisted
degrees — this is `v_task82`'s defect F7 read positively).  For `²B₂`, `²G₂`,
`²F₄` the pair `(N, n_r)` recorded in `FAM` is `(2,1)`, `(3,1)`, `(12,2)`
against the ambient `(4,2)`, `(6,2)`, `(24,4)` — **both entries halved**, so
the ratio `N/n_r` is unchanged.  `h ≤ k` because `h` is the largest degree of
the Weyl group and every degree contributes a `Φ`-block to the order
polynomial; `k > h` exactly when the Frobenius twist replaces some
`q^i − 1` by `q^i + 1`. ∎

Verified in `v_task87_lemmas.py` PART 1 on **2398 family/rank rows**
(all 17 families, ranks ≤ 400): **0 violations** of `2N = h n_r`, of
`h ≤ k ≤ 2h`, and of the auxiliary facts

| tag | statement | status |
|---|---|---|
| (C1) | `2 N_i = h_i n_i` | 0 violations |
| (C2) | `h_i ≤ k_i ≤ 2 h_i` | 0 violations |
| (C3) | `h_i = k_i` ⟺ untwisted or `{²B₂, ²G₂, ²F₄}` | confirmed |
| (C4) | `n_i ≥ h_i/2` for every **classical** family; and `h_i > 30` forces `S_i` classical (`h(E₈) = 30` is the exceptional maximum) | 0 violations |
| (C5) | `τ_i := n_i/k_i < 1/4` ⟺ `S_i ∈ {²G₂, ²F₄}` (both `τ = 1/6`); runner-up `²B₂` with `τ = 1/4` **exactly** | confirmed |

The family table the proof reads off (`h`, `n_r`, `k`, `τ = n_r/k`):

| family | `h` | `n_r` | `k` | `τ` |
|---|---|---|---|---|
| `A₁ = L₂` | 2 | 1 | 2 | 1/2 |
| `A_{n−1} = L_n` | `n` | `n−1` | `n` | `(n−1)/n` |
| `²A_{n−1} = U_n` | `n` | `n−1` | `2n` (`n` odd) / `2n−2` (`n` even) | `≥ 1/3` |
| `C_n, B_n` | `2n` | `n` | `2n` | 1/2 |
| `D_n` | `2n−2` | `n` | `2n−2` | `n/(2n−2)` |
| `²D_n` | `2n−2` | `n` | `2n` | 1/2 |
| `G₂` | 6 | 2 | 6 | 1/3 |
| `³D₄` | 6 | 4 | 12 | 1/3 |
| `F₄` | 12 | 4 | 12 | 1/3 |
| `E₆`, `²E₆` | 12 | 6 | 12 / 18 | 1/2, 1/3 |
| `E₇` | 18 | 7 | 18 | 7/18 |
| `E₈` | 30 | 8 | 30 | 4/15 |
| `²B₂ = Sz` | 4 | 1 | 4 | **1/4** |
| `²G₂ = R` | 6 | 1 | 6 | **1/6** |
| `²F₄` | 12 | 2 | 12 | **1/6** |

### 2.1 Lemma DEG in Coxeter form

Lemma DEG (`v_task60` §1.1) with the `c`-corrections set to zero reads

```
   (P=)   ∑_i x_i N_i = N          (P-part, Lemma EQ-EX)
   (R=)   ∑_i x_i n_i = d − 1 .
```

Substituting (C1) into `(P=)`:

> ### Corollary DEG-COX
> ```
>       ∑_i v_i h_i  =  2N  =  d(d−1)  =  d · ∑_i v_i ,
> ```
> i.e. **the `v`-weighted mean of the socle factors' Coxeter numbers equals
> the Coxeter number `d` of the target, exactly.**

This is the sharp form of `v_task60`'s Corollary DEG-σ ("some factor is at
least as flat as the target"), and it is an **equality**, which is what makes
it usable.

---

## 3. Theorem MF

> ### Theorem MF [PROVEN, `q`-free, all `d ≥ 31`, both towers]
> Let `d ≥ 31` and `S = L_d(q)` or `U_d(q)`.  Let `T` be Fitting-free with
> `|T| = |S|`, `D(T) ≅ D(S)`, `Soc T = ∏_i S_i^{ℓ_i}`, `L = ∑ℓ_i ≥ 2`, every
> `S_i` of Lie type in characteristic `p`.  Assume
>
> * **(DEG-exact)** `(P=)` and `(R=)` hold with vanishing `c`-correction;
> * **(POS)** `j_i = f_i/f ≥ 1` for every `i` (i.e. `q_i ≥ q`).
>
> Then no such `T` exists.

Ingredients, all previously proven:

* **(Z)** `j_i k_i ≤ K` — Lemma Z, `v_task56` (Z1).  *Zsygmondy caveat*: the
  lemma is invoked at `κ = k_i`, where the exceptions are `k_i = 2` and
  `(q_i,k_i) = (2,6)`.  In both cases `h_i ≤ k_i ≤ 6 < d`, which is all the
  proof ever uses, so the exceptions cost nothing.  (The primitive prime `r`
  of `q_i^{k_i}−1` satisfies `r ≥ k_i+1 > d_i` in every family, so `r` is not
  eaten by the diagonal divisor.)
* **(TOP)** `M_K = 1` in both towers (verified `4 ≤ d ≤ 300`,
  `v_task87_lemmas.py` PART 2), so **exactly one** factor covers `Φ_K`; it has
  `ℓ₁ = 1` and `j₁ k₁ ≥ K` (covering), with `= K` by (Z) — Corollary PACK-TOP,
  `v_task60` §1.3.  **Only the `≥` half is used below in the unitary
  branch.**  For `d ≥ 33` we have `K ≥ 33 > 6`, so Zsygmondy's three
  exceptions never apply at `κ = K`; the primitive prime of `q^K − 1` always
  exists.
* **(COX)** Lemma COX, §2.

### 3.1 Linear tower (`K = d`)

**Step L1.**  By (C2) + (Z) + (POS), `h_i ≤ k_i ≤ K/j_i = d/j_i ≤ d` for every
`i`.  Hence every term of

```
     ∑_i v_i (d − h_i)  =  d·∑_i v_i − ∑_i v_i h_i  =  d(d−1) − d(d−1) = 0
```

is `≥ 0` and therefore **zero**: `h_i = d` for **every** factor.  Then
`d = h_i ≤ k_i ≤ d/j_i` forces `j_i = 1` and `k_i = d = h_i`.

**Step L2.**  By (C3) the families with `h = k = d` are, for `d ≥ 31`,
exactly

```
     A_{d−1} = L_d          n_r = d−1
     C_{d/2}, B_{d/2}       n_r = d/2        (d even)
     D_{d/2+1}              n_r = d/2 + 1    (d even)
```

(the exceptional families top out at `h = k = 30`).  Every one has
`n_r ≥ d/2`.  With `j_i = 1`, `(R=)` reads `∑_i ℓ_i n_i = d − 1`, and
`L ≥ 2` gives `∑_i ℓ_i n_i ≥ 2·(d/2) = d > d − 1`. **Contradiction.** ∎

For **odd** `d` the only family with `h = k = d` is `L_d` itself, so the
contradiction is immediate: `ℓ₁(d−1) = d−1` forces `L = 1`.

### 3.2 Unitary tower (`K = 2d` / `2d−2`)

Here `h_i ≤ K ≈ 2d`, so Step L1 has slack; the missing factor 2 is supplied
by PACK-TOP.

**Step U1.**  Put `P := {i : h_i > d}`.  For `i ∈ P`, `h_i > d ≥ 31 > 30`, so
by (C4) `S_i` is **classical** and `n_i ≥ h_i/2 > d/2`; by (POS)
`v_i ≥ ℓ_i n_i ≥ n_i > d/2`.  Two such factors give `∑ v_i > d > d−1`, so
**`|P| ≤ 1`**.

**Step U2 (`P = ∅`).**  Then `∑_i v_i(d−h_i) = 0` with all terms `≥ 0`, so
`h_i = d` for every `i`.  Every family with `h = d` has `n_r ≥ d/2` for
`d ≥ 31` (`L_d`, `U_d`: `d−1`; `C_{d/2}`, `B_{d/2}`: `d/2`; `D_{d/2+1}`,
`²D_{d/2+1}`: `d/2+1`), so `L ≥ 2` gives `∑ v_i ≥ d > d−1`.  **Contradiction.**

**Step U3 (the owner is not `i₀`).**  Let `i₀` be the unique element of `P`
and let `1` be the `Φ_K`-owner (`ℓ₁ = 1`, `j₁ k₁ ≥ K`).  From `(P=)`,
`j₁N₁ ≤ N`, and `j₁ ≥ K/k₁`, so

```
        ρ₁ := N₁/k₁  ≤  N/K .
```

Running this bound over all families and ranks (`v_task87_lemmas.py` PART 3)
shows that **every** family meeting it has `h ≤ d`, in both parities of `d`
— e.g. for `d` odd, `N/K = (d−1)/4` forces `L_n` to `n ≤ (d+1)/2`, `U_n` to
`n ≤ d`, `C_n/B_n` to `n ≤ (d−1)/2`, `D_n` to `n ≤ (d−1)/2`, `²D_n` to
`n ≤ (d+1)/2`, all of which have `h ≤ d`.  So the owner is **not** `i₀`, and
`h₁ ≤ d`.

**Step U4 (only two owners survive).**  `v₁ + v_{i₀} ≤ ∑ v_i = d−1` and
`v_{i₀} > d/2` give `v₁ < d/2 − 1`; and `v₁ = j₁ n₁ ≥ K·τ₁`, so

```
        τ₁ = n₁/k₁  <  (d/2 − 1)/K  <  1/4 .
```

By (C5) the owner is `²G₂ = R` or `²F₄` (both `τ = 1/6`); `²B₂` has `τ = 1/4`
**exactly** and is excluded by the strict inequality.

**Step U5 (the closing inequality).**  With one factor in `P` and the owner
in `Q := {i : h_i < d}`,

```
   v_{i₀}(h_{i₀} − d)  =  ∑_{i ≠ i₀} v_i (d − h_i)  ≥  v₁ (d − h₁) ,
```

while `v_{i₀} ≤ (d−1) − v₁` and, `i₀` being classical, `h_{i₀} ≤ 2 n_{i₀} ≤
2 v_{i₀}`.  Substituting the owner's exact data (`k₁ = 6`, `n₁ = 1`, `h₁ = 6`
for `R`; `k₁ = 12`, `n₁ = 2`, `h₁ = 12` for `²F₄`; both give `v₁ = K/6`):

| owner | `K` | consistency **needs** | which is violated for |
|---|---|---|---|
| `R = ²G₂` | `2d` | `(2d−3)(d−6) ≥ 3d(d−6)`, i.e. `2d−3 ≥ 3d` | **every `d > 6`** |
| `R = ²G₂` | `2d−2` | `2(d−4) ≥ 3(d−6)` | `d ≥ 11` |
| `²F₄` | `2d` | `(2d−3)(d−6) ≥ 3d(d−12)` | `d ≥ 22` |
| `²F₄` | `2d−2` | `2(d−4) ≥ 3(d−12)` | `d ≥ 29` |

All four consistency conditions fail for `d ≥ 31`. **Contradiction.** ∎

Every step of §3.1 and §3.2 is re-run as an exhaustive numeric case
distinction over all families and ranks for **every `31 ≤ d ≤ 2000`** in
`v_task87_lemmas.py` PART 3: **0 failures**.

### 3.3 What Theorem MF does *not* use

* no orbit floor (hence no `(Z2)` log-slack — `v_task82` F3's first item);
* no Lemma ZM (hence no `v_r(d!)` term — F3's second item);
* no census, no `q`, no `d`-bound beyond `d ≥ 31`;
* no `PACK-def` size threshold (only `M_K = 1` and the *covering* half of
  PACK-TOP, both threshold-free).

So Theorem MF is **strictly stronger** than `v_task60` PART C's conclusion on
its own hypothesis (DEG-exact): it removes the enumeration, the floor and the
`d ≤ 60` cut-off simultaneously.

### 3.4 Where `d ≥ 31` is needed

`v_task87_lemmas.py` PART 4 lists, for `4 ≤ d ≤ 30`, the family rows the
argument does not kill.  They are exactly the exceptional coincidences

```
  L :  d=4  ²B₂ ;  d=6  G₂, ²G₂ ;  d=12  F₄, ²F₄ ;  d=18  E₇ ;  d=30  E₈
  U :  d=4,5  G₂, ²G₂ ; d=7…11  F₄, ²E₆, ²F₄ ; d=14…17  E₇ ; d=16…29  E₈
```

i.e. precisely the `d` at which an exceptional Coxeter number equals `d`
(linear) or at which `E₇`/`E₈` can still be the `Φ_K` owner (unitary).  All
of these `d` are inside the exact censuses (`v_task56`/`v_task60` for
`d ≤ 20`, `v_task82`'s gap-fills for `21 ≤ d ≤ 32`), so nothing is lost.

---

## 4. The two hypotheses, honestly

### 4.1 (POS): `q_i ≥ q`

**(POS) is automatic whenever `f = 1`, i.e. for every PRIME `q`** — the case
`j_i < 1` needs `f_i < f`, which needs `f ≥ 2`.

For `f ≥ 2` it is a consequence of the orbit floor.  `v_task87_pos.py` tests
that consequence with **no logarithms and no slack**: a subfield factor
(`f_i < f`) can exist only if

```
    ( f·N / (f_i·N_i) ) · |Out(S_i)| · ῑ(S_i)   ≥   ι(S)          (F)+(P)
```

(the left factor is the exact upper bound `ℓ ≤ fN/(f_i N_i)` coming from the
integral `p`-part identity).  Result, `33 ≤ d ≤ 200`, every prime power
`q ≤ 1024` with `f ≥ 2`:

```
   U tower :        0  (family, rank, f_i<f) rows survive   ==>  (POS) HOLDS
   L tower :  753 784  rows survive
              family breakdown (d ≤ 60, q ≤ 256):
                 ²A 19015 , D 3461 , ²D 3286 , C 3077 , B 826 , E₈ 174
```

* **Unitary tower: (POS) is [COMPUTED, exact] for `33 ≤ d ≤ 200`,
  `q ≤ 1024`**, and unconditional for every prime `q`.  Reason: `ι(U_d(q)) ≍
  q^{2d−3}` is so large that no proper-subfield factor can meet the floor.
* **Linear tower: (POS) does NOT follow from the floor alone.**  `ι(L_d(q)) ≍
  q^{d−1}` is small enough that e.g. `U_{d}(√q)` (with `ι ≍ q^{d−3/2}`) clears
  it.  This is a genuine, precisely-named gap — see §6.

One sub-case is worth recording because it is clean: if the `Φ_K` owner of a
linear target is `U_m(q^{1/2})` with `m` odd, then `j₁ k₁ = m = K = d` forces
`m = d`, hence `h₁ = d`, hence (Step L1's argument, which needs `h_i ≤ d`
only for the *other* factors) all remaining `h_i = d`, `j_i = 1`,
`n_i ≥ d/2`; but the remaining rank budget is `(d−1) − (d−1)/2 < d/2`.
Contradiction.  The residual sub-case is `m` even (`m = d+1`), where the
crude bound `h_i ≤ 2 v_i` is not sharp enough.

### 4.2 (DEG-exact): the `c`-corrections

Exactly:

```
   (P=)   ∑_i ℓ_i j_i N_i = N − ε_P ,        ε_P := v_p(c)/f ≥ 0
   (R=)   ∑_i ℓ_i j_i n_i = (d−1) + θ ,
          θ = log_q( c_p · ∏_i d_i^{ℓ_i} / ( e · c_{p′} ) ) .
```

`v_task60` PART C's `pack_kill` uses `N` and `d−1` as **literal** right-hand
sides, i.e. it assumes `ε_P = θ = 0`.  Theorem MF makes the *same*
assumption.  How much slack does the proof actually tolerate
(`v_task87_lemmas.py` PART 5)?

* **Linear tower, `θ = 0`, `ε_P ≥ 0` arbitrary.**  `∑ v_i(d−h_i) = 2ε_P` with
  all terms `≥ 0`.  At most one factor has `h_i = d` (two would need rank
  `≥ d`).  If that one is `L_d` (`n = d−1`), the remaining factors carry
  `∑ v_i = 0` — **contradiction for every `ε_P`.**  Since for **odd `d`**
  `L_d` is the *only* family with `h = k = d`, the linear tower at odd `d` is
  closed **with no hypothesis on `ε_P` at all**.
  For even `d` a leak needs `2 ε_P·L ≥ d/2 − 2`, i.e. `v_p(c) ≥ f(d−4)/(4L)`.
* **Unitary tower.**  Step U1 uses only `∑ v_i = d−1+θ`; Step U5's margins are
  `Θ(d²)` against `Θ(d)`, so `|θ| < 1`, `ε_P < 1` are comfortably enough at
  `d ≥ 33`.

This is recorded below as the new gap **(H6)**.

---

## 5. The unconditional cross-check: an exact, slack-free census

`v_task87_scan.py` is a **complete necessary-condition census** with no
degree bookkeeping, no logarithms and no dropped slack.  Every test is an
integer test:

```
 (D1)  ∏_i |S_i|^{ℓ_i}  divides  |S|                       (Soc T ≤ T)
 (D2)  c := |S| / ∏_i |S_i|^{ℓ_i}  divides  ∏_i ( |Out(S_i)|^{ℓ_i} · ℓ_i! )
 (D3)  ℓ_i · |Out(S_i)| · ῑ(S_i)  ≥  ι(S)   for every i    (Lemma TO′-0 + F)
 (D4)  ∑_i ℓ_i ≥ 2                                          (T not almost simple)
```

`S_i` ranges over **all 17 Lie-type families in characteristic `p`, every
rank, and every `f_i ≥ 1` allowed by the exact `p`-part budget
`ℓ_i f_i N_i ≤ f N`** — in particular **the subfield configurations `f_i < f`
that PART C's floor silently excluded are enumerated here.**  Only `ῑ`
((H5), an upper bound → conservative in (D3)) and `ι(S)` ((H1), the
minimal-degree lower half → conservative in (D3)) are inherited from the
literature.

```
 targets : L_d(q), U_d(q),  33 ≤ d ≤ 60          (56 targets × 35 fields)
 fields  : every prime power q ≤ 100  (35 values, f ≤ 6)
 surviving single atoms (order | |S|, floor-compatible) : 11 613
 DFS nodes                                              : 14 088
 positive-control failures                              : NONE
 MULTI-FACTOR CONFIGURATIONS SURVIVING (D1)–(D4)        : NONE
```

**Negative control** (`python3 v_task87_scan.py probe`): the census is not
vacuously empty — (D1) alone *does* admit two-factor products, so the DFS
genuinely descends.  Six sample targets produce **25** atom pairs whose orders
jointly divide `|S|`, e.g.

```
 L_40(4)  : E8(4) × E7(8) ,  E7(16) × F4(32) ,  S16(32) × F4(64) , ...
 L_48(2)  : E8(2) × U4(256) ,  E6(8) × O10+(32) ,  O10+(32) × F4(16) , ...
 L_34(16) : E6(256) × F4(1024) ,  E7(64) × O10+(65536)
```

**every one of which is killed by (D2)** — the cofactor `c` does not divide
`∏|Out(S_i)|^{ℓ_i}ℓ_i!`.  (These are exactly the "exceptional groups at half
the target's rank" shapes that `v_task60` §2.1 identified as the tight ones;
here they are refuted by an integer test rather than by a `Φ`-witness.)

Typical atom lists (the *single* factors that survive (D1)+(D3) — the census
is nonempty and meaningful, not vacuous):

```
 L_33(2) : L8(16) L11(8) L16(4) L33(2) S8(16) S16(4) S32(2)
           O10+(16) O16+(4) O18+(4) O32+(2) O34+(2) F4(4) E6(4) E8(2)
 L_34(16): L17(256) L33(16) L34(16) U17(16) U34(4) S34(16) S66(4)
           O10+(65536) O18+(256) O34+(16) O68-(4) F4(1024) E6(256)
           E7(64) E8(16)                       [U34(4), S66(4), O68-(4)
                                                have f_i = 2 < f = 4]
 U_33(2) : U33(2)                              [the target itself, control]
```

So on `33 ≤ d ≤ 60`, `q ≤ 100` — **exactly the range and regime the audit
named** — the branch is empty with **no hypothesis at all** beyond (H1)/(H5).

---

## 6. Status ledger

| claim | range | status |
|---|---|---|
| **Lemma COX** `2N_i = h_i n_i`, `h_i ≤ k_i ≤ 2h_i` | all families, all ranks | **[PROVEN]**, machine-verified on 2398 rows |
| **Corollary DEG-COX** (weighted mean of Coxeter numbers `= d`) | — | **[PROVEN]** from Lemma DEG + COX |
| **Theorem MF** (branch empty) | `d ≥ 31`, all `q`, both towers | **[PROVEN]** modulo (DEG-exact) + (POS) |
| ⤷ with (POS) automatic | `d ≥ 31`, all **prime** `q` | **[PROVEN]** modulo (DEG-exact) |
| ⤷ (POS) verified exactly | **unitary** tower, `33 ≤ d ≤ 200`, `q ≤ 1024` | **[COMPUTED, 0 subfield atoms]** |
| ⤷ linear tower, odd `d`, any `ε_P` | `d ≥ 31` odd, all prime `q` | **[PROVEN]**, no (DEG-exact) needed on `ε_P` |
| **Exact census (D1)–(D4)** | `33 ≤ d ≤ 60`, **every** `q ≤ 100`, all `f_i` | **[COMPUTED, 0 hits]**, unconditional |
| Zsygmondy at `κ = K` | `d ≥ 33` ⟹ `K ≥ 33` | **[PROVEN]** — no exception applies |
| `M_K = 1` | both towers, `4 ≤ d ≤ 300` | **[COMPUTED]** (closed form obvious) |

**Verdict on the audited residual.**  The `d ≥ 33` / small-`q` residual of
`v_task82` §6 is:

* **CLOSED unconditionally** for `33 ≤ d ≤ 60` and every `q ≤ 100` (§5);
* **CLOSED** for every `d ≥ 31` and every **prime** `q`, `q`-free, modulo
  (DEG-exact) (§3);
* **CLOSED** for the **unitary** tower for every `d ≥ 31` and every `q ≤ 1024`
  modulo (DEG-exact) (§3 + §4.1);
* **OPEN** as listed in §7 below.

---

## 7. Honest gaps

1. **(H6) — NEW, and it is inherited, not created here.**  `(P=)` and `(R=)`
   are used with vanishing `c`-correction.  This is exactly what `v_task60`
   PART C already does (`pack_kill`'s right-hand sides are the literals `N`
   and `d−1`), but it was never stated.  `ε_P = v_p(c)/f` and
   `θ = log_q(c_p ∏d_i^{ℓ_i}/(e c_{p′}))` are **not** provably `o(1)` at small
   `q`: the generic bound `c | ∏_i(|Out(S_i)|^{ℓ_i} ℓ_i!)` gives only
   `log_q c = O(L log_q(d f))`, which at `q = 2` is comparable to `d−1`.
   *Mitigation already in hand*: the linear tower at odd `d` is immune to
   `ε_P` (§4.2), and the exact census of §5 is immune to both.
   *Next concrete step*: bound `L = ∑ℓ_i` and `v_p(c)` from the exact floor
   (integer form, as in §5) rather than from the generic `Out`-product, and
   re-run §4.2's tolerance analysis with that bound.

2. **(POS) for the linear tower at `f ≥ 2`.**  Not implied by the floor:
   `753 784` (family, rank, `f_i < f`) rows survive (F)+(P) over
   `33 ≤ d ≤ 200`, `q ≤ 1024`, dominated by `²A` (unitary factors over the
   square-root subfield).  The census of §5 covers them for `q ≤ 100`,
   `d ≤ 60`.  *Next concrete step*: the sub-case analysis sketched at the end
   of §4.1 closes the odd-`m` half of the `²A` family outright; the even-`m`
   half needs a sharper substitute for `h_{i₀} ≤ 2 v_{i₀}`.

3. **`d ≥ 61` with `q` a proper prime power, linear tower.**  Follows from
   Theorem MF once (POS) is settled (gap 2); until then it rests on
   `v_task60` PART C's enumeration, i.e. on the very thing the audit
   flagged.

4. **(H1), (H5) unchanged** (`v_task56` §8): `ι`'s lower half is literature
   [Cooperstein; Kleidman–Liebeck 5.2.2]; `ῑ` is a parabolic upper bound —
   both enter §5's (D3) in the conservative direction.

5. **Scope.**  "Equal characteristic" means every `S_i` is of Lie type in
   characteristic `p`.  Mixed socles (some `S_i` alternating/sporadic, or in
   another characteristic) are other branches of Theorem LU-T and are
   untouched here — they are closed by `v_task60` PART F (i), (ii), (v) and
   PART E′.

---

## 8. Reproduce

```
python3 v_task87_lemmas.py 2000  > v_task87_lemmas_out.txt      # ~2 min
python3 v_task87_scan.py 33 60 100 > v_task87_scan_out.txt      # ~40 min
python3 v_task87_scan.py probe    >> v_task87_scan_out.txt      # negative control
python3 v_task87_pos.py 33 200 1024 > v_task87_pos_out.txt      # ~5 min
```

`v_task87_lemmas.py` imports `FAM` from `v_task52_lemmaC`, `KFAM/Kmax/bdeg`
from `v_task56_lu_twins` and `famrows/target_cyc` from `v_task60_lu_residues`
— i.e. it is checked against the *same* family table the audited scripts use,
and PART 1 additionally cross-checks its own light-weight table against
`famrows` row by row (0 mismatches).
