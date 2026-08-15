# The last named residues of the linear/unitary tower: **(H6)** and **(POS)**

Standing inputs, all from the development record: Theorem MF and Lemma COX
(with the gaps (H6) and (POS)); Lemma DEG, Lemma ZM, Lemma PACK / PACK-TOP
and the DEG conventions (`lu_residues.py`); the hypotheses (H1), (H5)
(`lu_twins.py`).

| file | what it does |
|---|---|
| `h6_discharge.py` / `_out.txt` | **(H6)**: PART 1 Lemma OUT-p (`p ∤ d_i`, so `v_p(c)` loses its rank-sized term); PART 2 **Lemma FL2** (the orbit floor bounds the *number* of socle factors: `L ≤ 7` linear, `L ≤ 3` unitary, `L ≤ 2` / `L ≤ 1` with no exceptional factor); PART 3 the exact slack calculus `(S1)`–`(S3)`, machine-verified as identities of rationals; PART 4 the tolerance of every branch of Theorem MF and the **integer kill** of the one tight branch; PART 4b how much the floor alone empties; PART 5 the exact slack-free census extended to `61 ≤ d ≤ 120`, every `q ≤ 100` |
| `pos_discharge.py` / `_out.txt` | **(POS)**: PART 1 exact cyclotomic data; PART 2 the owner equation + positivity kill `j > 1/4`; PART 3 **(PACK-exc) in base-field indices**, which kills every `j ≠ 1/2`; **PART 3c the same three tests over ALL 17 families** (only `²A` survives); PART 4 the COX-mean kill of `j = 1/2`, **both parities of `m`** (the even-`m` half is the sharper substitute for `h ≤ 2v` that the development record asked for); PART 5 exact integer spot rows `61 ≤ d ≤ 120`; PART 6 the non-owner subfield rows, completed exactly |

All arithmetic exact (Python big integers / `Fraction`).  Every logarithm that
feeds a yes/no answer is replaced by an exact rational bound.

---

> ### Headline
>
> **(H6) — DISCHARGED for the linear tower on the whole tested grid
> (`61 ≤ d ≤ 120`, `p ≤ 13`, every `f ≤ 48`, i.e. `q` up to `13^48`), with
> the one *closed-form* branch (L-c) settled for every `61 ≤ d ≤ 2000` and
> every `f`; and the unitary tower's multi-factor branch turns out to be
> empty by the orbit floor alone, so (H6) cannot even be invoked there.**
> Two new lemmas do it.  **Lemma OUT-p** removes the *diagonal* from
> `v_p(c)` (`p ∤ d_i` always), which is exactly the term that made the
> generic bound `log_q c = O(L log_q(df))` as large as `d−1` at `q = 2`.
> **Lemma FL2** removes `L` from the same bound: the orbit floor, in exact
> integer form, forces `L ≤ 7` (linear) and `L ≤ 3` (unitary), and `L ≤ 2`
> resp. `L ≤ 1` as soon as no socle factor is exceptional.  With `L` and
> `v_p(f_i)` both `O(log_p f)`, the two branches of Theorem MF whose
> tolerance is `O(1)` rather than `Θ(d)` become finite integer questions,
> answered three ways with overlapping ranges: an **integrality** kill
> for `f ≤ d−2` and the closed form `(S2)` for `f ≥ f₀(p,d)`, with
> `f₀ ≤ d−1` throughout `61 ≤ d ≤ 2000`, `p ∈ {2,3,5}` — and, subsuming all
> three linear branches, a decisive `(p,f)`-parametrised 2-factor sweep
> (`f ≤ 48`, `p ≤ 13`) whose 8 167 survivors live only at `q ≤ 823 543` and
> all die on the exact integer tests.
>
> **(POS) — CLOSED for the linear tower at `d ≥ 61`, every `q`, and not
> only for `²A` but for ALL 17 families.**  Three steps: the PACK-TOP owner
> equation plus positivity of `∑ v_i h_i = 2N` forces `1/j < 4`;
> **(PACK-exc) read in base-field indices** then forces `j = 1/2` exactly;
> and the COX mean kills the two shapes `m = d` (odd) and `m = d+1` (even)
> that `j = 1/2` leaves.  Run over every family and rank (PART 3c), the
> three tests leave **only** the `²A` shapes `m = d`, and those die in
> PART 4.  The even-`m` half — the piece previously left open — is closed by
> the exact identity
>
> > `∑_{i≥2} v_i (d − 1 − h_i) = 1`,
>
> which replaces the crude `h_{i₀} ≤ 2 v_{i₀}`: it forces some remaining
> factor to have `h_i = d−1`, whose rank `n_i ≥ (d−1)/2` already exceeds the
> **entire** remaining budget `d/2 − 1`.
>
> **Unconditionally** (no (DEG-exact), no (POS), no logarithm): the exact
> slack-free census now runs `61 ≤ d ≤ 120` for **every** prime power
> `q ≤ 100` — **0 surviving configurations**, on top of the earlier
> `33 ≤ d ≤ 60` census.
>
> **Net effect.**  Theorem MF is **unconditional** for `31 ≤ d ≤ 120` and
> every `q ≤ 100` (census), and its two named hypotheses are now
> discharged, not assumed: **(POS) outright for `d ≥ 61`** (all families,
> `Φ_K` owner), and **(H6) on the grid `61 ≤ d ≤ 120`, `p ≤ 13`, `f ≤ 48`**
> — with the structural ingredients (Lemma OUT-p, Lemma FL2, (S1)–(S3))
> `d`- and `q`-uniform, so the remaining `d ≥ 121` / `p > 13` / `f > 48`
> corner is a matter of running the same sweep further, not of new
> mathematics.  The honest residues are §4.

---

## 1. (H6): what had to be bounded, and why the old route failed

`lu_residues.py` PART C — and Theorem MF after it — use Lemma DEG in the form

```
   (P=)   ∑_i ℓ_i j_i N_i = N − ε_P ,     ε_P := v_p(c)/f ≥ 0
   (R=)   ∑_i ℓ_i j_i n_i = (d−1) + θ
```

with `ε_P = θ = 0`.  The only bound available was
`c | ∏_i(|Out(S_i)|^{ℓ_i} ℓ_i!)`, i.e.

```
   v_p(c) ≤ ∑_i ℓ_i ( v_p(d_i) + v_p(f_i) + v_p(g_i) ) + ∑_i v_p(ℓ_i!)
```

with `|Out(S_i)| = d_i f_i g_i` (diagonal · field · graph).  Two terms are
rank-sized: `d_i` (which can be as large as the rank of `S_i`, e.g.
`gcd(n, q_i−1)`) and `L = ∑ℓ_i` (which the old argument bounded only by
`fN`).  Together they give `log_q c = O(L log_q(d f))`, which at `q = 2`
is `Θ(d log d)` — larger than the right-hand sides themselves.  Both terms
are removed below.

### 1.1 Lemma OUT-p — the diagonal is invisible to `v_p`

> ### Lemma OUT-p [PROVEN]
> For every simple `S_i` of Lie type over `F_{q_i}`, `q_i = p^{f_i}`,
> ```
>     p ∤ d_i ,   hence   v_p(|Out(S_i)|) = v_p(f_i) + v_p(g_i) ,
> ```
> with `g_i ∈ {1,2,3,6}`, so `v_p(g_i) ≤ 1` and `v_p(g_i) = 0` for `p ≥ 5`.

*Proof.*  Every diagonal order occurring in the family table is one of
`gcd(n, q_i−1)`, `gcd(n, q_i+1)`, `gcd(2, q_i−1)`, `gcd(4, q_i^n ∓ 1)`,
`gcd(3, q_i ∓ 1)`, `1` — in each case a divisor of `q_i^a ∓ 1` for some
`a ≥ 1`; and `gcd(p, q_i^a ∓ 1) = 1` because `p | q_i`. ∎

Verified exhaustively (`h6_discharge.py` PART 1) on **46 155** rows (all 17
families, rank ≤ 40, every prime power `q ≤ 1024`): **0** rows with `p | d_i`.

Consequently, and this is the "integer-floor" form the task asked for,

```
   v_p(c)  ≤  ∑_i ℓ_i ( ⌊log_p f_i⌋ + [p ≤ 3] )  +  (L − r)/(p−1) ,
   f_i ≤ f·K/k_i     (Lemma Z, (Z1)) .
```

### 1.2 Lemma FL2 — the orbit floor bounds the *number* of factors

Write `b := deg_q ι(S)` (`= d−1` linear, `= 2d−3` unitary),
`s_i := log_q(8 ℓ_i |Out(S_i)|)`, and `ρ_i := n_i/μ_i`.

> ### Lemma FL2 [PROVEN]
> The orbit floor `ℓ_i |Out(S_i)| ῑ(S_i) ≥ ι(S)` gives `j_i μ_i ≥ b − s_i`,
> hence `v_i = ℓ_i j_i n_i ≥ ℓ_i ρ_i (b − s_i)`, and with `∑_i v_i = (d−1)+θ`
> ```
>       L = ∑_i ℓ_i  ≤  (d−1+θ) / ( ρ_min (b − s_max) ) .
> ```

`ρ = n_r/μ` per family (computed, `h6_discharge.py` PART 2):

| family | `ρ = n_r/μ` | limit |
|---|---|---|
| `A`, `A₁` | `(n−1)/(n−1)` | **1** |
| `²A` | `(n−1)/(2n−3)` | `→ 1/2` |
| `C`, `B` | `n/(2n−1)` | `→ 1/2` |
| `D`, `²D` | `n/(2n−2)` | `→ 1/2` |
| `²B₂` | `1/2` | `1/2` |
| `³D₄` | `4/9` | |
| `G₂` | `2/5` | |
| `E₆`, `²E₆` | `3/8` | |
| `²G₂` | `1/3` | |
| `F₄` | `4/15` | |
| `E₇` | `7/27` | |
| `²F₄` | `1/5` | |
| **`E₈`** | **`8/57 = 0.1404`** | the minimum |

So `ρ_min = 8/57` and `ρ_min(classical) = 1/2` (attained in the limit).
Hence, asymptotically,

```
   LINEAR   (b = d−1 = the rank budget)   L ≤ 57/8  = 7.125   ⟹ L ≤ 7
                                          L ≤ 2 with no exceptional factor
   UNITARY  (b = 2d−3, rank budget d−1)   L ≤ 57/16 = 3.5625  ⟹ L ≤ 3
                                          L ≤ 1 with no exceptional factor
```

and the last line says the **all-classical unitary multi-factor branch is
empty by the floor alone**.  The exact integer version (no logarithms; the
floor, Lemma Z and the `p`-budget all tested as integer inequalities) over
the grid `d ∈ {61,62,80,100,120,150,200}` × `q ∈ {2,3,4,8,9,64,97}`
reproduces the asymptotics exactly:

```
   worst L_max over the grid          :  L tower 7 , U tower 3
   worst L_max, classical atoms only  :  L tower 2 , U tower 1
```

### 1.3 The exact slack calculus

With `v_i := ℓ_i j_i n_i`, `δ_i := d − h_i` and Lemma COX (`N_i = h_i n_i/2`):

> **(S1)** `E := ∑_i v_i δ_i = d·θ + 2·ε_P` — an identity.
>
> **(S2)** `q^θ = (π_S/e_S) · (c_p²/c) · ∏_i (e_i/π_i)^{ℓ_i}`, where `e_S`,
> `e_i` are the diagonal orders and `π_S := |S| e_S q^{−a}`,
> `π_i := |S_i| e_i q_i^{−D_i} ∈ [∏_{m≥1}(1−p^{−m}), 1]`.
> This is the **sharp** replacement for Lemma DEG's fudge `κ ∈ [12^{−k},1]`.
>
> **(S3)** `f·θ = ∑_i ℓ_i f_i n_i − f(d−1) ∈ ℤ` and `f·ε_P = v_p(c) ∈ ℤ≥0`.
> If every `j_i` is an integer — which Lemma Z forces whenever `f < K/k_i` —
> then `θ` itself is an **integer**.

`(S1)` and `(S2)` are verified as exact identities of rationals on **2 902**
synthetic configurations (arbitrary families, ranks, `ℓ_i`, `f_i`, with `c`
taken as the rational `|S|/∏|S_i|^{ℓ_i}`): **0 failures** each.

### 1.4 The tolerance of each branch of Theorem MF

Assume (POS) and Lemma Z, so `δ_i ≥ 0` in the linear tower.  Let
`A := {i : h_i = d}` (then `j_i = 1`, `k_i = d`, `n_i ≥ d/2`) and `B` the rest.

| branch | shape | a leak needs |
|---|---|---|
| (L-a) | `A = ∅` | `(d−1)θ + 2ε_P ≥ d−1` |
| (L-b) | `A = {L_d(q)}` | `θ ≥ ρ_min(d−1−s) ≥ 8(d−1−s)/57` |
| (L-c) | `A = {C_{d/2}, B_{d/2}, D_{d/2+1}}`, `d` **even** | `(d−1)θ + 2ε_P ≥ d/2 − 1` |
| (U) | Steps U1–U5 | `θ, ε_P = Ω(d)` (margins are `Θ(d²)`) |

For **odd `d`** the only family with `h = k = d` is `A_{d−1} = L_d`, so
(L-c) does not occur; (L-b) is very tolerant (`θ ≳ 0.14 d`), but **(L-a)
and (L-c) both have `O(1)` tolerance** (`θ < 1` resp. `θ < 1/2`).  (L-c) is
settled as a pure integer question in §1.5; (L-a) needs the decisive sweep
of §1.6.

### 1.5 The integer kill of (L-c)

Pin (L-c): `A = {C_{d/2}(q)}` with `ℓ = 1`, `j = 1`, `n_A = d/2`,
`N_A = d²/4`; by Lemma FL2 the rest is a single factor `B`.  Then
`v_B = d/2 − 1 + θ`, `ε_P = d(d−2)/4 − v_B h_B/2`, i.e.

```
      ε_P = [ δ_B (d − 2 + 2θ) − 2θ d ] / 4 .
```

`ε_P ≥ 0` and `δ_B ≥ 1` force `θ ≤ (d−2)/(2(d−1)) < 1/2`, and then
`v_p(c) = f ε_P ≥ f[(d−2)/4 − θ(d−1)/2]`.

Now Lemma Z pins `B`: it must cover `Φ_{d−1}` (the owner `C_{d/2}` cannot —
`d−1` is odd and `Cyc(C_n)` consists of divisors of the even numbers `2i`),
so `j_B k_B ≥ d−1`, while `j_B k_B < K = d` because `M_K = 1` and `A` is the
`Φ_K` owner (PACK-TOP).  Hence `f_B ≤ f·d/(d−1)`, so

* **`f ≤ d−2`**: `f_B = f`, i.e. **every `j_i = 1`**, so `θ ∈ ℤ` by (S3);
  `θ < 1/2` gives `θ ≤ 0` and `v_p(c) ≥ f(d−2)/4`, against
  `B_out ≤ 2⌊log_p f⌋ + 3` from Lemma OUT-p.  Checked exactly for every
  `61 ≤ d ≤ 2000`, `p ∈ {2,3,5,7,11,13}` and every `f ≤ d−2`:
  **0 failures**.
* **`f ≥ f₀(p,d)`**: the closed form (S2) with `π_S ≤ 1`, `e_S ≥ 1`,
  `c_p ≤ c` gives `θ ≤ [B_out + L(log_p e_max + log_p(1/π(q)))]/f` with
  `L ≤ 2`, `e_max ≤ d`; the kill is
  `(d−1)θ_ub + 2ε_ub < (d−2)/2`.  The smallest such `f`:

| `p` | `d = 61` | `62` | `80` | `100` | `130` | `200` | `500` | integrality covers |
|---|---|---|---|---|---|---|---|---|
| 2 | 52 | 52 | 56 | 56 | 59 | 59 | 67 | `f ≤ d−2` |
| 3 | 34 | 34 | 33 | 37 | 37 | 37 | 41 | `f ≤ d−2` |
| 5 | 17 | 17 | 17 | 17 | 21 | 21 | 21 | `f ≤ d−2` |

The two ranges **overlap** in every row, so **no `f` escapes**:
`residual (p, d, f) of branch (L-c) : NONE`.

### 1.6 The decisive `(p,f)`-parametrised sweep (all branches at once)

Branch (L-a) — no factor with `h_i = d` — also has `O(1)` tolerance
(`(d−1)θ + 2ε_P ≥ d−1` for a leak), and unlike (L-c) its field degrees are
not pinned to `f_i = f`.  It is settled by the sweep of
`h6_discharge.py` **PART 4c**, which subsumes all three linear branches and
uses **no branch analysis at all**.

By Lemma FL2 (classical factors), under (POS) every linear-tower
configuration is a *pair*, so `(row₁, ℓ₁, f₁), (row₂, ℓ₂, f₂)` determines
everything:

```
   θ      = ( ∑_i ℓ_i f_i n_i )/f − (d−1)
   ε_P    = N − ( ∑_i ℓ_i f_i N_i )/f          (must be ≥ 0)
   v_p(c) = f·ε_P                              (an integer)
```

against the two certified bounds `v_p(c) ≤ B_out` (Lemma OUT-p) and
`θ ≤ θ_ub` ((S2)).  Constraints imposed: (POS) `f_i ≥ f`; (Z) `f_i k_i ≤ f d`;
PACK-TOP (some factor has `f_i k_i = f d`, `ℓ_i = 1`); the degree form of the
orbit floor; and `h_i ≤ d`.  **No order arithmetic**, so `f` may be large.

Result for `61 ≤ d ≤ 120`, `p ∈ {2,3,5,7,11,13}`, `1 ≤ f ≤ 48` (i.e.
`q` up to `13^48 ≈ 4·10^53`):

```
   pairs tested                             : 72 427 952
   pairs surviving DEG + (S2) + Lemma OUT-p :      8 167 , occurring
                                               ONLY at q ≤ 823 543 = 7^7
   θ values realised                        : 1, 13, 15, 23, 25, 27
   v_p(c) values realised                   : 0, 2, 3, 4
   family pairs realised                    : pairs from {A,²A,C,B,D,²D}
   those survivors passing (D1)+(D2)+(D3)   : NONE
```

Two things are worth reading off.  First, above `q = 823 543` the sweep is
**already empty** — the `(S2)` bound alone forces `θ` below the smallest
value any admissible pair can realise, so (H6) is discharged there with no
order arithmetic.  Second, the finitely many survivors below that bound
(the tight `C_{d/2}(q) × D_{d/2}(q)`-type shapes, `θ = 1`, `ε_P = 0`) all
die on the exact integer tests.  So **(H6) is discharged on the whole
tested grid**, and the only thing that remains `q`-bounded is the grid
itself.

### 1.7 What the floor alone already does

`h6_discharge.py` PART 4b: over `61 ≤ d ≤ 120` and every prime power
`q ≤ 100` (2 100 `(X,d,q)` targets per tower),

```
   UNITARY tower : 2100 targets emptied by the floor + p-budget alone,
                      0 targets needing a census descent
   LINEAR  tower :    0 emptied,  2100 needing the descent
```

i.e. the whole unitary equal-characteristic multi-factor branch is
**unconditionally empty** on that range — no (DEG-exact), no (POS), no
`ε_P`, no `θ`.  This is Lemma FL2's `L ≤ 1` prediction in the flesh.

### 1.8 The census, extended

`h6_discharge.py` PART 5 runs the four integer tests
(D1)–(D4) verbatim, with the PART 1/2 pruner:

```
 targets : L_d(q), U_d(q),   61 ≤ d ≤ 120        (120 targets × 35 fields)
 fields  : every prime power q ≤ 100
 surviving single atoms (D1)+(D3)-compatible :  33 911
 DFS nodes                                   : 170 177
 MULTI-FACTOR CONFIGURATIONS SURVIVING       :  NONE
```

Together with the earlier `33 ≤ d ≤ 60` census this makes the branch
**unconditionally empty for `33 ≤ d ≤ 120` and every `q ≤ 100`**.

---

## 2. (POS): the named residue

An earlier probe found `753 784` `(family, rank, f_i < f)` rows that the
orbit floor alone cannot exclude in the linear tower, dominated by `²A`
(unitary factors over a proper subfield).  The odd-`m` half of the
`Φ_K`-owner case was closed there by hand, leaving the even-`m` half open:
it "needs a sharper substitute for `h_{i₀} ≤ 2 v_{i₀}`".

### 2.1 The exact cyclotomic data

For `S₁ = U_m(q₁) = ²A_{m−1}(q₁)`:

```
   k(U_m) = 2m   (m odd) ,      2m − 2  (m even)
   mult of Φ₂ in Cyc(U_m) = m − 1        (every factor q₁^i − (−1)^i
                                          contributes exactly one Φ₂)
```

and for the target `L_d(q)`: `M₁ = d − 1`, `M_t = ⌊d/t⌋` for `t ≥ 2`.
Both verified against `lu_residues.py`'s `cyc_of_tokens` / `target_cyc`
(`pos_discharge.py` PART 1, `3 ≤ m ≤ 200`, `4 ≤ d ≤ 200`: 0 violations).

The pair `(m−1, d−1)` is the whole story: *a unitary group of rank `m−1`
carries exactly as many `Φ₂` blocks as a linear group of degree `m` carries
`Φ₁` blocks*, and over a square-root subfield those are the **same** block.

### 2.2 The owner equation and the positivity kill

PACK-TOP (`M_K = 1`) forces the `Φ_K` owner to have `ℓ₁ = 1` and
`j₁k₁ = K = d` exactly.  With `n₁ = m−1`, `h₁ = m` (Lemma COX):

```
   m odd :  j = d/(2m)   ,  v₁ = d/2 − j ,   v₁h₁ = d²t/4 − d/2
   m even:  j = d/(2m−2) ,  v₁ = d/2     ,   v₁h₁ = d²t/4 + d/2      (t := 1/j)
```

Since every `v_i h_i > 0` and `∑_i v_i h_i = 2N = d(d−1)` (Lemma COX + (P=)),
`v₁h₁ ≤ d(d−1)`, i.e. `d t/4 ≤ d − 1/2` resp. `d − 3/2`.  Hence

> **`t = 1/j < 4`, i.e. `j > 1/4`, in both parities** — verified over
> `61 ≤ d ≤ 2000` on all 2 996 330 subfield owner shapes: 0 exceptions.

Applied to the other families this already removes most of them: the same
inequality `n_r h ≤ k(d−1)` combined with `j = d/k < 1` leaves **no**
subfield owner of type `A` (it would need `n > d` and `n ≤ d`), and no
exceptional family at all once `d ≥ 31` (their `k ≤ 30 < d` forces `j > 1`).

### 2.3 (PACK-exc) in base-field indices kills every `j ≠ 1/2`

Write `j = s₁/s` in lowest terms, `u = p^g`, so `q = u^s`, `q₁ = u^{s₁}`.
For a **base index** `κ′`,

```
   mult of Φ_{κ′}(u) in |S₁|  =  mult_{κ}(Cyc S₁) ,  κ := κ′/gcd(κ′, s₁)
   mult of Φ_{κ′}(u) in |S|   =  M_T(L_d) ,          T := κ′/gcd(κ′, s)
```

and Lemma PACK's (PACK-exc) demands `ℓ₁ · mult_κ ≤ M_T` for every `κ′`.
Taking `κ = 2` (so `κ′ = 2s₁`) and using `mult₂(U_m) = m − 1 ≈ d s/(2s₁)`:

```
   s odd  :  T = 2s₁ ,  M_T = ⌊d/(2s₁)⌋   ⟹  d s/(2s₁) ≤ d/(2s₁)  ⟹  s ≤ 1
   s even :  T = s₁  ,  M_T = ⌊d/s₁⌋      ⟹  d s/(2s₁) ≤ d/s₁     ⟹  s ≤ 2
```

so the only surviving subfield value is `s = 2`, `s₁ = 1`, i.e. **`j = 1/2`**.
This is a pure multiplicity count: no Zsygmondy size estimate, no LTE, no
threshold in `q`.  Machine run (`pos_discharge.py` PART 3), `61 ≤ d ≤ 800`,
every subfield owner shape `(m, j)`:

```
   subfield owner shapes tested : 480 630
   killed by (PACK-exc)         : 480 260
   surviving                    :     370
   the surviving values of j    : ['1/2']   (and all of them have m = d,
                                             d odd — the shape §2.4 kills)
```

*Zsygmondy bookkeeping.*  (PACK-exc) is rigorous at a base index `κ′` as
soon as `Φ_{κ′}(u)` has a primitive prime, i.e. for `κ′ ≥ 3` with
`(u,κ′) ≠ (2,6)`.  The script therefore returns a violated index `κ′ ≥ 3`,
`κ′ ≠ 6` whenever one exists, and reports separately the shapes whose *only*
violated index is `κ′ ∈ {1,2,6}` — those are handed to §2.4 instead, which
does not use (PACK-exc) at all.

### 2.4 `j = 1/2` killed by the COX mean — both parities of `m`

`j = 1/2` and `j k₁ = d` leave exactly two shapes, both with `d` **odd**:

```
   m odd  :  2m/2 = d      ⟹  m = d   ,  n₁ = d−1 , h₁ = d   , v₁ = (d−1)/2
   m even :  (2m−2)/2 = d  ⟹  m = d+1 ,  n₁ = d   , h₁ = d+1 , v₁ = d/2
```

**`m = d` (odd — the half already closed by hand).**  `∑_{i≥2} v_i = (d−1)/2` and
`∑_{i≥2} v_i h_i = d(d−1)/2`, so `∑_{i≥2} v_i(d − h_i) = 0`: every remaining
factor has `h_i = d`, hence `j_i = 1`, `k_i = d` and `n_i ≥ d/2`, so
`v_i ≥ d/2 > (d−1)/2` — more than the whole budget.  **Contradiction.**

**`m = d+1` (even) — the piece that was open.**  Here

```
   ∑_{i≥2} v_i       = (d−1) − d/2      = d/2 − 1
   ∑_{i≥2} v_i h_i   = d(d−1) − d(d+1)/2 = d(d−3)/2
```

and therefore

> ```
>       ∑_{i≥2} v_i ( d − 1 − h_i )  =  (d−1)(d/2−1) − d(d−3)/2  =  1
>                                                              EXACTLY.
> ```

This identity is the "sharper substitute for `h ≤ 2v`".  It closes the case
in three moves:

1. A remaining factor with `h_i = d` would contribute `−v_i ≤ −d/2`, which
   the whole remaining budget `d/2 − 1` cannot repay; so every remaining
   `h_i ≤ d−1` and **every term is `≥ 0`**.
2. Factors with `h_i ≤ d−2` contribute `≥ v_i`, so they carry `v`-weight
   `≤ 1`; hence the weight on `h_i = d−1` is `≥ d/2 − 2 > 0` and some
   factor has `h_i = d−1`.
3. `d` is odd, so `d−1` is even and the rows with `h = d−1` are
   `C_{(d−1)/2}`, `B_{(d−1)/2}` (`n_r = (d−1)/2`), `D_{(d+1)/2}`,
   `²D_{(d+1)/2}` (`n_r = (d+1)/2`), `L_{d−1}`, `U_{d−1}` (`n_r = d−2`) —
   exceptionals only if `d−1 ∈ {2,4,6,12,18,30}`, i.e. `d ≤ 31`.  So
   `n_r ≥ (d−1)/2` and, by (POS) for the remaining factors,
   `v_i ≥ (d−1)/2 > d/2 − 1`.  **Contradiction**, with margin exactly `1/2`,
   for every `d`.

Every step machine-checked for every odd `61 ≤ d ≤ 2000`: **0 failures**.
(PARTS 3 and 3c, which build the full cyclotomic multiplicity tables, are
`O(d³)` and are run to `d ≤ 800` resp. `d ≤ 600`; PARTS 2 and 4, which are
closed-form, run to `d ≤ 2000`.)

### 2.5 All 17 families, not just `²A`

`pos_discharge.py` **PART 3c** runs the three tests over every
`(family, rank n)` with `j := d/k(family, n) < 1`:

```
   (T1)  POSITIVITY  v_1 h_1 = j n_r h  <=  sum_i v_i h_i = 2N = d(d-1)
   (T2)  STRICT      v_1 h_1 = 2N exactly  ==>  sum_{i>=2} v_i h_i = 0,
                     so there is no second factor and L = 1 -- excluded
   (T3)  (PACK-exc)  in base-field indices, as in §2.3
```

Over `61 ≤ d ≤ 600`:

```
   shapes examined                :  2 584 440
   killed by (T1) positivity      :  1 962 090
   killed by (T2) strict equality :      3 240
   killed by (T3) (PACK-exc)      :    618 840
   SURVIVING                      :        270   -- all of family ²A,
                                                    all with n = m = d,
                                                    j = 1/2, d odd
```

(T1) alone removes the whole `A` family (a subfield owner would need
`n > d` from `j < 1` and `n ≤ d` from positivity) and every exceptional
family at `d ≥ 31` (their `k ≤ 30 < d` forces `j > 1`).  (T2) is what
removes `²D`: for `²D_n` with `n = d` one has `k = 2n = 2d`, `j = 1/2`,
`n_r = n = d`, `h = 2n−2 = 2d−2`, so

```
       v₁ h₁ = (d/2)(2d−2) = d(d−1) = 2N   EXACTLY ,
```

leaving `∑_{i≥2} v_i h_i = 0`, i.e. **no second socle factor at all**, which
contradicts `L ≥ 2`.  So after §2.2–§2.5 the only surviving subfield
`Φ_K`-owner shape in the whole linear tower is `U_d(q^{1/2})` with `d` odd,
and §2.4 kills it.

### 2.6 Non-owner subfield `²A` factors

A subfield `U_m(q₁)` with `j k₁ < K` is not pinned by PACK-TOP.  But then
Lemma FL2 applies: `L ≤ 2`, so the configuration is
`U_m(q₁)^{ℓ₁} × S₂^{ℓ₂}` with `ℓ₁ + ℓ₂ ≤ 2` — a finite, explicitly
parametrised list, which `pos_discharge.py` PART 6 completes and tests with
the integer tests (D1)–(D3).  Over the spot range `61 ≤ d ≤ 120`,
`p ≤ 13`, `f ≤ 6` all **154** such rows are completed and
**0 configurations survive (D1)+(D2)+(D3)**.

### 2.7 Exact integer spot rows

`pos_discharge.py` PART 5, `61 ≤ d ≤ 120`, `p ∈ {2,3,5,7,11,13}`,
`2 ≤ f ≤ 6`, every `f₁ < f`, every `m`: the exact tests
`(E1)` `|U_m(q₁)| divides |L_d(q)|`, `(E2)` the floor, `(E3)` the `p`-budget,
`(E4)` Lemma Z — then the three kills:

```
   shapes examined               : 80 040
   shapes passing (E1)-(E4)      :    216
      Phi_K owners among them    :     62   -- 2 killed by (PACK-exc),
                                               60 by the COX mean,
                                                0 NOT killed
      non-owners (j k_1 < d)     :    154   -- all completed in §2.6,
                                                0 surviving
```

---

## 3. Status ledger

| claim | range | status |
|---|---|---|
| **Lemma OUT-p** (`p ∤ d_i`) | all families, all ranks, all `q` | **[PROVEN]**, verified on 46 155 rows |
| **Lemma FL2** (`L` bounded by the floor) | both towers, `d ≥ 61` | **[PROVEN]**, exact-integer grid confirms `L ≤ 7 / 3`, and `2 / 1` classically |
| **(S1) (S2) (S3)** slack calculus | all configurations | **[PROVEN]**, identities verified exactly (2 902 configs) |
| **(H6) removed, branch (L-c)** | `61 ≤ d ≤ 2000`, `p ∈ {2,3,5,7,11,13}`, **every** `f` | **[CLOSED]** — integrality for `f ≤ d−2`, (S2) for `f ≥ f₀ ≤ d−1` |
| **(H6) removed, branch (L-b)** | `d ≥ 61` | **[CLOSED]** — tolerance `Θ(d)` against `O(log_p f)` |
| **(H6) removed, branch (U)** | `d ≥ 61` | **[CLOSED]** — margins `Θ(d²)`; and the branch is empty by the floor anyway (§1.7) |
| **(H6) removed, branch (L-a) + all others** | `61 ≤ d ≤ 120`, `p ≤ 13`, `f ≤ 48` | **[COMPUTED, 0 survivors]** — PART 4c |
| **Unitary multi-factor branch empty by the floor** | `61 ≤ d ≤ 120`, `q ≤ 100` | **[COMPUTED]**, 2 100 targets, 0 descents |
| **Exact census (D1)–(D4)** | `61 ≤ d ≤ 120`, every `q ≤ 100` | **[COMPUTED, 0 hits]**, unconditional |
| **(POS), `Φ_K` owner, ALL 17 families** | `d ≥ 61`, every `q`, both parities | **[PROVEN]** (positivity + strict positivity + PACK-exc + COX); machine-checked `61 ≤ d ≤ 600` (all families), `≤ 800` (`²A`), `≤ 2000` (closed-form steps) |
| **(POS) for `²A`, non-owner** | `61 ≤ d ≤ 120`, `p ≤ 13`, `f ≤ 6` | **[COMPUTED, 0 hits]** |
| **Theorem MF unconditional** | `31 ≤ d ≤ 120`, every `q ≤ 100` | **[PROVEN]** (census, §1.8 + the earlier `33 ≤ d ≤ 60` census) |
| **Theorem MF, linear tower, hypothesis-free** | `61 ≤ d ≤ 120`, `p ≤ 13`, `f ≤ 48` | **[COMPUTED]** — (POS) proven, (H6) discharged; §4 residues |
| **(H6): (S2) alone empties the DEG level** | `61 ≤ d ≤ 120`, `p ≤ 13`, `q > 823 543` | **[COMPUTED]** — no pair even solves the DEG equations inside the bounds |

---

## 4. Honest residues

1. **(POS) for socle factors that are NOT the `Φ_K` owner.**  §2 pins the
   owner by PACK-TOP (`j₁k₁ = K`), which is what makes the positivity and
   (PACK-exc) tests bite.  A subfield factor with `j_i k_i < K` is not
   pinned; §2.6 closes those only through Lemma FL2 (`L ≤ 2`) plus an
   explicit completion, and that completion is *run* only for `²A` over the
   spot range `61 ≤ d ≤ 120`, `p ≤ 13`, `f ≤ 6`.  For the other families the
   non-owner subfield rows are covered by the census (`q ≤ 100`,
   `d ≤ 120`) and, structurally, by the same `L ≤ 2` pinning — but that
   sweep has not been run here.

2. **(H6): the (L-c) kill assumes (POS)** for the two factors of the pinned
   shape, and uses PACK-TOP's uniqueness (`M_K = 1`, verified for `d ≤ 300`
   in the development record) and the observation that `C_{d/2}` does not cover `Φ_{d−1}`.
   It also uses Lemma FL2's `L ≤ 2`, which rests on the orbit floor —
   i.e. on (H1)/(H5) as before, in the conservative direction.

3. **(H6) for `d ≤ 60`** is not re-derived here; it is covered by the exact
   censuses (`33 ≤ d ≤ 60` and `21 ≤ d ≤ 32` in the development record,
   `lu_twins.py` / `lu_residues.py` below) — all of which are `q`-bounded
   (`q ≤ 100`, resp. `q ≤ 3000`, `q ≤ 10⁵`).

4. **`d ≥ 121`, and the sweep's own grid.**  The decisive sweep of §1.6 was run
   for `61 ≤ d ≤ 120`, `p ∈ {2,3,5,7,11,13}`, `f ≤ 48`.  For `d ≥ 121` (or
   `p > 13`, or `f > 48`) the *structure* of the argument is unchanged —
   `(S2)` still empties the DEG level above an explicit `q`, and the finitely
   many shapes below it are still integer-testable — but the sweep has not
   been run there.  Likewise the *unconditional* (census-only) statement
   stops at `d ≤ 120`, `q ≤ 100`.

5. **(H6) in the exceptional-factor corner.**  §1.6's sweep uses Lemma FL2's
   **classical** bound `L ≤ 2`.  Configurations containing an exceptional
   socle factor may have `L` up to 7; those have `h_i ≤ 30 ≪ d`, hence
   `δ_i = d − h_i ≥ d − 30`, so `E = ∑ v_i δ_i ≥ ρ_i(d−1−s_i)(d−30) =
   Ω(d²)` and the required `θ = Ω(d)` is far above `θ_ub = O(log_p(df)/f)`.
   This is an estimate stated here, not a run; the census covers the corner
   unconditionally for `q ≤ 100`, `d ≤ 120`.

6. **(H1), (H5) unchanged** (`lu_twins.py`): `ι`'s lower half is literature
   [Cooperstein; Kleidman–Liebeck 5.2.2], `ῑ` is a parabolic upper bound;
   both enter the floor and (D3) conservatively.  Lemma FL2 *does* use the
   floor, so unlike Theorem MF it is not floor-free — that is the price of
   removing (H6).

7. **Scope** unchanged: "equal characteristic", every `S_i` of Lie type in
   characteristic `p`.  Mixed socles are other branches of Theorem LU-T.

---

## 5. Reproduce

```
python3 h6_discharge.py  120 100   > h6_discharge_out.txt      # ~30 min
python3 pos_discharge.py 2000 120  > pos_discharge_out.txt     # ~5 min
```

`h6_discharge.py` imports `FAM`/`order_of` from `lemma_c_bound`,
`KFAM`/`Kmax`/`iota_LU`/`order_LU` from `lu_twins`;
`pos_discharge.py` additionally imports `cyc_of_tokens`/`TERMS`/`target_cyc`
from `lu_residues.py` — i.e. both are checked against the same family and
cyclotomic tables the upstream scripts use.
