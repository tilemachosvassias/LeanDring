# v_task64 — Theorem BC3 REPAIRED, and generalised to all `n ≥ 3`:
# the separation is by a single `ind*` VALUE, not by `mult₁`

Date 2026-08-08.  Scripts `v_task64_bc3_repair.g` (GAP 4.16),
`v_task64_bc3_repair.py`; outputs `v_task64_bc3_repair_out.txt`,
`v_task64_bc3_repair_py_out.txt`.  **NOTES.md not edited** (per brief).

---

## 0. Headline

The brief's first item — "compute `ι₂` on both sides, it might make the psn
route unnecessary" — **succeeded, but not through `ι₂` and not through
parabolics.**

`ι₂` *as a min-of-parabolic-indices* would have tied: `B₃` and `C₃` are
polar spaces of rank 3 with the *same* parameters `(q, 1)`, so **every**
parabolic index of `Ω₇(q)` equals the corresponding index of `Sp₆(q)`.  The
brief's suggested `[Sp₆:P₂] vs [Ω₇:P₂]` comparison is a tie, identically in
`q`, and so is `[·:P₃]`.  The separation comes from a **non-parabolic**
`ind*` value that exists on the orthogonal side and cannot exist on the
symplectic side:

> ### Theorem BC-n [PROVEN, unconditional, all `n ≥ 3`, all odd `q`]
>
> Let `q` be odd, `n ≥ 3`.  Put `ι₁ = (q^{2n} − 1)/(q − 1)` and
> `v_ε = q^n(q^n − ε)/2` for `ε ∈ {+1, −1}`.  Then for exactly one `ε`
> (determined by `disc(V)`, see §2)
>
> * `v_ε ∈ I(B_n(q))` — witnessed by the abelian subgroup `⟨z_e⟩`,
>   `z_e = −r_e` for an anisotropic point `⟨e⟩`;
> * `v_ε ∉ I(C_n(q))` — because every element of `I(PSp_{2n}(q))` below
>   `q^{2n}` is divisible by `ι₁`, and `ι₁ ∤ v_ε`.
>
> Hence `I(B_n(q)) ≠ I(C_n(q))`, the conductor multisets differ, and
> **`D(B_n(q)) ≇ D(C_n(q))`**.
>
> **No (PAR).  No Lemma GLUE.  No psn census.  No `S`-table.  No BHR
> rebuild.  Uniform in `n`.**

This supersedes the whole `mult₁`/`Δ(q)` route for `B/C`.  Since the only
obstruction left in the symplectic/orthogonal towers after v_task59 was the
`B_n ≅_{order} C_n` simple–simple pair, **that pair is now closed**, and with
it `Sp_{2n}(q)` and `Ω_{2n+1}(q)` are D-rigid among all finite groups for
every `n ≥ 3` and every `q` (`q` even is vacuous: `B_n(2^f) ≅ C_n(2^f)`).

---

## 1. The invariant

Notation of §4aj/§4ba.  For `1 ≠ H ≤ G`,

```
ind*(H) = |G|·|H'| / |N_G(H)|,        I(G) = { ind*(H) : 1 ≠ H ≤ G }.
```

By Müller Satz 2.3.3 the pair `(H, H')` has conductor `|N_G(H)|/|H'|`, so
`I(G)` is read off the conductor multiset of `D(G)` together with `|G|`
(order transfer).  `conductorMultiplicity_eq_of_ringEquiv` is
kernel-checked, so **`I(G)` is a `D`-invariant** — the same footing on
which `ι = min I` and `κ` already stand.  For **abelian** `H`, `H' = 1` and
`ind*(H) = [G : N_G(H)]`; both witnesses below are abelian, so the (AB)
convention is not consumed beyond what §4ba already uses.

---

## 2. The orthogonal witness `v_ε ∈ I(Ω_{2n+1}(q))`

Let `V = 𝔽_q^{2n+1}` with quadratic form `Q`, `S = Ω(V) = Ω_{2n+1}(q)`,
`q` odd.  For an anisotropic vector `e` put

```
z_e := −r_e   ( +1 on ⟨e⟩,  −1 on e^⊥ ),   det z_e = (−1)^{2n} = 1.
```

`z_e` is the product of the `2n` reflections in an orthogonal basis of
`e^⊥`, so `θ(z_e) = disc(e^⊥) ≡ disc(V)·Q(e)` mod squares.  The two
`SO`-orbits of anisotropic points are the two square classes of `Q(e)`, so

> **exactly one** of the two classes has `z_e ∈ Ω(V)`.

For that class, `H = ⟨z_e⟩ ≅ C₂` is abelian, and

```
N_S(H) = C_S(z_e) = Stab_S(⟨e⟩),
ind*(H) = [S : Stab_S(⟨e⟩)] = |orbit of ⟨e⟩| = q^n(q^n − ε)/2 =: v_ε,
```

the orbit being a full square class of anisotropic points (`Stab_{SO}(⟨e⟩)
≅ O_{2n}^ε(q) ⊄ Ω`, so the `SO`-orbit does not split).  The two classes
have sizes `q^n(q^n−1)/2` and `q^n(q^n+1)/2`, summing to `q^{2n}` = the
number of anisotropic points.

**GAP verification** (`v_task64_bc3_repair.g` PART A, `Ω(7,q)` as a matrix
group, orbits on projective points computed outright):

| `q` | orbit, `Q(e)` square | orbit, `Q(e)` nonsquare | `z_e ∈ Ω` for | `|C_S(z_e)|` | `ind*` | `ι₁` |
|---|---|---|---|---|---|---|
| 3 | 378 | 351 | **nonsquare** | 13 063 680 | **351** | 364 |
| 5 | 7 875 | 7 750 | **square** | 29 016 000 000 | **7 875** | 3 906 |
| 7 | 58 996 | 58 653 | **nonsquare** | 4 662 288 691 200 | **58 653** | 19 608 |
| 9 | 266 085 | 265 356 | **square** | 203 039 372 390 400 | **266 085** | 66 430 |

In every case `z_e² = 1`, `det z_e = 1`, `[S : C_S(z_e)] = |orbit|`, and
`q^n(q^n ∓ 1)/2` reproduce the orbit sizes exactly.  Note that **which** `ε`
is realised is not constant in `q` (nonsquare at `q = 3, 7`, square at
`q = 5, 9`) — irrelevant, since the exclusion in §3 holds for both values.

*(The `q = 3` row is the KL 5.2.2 exception: `351 < 364`, i.e. the minimal
faithful degree of `Ω₇(3)` is 351, not `[Ω₇(3):P₁] = 364`.  So at `q = 3`
even `ι₁` already separates.  For `q ≥ 5`, `v_ε > ι₁` and `ι₁` ties, exactly
as Lemma SPO-ι says.)*

---

## 3. The symplectic exclusion

> **Lemma C-below.**  Let `q` be odd, `n ≥ 3`, `S = PSp_{2n}(q)`.  Every
> `x ∈ I(S)` with `x < q^{2n}` is divisible by `ι₁ = (q^{2n}−1)/(q−1)`.

*Proof.*  Let `1 ≠ H ≤ S` with `ind*(H) = [S:N_S(H)]·|H'| < q^{2n}`.  Then
`[S:N_S(H)] < q^{2n}`, and `N_S(H) ≠ S` (`S` simple, `H = S` gives
`ind* = |S|`).  So `N_S(H)` lies in a maximal subgroup `M` with
`[S:M] < q^{2n}`.  The only such `M` is `P₁` (below), whence
`ι₁ = [S:P₁]` divides `[S:N_S(H)]` divides `ind*(H)`. ∎

**The maximal-subgroup step, checked exactly** (`v_task64_bc3_repair.py`
STEP (C), all `n ∈ [3,8]` and all odd prime powers `q < 200`, **318 pairs,
0 violations**), class by class:

| Aschbacher class | index (or lower bound) | `≥ q^{2n}`? |
|---|---|---|
| `P₁` | `(q^{2n}−1)/(q−1)` | `< q^{2n}` — **the one exception** |
| `P₂` | `~q^{4n−5}` | yes for `n ≥ 3` |
| `P_n` (Siegel) | `∏_{i=1}^{n}(q^i+1) ~ q^{n(n+1)/2}` | yes for `n ≥ 3` |
| `P_k`, `2<k<n` | concave in `k`, min at the ends | yes |
| `C₁` `Sp_{2m} ⊥ Sp_{2n−2m}` | `~q^{4m(n−m)} ≥ q^{4n−4}` | yes |
| `C₂` `GL_n(q).2`, `Sp_{2m} ≀ S_t` | `~q^{n²+n}`, `~q^{2n²−2n}` | yes |
| `C₃` `Sp_{2n/r}(q^r).r`, `GU_n(q).2` | `~q^{n²+n}` and up | yes |
| `C₅` subfield | `~q^{n(2n+1)/2}` and up | yes |
| `C₆` `2^{1+2n}.O^-_{2n}(2)` | huge | yes |
| `S` | `n ≥ 4`: Liebeck `|M| < q^{6n}`; `n = 3`: BHR 8.28/8.29 explicit list | yes |

Two honest notes on this table.

* **`n = 3` is the tight case in two places.**  (i) `[Sp₆:P₃] = (q³+1)
  (q³+q²+q+1) = q⁶ + q⁵ + q⁴ + 2q³ + q² + q + 1 > q⁶` — true, but only by
  the lower-order terms; this is the closest call in the whole argument and
  it is an exact polynomial identity, not a numerical accident.
  (ii) Liebeck's generic `S`-bound `|M| < q^{3d} = q^{18}` is **too weak**
  against `|Sp₆(q)| ~ q^{21}` (it only gives index `> q³`).  For `n = 3` the
  script therefore uses the **explicit BHR Table 8.28/8.29 list** instead:
  the `S`-members of `Sp₆(q)`, `q` odd, are `2.L₂(q) = Sym⁵SL₂(q)`
  (order `q(q²−1)`), `SL₂(13)`, `2.L₂(7)`, `2.A₇`, `2.U₄(2)`, `6.L₃(4)`,
  `2.J₂` — so `|M| ≤ 4f·max(q(q²−1), 1 209 600)` and the index is
  `≫ q⁶` for every `q ≥ 3`.  **This is the only place the BHR tables are
  needed at all, and it needs only their ORDERS, not their class counts,
  fusion, or spinor norms.**  (Amusingly, the `Sym⁵SL₂(q)` member whose
  omission broke v_task62 reappears here — as a harmless order bound.)
* For `n ≥ 4` Liebeck's bound suffices: `q^{2n²+n−6n} ≥ q^{2n}` iff
  `2n² ≥ 7n`, i.e. `n ≥ 4`.

PART C of the GAP script cross-checks the maximal-subgroup step at `q = 3`
from ATLAS straight-line programs: for `S6(3)` the stored maxes give
indices `364` (`= P₁`, the only one below `q⁶ = 729`) and `1120` (`= P₃`).
`O7(3)` has no stored `maxes` SLPs in this AtlasRep installation, which is
harmless — the orthogonal side needs only the *witness*, not an exclusion.

---

## 4. The exclusion `ι₁ ∤ v_ε`

`gcd(ι₁, q) = 1` and `ι₁ ≥ q^{2n−1} > (q^n+1)/2 ≥ (q^n − ε)/2`.  Since
`v_ε = q^n·(q^n−ε)/2`, `ι₁ | v_ε` would force `ι₁ | (q^n−ε)/2`, impossible
by size.  Also `v_ε ≤ q^n(q^n+1)/2 < q^{2n}`, so `v_ε` is in the range where
Lemma C-below applies.

**Verified exactly** (STEP (X)): `n ∈ [3,12]`, all odd prime powers
`q < 400`, both `ε` — **1780 triples, 0 violations** (no divisibility, no
size violation, `gcd = 1` throughout).

Combining §2–§4: `v_ε ∈ I(B_n(q)) ∖ I(C_n(q))`. ∎

---

## 5. Consequences, and what this retires

1. **Theorem BC3 is repaired** and in a much stronger form: it is now
   `n`-uniform, unconditional, and cheap.  `q = 11`, `49`, `121`, `169` and
   the whole v_task63 tie set are settled with everything else:
   `v(11) = 11³·(11³−ε)/2 ∈ {885115, 886446}`, neither divisible by
   `ι₁ = 177156`.
2. **`(PAR)` and Lemma GLUE are no longer needed for `B/C`.**  Both were
   load-bearing only for the `mult₁` route.  (They remain open questions in
   their own right; nothing here proves them.)
3. **The brief's items 2–4 are moot.**  There is no `Δ` to restate over
   `(p, r)`, no tie set to characterise, and no tie-breaker to deploy.  The
   `C₅`-subfield bookkeeping and the `Sym⁵ SL₂` column — the two genuine
   v_task63 errata — remain *correct as errata* and should be recorded, but
   no census is built on them any more.
4. **`n > 3` is closed, not merely advanced.**  The argument never uses
   `n = 3`: `G₂(q) ⊂ Ω₇(q)`, the `Sp₆(2)`-tree, the spinor table, PSN-GF —
   all of it drops out.  What drives it is the elementary structural
   asymmetry: **`Ω_{2n+1}(q)` has anisotropic points and `Sp_{2n}(q)` has
   none**, and the resulting involution-centraliser index is coprime-ish to
   the symplectic minimal index.
5. **Combined with v_task59** (Theorems Sp-T, O-odd-T): `Sp_{2n}(q)` and
   `Ω_{2n+1}(q)` are **D-rigid among all finite groups** for `n ≥ 3`, all
   `q`.  The classical-group programme has no `B/C` residue left.

---

## 6. Honest tags

| statement | tag |
|---|---|
| `I(G)` is a `D`-invariant | **PROVEN** (Satz 2.3.3 + kernel-checked conductor invariance + order transfer) |
| `v_ε ∈ I(Ω_{2n+1}(q))`, `ε` determined by `disc(V)` | **PROVEN** (hand, §2) + **GAP-CONFIRMED** `q = 3,5,7,9`, `n = 3` |
| the two anisotropic orbit sizes are `q^n(q^n∓1)/2` | **PROVEN** (standard) + GAP-confirmed |
| `P₁` is the only maximal of `Sp_{2n}(q)` of index `< q^{2n}` | **PROVEN mod LIT** — Aschbacher/BHR classification (cited), Liebeck's `S`-bound for `n ≥ 4`, BHR 8.28/8.29 orders for `n = 3`; **exact numerical check** `n ≤ 8`, `q < 200` |
| `ι₁ ∤ v_ε` | **PROVEN** (size argument) + exact check `n ≤ 12`, `q < 400` |
| **Theorem BC-n** | **PROVEN**, unconditional modulo the cited classification of maximal subgroups |
| `mult₁`-route errata of v_task63 (`Sym⁵`, `C₅`) | **CONFIRMED, now unused** |

**Residual risk.**  A single citation carries the weight: the list of
maximal subgroups of `Sp_{2n}(q)`.  The step used is weak (only "no maximal
other than `P₁` has index `< q^{2n}`", i.e. a statement about *orders*), and
it is exactly the kind of statement Kleidman–Liebeck Theorem 5.2.2 /
Liebeck's bound already certify independently of BHR's fine data.  For
`n = 3` the `S`-class bound is the one spot where BHR's explicit list is
quoted; a reader who distrusts it can substitute any bound
`|M| < q^{15}` for `M ∈ S` in `Sp₆(q)` and the argument survives.
