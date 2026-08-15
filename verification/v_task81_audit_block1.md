# v_task81 — ADVERSARIAL AUDIT of the sporadic / L₂ / rank-1 twin-elimination
# block (`§4bb`–`§4bd` + addenda; `v_task50`–`v_task54`)

Date 2026-08-09.  **NOTES.md not edited.**
Brief: *break these results*.  Precedent: BC3 (`§4bk`) and `§4ae` were broken by
exactly this kind of audit; author-run scripts are treated as claims.

Everything below was **re-derived and re-computed independently**: a
from-scratch CFSG simple-order enumerator, a from-scratch census, a
from-scratch (and different) proof of Lemma C, from-scratch GAP `ι`
recursions, and a from-scratch GAP Ree computation.  Nothing was imported
from `v_task50`–`v_task54`.

| file | what it is |
|---|---|
| `v_task81_census.py` / `_out.txt` | independent CFSG simple-order enumerator; order-uniqueness; full coincidence hunt; the Phase-1 order census for 26 of the 27 sporadic targets; the 3-coprime simple-order census |
| `v_task81_arith.py` / `_out.txt` | independent proof of Lemma C by a *different and more elementary* route; (E1)/(E2)/(E3) window re-derivations; Lemma EQ/W/P; the rank-1 arithmetic; the alternating-socle branch |
| `v_task81_prefilter.py` / `_out.txt` | independent reproduction of `v_task50` §3.2's orbit-floor prefilter table, with self-derived `ι` bounds |
| `v_task81_iota.g` / `_out.txt` | independent Lemma-SP `ι` recursion, **three** mutually independent methods (character-table recursion, group-theoretic recursion, full subgroup lattice) |
| `v_task81_ree.g` / `_out.txt` | independent GAP verification of the Ree `ι` witness at `q = 27`, via a different route to the ovoid |

---

> ## VERDICT
>
> **No result in this block is BROKEN.**  Every load-bearing computation
> reproduced, several of them to the digit.  Seven **errata** are recorded
> below; all are gaps or imprecisions in *justification*, wording or reported
> constants, none changes a verdict, and each comes with a verified repair.
>
> | theorem | verdict |
> |---|---|
> | **Theorem Sporadic-T (SPT)** | **STANDS**, on the stated terms — i.e. still modulo the disclosed hypothesis **(AB-S)** for the 13 targets whose kill uses `ι(S)`.  The census-empty rows and the order-uniqueness bonus are unconditional and independently confirmed. |
> | **Theorem L2-T** | **STANDS, unconditional.**  Lemma C independently re-proven by a second route; the (E1) closed form is exactly right; (E2)/(E3) windows reproduce. |
> | **Theorem U3-T** | **STANDS, unconditional** — after erratum **E1** is repaired (the repair is verified here). |
> | **Theorem Sz-T** | **STANDS, unconditional.**  The 3-coprimality argument is airtight and the CFSG corollary is independently verified by direct inspection of the simple-order list. |
> | **Theorem Ree-T** | **STANDS, unconditional** — the `q = 27` `ι` witness reproduces exactly, by an independent route. |

---

## 1. `v_task50` — the sporadic block

### 1.1 The order census: reproduced **exactly**, 26 targets  [CONFIRMED]

`v_task81_census.py` implements the CFSG simple-order enumeration from
scratch (order formulas typed from the standard tables, exceptional
isomorphisms collapsed by *never generating* the alias, `|Out|` formulas
independent), then enumerates all multisets `{(S_i,ℓ_i)}` with
`∏|S_i|^{ℓ_i} ∣ |S|` and `c = |S|/∏ ∣ ∏(|Out(S_i)|^{ℓ_i}·ℓ_i!)`.

The order formulas pass a 37-entry self-check against independently known
orders (`selfcheck`).

**Non-simple census counts, mine vs `v_task50` §2.1:**

| S | mine | v_task50 | | S | mine | v_task50 |
|---|---|---|---|---|---|---|
| M₁₁ | 0 | 0 | | Suz | 8 | 8 |
| M₁₂ | 0 | 0 | | O′N | 0 | 0 |
| M₂₂ | **1** | **1** | | Co₁ | **119** | **119** |
| M₂₃ | 0 | 0 | | Co₂ | **7** | **7** |
| M₂₄ | **3** | **3** | | Co₃ | 0 | 0 |
| J₁ | 0 | 0 | | Fi₂₂ | **11** | **11** |
| J₂ | **2** | **2** | | Fi₂₃ | **3** | **3** |
| J₃ | 0 | 0 | | Fi₂₄′ | **2** | **2** |
| J₄ | 0 | 0 | | HN | **2** | **2** |
| HS | 0 | 0 | | Ly | 0 | 0 |
| McL | 0 | 0 | | Th | **6** | **6** |
| He | 0 | 0 | | B | **1225** (cap 8) / 1391 (uncapped) | 1225 |
| Ru | 0 | 0 | | ²F₄(2)′ | 0 | 0 |

**Every count agrees.**  The individual solutions agree too: e.g. `M₂₂`'s
single solution is `L₃(2) × L₂(11)`, `c = 4` — exactly the "worst socle" of
`v_task50` §3.4; `Fi₂₃`'s worst is `A₆ × L₂(17) × L₂(23) × L₂(27) × U₄(2)`
with `c = 3` (`U₄(2) = S₄(3)`), matching.  The Monster's *full* census is
computationally infeasible without a prefilter (as `v_task50` also reports);
its prefilter row is reproduced in §1.4 instead.

**14 census-empty rows: 13 verified directly** (M₁₁, M₁₂, M₂₃, J₁, J₃, J₄, HS,
McL, He, Ru, O′N, Co₃, Ly, ²F₄(2)′ — all of them).  The brief asked for 3.

### 1.2 Every census solution dies, under a *deliberately weaker* floor  [CONFIRMED]

Rather than reuse `v_task50`'s `ι` table, the audit kills each census solution
with the **maximally generous** surrogate

  `ℓ³·|S_i|² ≥ ι(S)³`   (i.e. `ℓ·|S_i|^{2/3} ≥ ι(S)`),

which by Lemma C is *implied by* the true orbit floor `ℓ|Out(S_i)|ι(S_i) ≥ ι(S)`,
so it kills strictly **fewer** factors.  Result across all 26 targets:
**every non-simple census solution is killed; 0 ALIVE.**  (For `B`: all 1391
uncapped solutions die.)  The elimination therefore does not depend on the
fine detail of the `ι` table at all.

### 1.3 The `c`-bound `c ∣ ∏(|Out(S_i)|^{ℓ_i}·ℓ_i!)`  [CONFIRMED — the wreath bound is right]

Re-derived from scratch, as the brief asks:

`F(T) = 1` ⟹ `Soc T = Q = ∏S_i^{ℓ_i}` is a product of non-abelian simples and
`C_T(Q) ∩ Q = Z(Q) = 1`; `C_T(Q) ⊴ T`, so if `C_T(Q) ≠ 1` it contains a minimal
normal subgroup of `T`, which lies in `Q` — contradicting the trivial
intersection.  Hence **`C_T(Q) = 1`**, the conjugation map `T → Aut(Q)` is
injective, and `Q = Inn(Q) ≤ T ≤ Aut(Q)`.  For pairwise non-isomorphic
non-abelian simple `S_i`,

  `Aut(∏_i S_i^{ℓ_i}) = ∏_i ( Aut(S_i) ≀ Sym(ℓ_i) )`,

so `|Aut(Q)| = ∏|Aut(S_i)|^{ℓ_i}·ℓ_i!` and, dividing by `|Inn(Q)| = |Q|`,

  **`|Out(Q)| = ∏_i |Out(S_i)|^{ℓ_i}·ℓ_i!`.**

`T/Q ↪ Out(Q)` (this is *exactly* where `T/Soc T` embeds — the brief's
question), so `c = [T:Q]` divides `|Out(Q)|` by Lagrange.  **The wreath bound
is correct as stated and is not an over-count**: the `ℓ_i!` is the block
permutation and the `|Out(S_i)|^{ℓ_i}` the componentwise outer part.

### 1.4 The prefilter table §3.2 and the three residual rows §3.3  [CONFIRMED]

`v_task81_prefilter.py` recomputes the "surviving proper factors" column using
only **self-derived** `ι` upper bounds — (a) `|S|/|S|_p` for every `p`
(witness `Z(Syl_p)`; needs no literature at all), (b) `C(m,3)` for `A_m`,
(c) the minimal-parabolic index for Lie type (Borel–Tits), (d) the `v_task39`
sporadic table (itself re-verified in GAP, §1.5).  Output:

* **survivors NONE** for 23 of the 27 targets, matching `v_task50` §3.2;
* `Fi₂₂ → {²F₄(2)′, U₆(2), Suz}` and `Fi₂₃ → {Suz}` — **exactly** their rows
  (my run additionally keeps `U₄(3)` at `ℓ = 2` because my prefilter tests
  `|S_i|^ℓ ≤ |S|` where theirs tests the sharper `|S_i|^ℓ ∣ |S|`; `3265920² ∤ |Fi₂₂|`,
  so their row is right and mine is merely looser);
* `M₁₁ → {A₆}` and `M₂₂ → {A₆, A₈, L₃(4)}` where they get `{}` and `{L₃(4)}`
  — again because my `C(m,3)` bound (20, 56) is weaker than the exact
  `ι(A₆) = 10`, `ι(A₈) = 15`, both of which my GAP run confirms.  **Their
  extra kills are valid.**

The five `c ∤ |Out(S₁)|` rows of §3.3, checked exactly:

| S | S₁ | `|S|/|S₁|` | exact? | `|Out(S₁)|` | `c ∣ |Out|`? | `|S₁|² ∣ |S|`? |
|---|---|---|---|---|---|---|
| M₂₂ | L₃(4) | 22 | yes | 12 | **no** | no |
| Fi₂₂ | ²F₄(2)′ | 3 592 512 | yes | 2 | **no** | no |
| Fi₂₂ | U₆(2) | 7 020 | yes | 6 | **no** | no |
| Fi₂₂ | Suz | 144 | yes | 2 | **no** | no |
| Fi₂₃ | Suz | 9 121 248 | yes | 2 | **no** | no |

All five dead, and `ℓ = 1` is forced in each.  §3.4's headline margin is also
confirmed: `M₂₂`, socle `L₃(2)×L₂(11)`, `F_max = min(2·7, 2·12) = 14`,
`ι(M₂₂)/F_max = 77/14 = 5.5` exactly.

### 1.5 The `ι` inputs  [CONFIRMED — 14/14, by three independent methods]

An independent GAP run (`v_task81_iota.g`) implemented the Lemma-SP recursion
from scratch in **three mutually independent ways** — (A) character-table
recursion over CTblLib `Maxes` with *separate* lower and upper bounds,
(B) the same recursion on the actual groups via `MaximalSubgroupClassReps`
and `FittingSubgroup` (no character tables at all), (C) the full definition
`min_{1≠H≤G} [G:N_G(H)]·|H′|` over the **complete subgroup lattice**.

All 14 claimed values confirmed, with `lo = up` (exact) in every case:
`ι(M₂₂)=77`, `ι(L₃(4))=21`, `ι(Fi₂₂)=3510`, `ι(Suz)=22880`, `ι(²F₄(2)′)=1755`,
`ι(M₁₁)=55`, `ι(M₂₃)=253`, `ι(M₂₄)=759`, `ι(U₃(3))=28`, `ι(U₄(2))=ι(S₄(3))=27`,
`ι(A₆)=10`, `ι(A₇)=35`, `ι(A₈)=15`, `ι(L₃(2))=7`; plus `ι(U₆(2))=693`,
`ι(L₂(q))=q+1` for `q=8,11,13,16,25,27,32`.  Every value is attained at a
**maximal** subgroup (the recursion never descends), and the fallback
substitutions where `Maxes` is missing were checked to be genuine *lower*
bounds — so the recursion cannot under-report.

**Method C is the direct test of `(AB-S)` at small scale:** for all 13 groups
where the full lattice is in reach (`A₅, L₃(2), A₆, L₂(8), L₂(11), L₂(13),
L₂(16), A₇, U₃(3), M₁₁, L₂(25), L₂(27), U₄(2)`), the all-`H` minimum **equals**
the abelian-only minimum, and the optimal `H` is itself abelian.  This is
evidence for `(AB-S)`, not a proof of it; §5 below records why the *factor*
side of the floor is `(AB)`-free regardless.

### 1.6 Order-uniqueness and the CFSG order theorem  [CONFIRMED]

* **All 27 sporadic orders (incl. `|²F₄(2)′| = 17 971 200`) are unique among
  all finite simple orders** — verified target by target with a complete
  enumeration (characteristic `p ∣ |S|`, `q³ ≤ 3|S|`, so the enumeration is
  provably exhaustive), including the Monster.  ✓ `v_task50` §5.
* **The CFSG order theorem's statement, checked**: enumerating *all* finite
  simple groups of order `≤ 10¹²` (1650 groups, 1648 distinct orders) the only
  order coincidences between non-isomorphic groups are
  **`{A₈, L₃(4)}`** at 20160 and **`{O₇(3), S₆(3)}` = `{B₃(3), C₃(3)}`** at
  4 585 351 680.  This is exactly the form cited (Artin 1955; completed by
  Kimmerle–Lyons–Sandling–Teague, *Composition factors from the group ring and
  Artin's theorem on orders of simple groups*, Proc. LMS (3) **60** (1990)
  89–122).  `|B_n(q)| = |C_n(q)|` is an identity of the shared order formula
  `q^{n²}∏(q^{2i}−1)/gcd(2,q−1)`, so the infinite family is structural.
  **Note for the record: `sources/` contains no copy of Artin or KLST** — the
  citation is literature-only, and the computation above is a check of the
  *statement*, not a proof of it.

---

## 2. `v_task51` / `v_task52` — L₂ and Lemma C

### 2.1 Lemma L2-ι, over **all** `H`  [CONFIRMED]

The proof in `v_task51` §1.1 is correct and — worth emphasising — **does not
use Dickson at all**, only Galois' minimal-index theorem:

* `N_S(H) = S` ⟹ `H = S` ⟹ `ind*(H) = |S| > q+1` for every `q ≥ 4`;
* otherwise `ind*(H) ≥ [S:N_S(H)] ≥ m(L₂(q)) = q+1`, `q ≠ 5,7,9,11`.

The four exceptional `m`-values are handled correctly.  The brief's worry
about `N(A₅)` is answered by the same clause: for `q = 9, 11` the
minimal-index subgroups are `A₅`, **maximal and self-normalising**, so
`N_S(H) = A₅` forces `1 ≠ H ⊴ A₅` hence `H = A₅` and `ind*(A₅) = 6·60 = 360`
(resp. `11·60`), not 6 (resp. 11); the next available index is `q+1`.  For
`q ≥ 13` there is nothing to check: `m(S) = q+1` and the Borel realises it as
a normaliser of the abelian `U`, so `ι = ι_ab = q+1` and the row is genuinely
`(AB)`-free.  `N(dihedral)`, `N(torus)`, `N(Borel)` all give indices `≥ q+1`
automatically — no case analysis is needed, because the bound is via `m(S)`.
GAP (`v_task81_iota.g`, Method C, full lattice) confirms
`ι(L₂(q)) = q+1` at `q = 8,11,13,16,25,27` and `ι(L₂(5)) = 5`, `ι(L₂(7)) = 7`.

### 2.2 Lemma C  [CONFIRMED — and re-proven by a second, stronger route]

Rather than re-run their (★)-window, the audit proves Lemma C **differently**.
Take `A := Z(Syl_p(G))`: it is abelian, `≠ 1`, and `Syl_p(G) ≤ N_G(A)`, so

  **`ι_ab(G) ≤ [G : Syl_p(G)] = |G| / |G|_p`** — *no Borel–Tits, no
  minimal-degree theorem, no parabolic-index formulas*.

Hence Lemma C follows from the exact integer inequality

  **(SC)  `|Out(G)|³·|G| ≤ (|G|_p)³`.**

`(SC)` closes every family except `A₁` outright, because `3N − D ≥ 1` for
every family and every rank (`N` = number of positive roots, `D = deg_q|G|`;
the full table is in `v_task81_arith_out.txt`), and `3N − D = 0` **only** for
`A₁`.  The failure window of `(SC)` was enumerated over all families and all
ranks `≤ 14` (`q ≤ 10⁷` for the families with `3N−D ≤ 1`, `q ≤ 4096`
otherwise) and **every one of the 665 223 window groups was then checked
exactly against Lemma C with the minimal-parabolic bound: 0 FAILURES.**

The tightest rows come out identical to `v_task52` §2:

| | | |
|---|---|---|
| `L₂(9) = A₆` 0.790 | `L₂(5)` 0.783 | `L₂(4)` 0.652 |
| `L₂(7)` 0.526 | `L₃(2)` 0.460 | `L₃(4)` 0.340 |

`A_m` (`m ≤ 199`, with the exact `ι(A₅)=5`, `ι(A₆)=10`): **0 failures.**
Sporadics with the (now independently re-verified) `ι` table: **0 failures**,
tightest `J₁` at 0.333 — matching.

The `A₁` tail, which `(SC)` cannot reach, is closed separately: Lemma C for
`L₂(q)` with `ῑ = q+1` is *exactly* `d⁵f³(q+1) ≤ q²(q−1)²`, verified for
every prime power `q ≤ 3·10⁶` (0 failures) and implied for all larger `q` by
`32(log₂q)³(q+1) ≤ q²(q−1)²`, whose two sides differ by `~q³/log³q`.

**Lemma C is confirmed with an empty exception list, by two independent
routes.**  Lemma K′ (`|G| < (|G|_p)³`) was checked as a by-product: 10 652
groups, 0 violations, tight only at `A₁` (ratio → 1⁻).

### 2.3 The (E1) closed form  [CONFIRMED — exactly]

Re-derived symbolically and verified as an identity (0 mismatches over
`q < 400`, `c < 200`):

* `q₁ = q+1`: cancelling `q(q+1)` gives **`c·d·(q+2) = d₁·(q−1)`**; with
  `c ≥ 2`, `d ≥ 1`, `d₁ ≤ 2` the LHS `≥ 2(q+2) > 2(q−1) ≥` RHS — **no
  solution, any `q`**.
* `q₁ = q−1`: cancelling `q(q−1)` gives **`c·d·(q−2) = d₁·(q+1)`**.
  *q even*: `d = 1`, `q₁` odd so `d₁ = 2`, whence `c = 2 + 6/(q−2)`, integral
  iff `(q−2) ∣ 6`, i.e. `q ∈ {3,4,5,8}` — even: `q = 4` (`q₁ = 3`, `L₂(3)`
  not simple) and `q = 8`.
  *q odd*: `d = 2`, `q₁` even so `d₁ = 1`, whence `4(q−2) ≤ 2c(q−2) = q+1`,
  i.e. `q ≤ 3`.
  Brute force over `4 ≤ q ≤ 10⁶` returns the single triple
  **`(q, q₁, c) = (8, 7, 3)`**, and `3 ∤ |Out(L₂(7))| = 2`.  **Unique, dead.**

The preceding case split is also sound: writing `q = kq₁ + ε₁`,
`q₁ = mp^a + ε₂` with `p^a = q/p^j`, one gets `q(p^j − km) = p^j(kε₂ + ε₁)`;
`km = p^j` forces `kε₂ + ε₁ = 0`, hence `k = 1`, `ε₂ = −ε₁`, `m = p^j` and
`q₁ = q ± 1`.  Exactly as claimed.

### 2.4 (E2), (E3)  [CONFIRMED, with one constant slightly off — E4 below]

* **(E3)**: the inequality `2^{v₂(m!)−1} ≤ 2|Out(A_m)|·C(m,3)` holds for
  `m ∈ {5,…,15}` and fails for every `m > 15`.  **Exactly** `v_task52`'s
  claim, reproduced digit for digit.
* **(E2)**: my evaluation of `|L₂(q₁)|² ≤ |L₂(q)|` against
  `4f₁(q₁+1) ≥ q+1` gives "empty for `q > 438`"; `v_task52` reports 839.
  Theirs is the more conservative number; both are far inside the `q ≤ 10⁶`
  census.  No issue.

---

## 3. `v_task53` / `v_task54` — the rank-1 families

### 3.1 `3 ∤ |Sz(q)|` and the CFSG corollary  [CONFIRMED — airtight]

`q = 2^f` with `f` odd ⟹ `q = 2·4^{(f−1)/2} ≡ 2 (mod 3)`; hence `q−1 ≡ 1`,
`q² ≡ 1` so `q²+1 ≡ 2`, and `q²` is a 2-power.  So `3 ∤ q²(q−1)(q²+1)`.
Machine check for every odd `f ≤ 401`: no exceptions.

The corollary **"a finite simple group of order prime to 3 is a Suzuki
group"** was verified *directly against the CFSG list*: enumerating all finite
simple groups of order `≤ 10²⁴` (Lie families over all `q ≤ 2·10⁵`, all `A_m`,
all sporadics), the groups with `3 ∤ |S|` are **exactly** `Sz(8)`, `Sz(32)`,
`Sz(128)`, `Sz(512)`, `Sz(2048)`, `Sz(8192)`, `Sz(32768)` — nothing else.
The uniform reason (worth recording, since it makes the citation checkable
rather than folkloric): if `3 ∤ q` then `3 ∣ q²−1`, and **every** family of
Lie type except `²B₂` has a `q−1` **and** a `q+1`-type factor in its order
(`²B₂(q) = q²(q−1)(q²+1)` is the unique family with no `q+1` block); `²G₂` and
`²F₄` are in characteristic 3 resp. contain `q⁴−1`; `3 ∣ |A_m|` for all `m ≥ 5`;
`3` divides every sporadic order.  The citation in `v_task54` L1
(Thompson/Glauberman) is the classical pre-CFSG attribution; the statement is
in any case a finite check against the CFSG list, which is what was done here.

Consequence chain re-checked: `(E)` gives `|S₁| ∣ |S|`, hence `3 ∤ |S₁|`,
hence `S₁ ≅ Sz(q₁)`. **Valid.**

**Lemma Sz-subfield** re-derived: `4f₁ ≥ 12`, Zsygmondy gives a primitive
prime `r ∣ 2^{4f₁}−1`; since `2^{4f₁}−1 = (2^{2f₁}−1)(q₁²+1)`, `r ∣ q₁²+1`;
`r` odd divides `(q−1)(q²+1) ∣ 2^{4f}−1`, so `ord_r(2) = 4f₁ ∣ 4f`, i.e.
`f₁ ∣ f`; `f/f₁` odd `≥ 3` gives `q/q₁ ≥ q₁²` and `c ≳ q₁¹⁰ ≥ 9·10⁸` against
`c ≤ f₁`.  Independent computation over every pair `f₁ ∣ f`, `f ≤ 201`:
**0 hits**, smallest ratio `c/|Out|` = **1 205 899 264/3 at `(f,f₁) = (9,3)`**
— the same number `v_task54` reports.  **CONFIRMED.**

So **Sz-T really is census-free**, exactly as claimed.

### 3.2 `ι(U₃(q)) = q³+1` including `U₃(5)`  [CONFIRMED]

The `U₃(5)` argument is correct and I can tighten the statement of *why*:
`ind*(H) < 126` needs `[S:N_S(H)] < 126`, and the possible values are `1` and
`50` (`m(U₃(5)) = 50`, next maximal index 126, and `126/50 < 3` rules out any
intermediate non-maximal index since an index-2 subgroup of `A₇` does not
exist).  `[S:N_S(H)] = 1` gives `H = S`, `ind* = |S|`.  `[S:N_S(H)] = 50` gives
`N_S(H) ≅ A₇` and `1 ≠ H ⊴ A₇`, so `H = A₇` and `ind*(H) = 50·2520 = 126 000`.
Hence `ι(U₃(5)) = 126 = 5³+1` — **the exceptional minimal degree does not
become an `ι` exception.** ✓

### 3.3 Lemma EQ / Lemma W / Lemma P  [CONFIRMED]

* **Lemma EQ** re-derived: `q₁^{N₁} ≤ q^N` from `|S₁|_p ∣ |S|_p`; `(F)` with
  `(T2)`/`(T3)` gives `4d₁f₁g₁q₁^{μ₁} ≥ q^N+1 > q^N ≥ q₁^{N₁}`; divide.
  Valid.  The only input is `(T2)` (`ῑ ≤ 4q^μ`) — see erratum **E2**.
* **Lemma P** (`N − μ = 0` iff rank 1) reproduced exactly:
  `A₁, ²A₂, ²B₂, ²G₂` give 0; `L₃ 1, U₄ 1, S₄ 1, G₂ 1, ²F₄ 2, L₄ 3, U₅ 3,
  ³D₄ 3, C₃/B₃ 4, D₄ 6, F₄ 9, E₆ 20, E₇ 38` — matching `v_task54` §4 with the
  single exception `E₈` (mine 65, theirs 69; both are `≥ 7`, the window is
  empty either way).
* **The Lemma-EQ window**: with *exact* `|Out|` I get **43** admissible
  `(family, q₁)` pairs; `v_task54` reports **71**, computed with the
  conservative caps `d₁ ≤ max(n₁,4)`, `g₁ ≤ 6`.  I checked family by family
  that **their window contains mine** (`L₃`, `U₄`, `U₅`, `S₄`, `G₂`, `³D₄`,
  plus `L₄` and `D₄` which my exact `|Out|` already excludes).  Their window
  is therefore **sound (a superset)** and the "0 hits" verdict is unaffected.
* **`θ = D/μ` table**: reproduced; `min θ = 7/3` at Ree, `Sz 5/2`, `²F₄ 13/5`,
  `U₃ 8/3`, `G₂ 14/5`, `A₁ 3`, `L₃ 4`.  Matches.

### 3.4 The `ppmax` bounds and the cross-characteristic thresholds  [CONFIRMED]

* `v_task53` Input 4 bounds re-checked by exact factorisation: `U₃(q) ≤ max(q³, 2(q+1)²)`,
  `Sz(q) ≤ q²+1`, `R(q) ≤ q³` — **no violations**, and attained.
* The `c·ppmax_{p′}³ < |S|` kill: my evaluation gives **`U₃`: valid for all
  `q > 173`** (`v_task53` says `q ≥ 179` — the next prime power, so identical
  in effect) and **`R`: valid from `q = 2187` on, `q ∈ {27,243}` surviving**
  (exactly their statement).  `Sz` indeed gets no kill this way — the
  structural obstruction is real.  ✓

### 3.5 The Ree `ι` at `q = 27`  [CONFIRMED]

An independent GAP run (`v_task81_ree.g`) reached the ovoid by a *different*
route (memory-capped line-orbit BFS from the basis vectors, not the
`P`-fixed-subspace seed) and reproduced every number: `|R(27)| = 10 073 444 472`,
ovoid length `19 684 = 27³+1`, faithful permutation action, `B`-orbits
`[1, 19683]` (2-transitive), `|Z(Syl₃)| = 27` elementary abelian with `A′ = 1`,
`Fix_ovoid(A) = {1 point}`, `|N_G(A)| = 511 758 = 19683·26 = |B|`,
`[G:N_G(A)] = 19 684`, `ind*(A) = 19 684 = q³+1`.  Both inclusions
`B ≤ N_G(A)` and `N_G(A) ≤ B` are genuinely established, and `Normalizer` was
run outright.  Kernel of the action verified trivial, so `|G|` is confirmed by
computation and not only by the library datum.

**Honest scope, as `v_task54` §5 also states**: this certifies
`ι(R(27)) ≤ 19 684`.  The matching *lower* bound is Ward's minimal-degree
theorem and remains literature-only — the same status as `U₃`/`Sz`
(Cooperstein / Suzuki).

---

## 4. ERRATA

> None of these changes a verdict.  Each is a defect in justification, wording
> or a reported constant, with a verified repair.

**E1 — `v_task53` §5.4 / `v_task54` §6: the alternating-socle branch is *not*
"complete in `q`" as scanned.  [ERRATUM + fix, verified]**
The claim is *"for alternating (`|Out| ≤ 4`) and sporadic (`|Out| ≤ 2`) `S₁`
the candidate list is complete, so those sub-branches are closed for all `q`."*
The **sporadic** half is genuinely complete (27 groups × `c ≤ 2`, and `(S₁,c)`
determines `q`).  The **alternating** half is not: the scan enumerated only
`A_m` with `|A_m| ≤ 10⁸⁰`, which caps `q`, not `m`.  `m` is unbounded a priori,
so "for all `q`" is unsupported by that scan.
*Repair (computed here, `v_task81_arith.py` PART 4(e)):* the orbit floor with
`ι_ab(A_m) ≤ C(m,3)` forces `|Out(A_m)|·C(m,3) ≥ ι(S) = q^N+1`, i.e.
`m ≥ m_min(q)`, while `(E)` forces `c·|A_m| = |S|` with `c ≥ 2`, i.e.
`|A_m| ≤ |S|/2`.  Checking `|A_{m_min(q)}| > |S|/2` exactly:
**for `R(q)` this holds at every `q`** (branch closed by proof, no scan);
**for `U₃(q)` it holds at every `q` except `q = 3` and `q = 4`**, both deep
inside the raw-empty census `q ≤ 50 000`.  So the conclusion stands; the
justification needs this paragraph.  (`Sz` is unaffected — 3-coprimality kills
alternating socles outright.)

**E2 — `v_task52` §2, proof of (T2).  [ERRATUM, immaterial]**
"Every `ῑ` in the table is a product of at most two quotients of the shape
`(q^a±1)/(q^b−1)`" is false for `E₇` (and `E₈`), where the minimal-parabolic
index is a product of three such factors; at `q₁ = 2` the constant `4` in
`ῑ ≤ 4q^μ` must then be relaxed (my instance: `E₇(2)`, ratio 7.76).  Since
`e(E₇) = 191` and `e(E₈) = 343`, replacing `9216` by `9216·8` in (★) changes
nothing whatever.  The *machine* check of (T2) at `q₁ = 2,3,4,5` is the real
support and is sound (the ratio `ῑ/q^μ` is decreasing in `q`).

**E3 — `v_task50` §2.1, the raw census table is cap-truncated.  [ERRATUM, disclosed but under-stated]**
The note says the socle-factor count is capped at 8 "for the raw statistics".
The numbers in the table are therefore **truncated counts, not the true raw
census**: for `B` the uncapped count is **1391**, not 1225 (166 solutions have
9–11 socle factors).  My run reproduces **1225 exactly when the cap is
re-imposed** — which is a good cross-validation of both implementations — and
**all 1391 die on the floor**, so §4.1's "the cap is non-binding" conclusion is
correct.  The table row should be labelled "`≤ 8` factors".

**E4 — `v_task52` §4.1(d)/PART 5, the `q > 600` threshold is not reproducible.  [ERRATUM, immaterial]**
Evaluating the same self-consistent system (`q ≤ 2c(k+1)`, `c ≤ 2log₂(2q+2)`,
`q₁³ ≥ q(q²−1)/(2c)`, `k ≤ 4(q+1)/q₁`) with exact integers I get the largest
satisfiable `q` = **650**, not 600 — the difference is entirely in how the
auxiliary bounds are rounded.  Both are inside the exhaustive census
`q ≤ 10⁶`.  The threshold should be quoted as a safe round number
(e.g. "`q ≤ 10³`") rather than a tight-looking 600.  Same remark for (E2):
mine 438 vs theirs 839.

**E5 — a dormant memoisation hazard in `v_task39`/`v_task50`'s `ι` recursion.  [ERRATUM, verified dormant]**
The recursion prunes with `2·idx ≤ cap` but memoises keyed on the table
identifier **only**, ignoring `cap`.  If the cap ever bound, a table first
visited under a tight cap would cache an inflated `ilow`, and a later reuse
would silently return it — inflating `ι`, i.e. erring in the *unsafe*
direction for the census, and defeating the `EXACT=` self-check.  Tested by
instrumenting a copy: **`CAP-BINDS` fires 0 times across all 27 groups** at
`cap = 10⁴⁰`, and a pruning-free rerun reproduces every line byte-identically.
The hazard is real but dormant; the memo should be made cap-aware before that
recursion is reused with a smaller cap.

**E6 — `Lemma C`'s statement should read `ι_ab`, not `ι`.  [ERRATUM, notational but load-bearing for reuse]**
This is the one worth fixing in the notes, because it is a trap for a future
reuser.  The orbit floor (F) comes from Lemma TR-1, which quantifies over
**abelian** `1 ≠ A ≤ K_i`; via Lemma F it needs

  `ι(K≤Ā)_O ≤ |Out(S_i)| · ι_ab(S_i)`,   `ι_ab(G) := min_{1≠A ≤ G, A abelian}[G:N_G(A)]`,

so the quantity Lemma C must bound is `|Out(G)|·ι_ab(G)`, **not**
`|Out(G)|·ι(G)` with `ι = min` over *all* `H` (`ι ≤ ι_ab`, so the `ι`-version
is strictly weaker than what the chain needs).  What is actually *proven* in
`v_task52` is the `ι_ab` version — every bound used (parabolic index, `C(m,3)`,
the exact `v_task39` table, and my `|G|/|G|_p`) is an upper bound for `ι_ab` —
so **no result is affected**, and my §2.2 re-proof is likewise for `ι_ab`.
But `v_task51` §3 / `v_task52` §1 / `v_task53` §3 all *state* Lemma C with
`ι(G) := min_{1≠H≤G} ind*(H)`.  Anyone applying the stated lemma literally
would have a gap.  Recommend restating as
`|Out(G)|·ι_ab(G) ≤ |G|^{2/3}`.
*(Silver lining, worth recording: this also shows the **factor** side of the
floor is `(AB)`-free for every target — Lemma SP computes exactly `ι_ab`, which
is exactly what (F) needs.  Only the **target** side, `ι(S) = ι(T)`, needs
`(AB-S)`, which is what `v_task50` §6 says.)*

**E7 — the CFSG order theorem has no source in `sources/`.  [ERRATUM, provenance]**
`v_task50` C1/§5, `v_task51` C4, `v_task53` C7 all lean on Artin/KLST, and the
repository holds no copy.  The statement is confirmed computationally here for
all simple orders `≤ 10¹²`, and the correct full citation is
Kimmerle–Lyons–Sandling–Teague, Proc. LMS (3) **60** (1990) 89–122.  Tag should
be `[LIT, no local source]`.

---

## 5. What the audit did **not** find

* No arithmetic error in any census, any `ι`, any order formula, any `|Out|`.
* No unsound kill: every kill in the block survives being redone with a
  deliberately *weaker*, self-derived bound.
* No hidden dependence on the `Bₙ/Cₙ` residue: order-uniqueness of the sporadic,
  `L₂`, `U₃`, `Sz` and `R` orders is confirmed independently, and none of them
  is one of the two coincidence classes.
* No overstatement of the `(AB-S)` status: `v_task50` §6 states it plainly, and
  §1.5 above adds 13 groups of direct lattice-level evidence for it.

## 6. Reproduce

```
python3 v_task81_census.py selfcheck            # order formulas
python3 v_task81_census.py unique               # order-uniqueness + coincidence hunt
python3 v_task81_census.py cop3                 # 3-coprime simple orders
TARGETS="M22,Fi22,..." python3 v_task81_census.py census
python3 v_task81_prefilter.py                   # v_task50 §3.2 reproduction
python3 v_task81_arith.py                       # PARTS 1-5
~/gap-4.16.0/gap -q -o 4g v_task81_iota.g
~/gap-4.16.0/gap -q -o 8g v_task81_ree.g
```
All arithmetic is exact Python big-integer / `Fraction` / GAP rational; the
only floats are display columns.
