# v_task49 — Lemma V-BIG for **non-abelian** `H`: the `d ≥ d₀` branch closed.
# (H2′) becomes a theorem; Theorem GAP is hypothesis-free for `n ≥ 178089`.

Date 2026-08-08.  **NOTES.md not edited.**

| file | what it does |
|---|---|
| `v_task49_chain.g` / `_out.txt` | exhaustive machine check of the six structural inequalities (I)–(VI) that carry the proof, over **all** fixed-point-free `1 ≠ H ≤ A_s`, `s = 5..11`, abelian and non-abelian alike; also `V_s` and `min V_s` for `s ≤ 11` (new: `s = 11`) |
| `v_task49_chain11.g` | the `s = 11` run (same code, split off for runtime) |
| `v_task49_thresholds.py` / `_out.txt` | exact-integer/log certification of the numeric thresholds; the least `s₀`; the partition bound `d!/((a!)^b b!) ≥ 2^{d/2−1}` checked exactly for all `d ≤ 2000` |

---

## 0.  Verdict, stated first

> **Lemma V-BIG (general form) [PROVEN].**  For every `s ≥ s₀ = 178084` and
> every fixed-point-free `1 ≠ H ≤ A_s` — **abelian or not** —
>
>   `v(H) := s!·|H′| / |N_{S_s}(H)| = [S_s : N_{S_s}(H)]·|H′| > s⁶`,
>
> i.e. `min V_s > s⁶`.  With the sharpening of §5 the threshold drops to
> `s₀ = 15876`.
>
> **Consequences.**  Theorem GAP holds for **all** `H`, with no (AB)/(H2)/(H2′)
> input, for every `n ≥ n₀ = s₀ + 5 = 178089`.  Since Theorem GAP is invoked
> only for `n > 10¹¹` (below that, rows 2 and 3 are killed by the v_task45
> exact scan), **(H2′) is discharged in every place Theorem AT uses it.**
> Theorem AT stands on **(H1)** alone as far as this branch is concerned.

Nothing here uses CFSG, O'Nan–Scott, Praeger–Saxl, Maroti or Wiegold.  The
only classical input is **Bochert's 1889 theorem** on the index of a
primitive group (Wielandt, *Finite Permutation Groups*, Thm 14.2), and even
that is optional (§4, Remark 2).  The proof is elementary and uniform: the
Bochert direction that the task proposed is only one of two subcases, and the
other subcase (`A_d ≤ N_{S_d}(K)`) is settled by simplicity of `A_d` alone.

**The key change of parameters against v_task47's sketch.**  v_task47 put the
split at `d₀ = Θ(log s / log log s)` — the value at which the *abelian*
holomorph bound `d!/d^{1+log₂ d}` first exceeds `s⁶`.  At that `d₀` the
non-abelian large-orbit case is genuinely hard: a proper transitive
normaliser has index only `≈ 2^{d₀} ≈ s^{6/log d₀} ≪ s⁶`, so nothing is
provable there without controlling `|H′|`.  The observation that unlocks the
whole thing is that the small-orbit case has *enormous* slack: it survives up
to `d₀ ≈ √s/2`, not `log s`.  **Move the split to `d₀ = ⌊√s/2⌋ + 1` and the
large-orbit case becomes polynomial** (`s⁶ ≤ 4096·d¹²`), where the crudest
classical index bounds win by hundreds of orders of magnitude and `|H′|` is
not needed at all except in the one case where it is enormous.

---

## 1.  Setup and the two reductions

Throughout: `1 ≠ H ≤ A_s`, `supp(H) = {1..s}` (fixed-point-free), so every
`H`-orbit has size `≥ 2`; `N := N_{S_s}(H)`; `O₁,…,O_r` are the `H`-orbits
with sizes `e₁ ≥ … ≥ e_r ≥ 2`, `m_e := #{i : e_i = e}`, `r = Σ_e m_e ≤ s/2`;
`d := e₁` is the largest orbit size and `m := m_d`; `W := ⋃_{e_i = d} O_i`,
`|W| = dm`; `K_i := H|_{O_i} ≤ Sym(O_i)`, a **transitive** group of degree
`e_i`.  Write `D := ⌊√s / 2⌋`.

### Reduction 1 (orbit partition)  [PROVEN]

> `N` permutes the `H`-orbits preserving their sizes, hence
> `N ≤ ∏_e (S_e wr S_{m_e})` and `|N| ≤ ∏_e (e!)^{m_e}·m_e!`.

*Proof.*  For `g ∈ N` and an `H`-orbit `O`, `O^g` is an `H^g = H`-orbit of the
same size. ∎

### Reduction 2 (restriction to the dominant orbits)  [PROVEN]

> `|N| ≤ m! · (∏_{|O_i| = d} |N_{S_d}(K_i)|) · (s − dm)!`, and consequently
>
>   **(★)  `v(H) ≥ |K′| · [S_d : N_{S_d}(K)]`  for `K = K_i` any dominant
>   constituent** — indeed `v(H) ≥ C(s,dm)·∏_{|O_i|=d} [S_d : N_{S_d}(K_i)]`.

*Proof.*  `W` is `N`-invariant (Reduction 1), so restriction gives
`π : N → Sym(W)` with `ker π ≤ Sym({1..s}∖W)`, `|ker π| ≤ (s−dm)!`.  For
`g ∈ N`, `h ∈ H`: `(ghg^{-1})|_W = g|_W·h|_W·g|_W^{-1} ∈ H^W`, so
`π(N) ≤ N_{Sym(W)}(H^W)`, `H^W` = image of `H` in `Sym(W)`.  Elements of
`N_{Sym(W)}(H^W)` permute the `m` blocks `O_i ⊆ W`; the subgroup fixing each
block setwise embeds (restriction is injective there) into
`∏_i N_{Sym(O_i)}(K_i)`, because for such `g`,
`(ghg^{-1})|_{O_i} = g|_{O_i}h|_{O_i}g|_{O_i}^{-1} ∈ K_i`.  Hence
`|N_{Sym(W)}(H^W)| ≤ m!∏_i|N_{S_d}(K_i)|`, giving the displayed bound.

For (★): with `n_i := |N_{S_d}(K_i)|`,

  `[S_s:N] ≥ s! / (m!·∏n_i·(s−dm)!) = C(s,dm)·(dm)!/(m!∏n_i)
           ≥ C(s,dm)·(d!)^m m!/(m!∏ n_i) = C(s,dm)·∏_i (d!/n_i)`,

using `(dm)! ≥ (d!)^m·m!` (a multinomial count).  Finally `|H′| ≥ |K_i′|`,
because the restriction `H ↠ K_i` carries `H′` onto `K_i′`.  Dropping
`C(s,dm) ≥ 1` and all but one factor gives (★). ∎

*(Reductions 1 and 2 and (★) are machine-verified for every fixed-point-free
`H ≤ A_s`, `s = 5..11`, as inequalities (I), (II), (III), (V) — 814 subgroup
classes, 733 of them non-abelian, **0 violations**: `v_task49_chain_out.txt`.)*

---

## 2.  Case A: every orbit has size `≤ D = ⌊√s/2⌋`  [PROVEN, hypothesis-free]

> `v(H) ≥ [S_s:N] ≥ s! / (D^s·⌊s/2⌋!) ≥ 2^{s/2}`.

*Proof.*  By Reduction 1, `|N| ≤ ∏_e (e!)^{m_e}·∏_e m_e!`.  Since `e ≤ D`,
`∏_e (e!)^{m_e} ≤ ∏_e (e^e)^{m_e} ≤ D^{Σ_e e·m_e} = D^s`; and
`∏_e m_e! ≤ (Σ_e m_e)! = r! ≤ ⌊s/2⌋!` since every orbit has size `≥ 2`.
Next `s!/⌊s/2⌋! = ∏_{j=⌊s/2⌋+1}^{s} j ≥ (s/2)^{s/2}`.  Hence
`[S_s:N] ≥ (s/2)^{s/2}/D^s`, and with `D ≤ √s/2`,
`D^s ≤ s^{s/2}/2^s`, so the ratio is `≥ (s/2)^{s/2}·2^s/s^{s/2} = 2^{s/2}`. ∎

`2^{s/2} > s⁶` for all `s ≥ 76` (exact-integer check; last failure `s = 75`:
`v_task49_thresholds_out.txt`).  Note the slack: at `s = 10⁶` this case
delivers `2^{500000}` against a target of `2^{119.6}`.

This is the branch v_task48 already certified hypothesis-free; the only change
is that `d₀` is raised from `Θ(log s)` to `⌊√s/2⌋+1`, which the computation
above shows is exactly the largest scale the argument tolerates (the bound
degenerates to `1` at `D = √s/√2`).

---

## 3.  Case B: some orbit has size `d ≥ D+1 > √s/2`  [PROVEN, hypothesis-free]

Then `s < 4d²`, so **`s⁶ < 4096·d¹²`** — the target is now *polynomial* in the
degree of the dominant constituent.  Let `K := K₁` (transitive of degree `d`,
`d > √s/2 ≥ 211` in the range at issue) and `N_d := N_{S_d}(K)`.  `N_d` is
transitive (it contains `K`).  Two subcases.

### B1.  `A_d ≤ N_d`.  Then `|K′| ≥ d!/2`, so `v(H) ≥ d!/2`.  [PROVEN]

*Proof.*  `K ⊴ N_d`, so `K ∩ A_d ⊴ A_d`, which is simple (`d ≥ 5`).  If
`K ∩ A_d = 1` then `|K| ≤ [S_d:A_d] = 2`, impossible for `K` transitive of
degree `d ≥ 3`.  So `A_d ≤ K`, hence `K′ ⊇ A_d′ = A_d`, `|K′| ≥ d!/2`.  Now
`v(H) ≥ |K′|·[S_d:N_d] ≥ d!/2` by (★). ∎
*(Machine-checked as inequality (IV) for `s ≤ 11`.)*

### B2.  `A_d ⊄ N_d`.  Then `[S_d:N_d] ≥ min( ⌊(d+1)/2⌋! , 2^{d/2−1} )`.  [PROVEN]

*Proof.*  `N_d` is transitive of degree `d`, hence primitive or imprimitive.

* **Primitive.**  `N_d ≠ A_d, S_d`, so **Bochert's theorem** gives
  `[S_d : N_d] ≥ ⌊(d+1)/2⌋!`.
* **Imprimitive.**  `N_d ≤ S_a wr S_b` for some block system with `ab = d`,
  `a,b ≥ 2`, so `[S_d:N_d] ≥ P(d;a,b) := d!/((a!)^b·b!)`, the number of
  partitions of `d` points into `b` unordered blocks of size `a`.  Now

    `P(d;a,b) = ∏_{i=0}^{b−2} C(d − ia − 1, a − 1)`

  (choose the block containing the least unused point at each step).  Each
  factor has `d − ia = (b−i)a ≥ 2a`, so it is `≥ C(2a−1, a−1) ≥ 2^{a−1}`
  (`= ½C(2a,a) ≥ 2^{2a−1}/(2a+1) ≥ 2^{a−1}` for `a ≥ 3`, and `3 ≥ 2` at
  `a = 2`).  Hence `P ≥ 2^{(a−1)(b−1)}`, and
  `(a−1)(b−1) = d + 1 − (a+b) ≥ d + 1 − (d/2 + 2) = d/2 − 1`
  since `a + b ≤ d/2 + 2` when `ab = d`, `a,b ≥ 2`.  So `[S_d:N_d] ≥ 2^{d/2−1}`.
  ∎

*(The bound `P(d;a,b) ≥ 2^{d/2−1}` is verified exactly, over every
factorisation `ab = d`, for all `d ≤ 2000`: no failures.)*

Since `|K′| ≥ 1`, (★) gives `v(H) ≥ min(⌊(d+1)/2⌋!, 2^{d/2−1})` in case B2.

### Numerics of case B

All three case-B bounds `d!/2`, `⌊(d+1)/2⌋!`, `2^{d/2−1}` are increasing in
`d`, so the binding value is `d = D+1`.  Exact certification
(`v_task49_thresholds_out.txt`), with `d = ⌊√s/2⌋+1`:

| condition | last `s` at which it fails |
|---|---|
| `2^{s/2} > s⁶` (case A) | 75 |
| `d!/2 > s⁶` (B1) | 1763 |
| `min(⌊(d+1)/2⌋!, 2^{d/2−1}) > s⁶` (B2) | **178083** |

so **all three hold for every `s ≥ s₀ = 178084`**, checked on every integer
`s ∈ [4, 400000)` and extended to all `s` by monotonicity: `s/2 − 6log₂s` is
increasing for `s ≥ 18`, and `√s/4 − 1 − 6log₂ s` is increasing for
`s ≥ 4800` (derivative `1/(8√s) − 6/(s ln 2) > 0 ⟺ √s > 69.3`), both already
positive at `s = 400000`.  Exact-integer confirmation is printed at
`s = 178084` and at `s = 10⁶`.  Margins at `s = 10⁶` (log₂):
target `119.59`; case A `500000`; B1 `3775`; B2 `249.5`. ∎

**This proves Lemma V-BIG in general form with `s₀ = 178084`.**

---

## 4.  Remarks on the proof

1. **Where `|H′|` is (and is not) needed.**  Only in B1, and there it is
   overwhelming (`d!/2`).  Everywhere else `|H′| ≥ 1` suffices.  This is why
   the "metabelian `H` with tiny `H′`" corner the task worried about is not a
   corner at all: a tiny `H′` forces nothing, because at `d ≈ √s` the raw
   index of a proper transitive normaliser already beats `s⁶` by hundreds of
   orders of magnitude.  The abelian proof's holomorph input
   (`|N_{Sym(O)}(A)| = d·|Aut(A)| ≤ d^{1+log₂ d}` for regular abelian `A`) is
   **not used anywhere**; the general proof does not specialise to it.
2. **Bochert is avoidable.**  Any bound of the shape `|G| ≤ c^d` for primitive
   `G ⊉ A_d` does the job (Praeger–Saxl `|G| < 4^d`, or Babai's elementary
   `|G| < exp(4√d log²d)`), since `d!/4^d > s⁶` for `d ≥ 30`.  One may also
   drop the primitive/imprimitive split entirely by using
   `|N_d| ≤ |C_{S_d}(K)|·|Aut(K)| ≤ d·|Aut(K)|` when `K` is regular; but that
   route needs `Aut` control for non-regular `K` and is strictly worse.
3. **`N_{S_d}(K)` may be intransitive?**  No: `K ≤ N_d` and `K` is transitive
   on its orbit by construction.  This is the point at which "Ω is an orbit"
   is used, and it is used essentially.
4. **The claim is sharp in shape, not in constant.**  `min V_s` is genuinely
   *not* `> s⁶` for small `s`: `min V_10 = 945 < 10⁶` and
   `min V_11 = 4950 < 11⁶ = 1771561` (both computed exhaustively here).  A
   threshold is unavoidable; the content is that it is finite and explicit.

---

## 5.  Sharpening: `s₀ = 15876`  [PROVEN]

Two factors were thrown away in §3: `C(s,dm)` and all but one of the `m`
dominant-orbit factors of (★).  Keeping them, and rebalancing the split to
`D := ⌊2√s/3⌋`:

* **Case A** (`all orbits ≤ D`): as in §2, `[S_s:N] ≥ (s/2)^{s/2}/D^s` and
  `D ≤ 2√s/3` gives `D^s ≤ (4s/9)^{s/2}`, hence `v(H) ≥ (9/8)^{s/2}`.
* **Case B** (`d ≥ D+1 > 2√s/3`):
  * if some dominant constituent `K_i` has `A_d ≤ N_{S_d}(K_i)`: `v ≥ d!/2` (B1);
  * else every dominant constituent satisfies `[S_d:N_{S_d}(K_i)] ≥ β(d) :=
    min(⌊(d+1)/2⌋!, 2^{d/2−1}) ≥ 2^{d/2−1}`, and (★) in its full form gives
    `v(H) ≥ C(s,dm)·β(d)^m`.  Split on `dm`:
    * `dm ≥ s/2`: then `m ≥ s/(2d)` and
      `v ≥ 2^{m(d/2−1)} ≥ 2^{s/4 − s/(2d)} ≥ 2^{s/8}` (using `d ≥ 4`);
    * `dm < s/2`: then `C(s,dm) ≥ (s/(dm))^{dm} > 2^{dm} ≥ 2^{d} > 2^{⌊2√s/3⌋}`.

All four conditions `(9/8)^{s/2} > s⁶`, `d!/2 > s⁶`, `2^{s/8} > s⁶`,
`2^{⌊2√s/3⌋} > s⁶` hold for every `s ≥ 15876` (individual last failures
`661`, `840`, `417`, `15875`; exact-integer confirmation at `s = 15876`).

So **Lemma V-BIG holds for all `s ≥ 15876`**, all `H`.  Since the exponential
`2^{c√s}` must beat `s⁶`, no reshuffling of these constants gets below
`s ≈ 10⁴`; a genuinely smaller `s₀` would need a different mechanism (or
brute-force `V_s`, currently feasible only to `s = 11`).

---

## 6.  Consumption: Theorem GAP and (H2′)

### Corollary GAP-FREE  [PROVEN]

> For every `n ≥ n₀ := s₀ + 5 = 178089`,
> `I(A_n) ∩ (4C(n,4), 6C(n,5)) = ∅`, with **no** hypothesis on `H`
> (abelian or not).

*Proof.*  Let `1 ≠ H ≤ A_n` with `ind*(H) < 6C(n,5)` and `s := |supp H|`.
By the corrected Theorem SPEC (v_task48 §1),
`ind*(H) ∈ C(n,s)·(V_s ∪ ½V_s)`, the halving occurring only at `s ∈ {n−1,n}`.

* `s ≤ 5`: values `{C(n,3)} ∪ {1,3,4}C(n,4) ∪ {6,30,60}C(n,5)`, all outside
  the **open** interval (both endpoints are attained, so openness is used —
  v_task48 §2b).
* `6 ≤ s ≤ n−6`: `ind*(H) ≥ C(n,s)·min V_s ≥ C(n,6) = C(n,5)(n−5)/6 > 6C(n,5)`
  for `n > 41`, using only `min V_s ≥ 1`.
* `s ≥ n−5`: `ind*(H) ≥ ½·C(n,s)·min V_s ≥ ½ min V_s > s⁶/2` by Lemma V-BIG,
  valid since `s ≥ n−5 ≥ s₀`.  And `n ≤ s+5`, so
  `6C(n,5) ≤ 6n⁵/120 = n⁵/20 ≤ (s+5)⁵/20 ≤ (2s)⁵/20 = 8s⁵/5 < s⁶/2`
  for `s ≥ 4` (`(s+5) ≤ 2s` for `s ≥ 5`).  So `ind*(H) > 6C(n,5)`. ∎

### Effect on the hypothesis list

**(H2′)** ("no non-abelian `H ≤ A_n` of support `≥ 9` has
`ind*(H) < 6C(n,5)`") is exactly what Corollary GAP-FREE now supplies, for
`n ≥ 178089`.  And Theorem GAP is invoked **only** in the `n > 10¹¹` half of
Theorem AT — below `10¹¹`, rows 2 and 3 are killed by the exact scan
`v_task45_scan` (16 contiguous chunks, `10 ≤ n ≤ 10¹¹`, `0` survivors,
complete in `q` and `f` by construction), which does not go through the
`ind*`-hole at all.  Since `178089 ≪ 10¹¹`, **the two ranges overlap by six
orders of magnitude and (H2′) is never needed.**

> **Theorem AT (v_task49 form).**  For all `n ≥ 9`, no Fitting-free
> `T ≇ A_n` with `|T| = |A_n|` has `D(T) ≅ D(A_n)` — modulo **(H1)** cited
> classical facts **only**.  (H2)/(H2′)/(AB) are no longer inputs to this
> branch.

**Two honest caveats**, both outside the scope of this task:

1. (AB) may still be consumed elsewhere in the program at *small* `n` (see
   `v_task38_theorem_at_assembly.md` §3.5–3.6, input **I9**: the risk that a
   smaller true `ι₂(A_n)` invalidates the target `C(n,4)`).  What is proved
   here settles (AB) for **all** `H` at every `n ≥ 178089` (same three-case
   argument, with the threshold `3C(n,4)` in place of `6C(n,5)`, which is
   easier — with the crude §3 split the binding condition then holds from `s = 71824`).  For
   `9 ≤ n < 178089` the residue is exactly: `H` of support `s ∈ [n−5, n]` with
   `11 < s < 178084`, where `V_s` is neither computed nor covered by the
   asymptotic bound.  Whether Theorem AT's small-`n` scan itself needs (AB)
   is a separate audit question (it targets `C(n,3) = ι₁`, whose minimality
   over non-abelian `H` is the same kind of statement).
2. Everything above is about `I(A_n)`; the `T`-side statements (TR-1, TO′-0)
   are untouched.

---

## 7.  Machine verification

`v_task49_chain.g` re-derives `V_s` **from the definition** and checks, for
**every** conjugacy class of fixed-point-free `1 ≠ H ≤ A_s`, `s = 5..11`
(814 classes, 733 non-abelian):

| # | inequality | rôle |
|---|---|---|
| (I) | `\|N\| ≤ ∏_e (e!)^{m_e} m_e!` | Reduction 1 / case A |
| (II) | `\|N\| ≤ m!·∏_i\|N_{S_d}(K_i)\|·(s−dm)!` | Reduction 2 |
| (III) | `v(H) ≥ \|K_i′\|·[S_d:N_{S_d}(K_i)]` | (★) |
| (IV) | `A_d ≤ N_{S_d}(K_i) ⟹ A_d ≤ K_i` (`d ≥ 5`) | B1 |
| (V) | `\|H′\| ≥ \|K_i′\|` | (★) |
| (VI) | `[S_s:N] ≥ s!/(E^s·⌊s/2⌋!)`, `E` = max orbit size | case A shape |

**0 violations at every `s`.**  `V_s` reproduced identically to v_task47/48 at
`s ≤ 10` (`min V_7,…,V_10 = 35, 30, 280, 945`), and **new**:

  `min V_11 = 4950`,  `|V_11| = 46`  (364 fpf classes, 342 non-abelian).

Extending beyond `s = 11` is not cheap: the run time is dominated by
`ConjugacyClassesSubgroups(A_s)` and `s = 12` was not attempted.

`v_task49_thresholds.py` certifies, in exact integer arithmetic where the
numbers permit and in `lgamma` logs otherwise (with exact-integer spot checks
at every announced threshold): the three (resp. four) numeric conditions, the
least `s₀` in both the crude and sharpened forms, the partition bound
`P(d;a,b) ≥ 2^{d/2−1}` for all `d ≤ 2000` and all factorisations, and (for
orientation only) that `argmax_{ab=d}(a!)^b b!` is `b = 2`.

---

## 8.  Status table

| statement | status |
|---|---|
| Reduction 1 (`N ≤ ∏(S_e wr S_{m_e})`) | **[PROVEN]** + machine-checked `s ≤ 11` |
| Reduction 2 and (★) | **[PROVEN]** + machine-checked `s ≤ 11` |
| Case A (`all orbits ≤ ⌊√s/2⌋` ⟹ `v ≥ 2^{s/2}`) | **[PROVEN]**, hypothesis-free |
| Case B1 (`A_d ≤ N_{S_d}(K)` ⟹ `v ≥ d!/2`) | **[PROVEN]** (simplicity of `A_d` only) |
| Case B2 imprimitive (`[S_d:N_d] ≥ 2^{d/2−1}`) | **[PROVEN]** (elementary partition count) + exact check `d ≤ 2000` |
| Case B2 primitive (`[S_d:N_d] ≥ ⌊(d+1)/2⌋!`) | **[PROVEN]**, cites Bochert 1889 (H1-class; replaceable) |
| **Lemma V-BIG, general `H`, `s ≥ 178084`** | **[PROVEN]** |
| Lemma V-BIG, general `H`, `s ≥ 15876` (sharpened) | **[PROVEN]** |
| Corollary GAP-FREE (`n ≥ 178089`, all `H`) | **[PROVEN]** |
| **(H2′) discharged wherever Theorem AT uses it** | **[PROVEN]** (overlap `178089 ≤ 10¹¹` with the v_task45 scan) |
| `min V_11 = 4950` | **[COMPUTED]**, exhaustive |
| (AB)/I9 at `9 ≤ n < 178089`, support `∈ [n−5,n]` | **[OPEN]** — outside this task; not used by Theorem GAP |

---

## Reproduce

```
gap -q -b --nointeract v_task49_chain.g      # s = 5..10   (~minutes)
gap -q -b --nointeract v_task49_chain11.g    # s = 11      (~15 min, 24g workspace)
python3 v_task49_thresholds.py               # thresholds  (~minutes)
```
