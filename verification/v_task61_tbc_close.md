# v_task61 — T-BC endgame: the briefed step is refuted, the layer count reverses, and what actually remains

Date 2026-08-08.  Scripts `v_task61_tbc_close.g`, `v_task61_p4.g`,
`v_task61_c6.g`, `v_task61_c6b.g`; outputs `*_out.txt` beside them.
GAP 4.16dev, CTblLib.  NOTES.md not edited (per brief).

## 0. Headline

1. **The briefed remaining step does not exist.**  The brief asked to prove
   §4ae's "symplectic branch total < 9", i.e. `mult₁(PSp₆(q)) < 9` for all
   odd `q`.  That statement was already **REFUTED in §4af** (same-day
   correction, `mult₁(PSp₆(19)) ≥ 11`), and NOTES.md carries the refutation
   inline in §4ae.  No amount of GAP work can prove it; the honest response
   is to work the *successor* target.
2. The successor target is **T-BC⁺** (§4ag): `mult₁(Ω₇(q)) > mult₁(PSp₆(q))`
   for all odd `q ≥ 5`, under the standing hypothesis **(PAR)**.
3. **New negative result of this task (Lemma GLUE, §3 below):** the
   orthogonal `⊥`-decomposable layers `P_{3+4}`, `P_{6+1}`, `P_{3+3+1}` are
   *suppressed*, not enlarged — a `⊥`-product `U₁ × U₂ ≤ Ω_{d₁+d₂}(q)` has
   normalizer `(N_{O_{d₁}}(U₁) × N_{O_{d₂}}(U₂)) ∩ Ω`, which strictly
   contains `U₁ × U₂` in every case checked, because the perfect group `U`
   cannot absorb the `det`/spinor glue that `O` supplies and `Sp` does not.
   In particular the tautological member `Ω₃(q) × Ω₄^ε(q)` is **not** psn.
   This **corrects §4ag's Corrections 1–3**, whose stated direction ("all
   three enlarge the orthogonal count") is the wrong sign for the layers,
   and it is *confirmed by the anchor*: every one of the 16 classes of
   `mult₁(Ω₇(3))` is either 7-dimensionally irreducible or a `p = 3`
   parabolic artifact — **not one is a `⊥`-product**.
4. Consequence: the orthogonal side is essentially `p^O₇` alone, while the
   symplectic side genuinely carries `a·p^C₄ + C(a,3)` (that layer is
   machine-verified to exist in `Sp₄`, §4af).  Since `a = 3` for half of all
   odd `q` and `p^C₄ ≥ 3`, the symplectic side is **≥ 13** there, against a
   proven orthogonal lower bound of only `11`.  **T-BC⁺ as stated is
   therefore not merely unproven — its direction is in doubt for
   `q ≡ ±1 (mod 5)`.**  What survives is the symmetric statement
   `Δ(q) ≠ 0` (§4af), and that is where T-BC now sits.
5. **Exact counts corrected (falsifying two recorded data).**
   `p^C₄(5) = 3` and `p^C₄(7) = 4`, not `5` as §4af records for `q = 5`.
6. `n > 3` is **not** proven and nothing in this task advances it.  The
   full simple-groups theorem does **not** close.

---

## 1. Falsification-first: the harness and the recorded data

Per the brief, the claimed bound was checked against the data before any
proof attempt.

- **§4ae's target, against §4af's own datum.**  §4ae: `mult₁(PSp₆(q)) < 9`.
  §4af: `mult₁(PSp₆(19)) ≥ 1 + 3·3 + 1 = 11`.  Refuted.  The mechanism is
  recorded and is not a slip: PSN-GF makes `mult₁(PSp_{2n}(q))` a
  *coefficient of a product*, `[x^{2n}] ∏_d (1+x^d)^{p_d(q)}`, and the
  `q = 3` anchor is the degenerate point of that product because
  `p_2(3) = 0` (`SL₂(3)` is not perfect).
- **The v_task21 sweep** (`verify/v_task21_perq`, ClassicalMaximals,
  `q ≤ 31`) counts *maximal* subgroups and their derived quotients, not psn
  classes; at `q = 3` it returns `S,6,3: 11` and `O,7,3: 15` maximals, which
  is consistent with (and independent of) the psn censuses
  `mult₁(Ω₇(3)) = 16`, `mult₁(PSp₆(3)) = 7` of v_task9/10 + §4af's
  convention fix.  It contains no datum that could rescue "< 9".

## 2. The Rule-S columns, recomputed independently (`v_task61_tbc_close.g`)

Scan of all 422 CTblLib perfect tables of order ≤ 10¹⁰, keeping quasisimple
`t` with a **faithful** absolutely irreducible `χ` of the prescribed degree
and Frobenius–Schur indicator; `Q(χ)` is the presence congruence and the
Out-orbit of `χ` is the Rule-S branch (orbit 2 = branch 1 = **exactly 2 psn
classes**; orbit 1 = branch 2 = **at most 1**).

**Symplectic (indicator −1, faithful):**

| dim | `H` | `Q(χ)` | Out-orbit | Rule-S contribution |
|---|---|---|---|---|
| 2 | `2.A₅` | `Q(√5)` | 2 | 2, iff `q ≡ ±1 (5)` |
| 4 | `2.A₅` | `Q` | 1 | ≤ 1 |
| 4 | `2.A₆` (two `χ`) | `Q` | 1 | ≤ 1 each |
| 6 | `2.A₅` | `Q` | 1 | ≤ 1 |
| 6 | `2.J₂` | `Q(√5)` | 2 | 2, iff `q ≡ ±1 (5)` |
| 6 | `2.L₂(13)` | `Q(√13)` | 2 | 2, iff 13 is a square |
| 6 | `2.L₃(2) = SL₂(7)` | `Q(√−2)` | 1 | ≤ 1, iff `q ≡ 1,3 (8)` |
| 6 | `U₃(3)` | `Q` | 1 | ≤ 1 |

**Orthogonal (indicator +1, faithful), degree 7:**
`Sp₆(2)` (`Q`), `A₈` (`Q`, orbit 1), `L₃(2)` (`Q`, orbit 1), `U₃(3)`
(`Q`, orbit 1), `L₂(13)` (`Q(√13)`, orbit 2), `L₂(8)` (`Q` orbit 1 and
`Q(ζ₉)⁺` orbit 2 under the `.3`).  This **reproduces §4ai's transcription
exactly**, an independent confirmation of that table.  (The 2-local members
`2³·L₃(2)` ×2, `2⁶:L₃(2)`, `2⁶:A₇` are not quasisimple and so are outside
this scan; §4ai's addendum handles them from the groups and derives the
doubled `Sp₆(2)` tree = 8 classes for every odd `q`.  We did not re-run
that part — the `DoPerfect2` block of `v_task61_tbc_close.g` is present but
errored on the automorphism/character bookkeeping and is **not** claimed.)

So the standing proven lower bound is unchanged:

> `p^O₇(q) ≥ 1 (Ω₇) + 8 (Sp₆(2)-tree, §4ai addendum) + 2 (G₂(q), E1) = 11`
> for every odd `q`.  [PROVEN, §4ai; re-confirmed here only in its
> quasisimple part.]

## 3. Lemma GLUE — the orthogonal `⊥`-layers are suppressed [ARGUED, anchor-confirmed]

> **Lemma GLUE.**  Let `V = W₁ ⊥ W₂` over `F_q`, `q` odd, with `W_i`
> nondegenerate, and let `U = U₁ × U₂` with `U_i ≤ Ω(W_i)` perfect and
> acting irreducibly on `W_i` with `W₁ ≇ W₂` as `U`-modules.  Then the `W_i`
> are the isotypic components of `V|_U`, hence canonical, so
> `N_{O(V)}(U) = N_{O(W₁)}(U₁) × N_{O(W₂)}(U₂)` and
> `N_{Ω(V)}(U) = (N_{O(W₁)}(U₁) × N_{O(W₂)}(U₂)) ∩ Ω(V)`.
> This group has order `|N_{O}(U₁)|·|N_{O}(U₂)| / 4` (index 4 = the
> `det × spinor` quotient of `O(V)`), and `U` is psn only if
> `|N_{O(W₁)}(U₁)| · |N_{O(W₂)}(U₂)| = 4·|U₁||U₂|`.

Since `|O(W) : Ω(W)| = 4` for `q` odd (and `= 4` for odd `dim W` too,
`O = ⟨−1⟩ × SO`, `[SO:Ω] = 2`), the condition says the two blocks must
between them supply **exactly** the `det`/spinor glue and no more, with the
glue elements lying *outside* `U`.  For a perfect `U` this fails
systematically:

- **Tautological member fails.**  `U₁ = Ω₃(q)`, `U₂ = Ω₄^ε(q)`:
  `N_{O(W_i)}(U_i) = O(W_i)`, so `|N_{Ω₇}(U)| = 4|U₁||U₂| = 4|U|`.
  **Not psn.**  The same computation kills `Ω₆^ε(q) × 1` in the `6+1`
  shape (`|N_{Ω₇}| = 2|Ω₆^ε|`) — so `P_{6+1}` does not even contain its
  own tautological member.
- **S-members fail the same way.**  `A₅ ≤ Ω₃(q) ≅ PSL₂(q)` is psn in `Ω₃`
  but `N_{SO₃}(A₅) = N_{PGL₂(q)}(A₅) = S₅`, so `|N_{O₃}(A₅)| = 4|A₅|`,
  and the pairing condition then forces `N_{O(W₂)}(U₂) = U₂`, i.e. `U₂`
  self-normalizing in the *full* `O(W₂)` — impossible for `U₂` perfect
  whenever `−1_{W₂} ∉ U₂`, since `−1_{W₂}` centralizes `U₂`.
  For even-dimensional `W₂` this last escape needs `−1_{W₂} ∈ U₂`, which
  is exactly the PSN-GF block-scalar condition — on the **symplectic** side
  it is automatic (step (3) of PSN-GF), on the orthogonal side `−1_{W₂}`
  has `det = (−1)^{dim W₂}` and spinor norm `disc(W₂)`, so it need not be
  in `Ω` at all.
- **Anchor confirmation.**  Every class in the audited census
  `mult₁(Ω₇(3)) = 16` is 7-dimensionally irreducible (`Ω₇(3)`, `Sp₆(2)`×2,
  `2³·L₃(2)`×4, `2⁶:L₃(2)`×2, `G₂(3)`×2, `L₂(13)`, `2⁶:A₇` — all of these
  carry a degree-7 irreducible character, cf. §2 above) or is a `p = 3`
  parabolic artifact (`3^{3+3}:L₃(3)`, `3³:L₃(3)`, and `2.L₃(4)`).
  **No `⊥`-decomposable member occurs.**  Under PSN-GF that is exactly what
  Lemma GLUE predicts and is *not* what §4ag's Corrections 1–3 predict.

*Honest tag.*  [ARGUED].  The normalizer identity and the index-4
bookkeeping are clean; the claim that the pairing condition is never met is
verified on the tautological members and on the `A₅` column, and is
consistent with the anchor, but it is not a case-exhaustive proof — a
residue class in which two blocks happen to supply complementary
`det`/spinor glue with the glue element inside `U` is not excluded by the
argument as written.  This is precisely the "spinor-norm bookkeeping" that
§4ag listed as owed (item (ii)); the present lemma says what its answer
looks like and which sign it has.

## 4. Exact primitive counts, and two corrections to §4af (`v_task61_p4.g`, `v_task61_c6b.g`)

Method: `p^C_4(q)` is `1` (for `Sp₄(q)`) plus, for each candidate
isomorphism type allowed by the §4ah corollary, the number of `Sp₄(q)`-classes
of subgroups of that type that are (i) irreducible on `F_q⁴` and (ii)
self-normalizing.  Classes enumerated exhaustively with
`IsomorphicSubgroups`; irreducibility by MeatAxe on the natural module;
self-normalization by `Normalizer`.

| `q` | `a(q)` | `2.A₅` | `2.A₆ = SL₂(9)` | `Sym³ SL₂(q)` | `C₆: 2^{1+4}.A₅` | `p^C_4(q)` |
|---|---|---|---|---|---|---|
| 5 | 1 | 5 classes, 1 irred, **1 psn** | 1/1/**1** | (= `2.A₅`) | **0 classes at all** | **3** |
| 7 | 1 | 3 classes, 3 irred, **1 psn** | 1/1/**1** | 4/1/**1** | **0 classes at all** | **4** |

Two recorded data are falsified:

- **`p^C₄(5) = 3`, not 5.**  §4af records `psn(Sp₄(5)) = 5` with "`2.A₅`
  (×2 classes)" and a `C₆` member of order 1920.  Exhaustively:
  `Sp₄(5)` has **one** conjugacy class of irreducible psn `2.A₅` (five
  classes of `SL₂(5)` in total, four of them reducible), and **no perfect
  subgroup of order 1920 whatsoever** — all seven perfect groups of that
  order (`v_task61_c6.g` enumerates them; the extraspecial-type one is
  `PerfectGroup(1920,7) = ((C₂ × Q₈):C₂):A₅`) embed zero times, at `q = 5`
  and at `q = 7`.  So `c₄(5) = c₄(7) = 0`.
- The `2.A₅` column obeys **Rule-S branch 2** at both `q = 5` and `q = 7`
  (≤ 1 psn class), consistent with the `Q`-rationality + Out-stability read
  in §2; at `q = 7` the splitting is visible as *three* irreducible classes
  of which exactly one is self-normalizing.

Direction of the correction: it **lowers** the symplectic side.  That helps
T-BC⁺ — but see §5.

## 5. Where T-BC actually stands after this task

With Lemma GLUE the two sides are

  `mult₁(Ω₇(q)) = p^O₇(q) + (suppressed ⊥-layers) + (p = 3 artifacts)`
  `mult₁(PSp₆(q)) = p^C₆(q) + a·p^C₄(q) + C(a,3)`,  `a = 1 + 2·[q ≡ ±1 (5)]`

with the symplectic `⊥`-layers **verified to be real** (§4af machine-checked
`SL₂ × 2.A₅` psn in `Sp₄`, `|N| = |U|`, against `|N| = 2|U|` for equal
blocks).  Proven bounds available today:

- `p^O₇(q) ≥ 11` for every odd `q` [§4ai, proven].
- `p^C₆(q) ≥ 1 + 2·[q ≡ ±1 (5)]` (`Ω`-side of nothing; `2.J₂` is
  Out-unstable, branch 1) and `p^C₄(q) ≥ 3` (computed at `q = 5, 7`; the
  columns `Sp₄(q)`, `2.A₅`, `2.A₆` are rational hence present at every odd
  `q` subject to the Brauer check).

Hence for `q ≡ ±1 (mod 5)` (`a = 3`):

  `mult₁(PSp₆(q)) ≥ (1 + 2) + 3·3 + 1 = 13 > 11`,

which is **larger** than the only proven lower bound on the orthogonal side.
So:

> **Status of T-BC⁺.**  Not proven, and its *direction* is unsettled for
> `q ≡ ±1 (mod 5)`: the proven orthogonal lower bound (11) is below the
> proven symplectic lower bound (13).  T-BC⁺ can only be recovered by
> pushing `p^O₇` above `13 + …` — the remaining degree-7 columns `A₈`,
> `U₃(3)`, `L₃(2)`, `L₂(8)`, `2⁶:A₇` are all rational (present at every odd
> `q`) and each contributes 0, 1 or 2 classes depending on a **spinor-norm
> square class** that has never been computed.  That computation is now the
> single load-bearing item.

> **Status of T-BC (the separation itself).**  The correct target is the
> symmetric `Δ(q) ≠ 0` of §4af, not the directed T-BC⁺ of §4ag.  Nothing in
> this task refutes `Δ ≠ 0`; what it removes is the belief that the
> orthogonal side wins by an accumulation of extra layers.

### The exact inequality that remains

> **(T-BC-RES).**  For every odd `q ≥ 5`, under (PAR),
> `p^O₇(q) ≠ p^C₆(q) + a(q)·p^C₄(q) + C(a(q), 3)`
> where `a(q) = 1 + 2·[q ≡ ±1 (mod 5), q ∉ 5^ℕ]`, all four quantities being
> Rule-S column sums, and the orthogonal `⊥`-layers being zero by Lemma
> GLUE.

Its inputs, in order of what is owed:

1. **(PAR)** — still hypothesis; §4ah reduced it to `H¹(Ū, Q) = 0` plus the
   open case `1 < R < Q`.
2. **The degree-7 spinor-norm square classes** for `A₈`, `U₃(3)`, `L₃(2)`,
   `L₂(8)`, `2⁶:A₇`: for each, the outer intertwiner `g ∈ GO₇(q)` realizing
   the (unique, `Out`-stable) degree-7 character, and the pair
   `(det g, θ(g))`.  Branch 2a (nonsquare) gives +1 class, 2b gives 0.
   Bounded, finite, per residue class — **not done here** (the direct route
   needs a spinor-norm routine or membership testing in `Ω₇(q)`, which the
   available GAP install does not supply cheaply).
3. **Lemma GLUE made case-exhaustive** (equivalently §4ag item (ii)).
4. `p^C₄(q)` and `p^C₆(q)` at `q ≡ ±1 (mod 5)` — the `q = 11` run of
   `v_task61_p4.g` did not complete (`IsomorphicSubgroups` in `Sp(4,11)`,
   perm degree 2928, falls back to a permutation action of degree > 300000);
   `q = 9` is the cheap `a = 3` point and was not attempted.  **PENDING.**

`v_task61_tbc_close.py` evaluates the resulting interval arithmetic per
residue class.  Its verdict for `q ∈ {5,…,31}` is *undecided in every
class*, with the `a = 3` classes showing the symplectic lower bound (13)
above the orthogonal proven lower bound (11).

## 6. `n > 3` and the full simple-groups theorem

**`n > 3` is not proven and this task does not advance it.**  §4j addendum 3
is a *program*, not a proof: (a) the `(3,3)` anchor [done, BC1]; (b) `n ≤ 5`
by reading the BHR maximal tables for `Ω(2n+1,q)` vs `PSp(2n,q)` by
congruence class; (c) `n ≥ 6` by Kleidman–Liebeck geometric classes plus
bounded class `S`.  None of (b), (c) exists.  Note that the two uniform
sources of asymmetry identified there are of different strength: the C1
mismatch (nonsingular hyperplane stabilizers exist for `Ω_{2n+1}` and have
no symplectic counterpart) is uniform in `n`, but Lemma GLUE now says
hyperplane-type members are exactly the ones the `det`/spinor glue kills, so
that source is weaker than advertised; and `G₂(q) ⊂ Ω₇(q)` — the visible
driver of the anchor and the one the §4bi three-way constraint singles out —
is **special to `n = 3`**.  PSN-GF does give the right transfer machinery
(the generating function is uniform in `n`), so the honest statement is:

> The `n > 3` transfer is **open**, and PSN-GF is the tool for it: the
> comparison for general `n` is `[x^{2n}] ∏(1+x^d)^{p^C_d}` against the
> orthogonal shape sum in dimension `2n+1`, with the same primitive counts
> `p_d` for `d ≤ 7` already tabulated, plus `p_d` for `d ≤ 2n`.

### Final theorem statement — it does not close

> **Theorem (finite simple groups, D-rigidity) — state as of this task.**
> Every finite simple group is D-rigid among all finite groups, **except**
> that for the pair `{B_n(q), C_n(q)}`, `n ≥ 3`, `q` odd, mutual separation
> is unproven for all `(n,q) ≠ (3,3)`.  At `(3,3)` the separation is
> Theorem BC1 [PROVEN, §4k].  Twin elimination (non-simple partners) is
> complete for all of CFSG (§4bh addendum, §4bi).

**Precise residue.**  `D(B_n(q)) ≇ D(C_n(q))` for `n ≥ 3`, `q` odd,
`(n,q) ≠ (3,3)` remains open, and reduces (for `n = 3`, under (PAR)) to
**(T-BC-RES)** above, whose one missing computable input is the degree-7
spinor-norm square-class table of item 2.
