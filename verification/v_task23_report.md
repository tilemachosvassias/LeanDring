# v_task23 — the psn generating function, and the refutation of §4ae's closing target

**Date:** 2026-08-06.  **Engine:** GAP 4.15.1 (`~/gap-4.15.1/gap`, macOS).
**Companion notes:** `Even/NOTES.md` §4af.

## Objective

§4ae reduced theorem T-BC (`D(Ω₇(q)) ≇ D(PSp₆(q))` for all odd `q`) to the
single statement **`mult₁(PSp₆(q)) < 9` for all odd `q`**, set against the
uniform lower bound `mult₁(Ω₇(q)) ≥ 9`.  This run tests that statement, by
computing the perfect self-normalizing (psn) censuses of the *branches* of
the symplectic tree — `SL₂(q)` and `Sp₄(q)` — which §4ae left unbounded.

## Method

`RepresentativesPerfectSubgroups` (GAP's exact Holt/Plesken cyclic-extension
enumeration) on a faithful permutation representation, followed by
`Normalizer` per representative; `U` is a psn hit iff `|N| = |U| > 1`.  Same
protocol as v_task22.  Representations used: `SL(2,q)` via
`IsomorphismPermGroup`; `Sp(4,q)` on the `q⁴−1` nonzero vectors; `PSp(4,q)`
on the `(q⁴−1)/(q−1)` projective points.  For the targeted rank-2 tests,
subgroups were **constructed** (block-diagonal embeddings; `Sym³` of the
natural `SL₂`-module) rather than enumerated, and their normalizers computed
in the projective permutation group.

## Results

### 1. Rank-1 law (exhaustive, `v_task23_sl2*`, `v_task23_psl2*`)

`|psn(SL₂(q))| = 1 + 2·[ 5 ∣ q²−1 and q ∉ 5^ℕ ]`, verified at
`q = 5,7,9,11,13,17,19,23,25,27,29,31,49,81,121`.  The two extra classes are
the two `SL₂(q)`-classes of `SL₂(5) = 2.A₅`.  `|psn(PSL₂(q))| =
|psn(Ω₃(q))|` obeys the **same** law on the same `q`-list.

Subfield members are never psn (`SL₂(5) < SL₂(25)`, `SL₂(3) < SL₂(27)`,
`SL₂(7) < SL₂(49)`, `SL₂(9)/SL₂(3) < SL₂(81)`, `SL₂(11) < SL₂(121)`) —
machine confirmation of NOTES §4ab (E3).

### 2. Rank 2 at `q = 5` (exhaustive, `v_task23_sp4_q5*`)

`psn(Sp₄(5)) = 5`, all five irreducible on the 4-space: `2.A₅` (×2 classes),
`SL₂(9) = 2.A₆`, the `C₆` member `2^{1+4}.A₅` (order 1920), and `Sp₄(5)`.
Non-hits recorded with their normalizer indices: `SL₂(5)×SL₂(5)` (index 2 —
the block swap), `SL₂(25)` (index 2 — the `C₃` glue), `5³:SL₂(5)` and
`5^{1+2}:SL₂(5)` (index 4 — parabolic-contained).

### 3. The block-product law (constructed, `v_task23_blocks*`)

In `PSp₄(q)` for `q = 9, 11` (where the rank-1 count is 3):

| subgroup | q=9 | q=11 | psn |
|---|---|---|---|
| `SL₂ × SL₂` | \|N\|=2\|U\| | \|N\|=2\|U\| | **no** |
| `SL₂ × 2.A₅_a` | \|N\|=\|U\| | \|N\|=\|U\| | **yes** |
| `SL₂ × 2.A₅_b` | \|N\|=\|U\| | \|N\|=\|U\| | **yes** |
| `2.A₅_a × 2.A₅_b` | \|N\|=\|U\| | \|N\|=\|U\| | **yes** |
| `2.A₅_a × 2.A₅_a` | \|N\|=2\|U\| | \|N\|=2\|U\| | **no** |

Exactly the prediction of Theorem PSN-GF (NOTES §4af): a block product is
self-normalizing iff its factors are, **and** no two blocks carry the same
class — equal blocks are swapped, giving normalizer index exactly 2.  Both
directions confirmed.

### 4. Four-dimensional primitives via `Sym³` (constructed, `v_task23_sym3*`)

`Sym³` of the natural `SL₂(q)`-module is 4-dimensional and symplectic.
Images in `PSp₄(q)`:

| q | `Sym³ SL₂(q)` | `Sym³ 2.A₅` |
|---|---|---|
| 7 | psn (order 168) | — (no `2.A₅` in `SL₂(7)`) |
| 9 | — (char 3: no nondegenerate invariant alternating form) | — |
| 11 | psn (order 660) | **not** psn (`\|N\|=2\|U\|`, normalizer `S₅`) |
| 13 | psn (order 1092) | — |
| 19 | psn (order 3420) | **psn** (order 60) |

All hits verified irreducible (`MTX.IsIrreducible`).  The two
`SL₂(19)`-classes of `2.A₅` **fuse** under `Sym³` in `PSp₄(19)`
(`IsConjugate` = true, `v_task23_conj19*`), so they contribute one primitive.

## Verdict: §4ae's closing target is REFUTED

At `q = 19`: the rank-1 count is `3`, and there are at least `3`
four-dimensional primitives (`Sp₄(19)`, `Sym³ SL₂(19)`, `Sym³ 2.A₅`).  By
the product law,

`mult₁(PSp₆(19)) ≥ 1 (G) + 3·3 (the 2+4 layer) + 1 (the 2+2+2 layer) = 11 > 9`.

The symplectic branch total is **not** bounded by the `q = 3` anchor value 6:
it is a product over block decompositions and therefore grows with `q`.  The
anchor is the degenerate case — `SL₂(3)` is not perfect, so at `q = 3` the
entire `2+4` and `2+2+2` layers vanish.

This refutes one *reduction step* only.  BC1 (the `q = 3` separation,
computed) and `simpleGroupTheorem` (which carries `ExceptionSeparation` as a
hypothesis) are untouched.  The corrected finite form of T-BC is in NOTES
§4af.

## Incompletes, honestly flagged

- Exhaustive `RepresentativesPerfectSubgroups` runs on `PSp₄(9)` and
  `PSp₄(11)` were launched and **died on GAP's default memory limit** after
  ~20 min; the exact values `p₄(9)`, `p₄(11)` are therefore not known here.
  Nothing in the verdict depends on them — the `q = 19` instance is
  established by construction, and every constructed subgroup is a genuine
  witness regardless of census completeness.
- `p₄(19)` is a **lower** bound (≥ 3): only `Sym³`-constructible primitives
  and `Sp₄(19)` itself were tested.  The `C₆` member `2^{1+4}.A₅` and the
  `2.A₆`-type S-members were not constructed at `q = 19`.
- (PAR) — that no psn subgroup of `Sp_{2n}(q)` lies in a parabolic — is a
  hypothesis of Theorem PSN-GF and is false at `q = 3`.  Its `R = Q` case is
  settled (§9 below, with the exact index formula); its `R = 1` case reduces
  to an `H¹` vanishing; the intermediate case `1 < R < Q` is open.

## Files

`v_task23_sl2.g/_out.txt`, `v_task23_psl2.g/_out.txt`,
`v_task23_sp4_q5.g/_out.txt`, `v_task23_blocks.g/_out.txt`,
`v_task23_sym3.g/_out.txt`, `v_task23_conj19.g/_out.txt`.

---

# v_task23 (continued) — the orthogonal half

## 5. `Ω₅(q) ≅ PSp₄(q)`: cross-check and shape decomposition

`v_task23_omega5.g/_out.txt`.  Exhaustive census of `Ω₅(5)` (degree 781,
order 4,680,000), with the fixed-space dimension of each hit computed on the
natural 5-dimensional module:

| psn subgroup | irreducible on the 5-space | dim fixed space | shape |
|---|---|---|---|
| `A₅` (60) | no | 1 | `4+1` |
| `A₅` (60) | yes | 0 | `5` |
| `A₆` (360) | yes | 0 | `5` |
| `2⁴:A₅` (960) | yes | 0 | `5` |
| `Ω₅(5)` | yes | 0 | `5` |

Total 5 — **equal to `psn(Sp₄(5)) = 5`** computed independently in the
symplectic guise (§2 above), as the isomorphism `Ω₅(q) ≅ PSp₄(q)` requires.
The admissible orthogonal shapes for dim 5 are exactly `5` and `4+1`, and
both occur.  Note "primitive" is form-dependent: all five subgroups are
irreducible for the 4-dimensional symplectic module, only four for the
5-dimensional orthogonal one.

## 6. The `Ω₄` laws

`v_task23_omega4_faithful.g/_out.txt` (and `..._projective_*` for the
superseded first pass).

- **`Ω₄^-(q) ≅ PSL₂(q²)`**: psn count `= 1 + 2·[5 ∣ q⁴−1, q² ∉ 5^ℕ]`, i.e.
  the rank-1 law at `q²`.  Verified `q = 5,7,9,11,13` → `1,3,3,3,3`.
- **`Ω₄^+(q) ≅ (SL₂(q)×SL₂(q))/⟨(−1,−1)⟩`**: psn count `= a(q)²` exactly,
  `a(q)` the rank-1 count.  Verified `q = 5,7,9,11` → `1,1,9,9`.  The
  members are the **ordered** pairs of psn subgroups of the two tensor
  factors, equal pairs included, because the factor swap is not realized
  inside `Ω₄^+`.  No diagonal member occurs — Lemma D′ confirmed once more.

**Methodological warning recorded:** the first pass computed this census in
`Ω₄^+/Z` (the action on projective points has a kernel of order 2 here),
where diagonal subgroups *do* appear as psn.  The projective group is the
wrong object; the faithful action on nonzero vectors is required whenever
the isometry group has a center.  `Ω₄^-` and `Ω₅` have trivial center, so
their projective computations are valid.

## 7. Consequence: three asymmetries, all favouring the `Ω` side

See NOTES §4ag.  (1) The distinctness condition of PSN-GF applies only when
the block swap lies *inside* the group — always true for symplectic
`⊥`-blocks, not for odd-dimensional orthogonal blocks (swap determinant
`(−1)^k`), so the orthogonal layers count multisets rather than subsets.
(2) Lemma D′ kills diagonals via the block scalar `(−1_{W_i},1)`, which is
in `Sp` always but in `SO_7` only for even-dimensional blocks — so the
`3+3+1` shape may carry a diagonal layer with no symplectic counterpart.
(3) The orthogonal side has more shapes and the doubled `Sp₆(2)`/`G₂(q)`
primitive trees.  The target is therefore the *directed* statement
`mult₁(Ω₇(q)) > mult₁(PSp₆(q))`, not a symmetric non-coincidence.

## 8. Still running / not obtained

`Ω₅(7)` and `PSp₄(7)` (the same group, order 138,297,600, in its two
guises) were launched as a further cross-check and to obtain `p^C_4(7)`;
both were still inside `RepresentativesPerfectSubgroups` after ~25 min and
were **stopped** at session end rather than left running (the `PSp₄(9)` and
`PSp₄(11)` attempts had already exhausted GAP's default memory limit at this
size, so a much larger workspace would be needed).  `Ω₄^+(19)`, `Ω₄^-(19)`
likewise not obtained.  Nothing above depends on them; the scripts are in
place to re-run with `-o` on a larger machine.

## 9. The Siegel-parabolic index (constructed, `v_task23_siegel*`)

Tests the `R = Q` case of Lemma PAR-red (NOTES §4ah): is
`U = Q:SL_n(q)` — the derived group of the Siegel parabolic of
`Sp_{2n}(q)` — self-normalizing in `PSp_{2n}(q)`?  Built explicitly as
block matrices (Levi `diag(A, (A^{-1})^T` reversed`)`, unipotent radical the
symmetric upper-right block), then normalized inside the projective
permutation action.

| `(n,q)` | \|U\| | index \|N:U\| | psn |
|---|---|---|---|
| (2,5) | 7,500 | 4 | no |
| (2,7) | 57,624 | 6 | no |
| **(3,3)** | **4,094,064** | **1** | **yes** |
| (3,5) | 5,812,500,000 | 2 | no |
| (3,7) | 662,444,812,512 | 3 | no |
| (3,9) | 22,563,369,279,360 | 4 | no |

All six match `|N:U| = (q−1)/2` for `n` odd and `q−1` for `n` even, so
`U` is psn **iff `q = 3` and `n` odd**.  At `(3,3)` the order is
`3⁶·|L₃(3)| = 4,094,064` — this **is** the anchor's maximal `3⁶:L₃(3)`
(v_task9/v_task10), here reproduced from the block construction rather
than from AtlasRep.  The `q = 3` anomaly of §4z–§4ae is therefore a
specific arithmetic coincidence `(q−1)/2 = 1`, not a vague small-field
artifact.

Note the comparison must be made in `PSp`, not `Sp`: in `Sp_{2n}(q)` the
index is `q−1` throughout, and the extra factor 2 for odd `n` comes from
the scalar `−I_n` of the Levi being the global centre `−I_{2n}`.  A first
draft of the lemma missed this and would have wrongly excluded the
anchor's own member.

## 10. The S-columns from character tables (`v_task23_scols*`, `v_task23_ocols*`, `v_task23_outstab*`)

Exhaustive scan of CTblLib's 468 perfect character tables (order ≤ 10^10 resp.
10^11) for faithful absolutely irreducible characters of the relevant degrees
and Frobenius–Schur indicator (`−1` symplectic, `+1` orthogonal).  The
character field is the presence congruence; `Out`-stability of the character
(tested by inducing to the `.2` table and taking the norm: 2 = extends =
stable, 1 = moved) decides between the two branches of Rule S (NOTES §4ai).

**Symplectic deg 6:** `2.A₅` (ℚ, stable), `2.(A₅×A₅)` (ℚ(√5), the `C₄`
tensor member), `2.J₂` (ℚ(√5), unstable), `2.L₂(13)` (ℚ(√13), unstable),
`2.L₃(2)=SL₂(7)` (ℚ(√−2), stable), `U₃(3)` (ℚ, stable).
**deg 4:** `2.(2⁴:A₅)` (the `C₆` member), `2.A₅` (stable), `2.A₆`.
**deg 2:** `2.A₅` only (ℚ(√5), unstable) — which *proves* the rank-1 law
`p₂(q) = 1 + 2·[q ≡ ±1 mod 5]` observed in §1 above.

**Orthogonal deg 7:** `2³·L₃(2)` split and non-split (ℚ), `2⁶:L₃(2)` (ℚ),
`2⁶:A₇` (ℚ), `Sp₆(2)` (ℚ), `A₈` (ℚ), `L₃(2)` (ℚ), `U₃(3)` (ℚ), `L₂(13)`
(ℚ(√13)), `L₂(8)` (ℚ, ℚ(ζ₉)⁺).

Two independent confirmations fall out: the deg-6 fields reproduce §4ac's
transcription of the BHR symplectic S-table (`2.J₂` at `q ≡ ±1 mod 5`,
`2.L₂(13)` when 13 is a square mod `q`, `SL₂(7)` at `q ≡ 1,3 mod 8`), which
had never been checked against a source; and the deg-7 rational list contains
exactly `psn(Sp₆(2)) ∖ {L₃(2)}` from v_task22, so §4ae's "doubled `Sp₆(2)`
tree" falls out of a scan that knows nothing about `Ω₇`.

**The comparison:** the deg-7 orthogonal S-family is largely *rational*
(present at every odd `q`), the deg-6 symplectic one largely
congruence-conditional, and its two rational members are both `Out`-stable
(≤ 1 class each) — the quantitative source of T-BC.

*Not computed:* the multiplier square-classes for the `Out`-stable columns
(needed to turn "≤ 1 class" into an exact count per residue), and
`Out`-stability for the orthogonal deg-7 candidates.

## 11. The doubled `Sp₆(2)` tree, derived (`v_task23_outdeg7*`, `v_task23_modp*`, `v_task23_mod7*`)

**Out-stability, computed from the groups** (the 2-local members have no `.2`
table in CTblLib, so `AutomorphismGroup` was used and the induced permutation
of conjugacy classes applied to each character):

| group | #faithful deg-7 orthogonal χ | \|Out\| | both χ moved? | Rule S branch |
|---|---|---|---|---|
| `2³:L₃(2)` split = `PerfectGroup(1344,1)` | 2 | 2 | yes | one → 2 classes |
| `2³·L₃(2)` non-split = `PerfectGroup(1344,2)` | 2 | 2 | yes | one → 2 classes |
| `2⁶:L₃(2)` = `PerfectGroup(10752,8)` | 2 | 2 | yes | one → 2 classes |
| `Sp₆(2)` | 1 | 1 | — (Out = 1) | one → 2 classes |

Total `2+2+2+2 = 8` — §4ae's "doubled `Sp₆(2)` tree", previously observed at
`q = 3` and asserted uniform, now **derived for every odd `q`**.  (The two
characters being swapped by `Out` means the two embeddings have the same
image, so each group is one subgroup contributing two classes — matching the
anchor's `1344 ×4`, `10752 ×2`, `S6(2) ×2` exactly.)

**Presence at every odd `q`, completed.**  The characters are rational, so
only `p ∣ |H|` needs checking (`p ∤ |H|` ⟹ the reduction of an ordinary
irreducible stays irreducible).  Relevant primes: 3, 5, 7.  Brauer tables
(`v_task23_modp*`) give irreducibility mod 3, 5, 7 for `Sp₆(2)` and mod 3
for the 2-locals; CTblLib has no mod-7 Brauer tables for the latter, so that
case was settled with the MeatAxe (`v_task23_mod7*`): `PerfectGroup(1344,1)`,
`(1344,2)`, `(10752,8)` have 3, 3, 5 absolutely irreducible 7-dimensional
`GF(7)`-modules respectively.  No prime is left unchecked.

**Net:** `p^O_7(q) ≥ 1 + 8 + 2 (G₂) = 11` for every odd `q`, with the
doubling proven rather than observed.
