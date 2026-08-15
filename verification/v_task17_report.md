# v_task17: proven-tier separation of the 5 sporadic order-twins by conductor-1 multiplicity

## Objective

`v_task16` (`Even/NOTES.md` §4q addendum) separated the 5 sporadic/twin pairs
flagged by `v_task15` — M22, M24 (two witnesses), J2, Suz, Th — by class
count and involution count, but flagged this as **[COMPUTED]**, not proven:
class/involution counts sit behind the wall-blocked "Gap 1" invariant. The
proven-tier completion queued by §4q addendum is the **conductor-1
multiplicity `mult₁`** — by Satz 2.3.3/2.3.7 (§4j/§4k), the number of
conjugacy classes of **perfect self-normalizing (p.s.n.) subgroups** — which
is unconditionally intrinsic to `D(G)` (kernel-checked in
`Even/OrderTransfer.lean`, no wall involved).

**Result: all 6 pairs (M22, M24×2, J2, Suz, Th) are SEPARATED-PROVEN.** For
every pair the sporadic's `mult₁` lower bound strictly exceeds the twin's
*exact* `mult₁` value — four of the six twin values (M22, J2, M24(a), M24(b))
are additionally cross-checked by brute-force full census on the twin group
itself, not just the Goursat argument below.

## Method

**Part 2 (sporadics, cheap, Tier-1 lower bound).** Same method as `v_task9`:
`Maxes(CharacterTable(name))`, count maximal classes with exactly 1 linear
character (perfect). For `G` simple, every maximal subgroup is automatically
self-normalizing (if `N_G(M) > M` for maximal `M`, then `N_G(M) = G`, forcing
`M` normal in the simple group `G` — contradiction), so **perfect maximal
count + 1 (for `G` itself) is a genuine `mult₁` LOWER BOUND**, not just a
maximal-subgroup count. Script: `v_task17_part2_sporadics.g` /
`_out.txt`.

**Part 1 (twins, exact).** The key structural fact used throughout: every
twin here is `Aut`-type or partially-`Aut`-type, so the extension quotient
`T / Socle(T)` is **abelian** in all 6 cases (`C2×C2` for M22/J2/Suz/M24(a);
`C2` for M24(b); `C3` for Th, using the `U3(8).3_1` witness). Since perfect
groups map trivially into abelian quotients, **every perfect subgroup of `T`
lies inside `Socle(T)`** — this reduces the problem to a genuine
multi-factor Goursat analysis on the simple-group product `S1 × S2 (× S3)`,
tested for self-normalizing in the full (possibly bigger) ambient `T`.

For each factor `F` (bare simple group, or `Aut(S)`-type extension), first
compute `RepresentativesPerfectSubgroups(F)` exactly (GAP's Holt/Plesken
cyclic-extension algorithm) and flag which classes are self-normalizing
*within F itself* ("own p.s.n. count"). By Goursat's lemma, every subgroup
`U ≤ A×B` corresponds to `(U1,N1,U2,N2,φ: U1/N1≅U2/N2)`; if `U` is perfect
then `U1 = pr_A(U)` and `U2 = pr_B(U)` are themselves perfect (homomorphic
images of a perfect group are perfect), so `U1,U2` range over each factor's
own `RepresentativesPerfectSubgroups` list — a *closed* case analysis, not a
heuristic. Two ways a candidate is ruled out:

- **Product terms** `U = U1 × U2` (`N1=U1`, `N2=U2`, quotient `Q=1`):
  self-normalizing iff `U1`, `U2` are each self-normalizing *in their own
  factor* — so the product-term count is exactly `own(A) × own(B)` (×
  `own(C)` for 3 factors).
- **Diagonal terms** (`N1=1`, since every base simple group used here is
  simple, so `N1 ⊴ U1` forces `N1 ∈ {1,U1}`): need a matching perfect
  subquotient `Q ≅ U1` inside the *other* factor. Ruled out by a clean
  **Lagrange/coprimality argument** in the two cases too large to brute
  force (Suz, Th): each has a "private prime" dividing one factor's derived
  group but not the other factor's order at all, so no subgroup of the
  right order can exist on the other side.

Where the twin's total order was tractable (M22: 443520, J2: 604800, M24(a)
and M24(b): 244823040 each), `RepresentativesPerfectSubgroups` was also run
**directly on the full twin group** as a brute-force cross-check — this
requires no Goursat argument at all and is ground truth. Suz (`|T| ≈
4.48×10^11`) and Th (`|T| ≈ 9.07×10^16`) are far beyond this; those two rely
on the Goursat + coprimality proof only, backed by *exact* (not bounded)
factor-level census data.

## Factor-level own-p.s.n. census (all exact)

| Factor | Order | `RepresentativesPerfectSubgroups` | own p.s.n. (nontrivial) | Script |
|---|---|---|---|---|
| `PGL(2,7)` (=`L2(7).2`, M22) | 336 | `{1, L2(7)}` | **0** | `v_task17_probe2.g` |
| `PGL(2,11)` (=`L2(11).2`, M22) | 1320 | `{1, A5, L2(11)}` | **1** (`A5`) | `v_task17_probe2.g` |
| `S5` (=`A5.2`, J2) | 120 | `{1, A5}` | **0** | `v_task17_probe2.g` |
| `S7` (=`A7.2`, J2) | 5040 | `{1, A5×2, A6, L2(7), A7}` | **1** (`L2(7)`) | `v_task17_probe2.g` |
| `A8` (M24(a) factor) | 20160 | 11 classes | **7** | `v_task17_probe2.g` |
| `S8` (=`A8.2`, M24(b)) | 40320 | 9 classes | **2** (`L2(7)`, `2^3:L2(7)`) | `v_task17_probe2.g` |
| `PGL(2,23)` (=`L2(23).2`, M24(a)) | 12144 | `{1, L2(23)}` | **0** | `v_task17_probe4.g` |
| `L2(23)` bare (M24(b)) | 6072 | `{1, L2(23)}` | **1** (itself, trivial ambient) | `v_task17_probe4.g` |
| `L3(3).2` = `Aut(L3(3))` (Suz) | 11232 | `{1, L3(3)}` | **0** | `v_task17_probe5.g` |
| `L3(3)` bare (Th) | 5616 | `{1, L3(3)}` | **1** (itself) | `v_task17_probe5.g` |
| `L2(125)` bare (Th) | 976500 | `{1, A5, L2(125)}` | **2** (`A5`, itself) | `v_task17_probe5.g` |
| `U3(8)` (Th, natural degree-513 rep) | 5515776 | `{1, L2(8), U3(8)}` | **1** (itself only) | `v_task17_u38_census.g` |

`U3(8)`'s native GAP permutation representation is degree 4161 (too slow for
`RepresentativesPerfectSubgroups` — aborted after being clearly the
bottleneck, `v_task17_probe7_out.txt`); `SmallerDegreePermutationRepresentation`
reduces it to the natural degree-513 action on the Hermitian unital
(`v_task17_u38_census.g`), on which the full census completed in 18s.

## Twin-by-twin verdicts

**M22 = `PGL(2,7) × PGL(2,11)`.** Direct full census on the twin
(`v_task17_probe3.g`): 6 perfect-subgroup classes total, **all 6
`selfnorm=false`**. **`mult₁ = 0` exact.**

**J2 = `S5 × S7`.** Direct full census (`v_task17_probe3.g`): 14 classes
(including two genuine diagonal `A5` subgroups, confirming the task's
warning about subdirect products is a real phenomenon here — but none of
them, nor any product term, is self-normalizing). **All 14
`selfnorm=false`. `mult₁ = 0` exact.**

**M24(a) = `L2(23).2 × A8` (= `PGL(2,23) × A8`).** Direct full census
(`v_task17_m24a_direct.g`): 20 classes, **all `selfnorm=false`**. **`mult₁ =
0` exact.**

**M24(b) = `L2(23) × S8`.** Direct full census (`v_task17_m24b_direct.g`):
16 classes; exactly **2** are self-normalizing: `PSL(3,2) × PSL(2,23)`
(order 1,020,096 — one of its two G-classes) and `((C2×C2×C2):PSL(3,2)) ×
PSL(2,23)` (order 8,160,768). Matches the hand Goursat prediction exactly
(`own(L2(23))=1 × own(S8)=2 = 2`, both product-term combinations realized,
no diagonal since `L2(23)` is simple with `L2(23)` itself as the only
nontrivial own class, self-normalizing since here the factor is used bare —
i.e. `L2(23)` is literally its own ambient in this witness, unlike the `.2`
witness in (a)). **`mult₁ = 2` exact.**

**Suz = `L3(3).2 × S11`.** Twin order ≈ 4.48×10^11 — brute force infeasible.
Goursat argument: `own(L3(3).2) = 0` (exact, `v_task17_probe5.g`), so no
product term regardless of `S11`. Diagonal: the only nontrivial perfect
subgroup of `L3(3).2` is `L3(3)` itself (order `5616 = 2^4·3^3·13`); a
diagonal needs a subgroup of `S11` with a quotient of order divisible by 13,
but `13 ∤ |S11| = 11! = 39916800` (`v_task17_coprimality_checks.g`, GAP-verified
arithmetic) — no such subgroup of `S11` can exist, period, regardless of
`S11`'s internal structure. **`mult₁ = 0` exact**, proven without needing
`S11`'s own perfect-subgroup census at all.

**Th = `L3(3) × L2(125) × U3(8).3` (witness `U3(8).3_1`).** Twin order ≈
9.07×10^16 — brute force infeasible. Reduction: `L3(3)` is bare (own p.s.n.
= 1, itself) and minimal-simple (`{1,L3(3)}` only, `13 | |L3(3)|`, and
`13 ∤ |L2(125) × U3(8).3|` since neither factor's order contains 13) — the
same coprimality argument as Suz forces every p.s.n. subgroup of the full
triple product to have `L3(3)` as its full first-factor projection, so
`mult₁(Th twin) = mult₁(L2(125) × U3(8).3)` exactly (the `L3(3)` factor
contributes multiplicatively as `1×`, not `0×`, since it is self-normalizing
in its own bare ambient). For the remaining 2-factor problem:

- Product term = `own(L2(125)) × own(U3(8).3)`. `own(L2(125)) = 2` (`A5`,
  itself). `own(U3(8).3)`: perfect subgroups of `U3(8).3` lie in `U3(8)`
  (abelian `C3` quotient), whose exact perfect-subgroup list is `{1, L2(8),
  U3(8)}` with **neither `L2(8)` nor `U3(8)` self-normalizing already
  inside the smaller ambient `U3(8)` itself** (`v_task17_u38_census.g`) —
  and normalizers only grow under group extension (`N_H(U) ⊆ N_K(U)` for
  `H ≤ K`), so neither becomes self-normalizing in the bigger `U3(8).3`
  either. `own(U3(8).3) = 0`. Product term = `2×0 = 0`.
- Diagonal from the `A5` slot: needs a subgroup of `U3(8)` with a quotient
  `≅ A5` (order 60); `U3(8)`'s only perfect subgroups are the simple groups
  `L2(8)` and `U3(8)` itself, whose only quotients are trivial or
  themselves — neither is `A5`. Ruled out.
- Diagonal from the `L2(125)` slot: needs `31 | |U3(8).3|`; `|U3(8).3| =
  2^9·3^5·7·19 = 16547328`, no factor of 31 (`v_task17_coprimality_checks.g`).
  Ruled out.

**`mult₁(Th twin) = 0` exact.**

## Summary table

| Sporadic | Twin witness | Sporadic `mult₁` | Twin `mult₁` | Basis | Verdict |
|---|---|---|---|---|---|
| M22 | `PGL(2,7) × PGL(2,11)` | **≥ 7** | **0** (exact) | twin: direct full census | **SEPARATED-PROVEN** |
| M24 | `L2(23).2 × A8` | **≥ 5** | **0** (exact) | twin: direct full census | **SEPARATED-PROVEN** |
| M24 | `L2(23) × S8` | **≥ 5** | **2** (exact) | twin: direct full census | **SEPARATED-PROVEN** |
| J2 | `S5 × S7` | **≥ 4** | **0** (exact) | twin: direct full census | **SEPARATED-PROVEN** |
| Suz | `L3(3).2 × S11` | **≥ 8** | **0** (exact) | twin: Goursat + 13-coprimality proof | **SEPARATED-PROVEN** |
| Th | `L3(3) × L2(125) × U3(8).3` | **≥ 4** | **0** (exact) | twin: Goursat reduction + exact `U3(8)` census + monotonicity + 31-coprimality | **SEPARATED-PROVEN** |

Sporadic lower bounds (Part 2, `v_task17_part2_sporadics.g`): M22 = 6 perfect
maximal classes + 1 = **≥7**; M24 = 4+1 = **≥5**; J2 = 3+1 = **≥4**; Suz =
7+1 = **≥8**; Th = 3+1 = **≥4**. These are lower bounds only (a genuine
Tier-1.5 census, as done for O7(3)/S6(3) in `v_task10`, would only raise
them further) — but since they already strictly exceed every twin's *exact*
value, no completion of the sporadic side is needed for separation.

## Verdict

**All 5 sporadics (6 pairs, counting M24's two witnesses) are
SEPARATED-PROVEN from their arithmetic order-twins by the conductor-1
multiplicity — an unconditional D-ring invariant with no wall involved.**
This closes the gap left by `v_task16`'s [COMPUTED]-only class/involution
separation: `v_task15`'s "5 need finer invariants" queue (`Even/NOTES.md`
§4q) is now fully resolved at proven tier. Combined with the 19
already-fully-D-rigid sporadics (§4q) and the SR1 apparatus (§4j–§4l), 24 of
26 sporadics are now proven D-rigid among all finite groups within the
program's stated CFSG-order-arithmetic scope; B and M remain flagged
inconclusive (orders beyond the candidate-generation bound, per §4q).

## Files

- `v_task17_probe1.g/_out.txt` — sanity check: `RepresentativesPerfectSubgroups`
  on `PSL(2,7)`, `PGL(2,7)`; `DirectProduct` construction timing.
- `v_task17_probe2.g/_out.txt` — own p.s.n. census: `PGL(2,7)`, `PGL(2,11)`,
  `S5`, `S7`, `A8`, `S8`.
- `v_task17_probe3.g/_out.txt` — direct full census, M22 twin and J2 twin.
- `v_task17_probe4.g/_out.txt` — own p.s.n. census: `PGL(2,23)`, `PSL(2,23)`.
- `v_task17_probe5.g/_out.txt` — own p.s.n. census: `L3(3).2` (via
  `AutomorphismGroup`), `L3(3)` bare, `L2(125)` bare.
- `v_task17_probe6.g/_out.txt` — CharacterTable-Maxes probe for `U3(8)`/
  `U3(8).3` variants: `CharacterTable("U3(8).3")` returns `fail`;
  `"U3(8).3_1/_2/_3"` load but `Maxes()` on them raises a GAP error (no
  method found) rather than returning stored data — dead end, superseded by
  the direct `U3(8)` census — and `A11`/`S11` cross-reference data (not
  needed for the Suz verdict, which is settled by the 13-coprimality
  argument independent of `S11`'s internal structure, but recorded for
  reference).
- `v_task17_probe7.g/_out.txt` — **aborted route**: `IsomorphismPermGroup`
  on `PSU(3,8)` gives a degree-4161 representation, too slow; killed and
  superseded by `v_task17_u38_census.g`.
- `v_task17_probe8.g/_out.txt`, `v_task17_probe8b.g` — dead-end/diagnostic:
  GAP's built-in `PSU(3,8)` is already a (large-degree) permutation group,
  not a matrix group as assumed.
- `v_task17_u38_census.g/_out.txt` — full exact census of `U3(8)` on its
  natural degree-513 representation (via
  `SmallerDegreePermutationRepresentation`).
- `v_task17_part2_sporadics.g/_out.txt` — Tier-1 `mult₁` lower bounds for
  M22, M24, J2, Suz, Th via perfect maximal classes.
- `v_task17_m24a_direct.g/_out.txt`, `v_task17_m24b_direct.g/_out.txt` —
  direct full census, M24 twins (a) and (b).
- `v_task17_coprimality_checks.g/_out.txt` — GAP-verified arithmetic behind
  the Suz and Th "no diagonal" arguments (13 ∤ |S11|, 23 ∤ |A8|/|S8|,
  31 ∤ |U3(8).3|).

All raw logs audited directly (exit 0 on every run except the two
explicitly-noted aborted/killed probes, which are honestly reported as dead
ends, not silently dropped).
