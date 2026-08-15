# v_task16: existence and separation of the 5 sporadic order-twins from v_task15

## Objective

`v_task15` (see `Even/NOTES.md` §4q) flagged 5 of the 26 sporadic simple
groups as having an *arithmetic* Fitting-free order-twin — a factorization
`|M| = |S1|·|S2|(·|S3|)·c` with `c | prod_i |Out(Si)|` — for which the cheap
SR1 divisibility test alone cannot certify D-rigidity:

| Sporadic | Socle factors | `c` | `prod |Out(Si)|` |
|---|---|---|---|
| M22 | L2(7) × L2(11) | 4 | Out(L2(7))·Out(L2(11)) = 2·2 = 4 |
| M24 | L2(23) × A8 | 2 | Out(L2(23))·Out(A8) = 2·2 = 4 |
| J2 | A5 × A7 | 4 | Out(A5)·Out(A7) = 2·2 = 4 |
| Suz | L3(3) × A11 | 4 | Out(L3(3))·Out(A11) = 2·2 = 4 |
| Th | L3(3) × L2(125) × U3(8) | 3 | Out(L3(3))·Out(L2(125))·Out(U3(8)) = 2·6·18 = 216 |

`c | prod|Out(Si)|` as a *number* is necessary but not sufficient: `c` must
be realizable as an actual **subgroup** of `Out(socle) = prod_i Out(Si)`
(valid here because in all 5 cases the factors are pairwise non-isomorphic,
so `Aut(socle) = prod_i Aut(Si)` exactly, no wreath/permutation term). Task
16 checks this existence condition first, then — for every twin that does
exist — separates it from the sporadic by two proven-cheap invariants:
number of conjugacy classes and involution count, computed exactly in GAP
from character tables (sporadic's own ATLAS table vs. a concretely
constructed witness group of matching order).

Files: `v_task16_twins.g` (script), `v_task16_out.txt` (raw log, run via
`gap -q < v_task16_twins.g > v_task16_out.txt`, exit 0, ~85s). All figures
below are quoted directly from `v_task16_out.txt`.

## Existence check (per pair)

**M22, J2, Suz — the "`c` = whole `Out(socle)`" cases.** In all three,
`Out(socle) = Out(S1) × Out(S2) = C2 × C2` (order 4), and `c = 4` equals the
order of the *entire* group `Out(socle)`. The full group is trivially a
subgroup of itself, so `c=4` embeds — **but only as the elementary abelian
`C2×C2`, not as cyclic `C4`** (the unique order-4 subgroup of `C2×C2` is
`C2×C2` itself; `C4` does not embed in `C2×C2` at all). This does not kill
existence, it just fixes which extension is realized: the twin is
`(S1×S2).(2×2)`, concretely `Aut(S1) × Aut(S2)` (the outer `C2×C2` acting
factorwise, independently on each `Si`):

- M22: witness = `Aut(L2(7)) × Aut(L2(11)) = PGL(2,7) × PGL(2,11)` =
  `L2(7).2 × L2(11).2`, order `336 × 1320 = 443520 = |M22|`. **EXISTS.**
- J2: witness = `Aut(A5) × Aut(A7) = S5 × S7` = `A5.2 × A7.2`, order
  `120 × 5040 = 604800 = |J2|`. **EXISTS.**
- Suz: witness = `Aut(L3(3)) × Aut(A11) = L3(3).2 × S11`, order
  `11232 × 39916800 = 448345497600 = |Suz|`. **EXISTS.**

**M24 — `c=2` in `Out(socle) = C2 × C2`.** Any group of even order has a
subgroup of order 2 (Cauchy); `C2×C2` concretely has three. Two independent
constructive witnesses (extend one factor's outer automorphism at a time):

- (a) `L2(23).2 × A8`, order `12144 × 20160 = 244823040 = |M24|`.
- (b) `L2(23) × A8.2` (`= L2(23) × S8`), order `6072 × 40320 = 244823040 = |M24|`.
- (a third "diagonal" order-2 subgroup of `C2×C2` also exists as a
  fiber-product/subdirect subgroup of `L2(23).2 × A8.2` of index 2; not
  separately constructed since (a)/(b) already witness existence.)

**M24 EXISTS** (two independent witnesses).

**Th — `c=3` in `Out(socle) = Out(L3(3)) × Out(L2(125)) × Out(U3(8)) = C2 ×
C6 × (S3×3)`, order `2·6·18 = 216`.** `3 | 216`, so by Cauchy's theorem this
order-216 group has an element (hence a subgroup) of order 3 — existence
needs no further structural argument since `c` is prime. Note: GAP's
character-table library confirms `Out(U3(8))` has structure `S3 × C3`
(non-abelian, library name `U3(8).(S3x3)`), *not* cyclic `C18` as a naive
"multiply the d.f.g factors" guess might suggest — but this doesn't matter
for a prime `c=3`, only for the choice of which of the several
non-conjugate order-3 subgroups to use. Witness: extend the `U3(8)` factor
only, by one of its three ATLAS-distinct order-3 subgroups (library names
`U3(8).3_1`, `.3_2`, `.3_3`):

- `L3(3) × L2(125) × U3(8).3_1`, order `5616 × 976500 × 16547328 =
  90745943887872000 = |Th|`.

**Th EXISTS.**

**Verdict: all 5 twins EXIST as genuine groups.** The existence check does
not kill any of the five candidates — none of the 5 sporadics is upgraded
to fully-rigid by this step alone.

## Invariant comparison (from `v_task16_out.txt`)

| Sporadic | Twin witness | Order match | Nr. classes (sporadic / twin) | Involutions (sporadic / twin) | Verdict |
|---|---|---|---|---|---|
| M22 | `L2(7).2 × L2(11).2` | OK (443520) | 12 / **117** | 1155 / **6099** | **SEPARATED** |
| J2 | `A5.2 × A7.2` | OK (604800) | 21 / **105** | 2835 / **6031** | **SEPARATED** |
| Suz | `L3(3).2 × A11.2` | OK (448345497600) | 43 / **840** | 2915055 / **12564991** | **SEPARATED** |
| M24 (a) | `L2(23).2 × A8` | OK (244823040) | 26 / **350** | 43263 / **167479** | **SEPARATED** |
| M24 (b) | `L2(23) × A8.2` | OK (244823040) | 26 / **308** | 43263 / **194055** | **SEPARATED** |
| Th | `L3(3) × L2(125) × U3(8).3_1` | OK (90745943887872000) | 48 / **28080** | 976841775 / **3338289855** | **SEPARATED** |

Every pair is separated by *both* invariants simultaneously (class count
and involution count each differ, usually by a large margin — e.g. Th: 48
vs 28080 classes), so the conductor-1 (perfect self-normalizing subgroup)
count from §4k/v_task9 was not needed for any of the 5; it would only be
required if class-count and involution-count had coincidentally agreed.

## Summary

| Sporadic | Twin | Existence | Separator | Sporadic value | Twin value |
|---|---|---|---|---|---|
| M22 | `PGL(2,7)×PGL(2,11)` | EXISTS | Nr. classes | 12 | 117 |
| M24 | `L2(23).2×A8` (or `L2(23)×S8`) | EXISTS | Nr. classes | 26 | 350 (or 308) |
| J2 | `S5×S7` | EXISTS | Nr. classes | 21 | 105 |
| Suz | `L3(3).2×S11` | EXISTS | Nr. classes | 43 | 840 |
| Th | `L3(3)×L2(125)×U3(8).3_1` | EXISTS | Nr. classes | 48 | 28080 |

**All 5 sporadics are SEPARATED** from their arithmetic order-twin by an
exactly-computed, proven-cheap invariant (number of conjugacy classes,
corroborated by involution count) — none is upgraded to fully-rigid by
non-existence, and none is left OPEN.
