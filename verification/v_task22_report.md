# v_task22 — perfect self-normalizing (p.s.n.) census: Sp6(2), U4(2), A7, G2(3)

## Objective

Fixed finite-group (q-independent) data feeding theorem T-BC (`NOTES.md`
§4z–§4ac): for each of `Sp6(2)`, `U4(2)`, `A7`, `G2(3)`, the full list of
conjugacy classes of perfect self-normalizing (p.s.n.) subgroups
`U` (`U = U'`, `N_G(U) = U`), including `G` itself.

## Method

`RepresentativesPerfectSubgroups(G)` (GAP's exact, deterministic Holt/Plesken
cyclic-extension algorithm — not a heuristic or bound) run directly on a
faithful permutation representation of `G`, exactly as in
`v_task17_u38_census.g`. For every representative `U`, `Normalizer(G,U)` is
computed; `U` is a p.s.n. hit iff `Size(Normalizer(G,U)) = Size(U)` (and
`U > 1`). Since `RepresentativesPerfectSubgroups` enumerates **all**
conjugacy classes of perfect subgroups exhaustively, every count below is
exact and complete — no recursion through maximal subgroups (the `v_task10`
fallback method) was needed for any of the four groups.

Permutation representations used:
- `Sp6(2)`: `AtlasGroup("S6(2)")`, native degree 28 (order 1,451,520).
- `U4(2)`: `AtlasGroup("U4(2)")`, native degree 27 (order 25,920).
- `A7`: `AlternatingGroup(7)`, natural degree 7 (order 2,520).
- `G2(3)`: AtlasRep stores **no** permutation representation for `G2(3)`
  (only matrix reps in its 25-entry representation table, `v_task22_probe2_out.txt`).
  Built degree-351 permutation rep via `FactorCosetAction(G, M1)` where
  `M1 = AtlasSubgroup("G2(3)", 1)` is the smallest-index maximal subgroup
  (`U3(3).2`, order 12096, index 351); confirmed faithful
  (`Size(pg) = Size(G)`), `v_task22_g23_probe3.g/_out.txt`.

All runs completed with exit 0, no timeouts, no aborted branches.

## Results

### Sp6(2) (order 1,451,520)

`RepresentativesPerfectSubgroups`: **21** perfect-subgroup classes total.
**psn count: 5.**

| order | StructureDescription | # G-classes |
|---|---|---|
| 168 | PSL(3,2) | 1 |
| 1344 | (C2×C2×C2):PSL(3,2) [split] | 1 |
| 1344 | (C2×C2×C2).PSL(3,2) [non-split] | 1 |
| 10752 | (C2×C2×C2×C2×C2×C2):PSL(3,2) | 1 |
| 1,451,520 | O(7,2) [= Sp6(2) itself] | 1 |

Script/log: `v_task22_psn.g` / `v_task22_psn_out.txt`.

### U4(2) (order 25,920)

`RepresentativesPerfectSubgroups`: **6** perfect-subgroup classes total.
**psn count: 2.**

| order | StructureDescription | # G-classes |
|---|---|---|
| 960 | (C2×C2×C2×C2):A5 | 1 |
| 25,920 | O(5,3) [= U4(2) itself] | 1 |

Script/log: `v_task22_psn.g` / `v_task22_psn_out.txt`.

### A7 (order 2,520)

`RepresentativesPerfectSubgroups`: **7** perfect-subgroup classes total.
**psn count: 5.**

| order | StructureDescription | # G-classes |
|---|---|---|
| 60 | A5 | 1 |
| 168 | PSL(3,2) | 2 |
| 360 | A6 | 1 |
| 2,520 | A7 [= A7 itself] | 1 |

Script/log: `v_task22_psn.g` / `v_task22_psn_out.txt`.

### G2(3) (order 4,245,696)

`RepresentativesPerfectSubgroups`: **11** perfect-subgroup classes total
(degree-351 rep, ~67s). **psn count: 3.**

| order | StructureDescription | # G-classes |
|---|---|---|
| 1,092 | PSL(2,13) | 1 |
| 1,344 | (C2×C2×C2).PSL(3,2) | 1 |
| 4,245,696 | G(2,3) [= G2(3) itself] | 1 |

Non-hits (perfect but not self-normalizing): two classes of order 168, one
of order 504 (= PerfectResiduum of the `L2(8).3` maximal, order 1512 — not
self-normalizing itself since its normalizer is the full `.3` maximal), two
of order 5,616 (= PerfectResiduum of the `L3(3).2` maximal, order 11232 —
same phenomenon, normalizer is the full `.2` maximal), two of order 6,048,
and the trivial subgroup. The two non-`G`-order hits correspond exactly to
two of G2(3)'s ten maximal-subgroup classes that are themselves already
perfect: `L2(13)` (maximal #9, order 1092) and `2^3.L3(2)` (maximal #8,
order 1344) — both automatically self-normalizing as maximal subgroups of a
simple group.

Scripts/logs: `v_task22_g23_probe3.g/_out.txt` (rep construction),
`v_task22_g23_census.g/_out.txt` (census).

## Summary

| Group | Order | Total perfect-subgroup classes | **psn count** |
|---|---|---|---|
| Sp6(2) | 1,451,520 | 21 | **5** |
| U4(2) | 25,920 | 6 | **2** |
| A7 | 2,520 | 7 | **5** |
| G2(3) | 4,245,696 | 11 | **3** |

## Completeness statement

All four censuses are **exact and exhaustive**, not lower bounds. Unlike
`v_task10` (O7(3)/S6(3), order ≈4.5×10^9, where TableOfMarks failed and a
maximal-subgroup-recursion route left several branches unreachable due to
missing AtlasRep straight-line programs), all four groups here were small
enough for `RepresentativesPerfectSubgroups` — GAP's complete deterministic
enumeration algorithm — to run directly to completion on a faithful
permutation representation, with no timeouts, no missing SLPs, and no
unexplored branches. Every reported count is final.

## Files

- `v_task22_probe1.g/_out.txt` — initial representation survey: confirms
  `AtlasGroup("S6(2))"` degree 28, `AtlasGroup("U4(2)")` degree 27, `A7`
  natural degree 7 are readily available; `AtlasGroup("G2(3)")` is a matrix
  group with no `NrMovedPoints` method (expected — no native perm rep).
- `v_task22_probe2.g/_out.txt` — `DisplayAtlasInfo("G2(3)")`: full
  representation table (25 matrix reps, 0 permutation reps) and confirms
  SLPs exist for all 10 maximal-subgroup classes.
- `v_task22_psn.g/_out.txt` — main census script and log for Sp6(2), U4(2),
  A7 (all three in one run).
- `v_task22_g23_probe3.g/_out.txt` — builds and validates the degree-351
  permutation representation of G2(3) via `FactorCosetAction` on the
  smallest-index maximal subgroup; also lists orders/indices of all 10
  maximal subgroup classes.
- `v_task22_g23_census.g/_out.txt` — full p.s.n. census for G2(3) on the
  degree-351 representation.
