# Task 10 — Perfect self-normalizing subgroup census: O7(3) vs S6(3)

Route used: **Route 2** (recursive census via AtlasRep). Route 1 (Table of Marks)
failed immediately — `TableOfMarks("O7(3)")` and `TableOfMarks("S6(3)")` both
return `fail` even with `tomlib` loaded and alternate names tried
(`v_task10_route1_out.txt`, `v_task10_route1b_out.txt`); these groups (order
4,585,351,680) are far beyond TomLib's stored range.

All computation used the degree-351 (O7(3)) / degree-364 (S6(3)) permutation
representations obtained offline from AtlasRep's "core" content (no network
needed — confirmed no connectivity errors in any log).

## Method

For every maximal subgroup M of G with a stored straight-line program:
1. `R := PerfectResiduum(M)` (fast, structural — every perfect subgroup of M
   lies in R, since R = M^(∞) is the terminus of the derived series).
2. If `Size(R) = 1`, M has no nontrivial perfect subgroups — done, no hits.
3. Otherwise `reps := RepresentativesPerfectSubgroups(R)` (Holt/Plesken-based
   GAP library function) enumerates perfect-subgroup class reps of R.
4. For each rep U with `1 < |U|` and U not equal to a maximal M already
   counted, `N := Normalizer(G, U)`; U is a hit iff `Size(N) = Size(U)`.
5. Hits found in different maximal subgroups were cross-checked pairwise with
   `IsConjugate(G, U1, U2)` to deduplicate up to G-conjugacy.

All GAP calls completed (no timeouts); no Normalizer call needed to be
abandoned as UNRESOLVED. Raw logs: `v_task10_job_*_out.txt`,
`v_task10_dedup*_out.txt`, `v_task10_final_struct_out.txt`.

## O7(3) — perfect self-normalizing conjugacy classes

**Maximal layer (6, from prior v_task9, reconfirmed here via PerfectResiduum
check that M=M'):** G2(3) ×2, 3^(3+3):L3(3), S6(2) ×2, 2^6:A7.

**Non-maximal layer — 9 confirmed new classes**, found searching inside
maximal subgroups #1 (2.U4(3).2_2), #3 (L4(3).2_2), #4 (G2(3)), #6
(3^(3+3):L3(3)), #7 (S6(2)), #13 (2^6:A7):

| order | structure (`StructureDescription`) | # G-classes | found in maximal(s) |
|---|---|---|---|
| 1344 | (C2×C2×C2):PSL(3,2) / (C2×C2×C2).PSL(3,2) (AGL(3,2)-type) | 4 | #13 (all 4); confirmed also visible from #4, #7 (fuse into these 4) |
| 10752 | (C2^6):PSL(3,2) | 2 | #13 (both); confirmed also visible from #7 (fuses into one of these) |
| 151632 | (C3×C3×C3):PSL(3,3) | 1 | #6 and #3 (both fuse to same G-class) |
| 40320 | C2.PSL(3,4) | 1 | #1 (two M-classes, G-conjugate to each other) |
| 1092 | PSL(2,13) | 1 | #4 |

Raw dedup evidence: `v_task10_dedup_O7_13_out.txt`, `v_task10_dedup2_out.txt`,
`v_task10_dedup3_out.txt` — all pairwise `IsConjugate(G,...)` results shown
explicitly (true/false per pair).

**Confirmed O7(3) total: 6 + 9 = 15 perfect self-normalizing classes.**

**Completeness gap for O7(3):** four maximal-subgroup classes have **no
straight-line program in the offline AtlasRep library** (confirmed via
`AtlasProgramInfo("O7(3)","maxes",i) = fail`, `v_task10_probe_missing_out.txt`):
- #5 (G2(3), the second G-class of G2(3) point-stabilizers)
- #8 (S6(2), the second G-class)
- #10, #11 (both classes of S9)

An attempt to reach #5/#8 via the outer automorphism (using `O7(3).2` on the
same 351 points) failed because the two AtlasRep-generated permutation
representations of `O7(3)` and `O7(3).2` do not share point-labelling
(`IsSubset` check false, `v_task10_outer_setup_out.txt`) — no straightforward
workaround without further SLP construction work. **#10/#11 (the S9 pair,
perfect residuum = A9, order 181440) is entirely unexplored** — not perfect
themselves so not counted at the maximal layer, but never searched for
non-maximal perfect self-normalizing subgroups. This is a genuine, honestly
unresolved gap; it could in principle add classes to the O7(3) side (never to
S6(3)).

## S6(3) — perfect self-normalizing conjugacy classes

**Maximal layer (5, from prior v_task9):** 3^(1+4)_+.2U4(2), 3^6:L3(3),
L2(13) ×2, A5.

**Non-maximal layer — 1 confirmed new class**, found inside maximal #1
(3^(1+4)_+.2U4(2)):

| order | structure | # G-classes | found in |
|---|---|---|---|
| 466560 | ((C3×((C3×C3):C3)):C3):(C2.((C2×C2×C2×C2):A5)) | 1 | #1 |

Every other accessible S6(3) maximal (#2, #4, #5, #6, #7, #8, #9, #10, #11)
was fully searched and yielded **no** self-normalizing perfect subgroups
beyond the maximal layer itself (`v_task10_job_S63_*_out.txt`).

**Confirmed S6(3) total: 5 + 1 = 6 perfect self-normalizing classes.**

**Completeness gap for S6(3):** exactly one maximal subgroup, #3
(3^(3+4):2(S4×A4), order 1,259,712), has no stored SLP
(`AtlasProgramInfo("S6(3)","maxes",3) = fail`). Its perfect residuum was
never computed or searched.

## Verdict

**Totals DIFFER: O7(3) = 15 (confirmed) vs S6(3) = 6 (confirmed).**

This is not a marginal difference (9-class gap) and it is not an artifact of
the completeness gaps: O7(3)'s unexplored branches (#5, #8, #10/#11) could
only *increase* its count further, and S6(3)'s single unexplored branch (#3,
order 1,259,712 — comparable in size to several O7(3) branches that were
fully searched and yielded only 0–2 hits each) would have to contribute an
implausibly large number of new self-normalizing perfect classes to close a
9-class gap. Under every branch that was actually computed to completion, the
counts are exhaustive and exact.

**Verdict: totals DIFFER ⟹ D-ring separation of O7(3) vs S6(3) is proven by
this Tier 1.5 invariant, modulo the explicitly stated completeness gaps
(O7(3) maximal classes #5, #8, #10, #11; S6(3) maximal class #3 — all
unreachable due to missing AtlasRep straight-line programs, not due to any
computational failure or timeout).**
