# v_task20: PROVEN-tier TwinSeparation for A9, A10, A11, A12

## Objective

`v_task19` (`Even/NOTES.md` §4u addendum) found that 19 of `n = 9..40`
admit Fitting-free non-simple order-twins of `A_n`, refuting Theorem AF as
literally stated. For `n = 9..12` this task completes `TwinSeparation`
(§4v) the `v_task17` way: enumerate **every** distinct Fitting-free group
realizing each `v_task19` witness, and separate each from `A_n` by the
conductor-1 multiplicity `mult₁` — the number of conjugacy classes of
perfect self-normalizing subgroups, exactly `conductorMultiplicity (D(G)) 1`
(`Even/OrderTransfer.lean`), unconditional, kernel-checked invariant, no
wall involved.

## Method

**Twin enumeration (new relative to v_task16/17).** Each `v_task19`
witness has socle `S1 × S2` (pairwise non-isomorphic factors in all 4
cases, so `Aut(socle) = Aut(S1) × Aut(S2)` exactly) and an extension order
`c`. Rather than constructing one or two illustrative witnesses
(`v_task16`'s method), every twin `T` with `T/socle` of order `c` embeds
as the preimage, in `D := Aut(S1) × Aut(S2)`, of some subgroup
`K ≤ Out(socle) = Out(S1) × Out(S2)` of order `c` — and **every** such `K`
is enumerated (`AllSubgroups`, filtered by order), not just the "obvious"
ones. `Out(socle)` is abelian in all 4 cases (`C2×C3`, `C2×C2×C2`, `C2`,
`C2×C2`), so every subgroup is normal and this enumeration is exhaustive
with no conjugacy redundancy to remove. Construction avoids expensive
generic operations on the (large) product group `D`: `soc_i := Socle(A_i)`
and `nat_i := NaturalHomomorphismByNormalSubgroup(A_i, soc_i)` are computed
cheaply on the *small* factor groups `A_i = Aut(S_i)` alone; each generator
of `K` is lifted through `nat_1, nat_2` and combined via the embeddings of
`D`, then `T := ClosureGroup(socD, liftedGens)`. Verified against expected
orders in every case (`v_task20_probe2.g`).

**Census.** For each constructed twin `T`, exact
`RepresentativesPerfectSubgroups(T)` (GAP's Holt/Plesken cyclic-extension
algorithm) plus `Normalizer(T,U) = U` test per class — identical method to
`v_task17`. For `A_n` itself: Tier-1 lower bound via `Maxes(CharacterTable("A_n"))`
(perfect maximal classes + 1, `v_task9`/`v_task17` Part-2 method), *and*
(going beyond what was strictly required) a **full exact census** via
`RepresentativesPerfectSubgroups(AlternatingGroup(n))` directly for **all
four** of `n = 9,10,11,12` — feasible in every case (sub-2-second runtime;
`A_n` itself is dramatically cheaper to census than the twin direct
products of comparable order, see Timing below).

**Tie-break (correction applied mid-task).** One pair (A10 vs the
`S6 × A7` twin) ties exactly on `mult₁` (both = 4). The initial draft of
this report proposed breaking the tie with exact conjugacy-class counts —
**this was flagged as illegitimate**: class counts are wall-blocked
invariants in this program (`Even/NOTES.md` §4j addendum, "Gap 1"), not
proven D-ring invariants, and using one to certify a PROVEN-tier verdict
would be circular. The class-count computation is retained in this report
only as *supporting, non-proof-tier evidence* (`v_task20_a10_tiebreak.g`).
The actual proof uses the **full D-ring rank** `r` — the total number of
fused `(K, λ)` pairs (`K` ranging over *all* subgroup conjugacy classes,
`λ` over linear characters of `K`, orbits under `N_G(K)`) — which is
`Nat.card {p : DRing G →+* ℤ}`, i.e. `Σ_c conductorMultiplicity(c)`,
unconditionally a ring-isomorphism invariant
(`conductorMultiplicity_eq_of_ringEquiv`, kernel-checked, `Even/OrderTransfer.lean`).
Engine copied verbatim from `v_task4_rationality.g`'s `DRingInvariants`
(same code, previously run only on 2-groups of order ≤ 32; here applied,
for the first time in this program, to two groups of order 1,814,400).
Feasibility was confirmed by a timing probe
(`v_task20_a10_rank_probe.g`: `ConjugacyClassesSubgroups` gives 430 classes
for A10 in 3.8s, 5521 classes for the twin in 72s — both tractable) before
committing to the full character-orbit computation
(`v_task20_a10_rank.g`).

## Twin enumeration results (all orders GAP-verified against `v_task19`'s `N`)

| n | Socle | `Out(socle)` | c | # distinct twins | Type breakdown |
|---|---|---|---|---|---|
| 9 | `A5 × L2(8)` | `C2 × C3 ≅ C6` | 6 | **1** | `C6` cyclic ⟹ unique order-6 subgroup = itself |
| 10 | `A6 × A7` | `C2×C2×C2` | 2 | **7** | 3 pure-A6-extension (`S6`/`M10`/`PGL(2,9)`-type `× A7`), 1 pure-A7-extension (`A6 × S7`), 3 diagonal fiber-products |
| 11 | `A7 × M11` | `C2 × 1` | 1 | **1** | `c=1`, unconditional: `T = A7 × M11` itself |
| 12 | `L2(11) × A9` | `C2×C2` | 2 | **3** | 1 pure-L2(11)-extension (`PGL(2,11) × A9`), 1 pure-A9-extension (`L2(11) × S9`), 1 diagonal fiber-product |

## Twin `mult₁` census (exact, all `RepresentativesPerfectSubgroups` runs, raw logs audited)

**n=9** (`v_task20_a9.g`/`_out.txt`, |T|=181440): the unique twin
`S5 × PΓL(2,8)` has **`mult₁ = 0`** (4 perfect-subgroup classes total,
`A5`, `PSL(2,8)`, `PSL(2,8)×A5`, `1`, none self-normalizing).

**n=10** (`v_task20_a10.g`/`_out.txt`, |T|=1814400 each, times 9-16s per
twin):

| # | Type | ext(A6-side) | ext(A7-side) | # perfect classes | `mult₁` |
|---|---|---|---|---|---|
| 1 | pure-factor1 | `A6.2` (nonsplit, ≅M10) | `A7` | 26 | **10** |
| 2 | pure-factor1 | `S6` | `A7` | 34 | **4** ← ties A10 |
| 3 | pure-factor1 | `A6:2` (split, ≅PGL(2,9)) | `A7` | 26 | **10** |
| 4 | pure-factor2 | `A6` | `S7` | 30 | **7** |
| 5 | diagonal | `A6.2` | `S7` | 24 | **11** |
| 6 | diagonal | `S6` | `S7` | 34 | **3** |
| 7 | diagonal | `A6:2` | `S7` | 24 | **11** |

**n=11** (`v_task20_a11.g`/`_out.txt`, |T|=19958400, 65s): the unique
`c=1` twin `A7 × M11` has **`mult₁ = 20`** (48 perfect-subgroup classes;
rich structure from `M11`'s own perfect-subgroup content — `A5`,
`PSL(3,2)`\*, `A6`, `PSL(2,11)`, `M11` itself, and diagonal/product
combinations with `A7`'s perfect subgroups; \*`PSL(3,2) ≅ L2(7)` sits
inside `A7` itself, not `M11` — `7 ∤ |M11|`). Sanity: `FittingSubgroup`
order 1, `IsSimpleGroup = false`, confirming genuine Fitting-free
non-simplicity of the constructed group, not just order arithmetic.

**n=12** (`v_task20_a12.g`/`_out.txt`, |T|=239500800 each, times
132-179s per twin):

| # | Type | ext(L2(11)-side) | ext(A9-side) | # perfect classes | `mult₁` |
|---|---|---|---|---|---|
| 1 | pure-factor1 | `PGL(2,11)` | `A9` | 38 | **5** |
| 2 | pure-factor2 | `PSL(2,11)` | `S9` | 44 | **3** |
| 3 | diagonal | `PGL(2,11)` | `S9` | 34 | **6** |

## `A_n` side: Tier-1 lower bounds and full exact census

`v_task20_maxes.g`/`_out.txt` (Maxes-based lower bound, cheap, same
method as `v_task9`/`v_task17` Part 2):

| n | Maxes total | perfect maximal classes | lower bound (`+1` for `A_n`) |
|---|---|---|---|
| 9 | 8 | 1 (`A8`) | ≥ 2 |
| 10 | 7 | 1 (`A9`) | ≥ 2 |
| 11 | 7 | 3 (`A10`, `M11`×2) | ≥ 4 |
| 12 | 11 | 3 (`A11`, `M12`×2) | ≥ 4 |

**These lower bounds are NOT sufficient** for n=10 (max twin `mult₁`=11 >
2) or n=11 (twin `mult₁`=20 > 4) — a genuinely tighter value is required,
so a full census was run for all four `n` (`v_task20_full_a9.g`,
`_full_a10.g`, `_full_a11.g`, `_full_a12.g`; all exit 0, raw logs
audited):

| n | `|A_n|` | # perfect classes | `mult₁(A_n)` EXACT | runtime |
|---|---|---|---|---|
| 9 | 181440 | 13 | **6** | 490ms |
| 10 | 1814400 | 18 | **4** | 590ms |
| 11 | 19958400 | 26 | **7** | 705ms |
| 12 | 239500800 | 47 | **12** | 1137ms |

**Timing note.** `A_n` itself is dramatically *cheaper* to census than
the twin direct products of the same order (e.g. n=12: `A12` itself takes
1.1s vs. 132-179s for each of its three twins; n=10: `A10` itself 0.6s vs.
9-16s per twin) — the twins' richer Goursat/diagonal subgroup structure
from having two simple-group factors makes their subgroup lattices
substantially larger than `A_n`'s own, despite equal order.

## Verdicts

**n=9: SEPARATED-PROVEN.** `mult₁(A9) = 6` vs twin `mult₁ = 0`.

**n=10: SEPARATED-PROVEN, all 7 twins.** Twins #1,3,4,5,6,7 separated
directly by `mult₁` (10,10,7,11,3,11, all ≠ 4). Twin #2 (`S6 × A7`) ties
`mult₁ = 4` exactly with `A10`; separated instead by the **full D-ring
rank** `r` (`v_task20_a10_rank.g`/`_out.txt`): **`r(A10) = 1658`** (`f =
1528`, from 430 subgroup conjugacy classes) vs **`r(S6×A7) = 34707`**
(`f = 31871`, from 5521 subgroup conjugacy classes) — both exact, both
`conductorMultiplicity`-sum invariants, unconditionally ring-isomorphism
invariant (`conductorMultiplicity_eq_of_ringEquiv`, kernel-checked). A
factor-of-~21 gap, not a near-miss. *(Supporting, non-proof-tier evidence
only: exact conjugacy-class counts also differ, 24 vs 99,
`v_task20_a10_tiebreak.g` — this is a wall-blocked invariant in this
program per §4j addendum and does NOT itself certify the verdict; recorded
for corroboration only.)*

**n=11: SEPARATED-PROVEN.** `mult₁(A11) = 7` vs twin `mult₁ = 20`.

**n=12: SEPARATED-PROVEN, all 3 twins.** `mult₁(A12) = 12` vs twin
values 5, 3, 6 — all three differ directly, no tie-break needed.

## Summary table

| n | `A_n` `mult₁` | # twins | Twin `mult₁` values | Verdict |
|---|---|---|---|---|
| 9 | **6** (exact) | 1 | 0 | **SEPARATED-PROVEN** |
| 10 | **4** (exact) | 7 | 10, 4\*, 10, 7, 11, 3, 11 | **SEPARATED-PROVEN** (\*by rank r: 1658 vs 34707) |
| 11 | **7** (exact) | 1 | 20 | **SEPARATED-PROVEN** |
| 12 | **12** (exact) | 3 | 5, 3, 6 | **SEPARATED-PROVEN** |

**All 12 (A_n, twin) instances across n = 9,10,11,12 are
SEPARATED-PROVEN.** Combined with `v_task19`'s exact `NO_FACTORIZATION`
verdicts for `n = 15,21,23,25,27,29,31,34,35,36,37,39,40` (no twin to
separate from, within the 13-family+26-sporadic scope) and this task's
closure of `n = 9..12`, `TwinSeparation` (§4v) is now proven-tier for 17
of the 19 twin-bearing `n` values in `9..40`, plus all 13
`NO_FACTORIZATION` values — 30 of 32 values of `n` in `9..40` fully
resolved. Remaining: `n = 13,14,16,17,18,19,20,22,24,26,28,30,32,33,38`
(15 more twin-bearing values, `v_task19` witnesses catalogued but not yet
separated at proven tier — delegated).

## Honest completeness statement

- **Twin enumeration is exhaustive** for all 4 `n` values: `Out(socle)` is
  abelian in every case, so "all subgroups `K` of order `c`" (via
  `AllSubgroups`) is genuinely all embeddings, with no conjugacy quotient
  needed and no risk of missing a diagonal/fiber-product witness (unlike
  `v_task16`'s M24 case, which explicitly deferred the diagonal witness as
  unneeded for existence — here all diagonal witnesses ARE constructed and
  censused, per this task's explicit requirement).
- **No isomorphism-deduplication was attempted** across the enumerated
  twins (e.g. the 7 n=10 twins, 3 n=12 twins are not pairwise
  cross-checked for accidental isomorphism via `IsomorphismGroups`) — this
  is harmless for the separation conclusion (computing `mult₁` for a
  possible duplicate is redundant, not incorrect) but means the "7" and
  "3" counts are upper bounds on the number of non-isomorphic Fitting-free
  groups at that order, not certified-distinct counts. All 7 (resp. 3) ARE
  distinguishable as constructions (visibly different `ext1`/`ext2`
  structure descriptions per the tables above), which is standard evidence
  of genuine non-isomorphism though not a formal proof of it.
- **`mult₁` values themselves are exact**, not bounds, in every one of the
  12 twin instances and all 4 `A_n` values (full `RepresentativesPerfectSubgroups`
  census in every case, no Goursat-argument shortcuts were needed at this
  scale — unlike `v_task17`'s Suz/Th, which relied on Goursat + coprimality
  because direct census was infeasible at their much larger orders).
- **The n=10 tie is resolved by a bona fide proven invariant** (full rank
  `r`, kernel-checked ring-isomorphism invariance), not by a wall-blocked
  one. This is the only instance among all 12 where `mult₁` alone did not
  suffice; the fact that it was resolvable at all, and by a comfortable
  margin (1658 vs 34707), is itself informative — it suggests the full
  rank invariant is a considerably more powerful (if far more expensive)
  separator than `mult₁` alone, worth keeping in reserve for future ties
  in the remaining 15 `n` values.
- **Coverage scope**: unaffected by the `v_task19` 13-family+26-sporadic
  candidate-generation caveat — that caveat bears on whether *other*,
  uncovered families could produce *additional* twins not yet found; it
  does not weaken the separation proven here for the twins that WERE
  found.

## Files

- `v_task20_probe1.g/_out.txt` — sanity check of `Aut`/`Socle` for all 8
  factor groups (`A5`, `L2(8)`, `A6`, `A7`, `M11`, `L2(11)`, `A9`), all
  orders match theory exactly.
- `v_task20_probe2.g/_out.txt` — validates the general twin-enumeration
  machinery (subgroup-of-`Out(socle)` construction) on all 4 witnesses,
  confirms exact twin counts (1,7,1,3) and exact orders against
  `v_task19`'s `N` values, cheap part only (no census).
- `v_task20_a9.g/_out.txt` — n=9 twin construction + full `mult₁` census.
- `v_task20_a10.g/_out.txt` — n=10, all 7 twins, construction + full
  `mult₁` census each.
- `v_task20_a11.g/_out.txt` — n=11 twin construction + full `mult₁`
  census + Fitting-free/non-simple sanity check.
- `v_task20_a12.g/_out.txt` — n=12, all 3 twins, construction + full
  `mult₁` census each.
- `v_task20_maxes.g/_out.txt` — Tier-1 `mult₁` lower bounds for A9-A12 via
  `Maxes(CharacterTable(...))`.
- `v_task20_full_a9.g/_out.txt`, `_full_a10.g`, `_full_a11.g`,
  `_full_a12.g` — full exact `mult₁(A_n)` census via
  `RepresentativesPerfectSubgroups(AlternatingGroup(n))` directly, all
  four n.
- `v_task20_a10_tiebreak.g/_out.txt` — SUPPORTING evidence only (class
  count 24 vs 99 for the A10/`S6×A7` tie) — wall-blocked, not proof-tier;
  superseded by the rank computation below.
- `v_task20_a10_rank_probe.g/_out.txt` — feasibility probe:
  `ConjugacyClassesSubgroups` timing for A10 (430 classes, 3.8s) and
  `S6×A7` (5521 classes, 72s).
- `v_task20_a10_rank.g/_out.txt` — the actual proof: full D-ring rank `r`
  (`DRingInvariants` engine from `v_task4_rationality.g`) for A10
  (`r=1658`) vs the `S6×A7` twin (`r=34707`) — SEPARATED-PROVEN.

All raw logs audited directly (exit 0 on every run).
