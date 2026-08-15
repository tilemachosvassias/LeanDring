# Task 4 — D-ring rationality sweep (orders 8, 16, 32)

- Script: `v_task4_rationality.g` (GAP 4.16.0), raw log: `v_task4_out.txt`
- Runtime: ~6.5 s total.

## Method

For each G = SmallGroup(n,i): for every conjugacy-class representative
K ≤ G (via `ConjugacyClassesSubgroups`), set N = N_G(K); linear characters
of K represented as value lists on the fixed sorted `Elements(K)`;
N-orbits computed by orbit closure over generators of N with the action
λ^n(x) = λ(n x n⁻¹). r(G) = total number of N-orbits summed over
subgroup classes (= fused pairs). For an orbit representative λ of order
d, the Galois stabilizer S = { j ∈ (ℤ/d)ˣ : λ^j (valuewise j-th power)
lies in the same N-orbit }, deg = φ(d)/|S| (deg = 1 for d ≤ 2). f(G) =
number of fused pairs with deg = 1; D-rational iff r = f.

**Sanity checks (both pass, see log lines 1–5):**
- C2: r = 3, f = 3, all rational — as required.
- C4: r = 7, f = 5, two fused pairs of degree (d=4, deg=2) — as required
  (the two faithful C4-characters are N-fixed, hence a genuine Galois
  orbit of degree 2).

## VERDICT

### T2(a) — extraspecial order 32 are D-rational: **CONFIRMED**
- SmallGroup(32,49) (2₊^{1+4}): r = 381, f = 381 — D-rational, every
  fused pair has deg = 1.
- SmallGroup(32,50) (2₋^{1+4}): r = 349, f = 349 — D-rational.
- Structural check Z(G) = G′ = Φ(G) of order 2 confirmed for both
  (and for 8,3 / 8,4).

### T2(b) — match with earlier independent point counts: **CONFIRMED EXACTLY**
- 32,49: computed r = f = 381 = the earlier "381 points". Match.
- 32,50: computed r = f = 349 = the earlier "349 points". Match.

### T2(c) — D8 and Q8 D-rational: **CONFIRMED**
- SmallGroup(8,3) = D8: r = f = 20.
- SmallGroup(8,4) = Q8: r = f = 16.

### T3 — collision lists for (r, f, degree multiset): **ALL EMPTY**
- Order 32 vs SmallGroup(32,49): `[ ]` — uniquely determined.
- Order 32 vs SmallGroup(32,50): `[ ]` — uniquely determined.
- Order 8 vs D8 = (8,3): `[ ]`; vs Q8 = (8,4): `[ ]`.

In fact r alone already separates: at order 32 the eight D-rational
groups have pairwise distinct r (see table below), so the extraspecial
groups are pinned down by r among D-rational groups, and no
non-D-rational group can collide since its multiset contains deg > 1
entries.

## D-rational census

| order | D-rational / total | indices |
|---|---|---|
| 8 | 3 / 5 | 3 (D8), 4 (Q8), 5 (C2³) |
| 16 | 3 / 14 | 11 (D8×C2), 12 (Q8×C2), 14 (C2⁴) |
| 32 | 8 / 51 | 27, 34, 35, 46, 47, 49, 50, 51 |

Order-32 D-rational groups with invariants (all have exponent 4 or 2;
multiset given as (d,deg):count):

| G(32,i) | r = f | multiset | abelian | exp | |Z| | |G′| | class |
|---|---|---|---|---|---|---|---|
| 27 | 281 | (1,1):65 (2,1):201 (4,1):15 | no | 4 | 4 | 4 | 2 |
| 34 | 213 | (1,1):54 (2,1):141 (4,1):18 | no | 4 | 4 | 4 | 2 |
| 35 | 149 | (1,1):34 (2,1):77 (4,1):38 | no | 4 | 4 | 4 | 2 |
| 46 | 583 | (1,1):118 (2,1):445 (4,1):20 | no | 4 | 8 | 2 | 2 |
| 47 | 407 | (1,1):78 (2,1):269 (4,1):60 | no | 4 | 8 | 2 | 2 |
| 49 | 381 | (1,1):83 (2,1):283 (4,1):15 | no | 4 | 2 | 2 | 2 |
| 50 | 349 | (1,1):73 (2,1):251 (4,1):25 | no | 4 | 2 | 2 | 2 |
| 51 | 2451 | (1,1):374 (2,1):2077 | yes | 2 | 32 | 1 | 1 |

Observations (order 32): every D-rational group has exponent ≤ 4 and
nilpotency class ≤ 2; the converse fails (e.g. 32,22 has exp 4, class 2
but 64 pairs of deg 2). Degrees > 2 occur only for d ≥ 8 characters;
maximal degree seen is 16 (faithful characters of C32 in 32,1). Groups
32,43 and 32,44 exhibit rational pairs with d = 8, deg = 1 (fused
faithful C8-characters covering a full φ(8)-orbit), the only (8,1)
entries in the sweep. The only exact full-invariant collision anywhere
in the order-32 list is the pair 32,13 / 32,14, which share
(r,f,multiset) = (83, 59, ...) and all T4 structurals — both
non-D-rational, unrelated to the extraspecial question.

Full per-group data for all 5 + 14 + 51 groups (with T4 structural data
at order 32) is in `v_task4_out.txt`.

## T5: order-128 frontier pair

- Script: `v_task5_frontier128.g` (same invariant code as T1-T4), raw
  log: `v_task5_out.txt`. Runtime ~4 s.
- Groups: SmallGroup(128,1597) and SmallGroup(128,1598).

### Structural verification

Both groups, identically:

| property | value |
|---|---|
| |Z(G)| | **8** (not 4 as stated in the task — see note) |
| |G′| | 8 |
| |Φ(G)| | 8 |
| Z = G′ = Φ | true (so both are **special** 2-groups) |
| Z elementary abelian | true (Z ≅ C2³) |
| G/Z elementary abelian | true (G/Z ≅ C2⁴) |
| nilpotency class | 2 |
| exponent | 4 |
| # elements of order 2 | 15 (identical fiber of squaring map over 1) |

Note (honest discrepancy): the coordinator's description said |Z| = 4;
the computation gives |Z| = |G′| = |Φ| = 8 for both groups. The
*special* structural description (Z = G′ = Φ, Z and G/Z elementary
abelian, class 2) is fully confirmed — only the stated center size was
off. These are special 2-groups of type 2^{4+3} (|G/Z| = 16, |Z| = 8),
consistent with the project-memory description "isoclinic special
2-groups differing only in the squaring map q" with rank-3 center.

### Invariant vectors

| G | r | f | D-rational | multiset (d,deg):count |
|---|---|---|---|---|
| SmallGroup(128,1597) | 1675 | 1031 | no | (1,1):209 (2,1):675 (4,1):147 (4,2):644 |
| SmallGroup(128,1598) | 1675 | 1031 | no | (1,1):209 (2,1):675 (4,1):147 (4,2):644 |

### VERDICT: **SAME**

The two groups have the **identical** invariant vector
(r, f, degree multiset): r = 1675, f = 1031, and the full degree
multisets agree entry for entry. No component differs — not even r.
Consequence for the recognition program: (r, f, degree multiset) does
NOT separate this danger pair, so these invariants alone cannot rule
out a D-ring isomorphism D(128,1597) ≅ D(128,1598). Whether the
D-rings are actually isomorphic (with their full ring structure) is
NOT decided by this computation — only that this obstruction vanishes.
