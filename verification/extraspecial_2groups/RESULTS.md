# Extraspecial 2-groups: (A) the n = 3 closed-form r-formula,
# (B) the cyclic-faithful intrinsicness claim

GAP 4.16.0, python3. Scripts and captured outputs: this directory.

## Task A — the r-formula at n = 3: both predictions match

The closed-form formula for the number r(G) of fused pairs predicts, for the
extraspecial groups of order 128 = 2^{1+6},
r(plus) = 27632 and r(minus) = 27136. These values are tested here against
the actual groups.

Method (independent of the formula): the generic engine
`ConjugacyClassesSubgroups(G)`, then for each class K the orbits of
N_G(K) on the linear characters of K; r = total orbit count. No use of the
formula's stratification. Script: `r_formula_check.g`, log:
`r_formula_check_out.txt`.

Preliminary checks:

* Engine re-verifies the four anchors: r(D8)=20, r(Q8)=16, r(32,49)=381,
  r(32,50)=349.
* Full scan of all 2328 groups of order 128 for |Z|=2, Z=G'=Phi(G): exactly
  ids **2326 and 2327** are extraspecial (the commonly cited candidates are
  confirmed).
* Type identification by involution count: G(128,2326) has **71**
  involutions (plus type 2^{1+6}_+ = D8∘D8∘D8: 2^3(2^3+1)-1 = 71);
  G(128,2327) has **55** (minus type: 2^3(2^3-1)-1 = 55). Both have
  exponent 4, |Z| = 2.

Decisive computation (ca. 15 s per group after the subgroup lattice):

| group | type | subgroup classes | computed r | prediction | agree |
|---|---|---:|---:|---:|---|
| SmallGroup(128,2326) | plus  | 2996 | **27632** | 27632 | yes |
| SmallGroup(128,2327) | minus | 2898 | **27136** | 27136 | yes |

Side observations (free from the same run): f = r for both groups, i.e. every
fused pair is rational — both D-rings are D-rational. Degree multisets:
plus: 2996 pairs with d=1, 24293 with d=2, 343 with d=4, all deg 1;
minus: 2898 / 23797 / 441, all deg 1.

Conclusion: the formula survives its first genuinely out-of-sample test at
n = 3, for both types, with the type assignment independently pinned by
involution counts.

## Task B — cyclic-faithful species under Aut(D(G))

Claim under test: "the set of cyclic-faithful species
{(L, mu): L cyclic, mu faithful linear character} of D(G) is preserved by
every ring automorphism of D(G)" — asserted in particular for extraspecial G.

Method: exact exhaustive Aut(D(G)) enumeration via `lib/fullaut3.py`
(deps `latauto`, `swaprigid`, `dring2`, all in `lib/`). Script:
`cyclic_faithful_check.py`, log: `cyclic_faithful_check_out.txt`; deep reruns of the two
capped groups: `cyclic_faithful_check_deep.py` / `cyclic_faithful_check_deep_out.txt`.

Parametrization/translation: fullaut3's
species points are conjugacy classes of (H, hH'); the claim's "(L, mu), L
cyclic, mu faithful" translates to **H cyclic and h a generator of H**
(cyclic duality: faithful character <-> generator; for cyclic H the coset
hH' is the single element h). The label is Galois-invariant, so the
Galois-twisted automorphisms of fullaut3 preserve the CF set iff their
species permutation pi does. Independently, the same test was run at the
**basis** level: fused pairs [K, lambda] with K cyclic, lambda faithful
(trivial kernel), checking whether the integral automorphism matrix Ut maps
the CF-spanned sublattice into itself (same mechanism as fullaut3's
eta(B)-setwise test).

**Convention (PRIMARY)**: the trivial pair (K = 1, trivial character) counts
as cyclic-faithful (its kernel is trivial). **STRICT** variant: K (resp. H)
nontrivial. Both reported, as they differ materially.

### Results, primary convention (K = 1 counts as CF)

| G | \|Aut D(G)\| | exhaustive | species-level | basis-level |
|---|---:|---|---|---|
| C2    | 6   | yes | **MOVED** (4/6)     | **MOVED** (4/6)   |
| C4    | 8   | yes | **MOVED** (4/8)     | **MOVED** (4/8)   |
| V4    | 48  | yes | **MOVED** (24/48)   | PRESERVED (0/48)  |
| Q8    | 384 | yes | **MOVED** (192/384) | **MOVED** (192/384) |
| C2xC4 | 64  | yes (deep rerun) | PRESERVED (0/64) | PRESERVED (0/64) |
| D8    | 64  | yes (deep rerun) | PRESERVED (0/64) | PRESERVED (0/64) |

Witness for Q8 (extraspecial): an automorphism with species permutation
pi = (1 0)(rest fixed), no twist — it exchanges the trivial species
(H = 1) with the species (H = Z(Q8) ≅ C2, h = e), i.e. maps the
cyclic-faithful point (1, 1) to the non-CF point (C2, trivial). Basis side:
Phi([1,1]) = -[1,1] + [C2,triv] + [C2,sign] (matrix column [-1,1,1,0,...]),
the known top-unit-type torsion alternative.

**Under the primary convention the intrinsicness claim is REFUTED for
extraspecial G**: 192 of the 384 ring automorphisms of D(Q8) move the
cyclic-faithful set, witness above. (Same failure already at C2 and C4.)

### Results, strict convention (K nontrivial)

| G | \|Aut D(G)\| | exhaustive | species-level | basis-level |
|---|---:|---|---|---|
| C2    | 6   | yes | **MOVED** (4/6)   | **MOVED** (4/6) |
| C4    | 8   | yes | PRESERVED (0/8)   | PRESERVED (0/8) |
| V4    | 48  | yes | **MOVED** (24/48) | **MOVED** (24/48) |
| Q8    | 384 | yes | PRESERVED (0/384) | PRESERVED (0/384) |
| C2xC4 | 64  | yes (deep rerun) | PRESERVED (0/64) | PRESERVED (0/64) |
| D8    | 64  | yes (deep rerun) | PRESERVED (0/64) | PRESERVED (0/64) |

Witness for the strict refutations: at C2 (and analogously inside V4) an
automorphism exchanges the species (C2, e) and (C2, s) — i.e. maps the
strict-CF point (C2, sign) to the non-CF point (C2, trivial); basis side
Phi([C2,sign]) = [1,1] - [C2,... ] (column [1,0,-1]).

So under the strict convention the claim survives at both extraspecial
groups (Q8: PRESERVED across all 384 automorphisms; D8: across all 64) but
is FALSE as a general-G statement (C2, V4 are counterexamples).

### Deep rerun of the two capped groups (node cap 10^8)

Both searches EXHAUSTED well under the raised cap
(`cyclic_faithful_check_deep_out.txt`):

* **D8**: 4 940 462 nodes, exhaustive. |Aut D(D8)| = **64**. CF set
  **PRESERVED** by all 64 automorphisms, under BOTH conventions, at both the
  species and the basis level. (Unlike Q8, D8 has no automorphism swapping
  the trivial species with (Z, triv).)
* **C2xC4**: 4 450 725 nodes, exhaustive. |Aut D(C2xC4)| = **64**. CF set
  **PRESERVED** by all 64 automorphisms, both conventions, both levels.

The summary tables above already incorporate these exhaustive results;
nothing remains capped or undecided.

### Task B-ideal — the Lean brauerKernel (intersection-of-kernels ideal)

The corresponding Lean-side claim is about the IDEAL, not the species set:
`brauerKernel := { x : s(x) = 0 for all cyclic-faithful species s }`, with
the trivial pair INCLUDED by that definition (= primary
convention). An automorphism could in principle move the CF species set yet
preserve the intersection of their kernels, so this was tested separately:
K = ker_Z of the CF-rows submatrix M of the species table (automatically
saturated), and for every automorphism matrix Ut (coordinate action
c -> Ut c, since `latauto.solve_matrix` solves Bm U = FB) it was checked
whether M (Ut k) = 0 for a kernel basis k. Script:
`brauer_kernel_check.py`, log: `brauer_kernel_check_out.txt`.

| G | \|Aut\| | dim K (primary) | ideal, primary | ideal, strict |
|---|---:|---:|---|---|
| C2    | 6   | 1  | **MOVED** (4/6)     | **MOVED** (4/6)   |
| C4    | 8   | 3  | **MOVED** (4/8)     | PRESERVED (0/8)   |
| V4    | 48  | 7  | **MOVED** (24/48)   | **MOVED** (24/48) |
| Q8    | 384 | 11 | **MOVED** (192/384) | PRESERVED (0/384) |
| D8    | 64  | 15 | PRESERVED (0/64)    | PRESERVED (0/64)  |
| C2xC4 | 64  | 19 | PRESERVED (0/64)    | PRESERVED (0/64)  |

**Q8, called out explicitly**: the witness automorphism pi = (1 0)(rest
fixed), no Galois twist — the one exchanging the trivial species with
(Z(Q8), triv) — **MOVES brauerKernel** under the primary convention
(direct check on the kernel lattice). So under that definition
(trivial pair included):

> **intrinsicness claim REFUTED for extraspecial G**: 192 of the 384 ring
> automorphisms of D(Q8) do not preserve brauerKernel as an ideal.

Under the strict convention (trivial pair excluded from CF) the Q8 ideal is
preserved by all 384 automorphisms — the refutation is exactly the trivial
pair's membership. D8, by contrast, is safe under both conventions.

Empirical observation: in every group/convention tested, the ideal-level
mover count equals the species-SET-level mover count (the anticipated
"set moved but ideal preserved" divergence never occurred). In particular
at V4/primary the ideal tracks the species-set level (24 movers), NOT the
basis-span level (0 movers).

### Caveats

* The MOVED/PRESERVED dichotomy for Q8 flips with the convention on the
  trivial pair; the claim as stated did not fix the convention, so both
  answers are reported. The primary-convention movers at Q8 are exactly those
  automorphisms exchanging the trivial species with (Z(Q8), triv); no
  automorphism of D(Q8) moves a nontrivial cyclic-faithful point.
* The species-level test uses the stated translation (faithful character <->
  generator under cyclic duality). The basis-level test needs no such
  translation and agrees with the species-level verdicts everywhere except
  V4/primary: there Phi([C2,sign]) = [1,1] - [C2,sign] leaks only onto the
  trivial pair [1,1], which lies inside the primary CF span (so the span is
  preserved) but outside the strict one (so strict reports MOVED) — while at
  the species level the CF point (C2, s) genuinely maps to the non-CF point
  (C2, e) under both conventions.
