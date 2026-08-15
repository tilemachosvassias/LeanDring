# verification/ — external computations (GAP, Python)

Supporting computations for the even-order layer. They corroborate numbers
quoted in the paper and guided the Lean development; they are **not** part of
it.

Nothing here is Lean, nothing here is compiled by `lake build`, and no theorem
in `LeanDring/` depends on any of it. These files are untrusted: the
mathematics is proved in Lean and in the paper, and this directory is
provenance, so that a reader can see where a census count or a worked example
came from and re-run it independently.

Each script is paired with its recorded output (`foo.g` / `foo_out.txt`), so
the results can be inspected without a GAP installation and re-derived with
one. Every cluster carries a `RESULTS.md` describing what was computed and
what it shows.

## Index

### `extraspecial_2groups/` — the rank of `D(G)` for extraspecial `2`-groups

Corroborates Proposition *(extraspecial rigidity)* of
`paper/sections/even-simple.tex` §"Extraspecial 2-groups": the closed-form
rank derived there is checked against a direct computation at `n = 3`, giving
`27632` versus `27136` at order `128`, with the two types pinned independently
by involution counts (`71` and `55`). The same cluster tests, and refutes, the
claim that the cyclic-faithful species set — equivalently the ideal
`brauerKernel` of `LeanDring/Even/` — is preserved by every ring automorphism
of `D(G)`: `192` of the `384` automorphisms of `D(Q8)` move it, once the
trivial pair is counted as cyclic-faithful.

* `r_formula_check.g` — GAP, `r(G)` from subgroup classes and normalizer fusion
* `cyclic_faithful_check.py`, `cyclic_faithful_check_deep.py` — exhaustive
  `Aut(D(G))` enumeration and the species-set test
* `brauer_kernel_check.py` — the same test at the level of the ideal
* internal record: v_task6

### `bc_character_invariants/` — `Ω₇(3)` versus `PSp₆(3)`, character-table data

Corroborates the remark following Theorem BC-`n` in
`paper/sections/even-simple.tex`: the two groups of order `4585351680` do
differ in element-order spectrum, class count (`58` versus `74`),
rational-class orbits (`56` versus `49`), Frobenius–Schur indicators and
character degrees — but every element-order difference is a factor of `2`
(`24 = 2·12`, `30 = 2·15`, `36 = 2·18`), which is exactly the ambiguity Müller,
Satz 2.3.8 leaves open, and class counts are not known to be `D`-ring
invariants. This is the data behind the paper's statement that these
invariants do *not* settle the pair.

* `bc3_invariants.g` — GAP/CTblLib comparison, including the `q = 5` analogue
* internal record: v_task8

### `bc_separation/` — Theorem BC-`n`, the `ind*`-value witness

Corroborates Theorem BC-`n` of `paper/sections/even-simple.tex`
(`D(Ω_{2n+1}(q)) ≇ D(PSp_{2n}(q))` for `n ≥ 3`, `q` odd), and is cited from
the header of `paper/sections/even-cancellation.tex`. The orthogonal witness
`v_ε = qⁿ(qⁿ−ε)/2` is computed outright as an orbit of anisotropic points for
`q = 3, 5, 7, 9`, and the symplectic exclusion — every `ind*` value of
`PSp_{2n}(q)` below `q^{2n}` is divisible by `ι₁` — is checked exactly for
`n ∈ [3,8]`, odd `q < 200` (318 pairs, 0 violations), with the divisibility
`ι₁ ∤ v_ε` checked for `n ∈ [3,12]`, odd `q < 400` (1780 triples).

* `orthogonal_witness.g` — GAP, `Ω(7,q)` orbits, centralizers, ATLAS cross-check
* `symplectic_exclusion.py` — maximal-subgroup index bounds and the
  divisibility sweep
* internal record: v_task64

### `bc_separation_recheck/` — independent re-derivation of the same theorem

Same paper claim as above, re-derived from scratch. It confirms the witness by
computing `C_S(z_e)` and `N_S(⟨z_e⟩)` directly rather than assuming the point
stabilizer, rebuilds the maximal-subgroup index bounds from Kleidman–Liebeck
Table 3.5.C including the two Aschbacher classes `C₄` and `C₇` omitted in
`bc_separation/`, and records one genuine erratum with its repair: the
exclusion must be stated over the whole conductor multiset, not over `I(S)`
alone. The repair — `N_G(H,hH') ≤ N_G(H)`, so every conductor value below
`q^{2n}` other than `1` is still divisible by `ι₁` — leaves the theorem
verbatim, and is the form carried into `LeanDring/Even/BCSeparation.lean`.

* `witness_recheck.g` — GAP/CTblLib, direct centralizers and complete maxes lists
* `maximal_index_bounds.py` — per-class index bounds, per-candidate at `n = 3`
* internal record: v_task65

### `simple_recognition_alignment/` — do the five Lean inputs say what the mathematics proves?

A statement-by-statement comparison of the five hypotheses of
`simpleGroupTheorem` (`LeanDring/Even/SimpleRigidity.lean`) against the
mathematics that is meant to discharge them. Corroborates the honest-status
discussion of `paper/sections/even-simple.tex` §"What is proved, and under
what hypotheses", parts (b) and (e): four of the five `Prop`s are aligned in
content, but instantiating the two separation `Prop`s from `ind*`-level
mathematics goes through Müller's conductor dictionary (Satz 2.3.3 together
with 2.3.6) — that is, they are not external to the ring theory, and the
dependency reduces to the single open `Prop` `BoltjeIntegrality`. There is
also a shape gap: the Lean `Prop`s demand an explicit separating conductor
multiplicity, while the paper theorems conclude non-existence of a
`D`-isomorphism. No scripts; the record is the analysis itself.

* internal record: v_task85

### `linear_tower_residues/` — the last named residues of the `L_d`/`U_d` tower

Corroborates the linear/unitary row of the twin-elimination theorem in
`paper/sections/even-simple.tex`, and specifically the scope sentence of
§"What is proved, and under what hypotheses" part (d): *"the decisive sweeps
of that tower were run for `d ≤ 120`, `q ≤ 100`, `p ≤ 13`, `f ≤ 48`, with the
structural argument proved beyond that range but the confirmations not run."*
These are those sweeps. Two hypotheses named there, `(H6)` and `(POS)`, are
discharged rather than assumed: `(POS)` in closed form for `d ≥ 61` over all
17 families, `(H6)` on the stated grid (72 427 952 pairs tested, 8 167
survivors, all killed by the exact integer tests), and the slack-free census
runs `61 ≤ d ≤ 120` for every prime power `q ≤ 100` with 0 surviving
configurations.

* `h6_discharge.py` — Lemma OUT-p, Lemma FL2, the slack calculus, the sweep
* `pos_discharge.py` — the owner equation, `(PACK-exc)` in base-field indices,
  the Coxeter-mean kill, the exact spot rows
* `sporadic_twins.py`, `l2_twins.py`, `lemma_c_bound.py`, `rank1_twins.py`,
  `rank1_gaps.py`, `lu_twins.py`, `lu_residues.py` — the simple-group order,
  `ι` and cyclotomic tables that the two scripts above import
* internal record: v_task88

## `lib/`

Four vendored Python modules (`dring2`, `swaprigid`, `fullaut3`, `latauto` —
about 1300 lines, standard library only) that `extraspecial_2groups/` imports.
They were copied from the private research monorepo this formalization was
developed in, so that this directory is self-contained in the published
repository.

## Reproducing

The GAP scripts were run under GAP 4.16 with the standard character-table
(`CTblLib`) and small-groups libraries; the ATLAS cross-checks additionally
use `AtlasRep`. They are independent of the Lean toolchain: no build step, no
ordering, and no dependency on the state of the library. The Python scripts
use exact integer and `Fraction` arithmetic and the standard library only.

```bash
gap bc_separation/orthogonal_witness.g
python3 bc_separation/symplectic_exclusion.py
python3 extraspecial_2groups/cyclic_faithful_check.py   # resolves ../lib relatively
python3 linear_tower_residues/h6_discharge.py  120 100  # ~30 min
python3 linear_tower_residues/pos_discharge.py 2000 120 # ~5 min
```

Paths are script-relative, so the scripts run from anywhere. The one exception
is the captured `*_out.txt` files: they are records of the original runs and
still contain absolute paths of the machine that produced them (mostly inside
GAP's own stack traces).

## The development record

These clusters are the corroboration core, not the whole computational
history. Further probes, the intermediate censuses they build on, and the
internal audit logs of this development — referred to above as *the
development record* — are private, as are the `§4xx` sections cited from
`simple_recognition_alignment/RESULTS.md`. They are available from the author
on request; the "internal record" identifiers above index them.
