# provenance/gap/ — the GAP scripts behind the order-`p⁴` and order-`5⁵` results

The computations that produce the paper's core objects: the monomial pair-class
data `M(G)`, the `2724 × 2724` species tables of the two order-`5⁵` twins
`SmallGroup(3125,68)` / `(3125,69)`, their alignment under a row/column
permutation, the subgroup / conjugacy-class / character census the Lean
certificate re-checks, and the order-`p⁴` species separations.

## Trust model: untrusted hint provider

Nothing here is trusted. GAP is an **untrusted hint provider**: it supplies
candidate data — presentations, subgroup inventories, normalizer generators,
conjugation matrices, alignment tables, column permutations — and every item is
re-derived and re-checked inside Lean by a kernel `decide`. A wrong hint can
only produce a failing `decide`, never an unsound proof. These scripts are
published so that the provenance of the data is inspectable, not because any
theorem rests on them.

That the model earns its keep is on the record: GAP's matching artifact for the
`5⁵` pair reported a 28-point column permutation that, checked against the
certified data, fails on 104 of 108 objects — while the identity pairing
validates all 12,200 entries involved. Two further GAP data errors were caught
the same way. See Section 8 of the paper.

## Index

Lean declarations below are the `LeanDring.Paper` aliases of
[`../docs/PAPER_THEOREM_MAP.md`](../docs/PAPER_THEOREM_MAP.md), where each is
tied to the internal name and file that carries the proof.

### The pair itself

| script | what it computes | re-checked in Lean by |
|---|---|---|
| `em06_brauer_pair.g` | order, exponent and class of `SmallGroup(3125,68)/(69)`; the single differing relation `f₂⁵ = f₅` vs `f₂⁵ = f₅²`; their non-isomorphy; equivalence of their character tables *including all power maps* (the Brauer-pair property of [EM06]); the necessary conditions for isoclinism; and agreement of their two tables of marks | nothing — this is the external input itself: caveats (ii) and (iii) of the theorem map, the two claims the paper takes from GAP rather than from Lean. The ring-theoretic side is `Paper.dring_isomorphism_of_5_5_twins` |

Cited by the paper at this exact path (§5.1 and the formalization section), and
listed as an ancillary file.

### `lib/` — the species engine

| script | what it computes | re-checked in Lean by |
|---|---|---|
| `lib/dring_sieve_standalone.g` | `SpeciesClassesD` — the monomial pair classes `(K, λ)` up to `G`-conjugacy, i.e. a basis of `M(G)/G` — and `SpeciesTableD`, the exact cyclotomic species table. Carries its own regression harness `DSelfTest`. Read by the scripts below | pair-class count → `Paper.pairClassTotal_coordinate1`, `Paper.card_charPairClass_coordinate1/2` (2724); rank statement → `Paper.rank_dring` |
| `lib/dg_correct.g` | `DG_G_coset`: the generally-correct parametrization of species rows by `N_G(H)`-orbits on the **cosets** `H/H'` (element-conjugacy only refines this, and overcounts when `H` is nonabelian). The pair-class enumeration used for the `5⁵` tables | `Paper.pairClassIndex_bijective_coordinate1` / `…_coordinate2` |
| `lib/dring_export.g` | `DExport`: writes a group's exact species table together with its table of marks in the plain text format the cross-isomorphism checker consumes | transport format only; its content is re-checked through the species-table rows above |

### `census/` — pair classes, subgroups, normalizers, characters

| script | what it computes | re-checked in Lean by |
|---|---|---|
| `census/g1_subgroups.g` | for both twins, one row per subgroup conjugacy class: `\|K\|`, `AbelianInvariants(K)`, `\|N_G(K)\|`, and the sizes of the `N_G(K)`-orbits on the linear characters of `K` — the subgroup, normalizer and character census in a single table | 676-subgroup inventory → `Paper.subgroupInventory_complete_coordinate1` / `…_coordinate2` (`P5Presentation.allSubs_complete`); 148 classes → `Paper.subgroupClasses_complete_coordinate1/2` and `Paper.subgroupClasses_distinct_coordinate1/2`; 5236 characters → `Paper.characterCount_complete_coordinate1/2` |
| `census/rank_p3.g` | `rank_ℤ D(G) = \|M(G)/G\|` computed directly, as the number of `N_G(H)`-orbits on `H/H'` summed over subgroup classes, for orders `27` and `125`, against Müller's closed formulas `p(4p+3)` and `3p(p+1)` | `Paper.rank_dring` |

### `species/` — the `5⁵` species tables and their alignment

| script | what it computes | re-checked in Lean by |
|---|---|---|
| `species/regen_3125.g` | full independent regeneration of both `2724 × 2724` species tables from the `(1/\|K\|)`-normalized species sum over `DG_G_coset` rows, with subgroup-class / fibre / character labels saved alongside. The paper's core object | `Paper.species_table_entry_match_coordinate12` (`P5Presentation.master`); column completeness → `Paper.speciesColsComplete_coordinate1` / `…_coordinate2` |
| `species/match_3125.g` | the alignment: finds a row/column permutation pair `(ρ, γ)` with `T₆₈[i][j] = T₆₉[ρ i][γ j]` by signature refinement, verifies it at **all** `2724²` entries, and reports whether `γ` carries the `[K,1]` block-start columns onto block-start columns | `Paper.row_column_match_coordinate12` (`P5Presentation.hmatch`); the row equivalence → `Paper.charPairClassEquiv_coordinate12` and `Paper.classElt_charPairClassEquiv_orbitRep` |
| `species/verify_3125_archive.g` | entry-by-entry re-verification of the recovered permutation certificate against the archived tables, plus the `[H,1]` block-start columns and the full Galois row action | as for `match_3125.g`, and the cell comparison `Paper.species_eq_of_fastcode_eq` |
| `species/verify_3125_sample.g` | a bounded independent recomputation: the leading `70 × 70` corner of each twin's table from the standalone engine, with Lemma A checked on the first 14 `[H,1]` species — a version-independent spot check of the generator | `Paper.species_eq_of_data_eq` and `Paper.species_eq_of_fastcode_eq` |
| `species/verify_5d.g` | the two semantic assumptions behind the generator — F1 (GAP's `RightTransversal` is two-sided for every subgroup-class representative) and A2 (row subgroup sizes nondecreasing) — plus a deterministic sample of archived entries recomputed from the unambiguous full-group formula `(1/\|K\|)·Σ_{g∈G} [H^g ≤ K]·λ(h^g)` | `Paper.species_table_entry_match_coordinate12` |
| `species/diag_3125.g` | ordering-independent comparison of the archived generation against the independent regeneration (multiset of sorted row and column multisets), which separates a genuine semantic discrepancy from a stalled matcher | provenance for the alignment above; no separate Lean anchor |

### `p4/` — the order-`p⁴` species computations

| script | what it computes | re-checked in Lean by |
|---|---|---|
| `p4/species_p4_small.g` | species-table separation for **all** groups of order `16` and `81`, the two computational cases of "no counterexample below `p⁵`": rank of `D(G)` first, then full tables plus a permutation-invariant Weisfeiler–Leman fingerprint on the rank collisions | `Paper.p4_pairwise_species_distinct`; capstone `Paper.p4_species_classifies` |
| `p4/p4_subgroup_counts.g` | settles the disputed `N_{p²}` subgroup-count row for models (xii)/(xiii) by building them from the paper's own presentations (equations (3) and (4)), with no Roman-numeral ↔ SmallGroup dictionary in between | `Paper.exceptional_p4_twins_separated` (`P4.isEmpty_tableIso_model_model`) |
| `p4/p4_sweep_profile.g` | ground-truth invariant table for every group of order `p⁴`, `p = 5, 7`: abelianization order, total subgroup counts and subgroup-class counts by order, cyclic-`p²` count, centre order, nilpotency class — the invariants a species-table isomorphism must preserve | `Paper.p4_pairwise_species_distinct` |
| `p4/verify_gjg10.g` | the classification data the paper cites: 15 groups of order `p⁴` (5 abelian, 10 non-abelian), subgroup counts by order, and identification of the (xii)/(xiii) presentations with their SmallGroup ids together with their centre, power-identity, maximal-abelian and orbit-count properties | the cited hypothesis `P4Classification p d` carried by `Paper.p4_species_classifies` |
| `p4/verify_gjg10_b.g` | identifies the (xiv)/(xv) models and checks the power identity `(ca^d)^p = a^{dp}` at several primes | as above |
| `p4/verify_gjg10_c.g` | whether full tables of marks separate `SmallGroup(p⁴, i)` for `i ∈ {3,8,9,10}` — the quartet left tied by the corrected subgroup counts | `Paper.p4_pairwise_species_distinct` |
| `p4/verify_gjg10_d.g` | confirms the subgroup-class-count polynomials `6p+5`, `4p+7`, `2p+8` for that quartet at `p = 11, 13`, exhibiting ids 9 and 10 as the tied pair | `Paper.exceptional_p4_twins_separated` |

## The series at larger primes (Section 7.4 of the paper)

Evidence, not proof, for the open problem of whether the D-ring isomorphism
persists along the order-`p⁵` series (the paper's Problem on the series):

| script | what it does |
|---|---|
| `series_higher_primes_defs.g` | shared definitions: the presented pair `Gpq(p, 1)` / `Gpq(p, d)` (`d` a quadratic non-residue mod `p`), `rank_Z D(G)` by normalizer orbits on `H/H'`, and diagonal-block fingerprints. Rank equality checked for `p = 5, 7, 11, 13, 17, 19` |
| `series_blocks_fast.g` | exact diagonal-block fingerprints of the species tables via canonical root-of-unity multiplicity vectors (integer arithmetic only, no cyclotomic field arithmetic); the multisets of blocks agree for `p = 5, 7, 11`. Agreement is a necessary condition for a species-table isomorphism — evidence; disagreement would be decisive |

Neither script feeds the Lean development: the `p = 5` theorem is certified
independently, and no paper claim rests on these runs.

## Running them

```bash
gap -q < provenance/gap/em06_brauer_pair.g   > results/em06_brauer_pair.log
gap -q < provenance/gap/p4/species_p4_small.g > results/species_p4_small.log
```

Written for GAP 4.16.0 with the standard character-table and small-groups
libraries. Paths inside the scripts are repository-relative, so run them from
the repository root; several write into `results/`, which you may need to
create.

Five of the `species/` scripts (`regen_3125.g`, `match_3125.g`, `diag_3125.g`,
`verify_3125_archive.g`, `verify_5d.g`) also read the archived preprint-era
tables under `provenance/gap/legacy/preprint_archive/` — 854 MB of bulk species dumps that
are deliberately not published here, being superseded by the certified Lean
data. They are included for their algorithms and their checks, which are
readable without the archive; `match_3125.g` runs its Phase A entirely on
`regen_3125.g`'s own output, and `species/verify_3125_sample.g` needs no archive
at all.

## What is not here

The even-order computations live separately, in
[`../verification/`](../verification/).

The exploratory corpus behind these scripts — the D-isomorphism sieves over
orders 32, 64, 128 and 256, the gauge and linkage experiments, the Smith-form
and hunt drivers, and the per-session task scripts — is part of the private
development record and is available from the author on request.
