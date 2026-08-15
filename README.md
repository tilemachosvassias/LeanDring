# LeanDring

[![Lean](https://img.shields.io/badge/Lean-4.32.0-blue)](lean-toolchain)
[![Mathlib](https://img.shields.io/badge/Mathlib-pinned-blue)](lake-manifest.json)
[![sorry-free](https://img.shields.io/badge/sorry--free-yes-brightgreen)](LeanDring/AxiomAudit.lean)
[![axioms](https://img.shields.io/badge/axioms-propext%20%7C%20Classical.choice%20%7C%20Quot.sound-brightgreen)](LeanDring/MainResults.lean)
[![License](https://img.shields.io/badge/license-Apache--2.0-lightgrey)](LICENSE)

A Lean 4 + Mathlib formalization of the **monomial representation ring**
`D(G)` (the ℂˣ-fibered Burnside ring) and of the species-table rigidity
results for groups of order `p⁴`, accompanying the author's preprint on
species-table isomorphism and the `5⁵` counterexample.

The headline theorem is **complete and unconditional**:

```lean
theorem LeanDring.P5Presentation.dring_equiv_coordinate12 :
    Nonempty (DRing (Coordinate 1) ≃+* DRing (Coordinate 2))
```

The two groups of order `5⁵` that GAP labels `SmallGroup(3125,68)` and
`SmallGroup(3125,69)` have isomorphic D-rings — a counterexample to D-ring
rigidity. The ring isomorphism is proved in Lean's kernel; the identification
of the two Lean pc-presentations with those GAP labels, and the two groups'
non-isomorphy, are exact GAP computations, stated as such wherever the claim
appears (see [Trust model](#trust-model-and-external-inputs)).

|  |  |
|---|---|
| **Size** | ~950,000 lines across 968 `.lean` files; **954 compiled by `lake build`** (the import closure of the root module) |
| **Trust base** | no `sorry`, no custom axioms, no `native_decide`; every headline theorem uses exactly `[propext, Classical.choice, Quot.sound]` |
| **External inputs** | four for the headline arc (two cited classical theorems, two exact GAP computations); the even-order layer carries its inputs as named `Prop` hypotheses — see [Trust model](#trust-model-and-external-inputs) |
| **Not in the trust base** | 14 files outside the build closure (`#eval` data generators, the axiom audit, a Mathlib availability check), listed individually in [`REPRODUCIBILITY.md`](REPRODUCIBILITY.md) |

**Start here**: [`LeanDring/MainResults.lean`](LeanDring/MainResults.lean) —
the mathematical results of the development, restated with full signatures and
English doc-strings, ending with an `#print axioms` line for each. The
technical certificate propositions the paper's computational claims rest on are
collected in the same style in
[`LeanDring/CertificateAnchors.lean`](LeanDring/CertificateAnchors.lean).
Verify them alone with `lake env lean LeanDring/MainResults.lean` (and
`LeanDring/CertificateAnchors.lean`).
[`docs/PAPER_THEOREM_MAP.md`](docs/PAPER_THEOREM_MAP.md) is the
paper-result ↔ Lean-declaration correspondence table.
[`LeanDring/AxiomAudit.lean`](LeanDring/AxiomAudit.lean) is the larger internal
audit (1300 `#print axioms` lines); building the library reprints the
certificates.

## What is proven

**Foundations.** The Burnside ring `B(G)` via a generic Grothendieck ring
construction; marks determine finite `G`-sets (a minimal-orbit matching
induction, no table-of-marks triangularity); the monomial ring `D(G)`
with the split embedding `η : B(G) ↪ D(G)`; species
`φ_{H,h} : D(G) →+* ℂ`; **species injectivity** (the table is a complete
invariant, Müller's ghost-ring embedding); Adams operations `ψᵏ` with
`η(B) = Fix(ψᴺ)` and the FIX-ψ² criterion for 2-groups.

**Müller's odd-order theorem.** Every complex point of `D(G)` is a
species (proved by complex species-table linear independence and scalar
extension). For odd-order `G`, the integer-valued points are exactly the
trivial-fibre/mark species: a nontrivial fibre produces an explicit odd
cyclotomic orbit sum which is not integral. Consequently every abstract
ring isomorphism `D(G) ≃+* D(H)` between finite odd-order groups induces
`B(G) ≃+* B(H)` (`OddOrder.burnsideEquivOfOddOrder`, Müller's odd-order theorem).

**The `[K,λ]` basis.** Induced basis elements with Müller's explicit
species formula, orbit decomposition, classification up to conjugation,
census uniqueness, and the free ℤ-basis of `D(G)` indexed by pair
classes; the certificate bridge (species-compatible class bijections
induce ring isomorphisms). Units: `±Ĝ ↪ D(G)ˣ`, the split
`D(G) = ℤĜ ⊕ I`, and Müller's Lemma 2.6.1 — every torsion unit factors
as `b(1 + a)`.

**The species→marks transport.** A `SpeciesTableIso` (row bijection plus
`(H,h)`-labelled, entry-equal column correspondences — the
Speziestafel-isomorphism) provably fixes the augmentation column,
transports subgroup orders and normalizer orders, and forces
**equal subgroup counts of every order**, the mark-table reduction of
[Hue09, Theorem 3.1]. The block correspondence it rests on — the induced
bijection `κ` of subgroup classes satisfies `|κK| = |K|` and matches the
mark tables of `K` and `κK` — is proven here rather than assumed.

**Order `p⁴` (`p ≥ 5`).** Lean models for all fifteen groups (ten
nonabelian, five abelian), built from presentations with `ZMod`-carry
and cocycle toolkits — GAP is used only to match models to SmallGroup
IDs, never as proof input. Machine-checked subgroup-count rows
(correcting an error in the [GJG10] table, `P4TableAudit`), the Gauss-sum
evaluation of the A-block for the critical pair (xii)/(xiii)
(`φ_{A,h}[A,χ] = χ(h)·ψ(−B²/4A)·χ₂(A)·g(χ₂,ψ)`), the
exceptional-pair arithmetic endgame (the mod-8 `ζ₈ₚ` contradiction, every odd
prime), and unconditional species-table separations
(`P4NoTableIso`, `P4Abelian`).

## Orientation

Top level, at a glance:

| path | what it is | compiled? |
|---|---|---|
| `LeanDring/`, `LeanDring.lean` | the Lean library — pure `.lean`, nothing else | **yes** |
| `docs/` | the paper ↔ Lean theorem correspondence table | no |
| `scripts/` | import-layering and paper-number checkers | no |
| `gap/` | the 19 GAP scripts that compute the order-`p⁴` and order-`5⁵` objects — species tables, the `5⁵` census, the table alignment — including the one the paper cites by path; untrusted hint providers, provenance only | no |
| `python/` | the seven emitters that generated the machine-emitted `5⁵` certificates; provenance only | no |
| `verification/` | GAP/Python computations that corroborate the even-order layer, in six per-topic clusters; provenance only | no |

The library itself is organized into five strata, each importing only downward
(`scripts/check_imports.py` enforces this mechanically):

- **`LeanDring/Theory/{DRing,OddOrder,Gauss,Cyclotomic}/`** — reusable
  mathematics with Mathlib-only imports: the Burnside/D-ring/species/marks
  foundations, Müller's odd-order theorem, the Gauss-sum and Gauss-sign
  machinery, and cyclotomic-field support. Imports only Mathlib and other
  `Theory/**` files.
- **`LeanDring/P4/`** — the order-`p⁴` rigidity development (the fifteen
  models, the 105 pairwise species-table separations, the Gauss-sum twin
  argument). Imports Mathlib, `Theory/**`, and other `P4/**` files.
- **`LeanDring/P5/Certificate/`** — the hand-written, order-`5⁵`-specific
  machinery: presentation, computable group model, subgroup/conjugacy/
  character theory, matching machinery, final assembly. Imports Mathlib,
  `Theory/**`, and other `Certificate/**` files (with a documented handful of
  assembly-layer exceptions that consume `P5/Data` chunks directly — see
  "Import direction" in `ARCHITECTURE.md`).
- **`LeanDring/P5/Data/`** — 13 families of machine-emitted, kernel-checked
  data chunks backing the `5⁵` certificate (one index file per family, plus
  the numbered chunks themselves). This is the bulk of the repository's line
  count and is **skippable** for a reader auditing the hand-written
  mathematics; everything that needs trusting is restated, with full
  signatures, in `MainResults.lean`.
- **`LeanDring/Even/`** — the even-order layer (Sections 6–7 of the paper):
  cancellation for `C₂ × H`, recognition of the finite simple groups, the
  Burnside marks/ghost machinery, Boltje's congruence, and the reduction of
  Dedekind's odd-order theorem to its `p`-group case. 39 modules, `sorry`-free,
  part of the build closure. Its theorems are verified *implications* whose
  external inputs are carried as explicit named `Prop`s — see "Trust model and
  external inputs" below.

Start with [`ARCHITECTURE.md`](ARCHITECTURE.md) for the full directory map,
the certificate pipeline, and the import-layering rule, and with
[`LeanDring.lean`](LeanDring.lean), the top-level import aggregator.

## Building

```bash
lake exe cache get      # fetch Mathlib's prebuilt oleans — required; building
                         # Mathlib from source takes hours
lake build
```

Requires the Mathlib toolchain pinned in `lean-toolchain` / `lakefile.toml`
(Lean 4.32.0); see [`REPRODUCIBILITY.md`](REPRODUCIBILITY.md) for the exact
pinned revisions of Mathlib and its transitive dependencies.

Several modules perform kernel `decide` calls over large embedded literals
and need on the order of 2 GB resident memory *each*; Lake's default
parallel build can therefore demand well beyond 16 GB on a small machine. On
a 16 GB machine, build serially with the included staged script instead of a
bare `lake build`:

```bash
sh compile.sh
```

`compile.sh` compiles the ~100 known-heavy modules one at a time (with
`[n/378]`-style progress output) before running the final `lake build`; see
`REPRODUCIBILITY.md` §6 for the mechanism and for a `systemd-run`/cgroup
fallback if even that is too much. 32 GB or more: prefer `JOBS=2 ./compile.sh`
(bounded parallelism); an unbounded plain `lake build` has crashed a 32 GB
machine on the kernel-heavy certificate chunks.

To verify only the declarations the paper cites (13 mathematical results plus
26 certificate anchors, each printing its axiom set):

```bash
lake env lean LeanDring/MainResults.lean
lake env lean LeanDring/CertificateAnchors.lean
```

For the larger internal audit (1300 `#print axioms` lines covering the
full landmark set):

```bash
lake env lean LeanDring/AxiomAudit.lean
```

## Scope and honesty notes

> **FORMALIZATION SCOPE POLICY (2026-07-19 — READ THIS BEFORE EXPANDING THE
> LIBRARY).** The project aims to prove every theorem that is central to the
> D-ring arguments. It does **not** automatically formalize a large general
> theory merely because that theory is remotely connected. A classical input
> may be accepted only when it is standard in the literature, isolated as a
> narrow named interface, and the cost of formalizing it is seriously
> disproportionate to its role. Such inputs must be flagged explicitly; they
> must never be hidden inside broad reduction hypotheses. Prefer the smallest
> target-specific verified certificate over a new general-purpose algebra or
> computation library. In particular, the `5⁵` checker targets conductor 25;
> it will use the explicit five-term polynomial `Φ₂₅`, not a home-grown general
> cyclotomic computer. This is a deliberate scope boundary, not a claim that
> the omitted general mathematics is unimportant.

- The classification of groups of order `p⁴` (Hölder 1893; modern
  exposition Adler–Garlow–Wheland, arXiv:1611.00461) is **cited, not
  formalized**: the fifteen models are constructed and analyzed, but the
  statement "every group of order `p⁴` is one of these" is not proven
  here.
- Gauss's sign theorem (for an odd prime `p`, `∑ⱼ e^{2πij²/p} = √p` if
  `p ≡ 1 (mod 4)`, `i√p` if `p ≡ 3 (mod 4)`) is **not** in Mathlib as of this
  writing, and so **is proved here from scratch**, self-contained over
  Mathlib: `GaussSign.gauss_eq` in
  [`LeanDring/Theory/Gauss/GaussSignTheorem.lean`](LeanDring/Theory/Gauss/GaussSignTheorem.lean),
  by Schur's DFT-matrix proof (eigenspace decomposition of the character
  DFT matrix `F`, with the phase of `det F` pinning the sign), with the
  Mathlib-idiomatic corollary `GaussSign.rootNumber_χℂ_eq_one` (root number
  of the quadratic Dirichlet character mod an odd prime is `1`) in
  [`LeanDring/Theory/Gauss/GaussRootNumber.lean`](LeanDring/Theory/Gauss/GaussRootNumber.lean).
  The **general** Landsberg–Schaar reciprocity relation is deliberately
  **not** formalized — it is not needed in general; only the single
  instance required by the `p⁴` exceptional-pair argument is used, and that
  instance is discharged directly as a mod-`8p` CRT identity rather than via
  the general reciprocity law.
- The `5⁵` collision certificate and the exceptional-pair separation are **done** (2026-07-27):
  the separation is `P4.isEmpty_tableIso_model_model` and the `5⁵` collision is
  `P5Presentation.dring_equiv_coordinate12`, both unconditional. What remains
  external there is provenance, not proof: the identification of the Lean
  pc-presentations `Coordinate 1` / `Coordinate 2` with GAP's
  `SmallGroup(3125,68)` / `(3125,69)`, and the non-isomorphy of those two groups,
  are `[COMPUTED]` (GAP), not formalized.

## Trust model and external inputs

Everything in this development is kernel-checked, with axiom sets contained
in `[propext, Classical.choice, Quot.sound]` — Lean's three standard
classical axioms; there is no `sorry`, no custom axiom, no `native_decide`.
GAP and Python are used only as **untrusted hint providers**: they supply
data (pc presentations, subgroup inventories, normalizer generators,
alignment tables), and every item is re-verified by a kernel `decide` that
checks its defining property from scratch. A wrong hint can only produce a
failing `decide`, never an unsound proof.

For the headline arc (the paper's Sections 2–5: order-`p⁴` rigidity, the
`5⁵` counterexample, odd order, the Gauss sign), exactly four inputs remain
external to the kernel:

1. the classical classification of groups of order `p⁴` (Hölder 1893;
   Adler–Garlow–Wheland, arXiv:1611.00461) — cited, not formalized, and
   carried as an explicit hypothesis `P4Classification` rather than an
   axiom;
2. the identification of the two Lean pc-presentations `Coordinate 1` /
   `Coordinate 2` with `SmallGroup(3125,68)` / `SmallGroup(3125,69)` — a GAP
   computation;
3. the non-isomorphy of those two groups — a GAP computation;
4. Dedekind's theorem in odd order (Robinson, *A Course in the Theory of
   Groups*) — cited, not formalized, and used only for the marks-to-
   abelianization lemma.

The even-order layer (the paper's Sections 6–7) additionally carries its own
external inputs — Boltje's integrality criterion, CFSG-dependent recognition
hypotheses — as **named `Prop` hypotheses written into the statements of its
conditional theorems**; see `LeanDring/Even.lean` and the paper's §7.6 for
the exact list.

See the paper's appendix (theorem map) and `sec:limitations` for the precise
statement of what
each of these gaps does and does not affect.

## AI assistance, stated plainly

This formalization was developed with substantial assistance from **Claude**
(Anthropic's AI assistant), working in human-directed sessions: large parts
of the Lean proofs, the certificate engineering, the restructuring, and the
documentation were drafted, repaired, and audited that way. Every file's
`Authors:` line records it (`formalization assisted by Claude`). The
mathematics, the accompanying paper, the decisions about what to prove and
what to cite, and the final review are the author's.

This does not enter the trust base. The point of a kernel-checked
development is precisely that trust rests on the *checker*, not on how the
proofs were found: every theorem here is verified by Lean's kernel against
the three standard axioms, the build and audit gates above are reproducible
by anyone, and a wrong proof — whoever or whatever wrote it — does not
compile. Treat the AI's role the way you would treat any proof assistant
tooling: it explains how the artifact was produced, not why it is correct.

## Citation

Cite this repository via [`CITATION.cff`](CITATION.cff) — GitHub renders it
under "Cite this repository" in the sidebar. It accompanies the preprint
(arXiv ID to be added on announcement); cite the exact commit hash or tagged
release, not a branch name — see `REPRODUCIBILITY.md` §7.

```bibtex
@software{vassias_leandring,
  author  = {Vassias, Tilemachos},
  title   = {{LeanDring}: a {Lean~4} formalization of the monomial
             representation ring and of species-table rigidity},
  url     = {https://github.com/tilemachosvassias/LeanDring},
  version = {v1.0.0},
  year    = {2026},
  license = {Apache-2.0}
}
```

## License

Apache 2.0 (see [`LICENSE`](LICENSE)).
