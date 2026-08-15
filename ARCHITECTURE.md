# Architecture

`LeanDring` proves D-ring rigidity results for `p`-groups and, at order `p⁵`,
a counterexample: the two groups `SmallGroup(3125,68)` and `SmallGroup(3125,69)`
(`Coordinate 1` / `Coordinate 2`) have isomorphic monomial representation
rings despite being non-isomorphic groups. The library is organized so that a
reader can audit the hand-written mathematics without wading through the
machine-emitted certificate data that backs the order-`5⁵` computation.

## Directory layout

```
LeanDring.lean                 -- top: imports Theory, P4, P5, Even, MainResults,
                                  CertificateAnchors
LeanDring/
  Theory.lean                  -- aggregator: imports every Theory/*/*.lean file
  Theory/
    DRing/                     -- core D-ring / Grothendieck-ring / species / marks /
                                   Burnside / Bridge / Adams / Census / Classification /
                                   Decomposition theory (imports only Mathlib + Theory)
    OddOrder/                  -- odd-order D-ring rigidity (OddOrder.lean)
    Gauss/                     -- Gauss sums / Gauss sign machinery
    Cyclotomic/                -- cyclotomic-field support (CyclotomicCode, CyclotomicNonMem)
  P4.lean                      -- aggregator: imports every P4/*.lean file
  P4/                          -- order-p⁴ D-ring rigidity development (imports Theory + P4)
  P5.lean                      -- aggregator: Certificate files + Data family indexes
  P5/
    Certificate/                -- hand-written 5⁵-specific machinery: presentation,
                                    computable group model, conjugacy/character/subgroup
                                    theory, matching machinery, assembly. Imports Theory
                                    and other Certificate files (and, for a handful of
                                    assembly-layer files, specific Data chunks — see
                                    "Import direction" below).
    Data/
      <Family>.lean            -- one index file per emitted data family, importing all
                                   its numbered chunks
      <Family>/C001.lean ...   -- the emitted chunks themselves (machine-generated,
                                   zero-padded, e.g. LeanDring/P5/Data/ColRestCheap/C037.lean)
      -- 681 generated files in 13 families. Each embeds a data block together
      -- with a kernel `decide` re-deriving its defining property, so nothing
      -- here is trusted: a wrong datum yields a failing `decide`, never an
      -- unsound proof. Chunked because one `decide` over the whole certificate
      -- would exhaust memory -- the same reason compile.sh builds the heavy
      -- modules one at a time. Skippable when auditing the mathematics.
  Even.lean                      -- aggregator: the 39 modules of the even-order layer
  Even/                          -- even-order theory (paper Sections 6-7): cancellation for
                                    C2 x H, recognition of the finite simple groups, Burnside
                                    marks/ghost machinery, Boltje congruence, Dedekind-odd
                                    reduction. Part of the certified build;
                                    sorry-free
  MainResults.lean               -- START HERE: the mathematical results the paper is about,
                                    restated with full signatures
  CertificateAnchors.lean        -- verification-facing companion: certificate landmarks,
                                    census counts, cell-discharge lemmas
  AxiomAudit.lean                -- `#print axioms` over ~900 declarations; NOT imported
                                    by LeanDring.lean, build explicitly via `lake env lean`
  MathlibCheck.lean              -- standalone Mathlib availability check; not imported
                                    by LeanDring.lean
  (Twelve `#eval` generator/emitter files under P5/Certificate are likewise
  outside the build closure -- Generators/Twin{1,2}/*, SpeciesTable/Twin{1,2}/
  SpeciesEmit.lean, Support/{EntryPilot,SupportCount}.lean; each carries an
  in-file "outside the build closure" note.)
scripts/check_imports.py         -- layering checker (see below)

gap/                             -- GAP scripts for the p^4 / 5^5 arc (199 files): species
                                    generation, the 5^5 censuses, gauge/linkage experiments,
                                    sieve searches. Untrusted hint providers -- every datum
                                    they emit is re-checked by a kernel decide in Lean. The
                                    paper cites gap/em06_brauer_pair.g by path
python/                          -- the seven emitters that generated the machine-emitted
                                    5^5 certificates, plus their shared helper. Published
                                    unmodified as provenance: they predate the P5/ block
                                    reorganisation and emit the old flat layout, so they
                                    reproduce the certificates' content, not their present
                                    paths (scripts/mapping.tsv records old -> new)
verification/                    -- external computations that corroborate the even-order
                                    layer: GAP scripts and their captured output, plus a few
                                    Python/Sage helpers. NOT Lean, not compiled, and nothing
                                    in the library depends on them; they are provenance for
                                    the numbers quoted in the paper
docs/PAPER_THEOREM_MAP.md        -- paper result <-> Lean declaration correspondence table
scripts/mapping.tsv              -- old-path <TAB> new-path record of the Basic/ -> current
                                    layout migration. Operational: compile.sh resolves its
                                    heavy-module list through this table and aborts if it
                                    is missing
```

## The certificate pipeline (order `5⁵`)

The `5⁵` counterexample is assembled in stages, one directory per stage under
`LeanDring/P5/Certificate/`.  Within a stage, `Twin1/` holds the material
specific to `Coordinate 1` (`q = 1`) and `Twin2/` that for `Coordinate 2`
(`q = 2`); files serving both twins sit directly in the stage directory.

| Stage | What it does | Files |
|---|---|---|
| `Presentation/` | the 5-generator pc presentations of `Coordinate 1`/`Coordinate 2` as `PresentedGroup`s | 1 |
| `ComputableModel/` | a kernel-decidable `Fintype`/`Group` model realizing the presentation, cardinality `3125` | 2 |
| `SubgroupInventory/` | all `676` subgroups, Frattini certificates and their discharge, subgroup-count certificates | 11 |
| `ConjugacyClasses/` | the `148` subgroup conjugacy classes, normalizer orbits, the pair-class bridge | 46 |
| `Characters/` | linear-character certification per class representative, extension and completeness | 66 |
| `SpeciesTable/` | per-column exponent-vector certificates, per-cell species-entry evaluation, over both twins | 27 |
| `RingIsomorphism/` | pairing the two species tables cell-by-cell and assembling the `D`-ring isomorphism | 4 |
| `Support/` | shared helpers and cost probes for the entry machinery | 6 |
| `Generators/` | the `#eval` generators that produced the certificate data; **outside the build closure** | 8 |

Bulk emitted data lives under `LeanDring/P5/Data/` (`ColRestCheap`,
`ColRestHeavy`, `ColCdd`, `ColTau`, `EntryK`, `EntryA`, `FixZero`,
`SpeciesDiv`, `SpeciesAlign`, `MatchLeaf`, `MatchMaster`, `MatchPair`,
`SpeciesOrbitChunk`); [`python/`](python/) holds the emitters that produced it.

The final theorem (`dring_equiv_coordinate12`, re-exported in
`MainResults.lean` as `LeanDring.Paper.dring_isomorphism_of_5_5_twins`) is
unconditional: it depends only on the standard axioms
`[propext, Classical.choice, Quot.sound]`.

## Import-direction rule

Layers may only import **downward**:

- `Theory/**` imports only Mathlib and other `Theory/**` files.
- `P4/**` imports Mathlib, `Theory/**`, and other `P4/**` files.
- `P5/Certificate/**` imports Mathlib, `Theory/**`, and other `P5/Certificate/**` files.
- `P5/Data/**` imports Mathlib, `Theory/**`, `P5/Certificate/**`, and other `P5/Data/**` files.

Nothing imports upward (`Theory` never imports `P4` or `P5`; `P4` never
imports `P5`). `P5/Data` is machine-emitted and **skippable** for a reader
auditing the hand-written mathematics — everything a reader needs to trust is
stated, with full signatures, in `MainResults.lean`.

`scripts/check_imports.py` enforces this mechanically by grepping import
lines against each file's directory. It currently reports a known, expected
class of violations: a handful of `P5/Certificate` assembly files (e.g.
`RingIsomorphism/MatchAll.lean`, `SpeciesTable/Twin{1,2}/SpeciesOrbits.lean`,
`Support/Stage5Core.lean`, `SpeciesTable/Twin2/SpeciesTau/*.lean`,
`SpeciesTable/Twin2/EntryDataGap.lean`) import specific `P5/Data` chunks
directly, because their job is precisely to consume named data cells at the
top of the species-table and ring-isomorphism assembly. These are pre-existing, intentional
cross-references from the original flat layout, not migration bugs.

## Naming conventions, and what deviates on purpose

The namespace tracks the mathematical object, not the file path: `Even/` →
`LeanDring.Even`, `P4/` → `LeanDring.P4`, `Theory/DRing/` → the per-structure
namespaces (`DRing`, `MonGSet`, `BurnsideRing`, …), and `P5/Certificate/` →
`LeanDring.P5Presentation` for the `q = 1` twin and `…P5Presentation.Q2` for
`q = 2`. Path components such as `Theory`, `Certificate`, `Twin1` do not
appear in namespaces.

Known, deliberate deviations:

- **Standalone `#eval` generator scripts keep one private namespace per file**
  (`P5Gen2`, `P5Gen2Cert`, `P5Gen2Char`, `P5EntryPilot`). Each script is
  self-contained and carries its own copy of small helpers (`closeFrom`,
  `commutator`, pilot data); the per-script namespaces are what keeps those
  copies from colliding. They are outside the build closure and are not part
  of the trust base — do not merge them into `P5Presentation`.
- **`Support/CyclotomicCode.lean` keeps the `P5CyclotomicCode` namespace**: it
  is referenced from 95 machine-emitted `P5/Data` files, and the prefix
  distinguishes it from the generic `Theory/Cyclotomic/CyclotomicCode.lean`.
- **Some Twin2 certificate files disambiguate in the declaration name**
  (`rowsChunk2a`, `basisChunk2_0`) rather than the `Q2` namespace. Migrating
  them to `Q2` would change fully-qualified names consumed by the
  kernel-decide assembly layer and the axiom audit; deferred until a full
  rebuild can verify the move.
- **A few files declare across the layer boundary** (`Theory/DRing/SubgroupCount.lean`
  and `Theory/Cyclotomic/CyclotomicNonMem.lean` declare into `LeanDring.P4`;
  `P4/Capstone.lean` declares into `LeanDring.DRing`). Same deferral, same
  reason.
