# Reproducibility

Everything needed to rebuild and re-verify the `lean_dring` formalization from a
clean checkout. Written for a referee: the goal is that you can convince
yourself, without reading Lean, that the claims in the paper are checked by
Lean's kernel and by nothing else.

## 1. Pinned toolchain and dependency lock

| file | pin |
|---|---|
| `lean-toolchain` | `leanprover/lean4:v4.32.0` |
| `lakefile.toml` | `[[require]] mathlib`, `rev = "v4.32.0"` |
| `lake-manifest.json` | exact revisions for mathlib and all transitive deps |

The manifest revisions (manifest format `1.2.0`):

| package | revision |
|---|---|
| `mathlib` | `81a5d257c8e410db227a6665ed08f64fea08e997` |
| `batteries` | `023ce7d62a0531e22a5331e20b587817a80d49ff` |
| `aesop` | `a7dbf0c63b694e47f425f3dcddbc0e178bb432d3` |
| `proofwidgets` | `6e311e2a844da9b2cc3971187df2fe0066947b93` |
| `Qq` | `38d591e778f100aec9762bb582f9c7f55f50e9dc` |
| `importGraph` | `7e9612bf0b9ee66db3cb5b9988a35afc706f5a12` |
| `LeanSearchClient` | `c5d5b8fe6e5158def25cd28eb94e4141ad97c843` |
| `plausible` | `e12c1910fe855cbfc38803cd4e55543906d5fa62` |
| `Cli` | `88679d088c9720c27ebdf2ba4dafe17341747f94` |

Some of these packages record `inputRev` values such as `"main"` or `"master"`.
That is irrelevant to reproducibility: `lake` resolves against the **`rev`**
recorded in `lake-manifest.json`, and the manifest is committed. As long as you
do not run `lake update`, the build is pinned to exactly the revisions above.

## 2. Clean-checkout build

```bash
git clone https://github.com/tilemachosvassias/LeanDring lean_dring
cd lean_dring
lake exe cache get      # fetch Mathlib's prebuilt oleans (required; building
                        # Mathlib from source takes hours)
lake build
```

`lake build` must end with

```
Build completed successfully (N jobs).
```

The job count `N` is informational and not a stable invariant — it changes with
Lake's internal job accounting and with the Mathlib cache state. What is stable
is the exit code and the absence of any `error:` line.

**What a clean log looks like**, precisely:

* exit code `0`, zero `error:` lines;
* the **only** warnings are the style linter's line-length notice
  (`This line exceeds the 100 character limit`), and they occur **only inside
  machine-emitted data files** — the `LeanDring/P5/Data/` chunk families and
  six emitted-data certificate files under `LeanDring/P5/Certificate/*/Twin2/`
  (`FrattiniCert`, `CharBoxReps`, `CharCert`, `EntryDataGap`, `SpeciesCosets`,
  `SpeciesOrbitData`). These are long generated data literals, not prose or
  proofs; the suppressions will move into the emitters if the data is ever
  regenerated. Hand-written modules build warning-free:

  ```bash
  grep 'warning:' build.log | grep -v 'exceeds the 100 character limit' | wc -l   # 0
  grep 'warning:' build.log | grep -v 'LeanDring/P5/' | wc -l                     # 0
  ```

* every `info: … depends on axioms:` line reports a subset of
  `[propext, Classical.choice, Quot.sound]`, and the token `sorryAx` appears
  nowhere in the log.

## 3. Build scope: 954 of 968 modules

`lakefile.toml` declares

```toml
[[lean_lib]]
name = "LeanDring"
```

with **no `globs` field**. Lake's default for a `lean_lib` is `Glob.one <name>`,
i.e. the single root module `LeanDring.lean` — so `lake build` compiles
`LeanDring.lean` together with its transitive `import` closure, and nothing else.
That closure is **954** of the repository's **968** `.lean` files (root module
included).

The 14 files outside the closure are, by design, not part of the trust base:

| file | role |
|---|---|
| `LeanDring/P5/Certificate/Generators/Twin1/Gen.lean` | `#eval` data generator |
| `LeanDring/P5/Certificate/Generators/Twin2/Gen.lean` | `#eval` data generator |
| `LeanDring/P5/Certificate/Generators/Twin2/GenCert.lean` | `#eval` data generator |
| `LeanDring/P5/Certificate/Generators/Twin2/GenChar.lean` | `#eval` data generator |
| `LeanDring/P5/Certificate/Generators/Twin2/ConjGen.lean` | `#eval` data generator |
| `LeanDring/P5/Certificate/Generators/Twin1/NormGen.lean` | `#eval` data generator |
| `LeanDring/P5/Certificate/Generators/Twin2/NormGen.lean` | `#eval` data generator |
| `LeanDring/P5/Certificate/SpeciesTable/Twin1/SpeciesEmit.lean` | `#eval` data generator |
| `LeanDring/P5/Certificate/SpeciesTable/Twin2/SpeciesEmit.lean` | `#eval` data generator |
| `LeanDring/P5/Certificate/Generators/Twin1/TransversalGen.lean` | `#eval` data generator |
| `LeanDring/P5/Certificate/Support/EntryPilot.lean` | cost-measurement scratch |
| `LeanDring/P5/Certificate/Support/SupportCount.lean` | cost-measurement scratch |
| `LeanDring/MathlibCheck.lean` | standalone Mathlib availability check |
| `LeanDring/AxiomAudit.lean` | axiom audit (1300 `#print axioms` lines); built explicitly via `lake env lean`, kept out of the default target so routine builds stay quiet |

**The even-order layer is *not* on that list.** `LeanDring/Even/` (39 modules,
paper Sections 6–7) is inside the closure: `LeanDring/Even.lean` is imported by
the root module, so `lake build` compiles it. It is `sorry`-free and rests on
the same three standard axioms.

These files *produce* candidate data by evaluation; they never *justify*
anything. The data they emit is pasted into the compiled modules and there
re-checked from scratch by kernel `decide`. A referee can delete all of them
and the theorems still compile. This is why they are excluded from the default
target, and it is why a build log will not mention them.

Repository shape (why the tree is so large):

| class | files | lines | note |
|---|---:|---:|---|
| human-written mathematical core | 107 | ~37 600 | includes `LeanDring/MainResults.lean` |
| machine-emitted by the Python emitters (`python/p5_*.py`) | 565 | ~800 700 | stage-5 mass certificate |
| machine-emitted by the in-tree `#eval` generators | 191 | ~86 200 | embedded data + chunked kernel decides |
| order-`p⁴` arc | 32 | ~12 400 | a separate paper-relevant result set |
| even-order layer | 39 | ~11 000 | paper Sections 6–7 |
| infrastructure (`Theory.lean`, `P4.lean`, `P5.lean`, `AxiomAudit.lean`, `MathlibCheck.lean`, root) | 6 | ~2 300 | |
| untrusted standalone generators | 12 | ~2 000 | the excluded files above |

About **94 %** of the lines are generated certificate data. Each emitted family
names its producing emitter in its module docstring.

The per-class file counts above are indicative rather than exact — they were
taken at different times and do not re-sum to the current total. The
authoritative figures are the ones at the head of this section: **968** `.lean`
files in the library, **954** of them in the build closure, both re-derivable
with `python3 scripts/check_paper_numbers.py`.

## 4. The paper verification target

The declarations cited by the paper are collected, with restated full signatures,
in namespace `LeanDring.Paper`, across **two** files:

| file | declarations | what it holds |
|---|---:|---|
| `LeanDring/MainResults.lean` | 15 | the mathematical results the paper is about |
| `LeanDring/CertificateAnchors.lean` | 26 | the certificate landmarks and census counts the computational claims rest on |
| **total** | **41** | |

Check them with

```bash
lake env lean LeanDring/MainResults.lean
lake env lean LeanDring/CertificateAnchors.lean
```

Each command elaborates its file against the already-built library and prints
one axiom line per declaration — 15 lines and 26 lines respectively. **Both are
needed**: the two `[propext]`-only exceptions noted in §5 live in
`CertificateAnchors.lean`, so running `MainResults.lean` alone will not show
them.

`docs/PAPER_THEOREM_MAP.md` (in the repository root's `docs/`) maps each paper
result to its `LeanDring.Paper.*` name, its internal name, and its file.

## 5. Expected axiom output

Every one of the 39 lines printed by the two commands above must have the form

```
'LeanDring.Paper.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

with two exceptions, which print a strict **subset** and are therefore strictly
stronger: `LeanDring.Paper.subgroupCount_coordinate1` and
`LeanDring.Paper.pairClassTotal_coordinate1` report `[propext]` only, because
they are pure `decide` computations over embedded data.

In particular, the headline theorem prints

```
'LeanDring.Paper.dring_isomorphism_of_5_5_twins' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Those three are Lean's standard classical axioms. Anything else — most
importantly `sorryAx` — would indicate an incomplete proof. There is none: the
development contains

* **0** `sorry` anywhere in the repository, the even-order layer
  `LeanDring/Even/` included; the token appears only in prose docstrings;
* **0** custom `axiom` declarations;
* **0** uses of `native_decide` (the token appears only in negative prose
  assertions);
* **0** uses of `unsafe`, `opaque`, `@[implemented_by]` or `@[extern]`;
  `partial def` occurs only in the out-of-closure `#eval` generator scripts
  (11 uses across 5 files, none reachable from any compiled theorem).

Every kernel computation in this development is checked by Lean's kernel, not by
compiled code.

The larger internal audit is `LeanDring/AxiomAudit.lean`: **1300** `#print axioms`
lines covering the full landmark set. It is outside the default build target
(so routine builds stay quiet); reprint all of them explicitly with

```bash
lake env lean LeanDring/AxiomAudit.lean
```

Publishing that log as a release asset is recommended.

## 6. Memory guidance

Several modules contain kernel `decide` calls over large embedded literals and
need ~2 GB of resident memory *each*. Lake builds modules in parallel by
default, which on a small machine means several such modules at once.

**16 GB machines — build serially and stage the heavy modules first.** Use the
included `compile.sh`, which compiles the ~100 known-heavy modules one at a time
before running the final `lake build`:

```bash
cd lean_dring
sh compile.sh
```

`compile.sh` lists the heavy modules explicitly (the `P5Conj*R*`,
`P5AllSubgroupsProofs*`, `P5FrattiniCert*`, `P5CharRows*`, `P5CharComplete*`,
`P5SpeciesCosets*`, `P5SpeciesOrbitChunk*`, `P5NormChunk*`, `P5EntryDataK1..12`
and `P5SpeciesDiv0` families) and runs

```sh
for m in $HEAVY; do
  newmod=$(old_to_new_module "$m")   # looks up the new module in mapping.tsv
  lake build "$newmod" || { echo "FAILED: $m"; break; }
done
lake build
```

Each `lake build <single module>` is an isolated process, so peak memory is one
module's worth rather than the parallel maximum. If even that is too much, cap
the build with a cgroup, e.g.

```bash
systemd-run --user --scope -q -p MemoryMax=14G lake build
```

**32 GB or more — use bounded parallelism, `JOBS=2 ./compile.sh`.** An
unbounded plain `lake build` lets Lake schedule several kernel-heavy
certificate chunks at once (single chunks peak at multiple GB, the heaviest
far above that) and has crashed a 32 GB machine; the staged script with
`JOBS=2` gives most of the wall-clock benefit without that risk.

Wall-clock and peak-RSS figures depend strongly on core count and on whether
`lake exe cache get` succeeded, so no single number is quoted here; the
staged-versus-parallel distinction above is the part that matters.

## 7. Citing an exact version

Cite the repository by full commit hash, not by branch name. `CITATION.cff` in
this directory carries the software metadata. For an archived, DOI-bearing
version, tag a release and connect the repository to Zenodo, then cite the
version-specific DOI in the paper alongside the commit hash.
