# provenance/emitters/ — the certificate emitters

The seven scripts that generated the machine-emitted parts of the `5⁵`
certificate, plus the helper module they share. They are published so that the
provenance of the generated Lean files is inspectable.

| script | what it emitted |
|---|---|
| `p5_match_emit.py` | the cell-match certificates (`RingIsomorphism/MatchAll.lean` and the stage-5 leaf/pair chunks) |
| `p5_stage34_emit.py` | the stage-3/4 residual real-decide certificates for divergent columns |
| `p5_tau_emit.py` | the τ-family (γ-moved) column certificates |
| `p5_align_emit.py` | the per-class character alignment (stage-5 σ layer) |
| `p5_alignmatch_emit.py` | the alignment-universal match certificates |
| `p5_fixzero_emit.py` | the off-support emptiness certificates |
| `p5_gapfill_emit.py` | the on-support cells the A-block pass did not cover |
| `p5_stage5_common.py` | shared helper module imported by the above |

## Status: provenance, not a build step

Nothing in `LeanDring/` is produced by running these at build time, and no
theorem depends on them. Their output is committed to the repository and is
re-checked by Lean's kernel with `decide`, exactly like the GAP data in
[`../gap/`](../gap/): a wrong emission can only produce a failing `decide`,
never an unsound proof.

**These scripts are the historical artifacts that produced the committed
data, and they are published unmodified.** They predate the reorganisation of
`LeanDring/P5/` into mathematical blocks, so they read and write the old flat
layout — a single `LeanDring/Basic/` directory, with module names like
`LeanDring.Basic.P5MatchLeaf0`. The reorganisation renamed every one of those
files; [`../../scripts/mapping.tsv`](../../scripts/mapping.tsv) records the complete
old → new correspondence.

Re-running them therefore reproduces the *content* of the certificates, not
their present file names or module paths. They are not maintained as a
runnable pipeline, and porting them to the current layout would mean rewriting
their output-naming logic — which would no longer be the code that actually
produced the committed data. Fidelity to the artifact was preferred.

They also write small manifest files into a `results/` directory that is not
part of this repository; that directory held the working notes of the original
development.

## Requirements

Python 3.10+, standard library only — no third-party packages.
