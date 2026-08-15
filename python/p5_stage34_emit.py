#!/usr/bin/env python3
"""GEM-19 stages 3-4 continuation emitter — residual real-decide certificates.

Parses the in-repo stage-2 data files
``lean_dring/LeanDring/Basic/P5ColData*.lean`` for every ``colCertDiv_*``
object (the twin-DIVERGENT columns: τ-moved + col-data-divergent, 2558 objects,
all with |T| = m ∈ {1,5,25}) and emits chunked Lean files, one theorem per
divergent column, that certify — with a single kernel ``decide`` over the
embedded exponent data — that the two twins' fast codes have equal cyclotomic
value for every character vector of the row class, position-aligned by the
identity row matching σ.

Emitted theorem shape (validated green against real data, rK=102/m=25, clean
axioms [propext, Classical.choice, Quot.sound])::

    theorem <name>_match :
        ((Q2.charsAt2 ⟨rK, by decide⟩).map (fun e =>
            decide (LeanDring.P5CyclotomicCode.sumPowers
                (fastCode (colFn <name>.D2 (m := m)) (e.map ZMod.val))
              = LeanDring.P5CyclotomicCode.sumPowers
                (fastCode (colFn <name>.D1 (m := m)) (e.map ZMod.val))))).all id = true := by decide

The certificate is the SAME-``e`` form: for each character ``e`` of the row
class, the two twins' fast codes (D2 vs D1) have equal cyclotomic value.  This is
σ-ROBUST — feeding the *same* character to both sides — so it holds regardless of
whether the class is char-reshaped.  Each ``= true`` is destructured at stage-5
assembly (via ``List.all_eq_true`` + ``of_decide_eq_true``) into the per-cell
``hcode`` consumed by ``species_eq_of_fastcode_eq`` (P5EntrySupport.lean).

IMPORTANT — what is NOT here (stage-5's row σ): a NAIVE position-aligned pairing
``charsAt.zip charsAt2`` is WRONG for char-reshaped classes (the q1/q2 character
orderings differ by a permutation — the stage-0 "reordering artifact"; verified:
the zip form is FALSE for rK=102).  The correct row matching σ is the character
SET-alignment permutation ``{charsAt rK} = {charsAt2 rK}``, a separate cheap
set-equality decide belonging to stage-5 assembly.  This emitter supplies only
the value-equality half (the residual real decides); it does NOT emit the σ
permutation.  If any ``_match`` decide evaluates FALSE the build fails loudly —
that would signal a genuine value mismatch (isomorphism failure), not a mere
reordering, and must be reported.

Usage:
    python3 python/p5_stage34_emit.py --dry-run      # report counts + chunk plan
    python3 python/p5_stage34_emit.py                # emit files + manifest
"""
from __future__ import annotations
import argparse
import glob
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASIC = os.path.join(REPO, "lean_dring", "LeanDring", "Basic")

# --- cost model (measured, seconds per single decide incl. kernel recheck) ---
PER_DECIDE = {1: 0.004, 5: 0.034, 25: 0.122}
# budget per emitted file's total kernel time.  Kept conservative because the
# kernel recheck roughly DOUBLES the tactic time and 16 GB tolerates no parallel
# heavy builds — build the manifest SEQUENTIALLY (`xargs -n1`), never `-n8`.
FILE_BUDGET_S = 120.0
# fallback char-count per class if charCounts unavailable (over-estimate = safe)
DEFAULT_NCHARS = 125

OBJ_RE = re.compile(r"^def (colCertDiv_\d+_\d+_\d+)\s*:\s*ColCertDiv\b", re.M)
FIELD_RE = {
    "rK": re.compile(r"rK\s*:=\s*⟨(\d+),"),
    "m": re.compile(r"\bm\s*:=\s*(\d+)"),
}


def parse_file(path):
    """Yield (objname, rK, m) for each colCertDiv in `path`."""
    with open(path, encoding="utf-8") as fh:
        text = fh.read()
    # split into blocks starting at each `def`
    starts = [(m.start(), m.group(1)) for m in OBJ_RE.finditer(text)]
    for idx, (pos, name) in enumerate(starts):
        end = starts[idx + 1][0] if idx + 1 < len(starts) else len(text)
        block = text[pos:end]
        rK = int(FIELD_RE["rK"].search(block).group(1))
        m = int(FIELD_RE["m"].search(block).group(1))
        yield name, rK, m


def load_char_counts():
    """Best-effort parse of `charCounts` literal from P5CharCount.lean; else {}."""
    for cand in ("P5CharCount.lean", "P5CharAssembly.lean"):
        p = os.path.join(BASIC, cand)
        if not os.path.exists(p):
            continue
        txt = open(p, encoding="utf-8").read()
        m = re.search(r"charCounts\s*:\s*List\s*(?:Nat|ℕ)\s*:=\s*\[([0-9,\s]+)\]", txt)
        if m:
            return {i: int(v) for i, v in enumerate(m.group(1).split(","))
                    if v.strip()}
    return {}


def module_of(path):
    rel = os.path.relpath(path, os.path.join(REPO, "lean_dring"))
    return rel[:-5].replace(os.sep, ".")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--out-prefix", default="P5SpeciesDiv")
    args = ap.parse_args()

    counts = load_char_counts()
    cols = []  # (objname, rK, m, source_module)
    for path in sorted(glob.glob(os.path.join(BASIC, "P5ColData*.lean"))):
        # τ-moved columns store SAME-INDEX data, not the cross-column γ-pairing
        # (q2 col i' vs q1 col γ(i')); they need a dedicated γ-paired emitter and
        # the match_A_perms.g column permutation — NOT the per-object same-e form.
        if "Tau" in os.path.basename(path):
            continue
        for name, rK, m in parse_file(path):
            cols.append((name, rK, m, module_of(path)))

    # cost per column = nchars * per_decide(m)
    def cost(rK, m):
        n = counts.get(rK, DEFAULT_NCHARS)
        return n * PER_DECIDE.get(m, 0.122)

    # greedy chunking under FILE_BUDGET_S, grouping by shared source modules
    chunks = []
    cur, cur_cost, cur_mods = [], 0.0, set()
    for name, rK, m, mod in cols:
        c = cost(rK, m)
        if cur and cur_cost + c > FILE_BUDGET_S:
            chunks.append((cur, cur_mods))
            cur, cur_cost, cur_mods = [], 0.0, set()
        cur.append((name, rK, m, mod))
        cur_cost += c
        cur_mods.add(mod)
    if cur:
        chunks.append((cur, cur_mods))

    print(f"[emit] {len(cols)} divergent columns -> {len(chunks)} files "
          f"(budget {FILE_BUDGET_S}s/file, charCounts={'yes' if counts else 'DEFAULT'})",
          file=sys.stderr)
    mdist = {}
    for _, _, m, _ in cols:
        mdist[m] = mdist.get(m, 0) + 1
    print(f"[emit] m-distribution: {mdist}", file=sys.stderr)

    if args.dry_run:
        return

    manifest = []
    for ci, (chunk, mods) in enumerate(chunks):
        modname = f"{args.out_prefix}{ci}"
        outpath = os.path.join(BASIC, f"{modname}.lean")
        imports = ["import LeanDring.Basic.P5EntrySupport",
                   "import LeanDring.Basic.P5CharAssembly",
                   "import LeanDring.Basic.P5CharAssembly2"]
        imports += [f"import {mod}" for mod in sorted(mods)]
        lines = [
            "/-",
            "Copyright (c) 2026 Tilemachos Vassias. All rights reserved.",
            "Released under Apache 2.0 license as described in the file LICENSE.",
            "Authors: Tilemachos Vassias (formalization assisted by Claude)",
            "-/",
            *imports,
            "",
            "/-!",
            "# M5 stages 3-4 — residual real-decide certificates (divergent columns).",
            f"Auto-emitted by python/p5_stage34_emit.py. Chunk {ci}: {len(chunk)} columns.",
            "Each theorem: for every character vector of the row class, the two twins'",
            "fast codes have equal cyclotomic value (identity row matching). Fed to",
            "`species_eq_of_fastcode_eq` at stage-5 assembly.",
            "-/",
            "",
            "namespace LeanDring.P5Presentation",
            "",
            "-- machine-emitted certificate: file-level heartbeat raise is intentional",
            "set_option linter.style.setOption false",
            "set_option maxHeartbeats 4000000",
            "set_option maxRecDepth 100000",
            "",
        ]
        for name, rK, m, _ in chunk:
            lines += [
                f"theorem {name}_match :",
                f"    ((Q2.charsAt2 ⟨{rK}, by decide⟩).map (fun e =>",
                "        decide (LeanDring.P5CyclotomicCode.sumPowers",
                f"            (fastCode (colFn {name}.D2 (m := {m})) (e.map ZMod.val))",
                "          = LeanDring.P5CyclotomicCode.sumPowers",
                f"            (fastCode (colFn {name}.D1 (m := {m})) (e.map ZMod.val))))).all id = true := by decide",
                "",
            ]
        lines += ["end LeanDring.P5Presentation", ""]
        with open(outpath, "w", encoding="utf-8") as fh:
            fh.write("\n".join(lines))
        manifest.append(f"LeanDring.Basic.{modname}")

    manpath = os.path.join(REPO, "results", "p5_stage34_manifest.txt")
    os.makedirs(os.path.dirname(manpath), exist_ok=True)
    with open(manpath, "w", encoding="utf-8") as fh:
        fh.write("\n".join(manifest) + "\n")
    print(f"[emit] wrote {len(chunks)} files + manifest {manpath}", file=sys.stderr)
    print("[emit] build SEQUENTIALLY (16 GB, no parallel heavy builds):",
          file=sys.stderr)
    print("[emit]   while read m; do lake build \"$m\" || break; done "
          "< results/p5_stage34_manifest.txt", file=sys.stderr)


if __name__ == "__main__":
    main()
