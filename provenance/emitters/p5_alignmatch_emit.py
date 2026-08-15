#!/usr/bin/env python3
"""Stage-5 NEW-2 — the α-paired residual decides (the 34 set-divergent classes).

In 34 of the 148 subgroup classes the q1 and q2 character lists are not equal as
sets, so the row equivalence σ pairs a q1 orbit-representative vector `v` with a
DIFFERENT q2 vector `w = repChars2[rK][alnPos[rK][q]]`.  The emitted stage-3/4
`_match` decides are all same-`e` and therefore say nothing about those cells.
This emitter closes them, one kernel `decide` per (column, moved row):

    sumPowers (fastCode (colFn <obj>.D1) (map val v)) = sumPowers (fastCode (colFn <obj>.D2) (map val w))

with `<obj>` the column's already kernel-bound `ColCert`/`ColCertDiv` (fields `D`
resp. `D1`/`D2`) and the two row vectors written exactly as the assembly layer
produces them (`(repChars.getD rK []).getD q []`, resp. the q2/`alnPos` form), so
the leaf can `exact` them after the `bind1`/`bind2` rewrites.

Every cell is validated in Python first (`p5_stage5_common`).

Usage:  python3 python/p5_alignmatch_emit.py [--dry-run]
"""
from __future__ import annotations
import glob, json, os, re, sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p5_stage5_common import Data, REPO, BASIC, sum_powers_fast_code

MANIFEST = os.path.join(REPO, "python", "p5_certificate", "stage2_manifest.json")
ALIGN = os.path.join(REPO, "python", "p5_align_data.json")
PER_CELL = {1: 0.004, 5: 0.034, 25: 0.122, 125: 0.5, 625: 4.6}
FILE_BUDGET_S = 90.0

HDR = '''/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Basic.P5CharAlign
%s

/-!
# Stage-5 NEW-2 — α-paired residual decides, chunk %d

For the 34 subgroup classes whose q1/q2 character SETS differ, σ pairs a q1
orbit-representative vector with a different q2 vector; this chunk certifies the
cyclotomic-value equality of the two fast codes at those pairs, over the already
kernel-bound column data.  Auto-emitted by `python/p5_alignmatch_emit.py`.
-/

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

'''


def object_index():
    """(rK,rH,p) -> (name, module, is_div)."""
    out = {}
    for path in sorted(glob.glob(os.path.join(BASIC, "P5ColData*.lean"))):
        mod = "LeanDring.Basic." + os.path.basename(path)[:-5]
        txt = open(path, encoding="utf-8").read()
        for m in re.finditer(r"def (colCert(Div)?_(\d+)_(\d+)_(\d+))\s*:", txt):
            key = (int(m.group(3)), int(m.group(4)), int(m.group(5)))
            out[key] = (m.group(1), mod, m.group(2) is not None)
    return out


def main():
    dry = "--dry-run" in sys.argv
    D = Data()
    man = json.load(open(MANIFEST, encoding="utf-8"))
    aln = json.load(open(ALIGN, encoding="utf-8"))
    alnPos, moved = aln["alnPos"], {int(k): v for k, v in aln["moved"].items()}
    objs = object_index()
    by_rK = defaultdict(list)
    for e in man:
        by_rK[e["rK"]].append(e)

    items = []          # (rK, rH, p, ncells, m, objname, objmod, is_div)
    for rK in sorted(moved):
        for e in sorted(by_rK[rK], key=lambda e: (e["rH"], e["p"])):
            key = (rK, e["rH"], e["p"])
            name, mod, is_div = objs[key]
            reps = D.orbit_reps(rK)
            for q in reps:
                a = alnPos[rK][q]
                v = tuple(D.repChars[rK][q]); w = tuple(D.repChars2[rK][a])
                assert sum_powers_fast_code(e["D1"], v) == sum_powers_fast_code(e["D2"], w), \
                    ("alpha pairing invalid", key, q, a)
            items.append((rK, e["rH"], e["p"], len(reps), e["ntrav"], name, mod, is_div))
    print("aligned cells: %d over %d columns, %d classes"
          % (sum(i[3] for i in items), len(items), len(moved)))
    est = sum(i[3] * PER_CELL.get(i[4], 0.5) for i in items)
    print("estimated kernel time: %.0f s" % est)
    if dry:
        return

    chunks, cur, cost = [], [], 0.0
    for it in items:
        c = it[3] * PER_CELL.get(it[4], 0.5)
        if cur and cost + c > FILE_BUDGET_S:
            chunks.append(cur); cur, cost = [], 0.0
        cur.append(it); cost += c
    if cur:
        chunks.append(cur)

    modules = []
    for ci, chunk in enumerate(chunks):
        imports = "\n".join("import " + m for m in sorted({it[6] for it in chunk}))
        body = [HDR % (imports, ci)]
        for (rK, rH, p, nq, m, name, mod, is_div) in chunk:
            f1, f2 = ("D1", "D2") if is_div else ("D", "D")
            body.append(f'''theorem alnAll_{rK}_{rH}_{p} : ∀ j, j < (repChars.getD {rK} []).length →
    (normIsRep.getD {rK} []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn {name}.{f1} (m := {m}))
        (List.map ZMod.val ((repChars.getD {rK} []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn {name}.{f2} (m := {m}))
        (List.map ZMod.val ((Q2.repChars2.getD {rK} []).getD ((alnPos.getD {rK} []).getD j 0) []))) := by decide

''')
        body.append("end LeanDring.P5Presentation\n")
        modname = "P5SpeciesAlign%d" % ci
        open(os.path.join(BASIC, modname + ".lean"), "w", encoding="utf-8").write("".join(body))
        modules.append("LeanDring.Basic." + modname)
    open(os.path.join(REPO, "results", "p5_alignmatch_manifest.txt"), "w").write(
        "\n".join(modules) + "\n")
    print("wrote %d chunk files (results/p5_alignmatch_manifest.txt)" % len(chunks))


if __name__ == "__main__":
    main()
