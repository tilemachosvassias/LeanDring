#!/usr/bin/env python3
"""Stage-5 NEW-3 — the off-support emptiness certificates.

12,725 subgroup-class pairs (rK,rH) satisfy |H| <= |K| yet have an EMPTY
fixed-point set (G/K)^H, so `species_basisElt_eq_zero_of_card_lt` cannot fire and
the vanishing has to be certified.  For each twin and each such pair the kernel
scans the [G:K] cosets of the class's certified full transversal `R<rK>`:

    theorem fixzq_<rK> : (<offList>).all (fun rH => decide (#{i | (repBases.getD rH []).all
        (fun g => siftB q (basisAt rK<rK>) (retConj q (R<rK> i) g)) = true} = 0)) = true := by decide

    theorem fzq_<rK>_<rH> : Fintype.card (fixedPoints (reps rH) (Coordinate q / reps rK)) = 0 :=
      repsFixedCard rK<rK> <rH> R<rK> hpxR<rK> hcardq<rK> (of_decide_eq_true (...))

One batched decide per (twin, rK) — same kernel work as 25,450 separate decides,
a fraction of the elaboration.  Measured envelope: 60 coset checks / s.

Usage:  python3 python/p5_fixzero_emit.py [--dry-run]
"""
from __future__ import annotations
import glob, json, os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p5_stage5_common import Data, REPO, BASIC

FILE_BUDGET_S = 200.0
RATE = 60.0                      # coset checks per second (measured)

HDR = '''/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
%s

/-!
# Stage-5 NEW-3 — off-support emptiness certificates, chunk %d

For each `(rK, rH)` in this chunk the `H`-fixed part of `G/K` is EMPTY (while
`|H| <= |K|`, so the order bound does not apply): one batched kernel `decide` per
class scans the certified full transversal `R<rK>`, and the per-pair theorems
reflect it through `repsFixedCard` into the fixed-point count.  Feeds
`species_zero_of_fixCard_zero` (`P5Stage5Core`).
Auto-emitted by `python/p5_fixzero_emit.py`.
-/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

'''


def rk_modules():
    out = {}
    for path in sorted(glob.glob(os.path.join(BASIC, "P5EntryData*.lean"))):
        mod = "LeanDring.Basic." + os.path.basename(path)[:-5]
        for m in re.finditer(r"def R(\d+)list", open(path, encoding="utf-8").read()):
            out[int(m.group(1))] = mod
    return out


def main():
    dry = "--dry-run" in sys.argv
    D = Data()
    cache = os.path.join(REPO, "results", "p5_support_pairs.json")
    if os.path.exists(cache):
        supp = supp2 = {tuple(x) for x in json.load(open(cache, encoding="utf-8"))}
    else:
        supp, supp2 = D.support(1), D.support(2)
    assert supp == supp2, "the twins' sub-conjugacy relations differ"
    json.dump(sorted(supp), open(os.path.join(REPO, "results", "p5_support_pairs.json"), "w"))
    mods = rk_modules()

    tasks = []                    # (rK, offList, n, cost)
    for rK in range(148):
        if rK not in mods:
            continue              # rK = 0 : K = bot, handled abstractly
        n = 5 ** (5 - len(D.repBases[rK]))
        off = [rH for rH in range(148)
               if len(D.repBases[rH]) <= len(D.repBases[rK]) and (rK, rH) not in supp]
        if not off:
            continue
        tasks.append((rK, off, n, 2 * len(off) * n / RATE))
    npairs = sum(len(t[1]) for t in tasks)
    print("empty pairs: %d over %d classes; est kernel %.0f s (both twins)"
          % (npairs, len(tasks), sum(t[3] for t in tasks)))
    if dry:
        return

    chunks, cur, cost = [], [], 0.0
    for t in tasks:
        if cur and cost + t[3] > FILE_BUDGET_S:
            chunks.append(cur); cur, cost = [], 0.0
        cur.append(t); cost += t[3]
    if cur:
        chunks.append(cur)

    modules = []
    for ci, chunk in enumerate(chunks):
        imports = "\n".join("import " + m for m in sorted({mods[t[0]] for t in chunk}))
        body = [HDR % (imports, ci)]
        for (rK, off, n, _c) in chunk:
            lst = "[" + ", ".join(str(x) for x in off) + "]"
            for q in (1, 2):
                s2 = "" if q == 1 else "_2"
                lem = "" if q == 1 else "2"
                bA = "basisAt" if q == 1 else "basisAt2"
                pre = "" if q == 1 else "Q2."
                rb = "repBases" if q == 1 else "Q2.repBases2"
                body.append(f'''theorem fixz{q}_{rK} : ({lst} : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin {n} => ({rb}.getD rH []).all
      (fun g => siftB {q} ({pre}{bA} rK{rK}) (retConj {q} ({pre}R{rK}{s2} i) g)) = true)).card = 0)) = true := by decide

''')
                for rH in off:
                    body.append(f'''theorem fz{q}_{rK}_{rH} : Fintype.card
    (fixedPoints ({pre}reps (⟨{rH}, by decide⟩ : Fin 148)) (Coordinate {q} ⧸ {pre}reps rK{rK})) = 0 :=
  {pre}repsFixedCard{lem} rK{rK} ⟨{rH}, by decide⟩ {pre}R{rK}{s2} {pre}hpxR{rK}{s2} {pre}hcardq{rK}{s2}
    (of_decide_eq_true ((List.all_eq_true.mp fixz{q}_{rK}) {rH} (by decide)))

''')
        body.append("end LeanDring.P5Presentation\n")
        modname = "P5FixZero%d" % ci
        open(os.path.join(BASIC, modname + ".lean"), "w", encoding="utf-8").write("".join(body))
        modules.append("LeanDring.Basic." + modname)
    open(os.path.join(REPO, "results", "p5_fixzero_manifest.txt"), "w").write(
        "\n".join(modules) + "\n")
    print("wrote %d chunk files (results/p5_fixzero_manifest.txt)" % len(chunks))


if __name__ == "__main__":
    main()
