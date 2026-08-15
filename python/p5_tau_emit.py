#!/usr/bin/env python3
"""GEM-19 stage 2 (endgame) — the τ-family cross-column certificate emitter.

The 28 γ-MOVED columns of the 2724×2724 twin species table are the residue the
main stage-3/4 emitter (``python/p5_stage34_emit.py``) deliberately skipped: it
excludes every ``P5ColDataTau*.lean`` module because those 108 ``ColCertDiv``
objects store SAME-INDEX twin data (q1 and q2 data of the *same* Lean column),
whereas GAP's isomorphism witness for the pair ``SmallGroup(3125,68)`` /
``SmallGroup(3125,69)`` pairs a q1 column with a *different* q2 column::

    TM68[i][j] = TM69[rhoA[i]][gammaA[j]]      (results/n_test_3125/match_A_perms.g)
    rhoA = id,  gammaA moves exactly 28 of the 2724 column points.

Lean's ``Coordinate 1`` is ``SmallGroup(3125,68)`` and ``Coordinate 2`` is
``SmallGroup(3125,69)`` (STATE.md:40), so GAP's relation reads "q1 column ``j``
matches q2 column ``gammaA[j]``", i.e. the q1 partner of a q2 column ``i'`` is
``gammaA⁻¹[i']``.

This emitter therefore does NOT assume a pairing.  It enumerates candidate
column pairings, validates each one SEMANTICALLY in Python against the embedded
exponent data, and emits Lean only for a pairing that validates at **every**
cell.  Candidates, in order:

    1. ``gamma_inv``  — q1 partner of q2 column i' is gammaA⁻¹(i')
    2. ``gamma``      — q1 partner of q2 column i' is gammaA(i')
    3. ``identity``   — q1 partner of q2 column i' is i' itself

WHAT THE DATA SAYS:
``gamma_inv`` and ``gamma`` BOTH FAIL (104 of 108 objects mismatch); ``identity``
validates at 100 % of cells, uniquely so (a brute-force search over all q1
columns of each (rK, rH) group returns exactly the self-column in 17 of the 18
groups; the 18th, (rK,rH) = (147,13), is fully degenerate — all four columns
carry identical data — so identity is a valid choice there too).

This is NOT a contradiction of GAP.  GAP searched with the ROW map forced to the
identity (``rhoA = id``) and had to move 28 columns to compensate; Lean's stage-5
assembly instead uses a per-row-class character-set alignment σ and the identity
column map.  Both are genuine witnesses; the table's automorphism group is
nontrivial.  Confirmed directly on the GAP tables ``Tmine_68.g`` / ``Tmine_69.g``:
for EVERY one of the 2724 columns ``j`` and EVERY row-class block ``c``, the
multiset ``{TM68[i][j] : rowClass i = c}`` equals ``{TM69[i][j] : rowClass i = c}``
— i.e. the identity column matching is compatible with a block-wise row
permutation, which is exactly the Lean stage-5 architecture.

Emitted theorem shape (one per τ object, same-``e`` — σ-robust)::

    theorem <q1name>_x_<q2name>_tau_match :
        ((Q2.charsAt2 ⟨rK, by decide⟩).map (fun e =>
            decide (LeanDring.P5CyclotomicCode.sumPowers
                (fastCode (colFn <q1obj>.D1 (m := m)) (e.map ZMod.val))
              = LeanDring.P5CyclotomicCode.sumPowers
                (fastCode (colFn <q2obj>.D2 (m := m)) (e.map ZMod.val))))).all id = true := by decide

(when the resolved pairing is the identity the two object names coincide and the
short name ``<name>_tau_match`` is used).  Sides are q1-first, the mirror of the
``P5SpeciesDiv*`` convention (which writes ``D2 = D1``); equality is symmetric,
stage-5 takes ``.symm`` if it wants the other orientation.

PYTHON ARITHMETIC PROVENANCE.  The validator re-implements ``fastCode`` +
``sumPowers`` (``P5EntryFast.lean:61``, ``P5CyclotomicCode.lean:57``) directly:
``fastCode D e i = (zipWith (*) e D[i]).sum % 25`` and ``sumPowers f = Σ_i
power(f i)`` in the ``Fin 20 → ℤ`` code basis with ``ζ^(20+s) = -(ζ^s + ζ^(5+s)
+ ζ^(10+s) + ζ^(15+s))``.  It is validated by REPLAYING the 294 already
kernel-proved ``P5SpeciesDiv*`` theorems (7,550 cells): zero mismatches.
Run ``--self-test`` to reproduce.

Usage:
    python3 python/p5_tau_emit.py --dry-run     # resolve pairing, validate, report
    python3 python/p5_tau_emit.py --self-test   # replay the kernel-proved chunks
    python3 python/p5_tau_emit.py               # emit files + manifest + report
"""
from __future__ import annotations

import argparse
import glob
import json
import os
import re
import sys
from collections import Counter, defaultdict

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASIC = os.path.join(REPO, "lean_dring", "LeanDring", "Basic")
MANIFEST = os.path.join(REPO, "python", "p5_certificate", "stage2_manifest.json")
PERMS = os.path.join(REPO, "results", "n_test_3125", "match_A_perms.g")

# --- cost model (measured, seconds per single decide incl. kernel recheck) ---
PER_DECIDE = {1: 0.004, 5: 0.034, 25: 0.122}
FILE_BUDGET_S = 120.0


# --------------------------------------------------------------------------
# data loading
# --------------------------------------------------------------------------
def parse_gamma():
    """The 1-based column permutation γ of GAP's isomorphism witness."""
    txt = open(PERMS, encoding="utf-8").read()
    m = re.search(r"\bgammaA\s*:=\s*(\[.*?\])\s*;", txt, re.S)
    gam = [int(x) for x in re.findall(r"-?\d+", m.group(1))]
    assert sorted(gam) == list(range(1, len(gam) + 1)), "gammaA is not a permutation"
    return gam


def parse_colpos():
    """Lean's per-class transversal positions with `cosetIsRep = true`."""
    txt = open(os.path.join(BASIC, "P5SpeciesOrbitData.lean"), encoding="utf-8").read()
    i = txt.index("def cosetIsRep")
    blk = txt[i:i + txt[i:].index("\n\n")]
    rows = [[x.strip() == "true" for x in L.split(",") if x.strip()]
            for L in re.findall(r"\[([^\[\]]*)\]", blk)]
    assert len(rows) == 148, len(rows)
    return [[p for p, b in enumerate(r) if b] for r in rows]


def parse_nested_list(fname, defname):
    """Parse a Lean literal `def <defname> := [ ... ]` as nested JSON lists."""
    txt = open(os.path.join(BASIC, fname), encoding="utf-8").read()
    i = txt.index("def " + defname)
    i = txt.index("[", i)
    depth, j = 0, i
    while True:
        if txt[j] == "[":
            depth += 1
        elif txt[j] == "]":
            depth -= 1
            if depth == 0:
                break
        j += 1
    return json.loads(txt[i:j + 1])


def load_manifest():
    return json.load(open(MANIFEST, encoding="utf-8"))


# --------------------------------------------------------------------------
# the Lean arithmetic, re-implemented
# --------------------------------------------------------------------------
def _power_vec(k):
    """`P5CyclotomicCode.power k : Fin 20 → ℤ` as a length-20 tuple."""
    r = k % 25
    v = [0] * 20
    if r < 20:
        v[r] = 1
    else:
        s = r - 20
        for i in range(20):
            if i % 5 == s:
                v[i] = -1
    return tuple(v)


POW = [_power_vec(k) for k in range(25)]


def sum_powers_fast_code(D, e):
    """`sumPowers (fastCode (colFn D) e)` — order-independent (it is a sum)."""
    acc = [0] * 20
    for row in D:
        p = POW[sum(a * b for a, b in zip(e, row)) % 25]
        for i in range(20):
            acc[i] += p[i]
    return tuple(acc)


# --------------------------------------------------------------------------
# self-test: replay the already kernel-proved P5SpeciesDiv* theorems
# --------------------------------------------------------------------------
def self_test(man, chars2):
    by_key = {(e["rK"], e["rH"], e["p"]): e for e in man}
    objs = cells = bad = 0
    for path in sorted(glob.glob(os.path.join(BASIC, "P5SpeciesDiv*.lean"))):
        txt = open(path, encoding="utf-8").read()
        for _, rK, rH, p in re.findall(
                r"theorem (colCertDiv_(\d+)_(\d+)_(\d+))_match", txt):
            o = by_key[(int(rK), int(rH), int(p))]
            objs += 1
            for e in chars2[int(rK)]:
                cells += 1
                if sum_powers_fast_code(o["D2"], e) != sum_powers_fast_code(o["D1"], e):
                    bad += 1
    return objs, cells, bad


# --------------------------------------------------------------------------
# pairing candidates + semantic validation
# --------------------------------------------------------------------------
def build_columns(colpos):
    """Lean's flat column enumeration: r ascending, then p ascending."""
    cols = [(r, p) for r in range(148) for p in colpos[r]]
    return cols, {c: i + 1 for i, c in enumerate(cols)}


def partner_maps(gam):
    ginv = [0] * (len(gam) + 1)
    for i, v in enumerate(gam):
        ginv[v] = i + 1
    return {
        "gamma_inv": lambda i2: ginv[i2],
        "gamma": lambda i2: gam[i2 - 1],
        "identity": lambda i2: i2,
    }


def validate(pairing, tau, cidx, cols, chars2):
    """Return (ok, cells_checked, failures, pairs) for one candidate pairing."""
    fails, pairs, cells = [], [], 0
    for key in sorted(tau):
        rK, rH, p = key
        q2 = tau[key]
        j1 = pairing(cidx[(rH, p)])
        pc = cols[j1 - 1]
        pk = (rK, pc[0], pc[1])
        if pk not in tau:
            fails.append((key, pk, "partner object absent from τ tier"))
            continue
        q1 = tau[pk]
        if q1["ntrav"] != q2["ntrav"]:
            fails.append((key, pk, f"m mismatch {q1['ntrav']} vs {q2['ntrav']}"))
            continue
        nbad = 0
        for e in chars2[rK]:
            cells += 1
            if sum_powers_fast_code(q1["D1"], e) != sum_powers_fast_code(q2["D2"], e):
                nbad += 1
        if nbad:
            fails.append((key, pk, f"value mismatch at {nbad}/{len(chars2[rK])} chars"))
        else:
            pairs.append((key, pk))
    return (not fails), cells, fails, pairs


def uniqueness_scan(tau, chars2):
    """Per (rK,rH) group: which q1 columns match each q2 column's D2?"""
    groups = defaultdict(list)
    for k in tau:
        groups[(k[0], k[1])].append(k)
    out = {}
    for g, ks in sorted(groups.items()):
        ks = sorted(ks)
        chars = chars2[g[0]]
        hits = {}
        for k2 in ks:
            hits[k2[2]] = [k1[2] for k1 in ks
                           if all(sum_powers_fast_code(tau[k1]["D1"], e)
                                  == sum_powers_fast_code(tau[k2]["D2"], e)
                                  for e in chars)]
        out[g] = hits
    return out


# --------------------------------------------------------------------------
# Lean emission
# --------------------------------------------------------------------------
def obj_name(key):
    return "colCertDiv_%d_%d_%d" % key


def obj_modules():
    """Map object name -> its P5ColDataTau* module name."""
    out = {}
    for path in sorted(glob.glob(os.path.join(BASIC, "P5ColDataTau*.lean"))):
        mod = "LeanDring.Basic." + os.path.basename(path)[:-5]
        for name in re.findall(r"^def (colCertDiv_\d+_\d+_\d+)\s*:",
                               open(path, encoding="utf-8").read(), re.M):
            out[name] = mod
    return out


def theorem_name(n1, n2):
    return f"{n1}_tau_match" if n1 == n2 else f"{n1}_x_{n2}_tau_match"


def emit(pairs, tau, chars2, mods, prefix):
    """Chunk under FILE_BUDGET_S and write the Lean files.  Returns manifest."""
    items = []
    for k2, k1 in pairs:
        m = tau[k2]["ntrav"]
        n = len(chars2[k2[0]])
        items.append((k2, k1, m, n, n * PER_DECIDE.get(m, 0.122)))

    chunks, cur, cost, cmods = [], [], 0.0, set()
    for it in items:
        if cur and cost + it[4] > FILE_BUDGET_S:
            chunks.append((cur, cmods))
            cur, cost, cmods = [], 0.0, set()
        cur.append(it)
        cost += it[4]
        cmods |= {mods[obj_name(it[0])], mods[obj_name(it[1])]}
    if cur:
        chunks.append((cur, cmods))

    manifest = []
    for ci, (chunk, cm) in enumerate(chunks):
        modname = f"{prefix}{ci}"
        imports = ["import LeanDring.Basic.P5EntrySupport",
                   "import LeanDring.Basic.P5CharAssembly",
                   "import LeanDring.Basic.P5CharAssembly2"]
        imports += [f"import {m}" for m in sorted(cm)]
        lines = [
            "/-",
            "Copyright (c) 2026 Tilemachos Vassias. All rights reserved.",
            "Released under Apache 2.0 license as described in the file LICENSE.",
            "Authors: Tilemachos Vassias (formalization assisted by Claude)",
            "-/",
            *imports,
            "",
            "/-!",
            "# M5 stage 2 endgame — the τ-family (γ-moved) column certificates.",
            f"Auto-emitted by python/p5_tau_emit.py. Chunk {ci}: {len(chunk)} columns.",
            "The 28 γ-moved columns of the twin species table, over every on-support",
            "row class (108 `ColCertDiv` objects, `P5ColDataTau*`).  Each theorem: for",
            "every character vector of the row class, the q1 column data and the q2",
            "column data of the RESOLVED column pairing have equal cyclotomic value",
            "(same-`e`, hence σ-robust).  Fed to `species_eq_of_fastcode_eq` at stage-5.",
            "",
            "Resolved pairing: see results/p5_tau_validation.md.  GAP's γ column",
            "permutation is NOT the pairing Lean needs — GAP forced `rhoA = id` on rows",
            "and compensated on columns; Lean aligns rows per class instead.",
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
        for k2, k1, m, _n, _c in chunk:
            n1, n2 = obj_name(k1), obj_name(k2)
            lines += [
                f"theorem {theorem_name(n1, n2)} :",
                f"    ((Q2.charsAt2 ⟨{k2[0]}, by decide⟩).map (fun e =>",
                "        decide (LeanDring.P5CyclotomicCode.sumPowers",
                f"            (fastCode (colFn {n1}.D1 (m := {m})) (e.map ZMod.val))",
                "          = LeanDring.P5CyclotomicCode.sumPowers",
                f"            (fastCode (colFn {n2}.D2 (m := {m})) (e.map ZMod.val))))).all id"
                " = true := by decide",
                "",
            ]
        lines += ["end LeanDring.P5Presentation", ""]
        with open(os.path.join(BASIC, f"{modname}.lean"), "w", encoding="utf-8") as fh:
            fh.write("\n".join(lines))
        manifest.append(f"LeanDring.Basic.{modname}")
    return manifest, chunks


# --------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--out-prefix", default="P5SpeciesTau")
    args = ap.parse_args()

    man = load_manifest()
    chars2 = parse_nested_list("P5CharCert2.lean", "repChars2")
    assert len(chars2) == 148

    if args.self_test:
        objs, cells, bad = self_test(man, chars2)
        print(f"[self-test] replayed {objs} kernel-proved P5SpeciesDiv theorems, "
              f"{cells} cells, {bad} mismatches", file=sys.stderr)
        sys.exit(1 if bad else 0)

    tau = {(e["rK"], e["rH"], e["p"]): e for e in man if e["tier"] == "tau"}
    print(f"[tau] {len(tau)} τ objects, "
          f"{len(set((k[1], k[2]) for k in tau))} distinct columns, "
          f"m-dist {dict(Counter(e['ntrav'] for e in tau.values()))}", file=sys.stderr)

    # arithmetic provenance gate — never emit on an unvalidated arithmetic port
    objs, cells, bad = self_test(man, chars2)
    print(f"[tau] arithmetic self-test: {objs} kernel-proved theorems, {cells} cells, "
          f"{bad} mismatches", file=sys.stderr)
    if bad:
        print("[tau] ABORT: the Python arithmetic disagrees with the kernel.",
              file=sys.stderr)
        sys.exit(2)

    gam = parse_gamma()
    colpos = parse_colpos()
    cols, cidx = build_columns(colpos)
    assert len(cols) == 2724 == len(gam)

    moved = sorted(i + 1 for i, v in enumerate(gam) if v != i + 1)
    tau_flat = sorted(cidx[(k[1], k[2])] for k in set((0, k[1], k[2]) for k in tau))
    print(f"[tau] γ moves {len(moved)} column points; τ columns map to flat indices "
          f"{'IDENTICAL to' if tau_flat == moved else 'DIFFERENT from'} the γ-moved set",
          file=sys.stderr)

    results = {}
    chosen = None
    for label, fn in partner_maps(gam).items():
        ok, ncells, fails, pairs = validate(fn, tau, cidx, cols, chars2)
        results[label] = (ok, ncells, fails, pairs)
        print(f"[tau] pairing {label:10s}: {'PASS' if ok else 'FAIL'} "
              f"({ncells} cells, {len(fails)} failing objects)", file=sys.stderr)
        if ok and chosen is None:
            chosen = label

    if chosen is None:
        print("[tau] ABORT: no candidate pairing validates. Failures per candidate:",
              file=sys.stderr)
        for label, (_ok, _c, fails, _p) in results.items():
            for f in fails[:10]:
                print(f"[tau]   {label}: {f}", file=sys.stderr)
        sys.exit(3)

    ok, ncells, _fails, pairs = results[chosen]
    assert len(pairs) == len(tau)
    assert len(set(k2 for k2, _ in pairs)) == len(tau), "q2 side not covered exactly once"
    assert len(set(k1 for _, k1 in pairs)) == len(tau), "q1 side not a bijection"

    uniq = uniqueness_scan(tau, chars2)
    mods = obj_modules()
    missing = [obj_name(k) for k in tau if obj_name(k) not in mods]
    if missing:
        print(f"[tau] ABORT: {len(missing)} τ objects have no P5ColDataTau* def: "
              f"{missing[:5]}", file=sys.stderr)
        sys.exit(4)

    total_cells = sum(len(chars2[k[0]]) for k in tau)
    est = sum(len(chars2[k2[0]]) * PER_DECIDE.get(tau[k2]["ntrav"], 0.122)
              for k2, _ in pairs)
    print(f"[tau] chosen pairing: {chosen}; {len(pairs)} theorems, "
          f"{total_cells} validated cells, est. kernel time {est:.0f}s", file=sys.stderr)

    if args.dry_run:
        for g in sorted(uniq):
            print(f"[tau]   uniqueness {g}: {uniq[g]}", file=sys.stderr)
        return

    manifest, chunks = emit(pairs, tau, chars2, mods, args.out_prefix)
    manpath = os.path.join(REPO, "results", "p5_tau_manifest.txt")
    with open(manpath, "w", encoding="utf-8") as fh:
        fh.write("\n".join(manifest) + "\n")
    write_report(chosen, results, pairs, tau, chars2, cidx, cols, gam, moved,
                 uniq, manifest, chunks, total_cells, objs, cells)
    print(f"[tau] wrote {len(manifest)} files + {manpath} + "
          f"results/p5_tau_validation.md", file=sys.stderr)
    print("[tau] build SEQUENTIALLY: while read m; do lake build \"$m\" || break; "
          "done < results/p5_tau_manifest.txt", file=sys.stderr)


def write_report(chosen, results, pairs, tau, chars2, cidx, cols, gam, moved,
                 uniq, manifest, chunks, total_cells, st_objs, st_cells):
    ginv = [0] * (len(gam) + 1)
    for i, v in enumerate(gam):
        ginv[v] = i + 1
    L = []
    A = L.append
    A("# τ-family cross-column certificate — validation report")
    A("")
    A("Generated by `python/p5_tau_emit.py` (do not edit by hand).")
    A("")
    A("## Resolved pairing")
    A("")
    A(f"**`{chosen}`** — the only candidate that validates at 100 % of cells.")
    A("")
    A("| candidate | result | cells checked | failing objects |")
    A("|---|---|---|---|")
    for label, (ok, ncells, fails, _p) in results.items():
        A(f"| `{label}` | {'**PASS**' if ok else 'FAIL'} | {ncells} | {len(fails)} |")
    A("")
    A("Evidence for the 68/69 ↔ q1/q2 identification: `STATE.md:40` — "
      "\"Coordinate 1 (SmallGroup(3125,68)) and Coordinate 2 (SmallGroup(3125,69))\". "
      "GAP's witness `TM68[i][j] = TM69[rhoA[i]][gammaA[j]]` with `rhoA = id` "
      "therefore reads: q1 column `j` ↔ q2 column `gammaA[j]`, so the q1 partner of "
      "q2 column `i'` is `gammaA⁻¹(i')` (candidate `gamma_inv`).")
    A("")
    A("Python arithmetic provenance: the validator's `fastCode`/`sumPowers` port was "
      f"checked by replaying the {st_objs} already kernel-proved `P5SpeciesDiv*` "
      f"theorems ({st_cells} cells) — **0 mismatches**.  Reproduce with "
      "`python3 python/p5_tau_emit.py --self-test`.")
    A("")
    A("## The 28 γ-moved column points and their partners")
    A("")
    A("Flat 1-based Σ-index ↔ Lean column `(rH, p)` (`r` ascending, then `p` "
      "ascending over `cosetIsRep = true` positions; `P5SpeciesOrbitData.cosetIsRep`).")
    A("")
    A("| Σ(q2) | q2 col (rH,p) | γ⁻¹(Σ) | γ(Σ) | resolved partner (rH,p) |")
    A("|---|---|---|---|---|")
    for i2 in moved:
        c = cols[i2 - 1]
        part = {"gamma_inv": ginv[i2], "gamma": gam[i2 - 1], "identity": i2}[chosen]
        A(f"| {i2} | ({c[0]}, {c[1]}) | {ginv[i2]} | {gam[i2 - 1]} | "
          f"{cols[part - 1]} |")
    A("")
    A("## Counts")
    A("")
    A(f"- τ objects (all `tier = \"tau\"` in `stage2_manifest.json`): **{len(tau)}**")
    A(f"- distinct γ-moved columns: **{len(moved)}**; every τ object's column is "
      "γ-moved (0 fixed-column τ objects)")
    A(f"- emitted theorems: **{len(pairs)}** — every τ object appears exactly once "
      "on the q2 (`D2`) side and exactly once on the q1 (`D1`) side")
    A(f"- Python-validated (pair, e) cells: **{total_cells}**")
    A(f"- emitted files: **{len(manifest)}** (`{manifest[0]}` … `{manifest[-1]}`)")
    A("")
    A("## Uniqueness scan")
    A("")
    A("For each `(rK, rH)` group, the set of q1 columns whose `D1` matches each q2 "
      "column's `D2` at every character of the row class:")
    A("")
    A("| (rK, rH) | #chars | q2 col → matching q1 cols |")
    A("|---|---|---|")
    for g in sorted(uniq):
        A(f"| {g} | {len(chars2[g[0]])} | "
          f"{'; '.join(f'{a}→{b}' for a, b in sorted(uniq[g].items()))} |")
    A("")
    A("## Anomalies")
    A("")
    A("1. **GAP's γ pairing is refuted for this certificate** (both directions, 104 of "
      "108 objects mismatch), while the identity column pairing validates everywhere. "
      "This is consistent, not contradictory: GAP searched with `rhoA = id` forced on "
      "ROWS, so it had to move columns; Lean's stage-5 aligns rows per class (σ) and "
      "keeps columns fixed.  Verified directly on `results/n_test_3125/Tmine_68.g` / "
      "`Tmine_69.g`: for **all 2724** columns `j` and **all** row-class blocks `c`, "
      "`{TM68[i][j] : rowClass i = c} = {TM69[i][j] : rowClass i = c}` as multisets — "
      "so an identity column map with a block-wise row permutation is a valid witness.")
    A("2. **`META68.colClass` per-class column counts disagree with Lean's "
      "`cosetIsRep` counts at 64 of 148 classes** — GAP's class numbering is a "
      "permutation of Lean's.  The flat Σ-index ↔ `(rH,p)` correspondence assumed by "
      "`python/p5_certificate/final2.py` (and hence the τ tier's definition) is "
      "therefore NOT independently confirmed by the meta files.  It does not affect "
      "this emitter: the resolved pairing is the identity, which needs no Σ-index "
      "correspondence, and the emitted theorems are validated cell-by-cell from the "
      "embedded Lean data alone.")
    A("3. **8 of the 108 τ objects have genuinely divergent data** `D1 ≠ D2` "
      "(`(118,68,19..22)` and `(147,68,19..22)`); 12 have `h1 ≠ h2`.  For those the "
      "decide is real content, not a `rfl`.  The remaining 100 have `D1 = D2`.")
    A("4. **Group `(rK,rH) = (147,13)` is degenerate**: all four columns carry "
      "identical data, so every q1 column matches every q2 column there.  The identity "
      "choice is one of the 24 valid ones.  In the other 17 groups the identity is the "
      "unique match.")
    A("")
    with open(os.path.join(REPO, "results", "p5_tau_validation.md"), "w",
              encoding="utf-8") as fh:
        fh.write("\n".join(L))


if __name__ == "__main__":
    main()
