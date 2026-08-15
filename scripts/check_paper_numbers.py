#!/usr/bin/env python3
"""Audit the numerals quoted in the paper against this repository.

The paper quotes many concrete counts (census sizes, entry counts, class
lists).  They fall into two classes:

  * theorem-backed -- the number appears in a kernel-checked Lean statement
    (MainResults.lean / CertificateAnchors.lean).  We check it is still there.
  * evaluation-derived -- produced by the standalone emitters or by a
    measurement run, and reported as such in the paper (Theorem 5.1 proof
    discussion, Table 2).  We cannot re-derive those here; we check the
    arithmetic identities they must satisfy instead.

Run from the repository root:  python3 scripts/check_paper_numbers.py
Exit status 0 iff every check passes.
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
FAILURES = []
CHECKS = 0


def report(ok, label, detail=""):
    global CHECKS
    CHECKS += 1
    print(f"  [{'ok ' if ok else 'FAIL'}] {label}{'  -- ' + detail if detail else ''}")
    if not ok:
        FAILURES.append(label)


def lean_sources():
    for p in sorted((ROOT / "LeanDring").rglob("*.lean")):
        yield p


def in_lean(value, files=None):
    """True if the literal appears in one of the given files (default: all)."""
    pattern = re.compile(rf"(?<![0-9]){value}(?![0-9])")
    targets = files or lean_sources()
    for p in targets:
        if pattern.search(p.read_text(encoding="utf-8", errors="ignore")):
            return p
    return None


print("== theorem-backed census numbers (must appear in the paper-facing files) ==")
FACING = [ROOT / "LeanDring" / n for n in ("MainResults.lean", "CertificateAnchors.lean")]
FACING = [p for p in FACING if p.exists()]
for value, label in [
    (3125, "group order 5^5 = 3125"),
    (676, "subgroups"),
    (148, "conjugacy classes of subgroups"),
    (5236, "linear characters over the 148 representatives"),
    (2724, "character-pair classes = rank_Z D(G)"),
]:
    hit = in_lean(value, FACING)
    report(hit is not None, f"{label} = {value}", hit.name if hit else "not found in MainResults/CertificateAnchors")

# Table 1 also quotes 71 normal classes, certified by `normal_count`.  That
# theorem lives in the certificate layer rather than the paper-facing files.
hit = in_lean(71)
has_thm = in_lean("normal_count") is not None
report(hit is not None and has_thm, "normal subgroup classes = 71 (theorem normal_count)",
       f"{hit.relative_to(ROOT) if hit else 'value missing'}"
       + ("" if any(f.name in ("MainResults.lean", "CertificateAnchors.lean") for f in [hit] if hit)
          else "  [suggestion: restate in CertificateAnchors.lean]"))

print("\n== arithmetic identities the paper's own numbers must satisfy ==")

strata = [1, 156, 306, 181, 31, 1]
report(sum(strata) == 676, "subgroup strata sum to 676", f"{strata} -> {sum(strata)}")

fibre = {1: 148, 5: 2376, 25: 200}
report(sum(fibre.values()) == 2724, "order-fibre split sums to 2724",
       f"{'+'.join(map(str, fibre.values()))} = {sum(fibre.values())}")

orbits = {1: 1, 5: 12, 9: 61, 13: 5, 25: 56, 29: 1, 45: 11, 125: 1}
report(sum(orbits.values()) == 148, "orbit-count multiplicities sum to 148",
       f"{sum(orbits.values())}")
weighted = sum(k * v for k, v in orbits.items())
report(weighted == 2724, "orbit-count weighted sum is 2724", f"{weighted}")

report(2724 ** 2 == 7420176, "2724^2 = 7,420,176", f"{2724 ** 2}")

on_support, off_support, total = 683027, 6737149, 7420176
report(on_support + off_support == total, "on-support + off-support = total entries",
       f"{on_support} + {off_support} = {on_support + off_support}")
pct = 100.0 * on_support / total
report(abs(pct - 9.20) < 0.01, "on-support share is 9.20 %", f"{pct:.4f} %")

# Table 2 is a four-level hierarchy, not a flat list of three sub-rows:
#
#   needing a real decide (sigma-optimal)   173,006
#     tau-moved-column entries                6,776
#     non-moved divergent                   166,230
#       column-data divergence              155,970
#       row-divergence contribution          11,140
#
# The outer split is a genuine partition. The inner pair is a UNION, not a
# sum: a non-moved entry needs a decide iff its column data diverges OR its
# row vector does, and 880 entries do both. Source:
# results/lean_p5_stage0_divergent_count.md.
tau_moved, non_moved = 6776, 166230
col_divergence, row_divergence, both = 155970, 11140, 880
decide_total = 173006

report(tau_moved + non_moved == decide_total,
       "Table 2 outer split partitions the decide total",
       f"{tau_moved} + {non_moved} = {tau_moved + non_moved} vs {decide_total}")

report(col_divergence + row_divergence - both == non_moved,
       "Table 2 inner rows are a union with the stated overlap",
       f"{col_divergence} + {row_divergence} - {both} = "
       f"{col_divergence + row_divergence - both} vs {non_moved}")

report(abs(decide_total / 76272 - 2.27) < 0.005,
       "173,006 is 2.27x the withdrawn placeholder 76,272",
       f"{decide_total / 76272:.4f}")

classes = set(range(28, 53)) | {64, 67, 73, 76, 90, 95, 100, 105, 110}
report(len(classes) == 34, "Theorem 5.1(6) class list has 34 members", f"{len(classes)}")

print("\n== repository shape claims made in the paper ==")
lean_files = list(lean_sources())
n_files = len(lean_files) + 1  # + the root LeanDring.lean
report(n_files == 968, "total .lean files = 968 (README / REPRODUCIBILITY headline)",
       str(n_files))

audit = ROOT / "LeanDring" / "AxiomAudit.lean"
if audit.exists():
    # anchored: the file also mentions `#print axioms` inside a prose comment,
    # which is not one of the audit's commands
    n_audit = len(re.findall(r"^#print axioms", audit.read_text(), re.MULTILINE))
    report(n_audit == 1300, "#print axioms lines in AxiomAudit.lean = 1300 (paper Section 6.2)",
           str(n_audit))

def build_closure():
    """Modules reachable from the root module -- the certified development."""
    seen, stack = set(), ["LeanDring"]
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        path = ROOT / (mod.replace(".", "/") + ".lean")
        if not path.exists():
            continue
        seen.add(mod)
        for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
            m = re.match(r"import (LeanDring[\w.]*)", line)
            if m:
                stack.append(m.group(1))
    return {ROOT / (m.replace(".", "/") + ".lean") for m in seen}


CLOSURE = build_closure()
report(len(CLOSURE) == 954, "root-module import closure = 954 (REPRODUCIBILITY section 3)",
       f"{len(CLOSURE)} modules")

def code_lines(path):
    """Yield (lineno, text) for lines outside comments (block and line)."""
    depth = 0
    for i, line in enumerate(path.read_text(encoding="utf-8", errors="ignore").splitlines(), 1):
        opens, closes = line.count("/-"), line.count("-/")
        was_in = depth > 0
        depth = max(0, depth + opens - closes)
        if was_in or opens:
            continue
        code = line.split("--", 1)[0]
        if code.strip():
            yield i, code


for token, label in [("sorry", "sorry"), ("native_decide", "native_decide")]:
    inside, outside = [], []
    for p in lean_files:
        for i, line in code_lines(p):
            if f"`{token}`" in line:
                continue
            if re.search(rf"(?<![A-Za-z_`]){token}(?![A-Za-z_`])", line):
                (inside if p in CLOSURE else outside).append(f"{p.relative_to(ROOT)}:{i}")
    report(not inside, f"no {label} in the certified build closure",
           f"{len(inside)} hit(s): {inside[:3]}" if inside else "")
    if outside:
        # Outside the closure nothing is claimed -- but a public repository
        # containing these will be grepped by referees, so surface them.
        print(f"       note: {len(outside)} {label} occurrence(s) OUTSIDE the closure, "
              f"e.g. {outside[:2]} -- excluded from every claim, but visible to readers")

print(f"\n{CHECKS - len(FAILURES)}/{CHECKS} checks passed")
if FAILURES:
    print("FAILED:")
    for f in FAILURES:
        print("  -", f)
    sys.exit(1)
