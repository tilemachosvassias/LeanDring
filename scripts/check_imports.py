#!/usr/bin/env python3
"""Import-direction (layering) checker for LeanDring.

Layering rule:
  - LeanDring/Theory/**        may import only Mathlib and LeanDring.Theory.*
  - LeanDring/Even/**          may import Mathlib, LeanDring.Theory.*, LeanDring.Even.*
  - LeanDring/P4/**            may import Mathlib, LeanDring.Theory.*, LeanDring.P4.*
  - LeanDring/P5/Certificate/** may import Mathlib, LeanDring.Theory.*,
                                LeanDring.P5.Certificate.*
  - LeanDring/P5/Data/**        may import Mathlib, LeanDring.Theory.*,
                                LeanDring.P5.Certificate.*, LeanDring.P5.Data.*
  - Top-level aggregators (LeanDring.lean, LeanDring/Theory.lean, LeanDring/P4.lean,
    LeanDring/P5.lean, LeanDring/MainResults.lean, LeanDring/CertificateAnchors.lean,
    LeanDring/AxiomAudit.lean, and the per-family LeanDring/P5/Data/<Family>.lean index
    files) are exempt: they exist precisely to pull layers together.

Nothing imports "upward": Theory must never import P4 or P5; P4 must never
import P5; P5/Certificate must never import P4 or P5/Data.
"""
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LD = os.path.join(REPO, "LeanDring")

EXEMPT_FILES = {
    os.path.join(REPO, "LeanDring.lean"),
    os.path.join(LD, "Theory.lean"),
    os.path.join(LD, "P4.lean"),
    os.path.join(LD, "P5.lean"),
    os.path.join(LD, "MainResults.lean"),
    os.path.join(LD, "CertificateAnchors.lean"),
    os.path.join(LD, "AxiomAudit.lean"),
}


def layer_of(relpath):
    """Return a layer tag for a LeanDring-relative path (module, dot form)."""
    parts = relpath.split(".")
    if parts[0] != "LeanDring":
        return None
    if len(parts) < 2:
        return None
    if parts[1] == "Theory":
        return "Theory"
    if parts[1] == "Even":
        return "Even"
    if parts[1] == "P4":
        return "P4"
    if parts[1] == "P5":
        if len(parts) >= 3 and parts[2] == "Certificate":
            return "P5.Certificate"
        if len(parts) >= 3 and parts[2] == "Data":
            return "P5.Data"
        return "P5.other"
    return "other"


ALLOWED = {
    "Theory": {"Theory"},
    "Even": {"Theory", "Even"},
    "P4": {"Theory", "P4"},
    "P5.Certificate": {"Theory", "P5.Certificate"},
    "P5.Data": {"Theory", "P5.Certificate", "P5.Data"},
}


def main():
    violations = []
    checked = 0
    for root, dirs, files in os.walk(LD):
        for fn in sorted(files):
            if not fn.endswith(".lean"):
                continue
            path = os.path.join(root, fn)
            if path in EXEMPT_FILES:
                continue
            # per-family Data index files, e.g. LeanDring/P5/Data/ColRestCheap.lean
            if os.path.dirname(path) == os.path.join(LD, "P5", "Data") and fn != "":
                continue

            relmod = os.path.relpath(path, REPO)[:-5].replace(os.sep, ".")
            file_layer = layer_of(relmod)
            if file_layer not in ALLOWED:
                continue
            checked += 1

            with open(path) as f:
                for lineno, line in enumerate(f, start=1):
                    m = re.match(r"^import (LeanDring\.\S+)$", line.strip())
                    if not m:
                        continue
                    target_mod = m.group(1)
                    target_layer = layer_of(target_mod)
                    if target_layer is None:
                        continue
                    if target_layer == "P5.other":
                        # aggregator-style import of LeanDring.P5 itself; skip
                        continue
                    if target_layer not in ALLOWED[file_layer]:
                        violations.append(
                            (relmod, file_layer, target_mod, target_layer, lineno)
                        )

    print(f"Checked {checked} files.")

    # Baseline: the accepted, documented cross-references (assembly files
    # consuming named P5/Data cells — see ARCHITECTURE.md "Import-direction
    # rule"). A violation counts as NEW only if its (module, import) pair is
    # not in the baseline; a stale baseline entry is reported so the file
    # never rots silently.
    baseline_path = os.path.join(REPO, "scripts", "import_exceptions.txt")
    baseline = set()
    if os.path.exists(baseline_path):
        with open(baseline_path) as f:
            for ln in f:
                ln = ln.strip()
                if ln and not ln.startswith("#"):
                    baseline.add(tuple(ln.split(" -> ")))

    current = {(relmod, target_mod) for relmod, _, target_mod, _, _ in violations}
    new = sorted(current - baseline)
    stale = sorted(baseline - current)

    for relmod, file_layer, target_mod, target_layer, lineno in violations:
        tag = "NEW " if (relmod, target_mod) in set(new) else ""
        print(
            f"  {tag}{relmod} [{file_layer}]:{lineno} imports {target_mod} [{target_layer}]"
        )
    print(f"{len(violations)} violation(s): {len(current) - len(new)} baselined, "
          f"{len(new)} new; {len(stale)} stale baseline entr(y/ies).")
    for a, b in stale:
        print(f"  stale baseline: {a} -> {b}")
    if new:
        print("FAIL: new layering violation(s) not in scripts/import_exceptions.txt")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
