#!/usr/bin/env python3
"""Stage-5 step 3 — the per-class character-alignment emitter.

Produces `LeanDring/Basic/P5CharAlign.lean`: the untrusted alignment table
`alnPos` (for every q1 character position, the position of the matched q2
character) together with its inverse-on-orbit-labels `alnInv`, and ONE cheap
kernel `decide` per class certifying

  * `alnPos[r][j] < |repChars2[r]|`                      (in range)
  * `alnLab[r][j] := Q2.normLabel[r][alnPos[r][j]] < |repChars2[r]|`
  * `Q2.normIsRep[r][alnLab[r][j]]`                      (lands on an orbit rep)
  * `alnInv[r][alnLab[r][j]] = j`                        (injectivity witness)

for every q1 *orbit-representative* position `j` — exactly the data the row
equivalence σ = orbRepClass₂ ∘ ψ ∘ orbRepClass₁⁻¹ needs (ψ ⟨r,j⟩ = ⟨r,alnLab[r][j]⟩).

THE ALIGNMENT ITSELF is chosen by column-profile matching against the embedded,
kernel-certified stage-2 column data: for each class the multiset of profiles
`(sumPowers (fastCode D1 v))_columns` on the q1 side equals the q2 multiset, and
the emitter pairs equal profiles (preferring the identity wherever available).
The choice is a HINT: every cell it commits to is re-decided in kernel by the
stage-4/NEW-2 certificates.  Classes where the pairing is NOT the identity on
vectors (34 of them — the q1/q2 character SETS genuinely differ there) are
reported; their cells are the work item NEW-2 of results/p5_stage5_design.md.

Usage:  python3 python/p5_align_emit.py [--dry-run]
"""
from __future__ import annotations
import json, os, sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p5_stage5_common import Data, REPO, BASIC, sum_powers_fast_code

MANIFEST = os.path.join(REPO, "python", "p5_certificate", "stage2_manifest.json")
OUT = os.path.join(BASIC, "P5CharAlign.lean")


def build_alignment(D, man):
    """Per class: dict q1-vector -> q2-vector, chosen by column-profile matching."""
    by_rK = defaultdict(list)
    for e in man:
        by_rK[e["rK"]].append(e)
    alpha = {}
    for rK in range(148):
        ents = sorted(by_rK[rK], key=lambda e: (e["rH"], e["p"]))
        c1 = [tuple(v) for v in D.repChars[rK]]
        c2 = [tuple(v) for v in D.repChars2[rK]]
        g1, g2 = defaultdict(list), defaultdict(list)
        for v in c1:
            g1[tuple(sum_powers_fast_code(e["D1"], v) for e in ents)].append(v)
        for v in c2:
            g2[tuple(sum_powers_fast_code(e["D2"], v) for e in ents)].append(v)
        assert set(g1) == set(g2), f"class {rK}: profile sets differ"
        assert all(len(g1[k]) == len(g2[k]) for k in g1), f"class {rK}: profile multiplicities differ"
        a = {}
        for k in g1:
            l1, l2 = sorted(g1[k]), sorted(g2[k])
            common = [v for v in l1 if v in l2]
            for v in common:
                a[v] = v
            r1 = [v for v in l1 if v not in common]
            r2 = [v for v in l2 if v not in common]
            for x, y in zip(r1, r2):
                a[x] = y
        assert sorted(a.values()) == sorted(c2), f"class {rK}: alignment not bijective"
        alpha[rK] = a
    return alpha


def build_tables(D, alpha):
    """alnPos (full rows) and alnInv (indexed by q2 orbit-label position)."""
    alnPos, alnInv, moved = [], [], {}
    for r in range(148):
        c1 = [tuple(v) for v in D.repChars[r]]
        idx2 = {tuple(v): i for i, v in enumerate(D.repChars2[r])}
        row = [idx2[alpha[r][v]] for v in c1]
        alnPos.append(row)
        n2 = len(D.repChars2[r])
        inv = [0] * n2
        reps1 = [j for j, b in enumerate(D.normIsRep[r]) if b]
        seen = {}
        for j in reps1:
            lab = D.normLabel2[r][row[j]]
            assert lab < n2 and D.normIsRep2[r][lab], (r, j, lab)
            assert lab not in seen, f"class {r}: label {lab} hit twice ({seen.get(lab)}, {j})"
            seen[lab] = j
            inv[lab] = j
        assert len(seen) == len(reps1) == len([p for p, b in enumerate(D.normIsRep2[r]) if b])
        alnInv.append(inv)
        mv = [j for j in reps1 if alpha[r][c1[j]] != c1[j]]
        if mv:
            moved[r] = mv
    return alnPos, alnInv, moved


HEADER = '''/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Basic.P5PairClassInj
import LeanDring.Basic.P5PairClassInj2

/-!
# Stage 5 step 3 — the per-class character alignment (row-σ data)

The q1 and q2 character lists of a subgroup class are **not** positionally
matched, and in 34 of the 148 classes they are not even equal as sets: the row
equivalence σ has to be told, per class, which q2 character each q1 character is
matched with.  `alnPos` is that (untrusted) table; `alnCheck` is the single cheap
kernel `decide` per class certifying everything σ's construction needs:

* the entry is a legal q2 character position;
* its q2 normalizer-orbit label `Q2.normLabel` is again a legal position and is
  an orbit representative (`Q2.normIsRep`) — so `ψ ⟨r,j⟩ = ⟨r, alnLab r j⟩` maps
  q1 orbit representatives to q2 orbit representatives;
* `alnInv` inverts `alnLab` on the q1 orbit representatives — the injectivity of
  `ψ`, from which bijectivity follows by the two proven counts (`2724` both
  sides).

The *semantic* content of the alignment (that the paired characters really carry
equal species values) is not in this file: it is discharged cell-by-cell by the
stage-2/3/4 column certificates, at the pair `(repChars[r][j], repChars2[r][alnPos[r][j]])`.

Emitted by `python/p5_align_emit.py`.
-/

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

'''

FOOTER = '''
/-- The q2 orbit-label of the aligned partner of the q1 character position `j`
of class `r` — the position half of `ψ`. -/
def alnLab (r j : Nat) : Nat :=
  (Q2.normLabel.getD r []).getD ((alnPos.getD r []).getD j 0) 0

/-- The per-class alignment certificate (checked at every q1 orbit-representative
position): in range, lands on a q2 orbit representative, and is inverted by
`alnInv`. -/
def alnCheck (r : Nat) : Bool :=
  (List.range (repChars.getD r []).length).all (fun j =>
    !((normIsRep.getD r []).getD j false) ||
      (Nat.blt ((alnPos.getD r []).getD j 0) (Q2.repChars2.getD r []).length &&
       Nat.blt (alnLab r j) (Q2.repChars2.getD r []).length &&
       (Q2.normIsRep.getD r []).getD (alnLab r j) false &&
       Nat.beq ((alnInv.getD r []).getD (alnLab r j) 0) j))

'''


def emit(alnPos, alnInv):
    def fmt(name, rows):
        body = ",\n ".join("[" + ", ".join(str(x) for x in r) + "]" for r in rows)
        return f"/-- Untrusted alignment data (see the module docstring). -/\ndef {name} : List (List Nat) :=\n[{body}]\n"

    chunks = [(0, 37), (37, 74), (74, 111), (111, 148)]
    thms = []
    for k, (a, b) in enumerate(chunks):
        thms.append(
            f"theorem alnChunk{k} : (List.range' {a} {b - a}).all alnCheck = true := by decide")
    thms.append("""
theorem alnCheck_all : (List.range 148).all alnCheck = true := by
  have e : List.range 148 =
      List.range' 0 37 ++ List.range' 37 37 ++ List.range' 74 37 ++ List.range' 111 37 := by decide
  rw [e]
  simp only [List.all_append, alnChunk0, alnChunk1, alnChunk2, alnChunk3, Bool.and_self]

theorem alnCheck_at (r : Fin 148) : alnCheck r.val = true :=
  (List.all_eq_true.mp alnCheck_all) r.val (List.mem_range.mpr r.isLt)

/-- Extraction at a q1 orbit-representative position. -/
theorem alnCheck_rep (r : Fin 148) {j : Nat} (hj : j < (repChars.getD r.val []).length)
    (hrep : (normIsRep.getD r.val []).getD j false = true) :
    ((alnPos.getD r.val []).getD j 0 < (Q2.repChars2.getD r.val []).length) ∧
      (alnLab r.val j < (Q2.repChars2.getD r.val []).length) ∧
      ((Q2.normIsRep.getD r.val []).getD (alnLab r.val j) false = true) ∧
      ((alnInv.getD r.val []).getD (alnLab r.val j) 0 = j) := by
  have h := (List.all_eq_true.mp (alnCheck_at r)) j (List.mem_range.mpr hj)
  simp only [hrep, Bool.not_true, Bool.false_or, Bool.and_eq_true, Nat.blt_eq,
    Nat.beq_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
""")
    txt = HEADER + fmt("alnPos", alnPos) + "\n" + fmt("alnInv", alnInv) + FOOTER \
        + "\n".join(thms) + "\n\nend LeanDring.P5Presentation\n"
    return txt


def main():
    dry = "--dry-run" in sys.argv
    D = Data()
    man = json.load(open(MANIFEST, encoding="utf-8"))
    alpha = build_alignment(D, man)
    alnPos, alnInv, moved = build_tables(D, alpha)
    nid = sorted(moved)
    print("classes with a non-identity orbit-rep alignment (NEW-2 work): %d" % len(nid))
    print("  ", nid)
    print("moved orbit-rep cells per class:", {r: len(v) for r, v in sorted(moved.items())})
    tot = 0
    by_rK = defaultdict(int)
    for e in man:
        by_rK[e["rK"]] += 1
    for r, mv in moved.items():
        tot += len(mv) * by_rK[r]
    print("cells needing NEW-2 alpha-paired decides:", tot)
    if dry:
        return
    open(OUT, "w", encoding="utf-8").write(emit(alnPos, alnInv))
    print("wrote", OUT)
    json.dump({"alnPos": alnPos, "alnInv": alnInv,
               "moved": {str(k): v for k, v in moved.items()}},
              open(os.path.join(REPO, "python", "p5_align_data.json"), "w"))


if __name__ == "__main__":
    main()
