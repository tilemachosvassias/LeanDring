#!/usr/bin/env python3
"""Stage-5 assembly emitter — leaves, per-pair theorems, per-rH masters, hmatch.

Emits, on top of the certificate layers:

  P5MatchCore.lean      column/row element wrappers, the three off-support
                        dispatchers, the two fast-code extractors, and the
                        per-class / per-column-class index decides
  P5MatchLeaf*.lean     one theorem per on-support (rK,rH,p) column: the twin
                        species values agree on every orbit-representative row
  P5MatchPair*.lean     one theorem per on-support (rK,rH) pair, quantified over
                        the column position p
  P5MatchMaster*.lean   one theorem per column class rH (148-way row dispatch)
  P5MatchAll.lean       the global master (148-way column dispatch)
  P5Assembly.lean       colsG1, hmatch and `dring_equiv_coordinate12`

Usage:  python3 python/p5_match_emit.py [--dry-run]
"""
from __future__ import annotations
import glob, json, os, re, sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p5_stage5_common import Data, REPO, BASIC

MANIFEST = os.path.join(REPO, "python", "p5_certificate", "stage2_manifest.json")
GAPMAN = os.path.join(REPO, "results", "p5_gapfill_manifest.json")
ALIGN = os.path.join(REPO, "python", "p5_align_data.json")
LEAF_CHUNK = 250
PAIR_CHUNK = 120
MASTER_CHUNK = 8

LIC = '''/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
'''
OPTS = '''
-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

'''


def scan(pattern, regex):
    out = {}
    for path in sorted(glob.glob(os.path.join(BASIC, pattern))):
        mod = "LeanDring.Basic." + os.path.basename(path)[:-5]
        for m in re.finditer(regex, open(path, encoding="utf-8").read()):
            out[m.group(0) if m.re.groups == 0 else m.groups()] = mod
    return out


def main():
    dry = "--dry-run" in sys.argv
    D = Data()
    man = json.load(open(MANIFEST, encoding="utf-8"))
    gap = json.load(open(GAPMAN, encoding="utf-8"))
    aln = json.load(open(ALIGN, encoding="utf-8"))
    moved = {int(k) for k in aln["moved"]}
    supp = {tuple(x) for x in json.load(open(os.path.join(REPO, "results",
                                                         "p5_support_pairs.json")))}

    # ---- certificate inventories -------------------------------------------
    colobj = {}                                    # (rK,rH,p) -> (name, mod, is_div)
    for path in sorted(glob.glob(os.path.join(BASIC, "P5ColData*.lean"))):
        mod = "LeanDring.Basic." + os.path.basename(path)[:-5]
        for m in re.finditer(r"def (colCert(Div)?_(\d+)_(\d+)_(\d+))\s*:",
                             open(path, encoding="utf-8").read()):
            colobj[(int(m.group(3)), int(m.group(4)), int(m.group(5)))] = \
                (m.group(1), mod, m.group(2) is not None)
    divthm, tauthm, alnthm, fixmod, entrymod = {}, {}, {}, {}, {}
    for path in sorted(glob.glob(os.path.join(BASIC, "P5SpeciesDiv*.lean"))):
        mod = "LeanDring.Basic." + os.path.basename(path)[:-5]
        for m in re.finditer(r"theorem (colCertDiv_(\d+)_(\d+)_(\d+))_match",
                             open(path, encoding="utf-8").read()):
            divthm[(int(m.group(2)), int(m.group(3)), int(m.group(4)))] = (m.group(1) + "_match", mod)
    for path in sorted(glob.glob(os.path.join(BASIC, "P5SpeciesTau*.lean"))):
        mod = "LeanDring.Basic." + os.path.basename(path)[:-5]
        for m in re.finditer(r"theorem (colCertDiv_(\d+)_(\d+)_(\d+))_tau_match",
                             open(path, encoding="utf-8").read()):
            tauthm[(int(m.group(2)), int(m.group(3)), int(m.group(4)))] = (m.group(1) + "_tau_match", mod)
    for path in sorted(glob.glob(os.path.join(BASIC, "P5SpeciesAlign*.lean"))):
        mod = "LeanDring.Basic." + os.path.basename(path)[:-5]
        for m in re.finditer(r"theorem alnAll_(\d+)_(\d+)_(\d+)",
                             open(path, encoding="utf-8").read()):
            alnthm[(int(m.group(1)), int(m.group(2)), int(m.group(3)))] = mod
    for path in sorted(glob.glob(os.path.join(BASIC, "P5FixZero*.lean"))):
        mod = "LeanDring.Basic." + os.path.basename(path)[:-5]
        for m in re.finditer(r"theorem fz(\d)_(\d+)_(\d+)",
                             open(path, encoding="utf-8").read()):
            fixmod[(int(m.group(1)), int(m.group(2)), int(m.group(3)))] = mod
    for path in sorted(glob.glob(os.path.join(BASIC, "P5EntryData*.lean"))):
        mod = "LeanDring.Basic." + os.path.basename(path)[:-5]
        txt = open(path, encoding="utf-8").read()
        for m in re.finditer(r"theorem cell(\d+)_(\d+) ", txt):
            entrymod[(int(m.group(1)), int(m.group(2)))] = mod

    # ---- the on-support triples --------------------------------------------
    trip = {}                                       # (rK,rH,p) -> ntrav
    for e in man:
        trip[(e["rK"], e["rH"], e["p"])] = e["ntrav"]
    for e in gap:
        trip[(e["rK"], e["rH"], e["p"])] = e["m"]
    triples = sorted(k for k in trip if k[1] != 0)   # rH = 0 is abstract
    pairs = sorted({(rK, rH) for (rK, rH, _p) in triples})
    missing = [k for k in triples if k not in colobj]
    assert not missing, ("no column certificate", missing[:5])
    for (rK, rH) in pairs:
        assert (rK, rH) in entrymod, ("no cell theorem", rK, rH)
    print("on-support triples (rH != 0): %d over %d pairs" % (len(triples), len(pairs)))

    # ---- P5MatchCore --------------------------------------------------------
    core = [LIC, ("import LeanDring.Basic.P5Sigma\n"
                  "import LeanDring.Basic.P5Stage5Core\n"
                  "import LeanDring.Basic.P5ColCert\n"
                  "import LeanDring.Basic.P5EntrySupport\n"
                  "import LeanDring.Basic.P5SpeciesComplete\n"
                  "import LeanDring.Basic.P5SpeciesComplete2\n"),
            '''
/-!
# Stage-5 assembly core

Wrappers for the two column elements and the two row basis elements the master
cell theorem is stated with, the three off-support dispatchers (order bound,
empty fixed-point set, `⊥` column), the two fast-code extractors (`P5SpeciesDiv`
/ `P5SpeciesTau` orientation), and the index decides: `alnId_<rK>` (the alignment
is the identity on vectors — the 114 classes whose q1/q2 character sets agree)
and `repPos_<rH>` (the certified orbit-representative column positions).
Auto-emitted by `python/p5_match_emit.py`.
-/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet
''', OPTS, '''
/-- The `q=1` column element at transversal position `p` of class `r`. -/
def colE1 (r : Fin 148) (p : Nat) (hp : p < (transData.getD r.val []).length) : ↥(reps r) :=
  ⟨(transData.getD r.val []).getD p zc, transElt_mem r hp⟩

/-- The `q=2` column element at transversal position `p` of class `r`. -/
def colE2 (r : Fin 148) (p : Nat) (hp : p < (Q2.transData.getD r.val []).length) : ↥(Q2.reps r) :=
  ⟨(Q2.transData.getD r.val []).getD p zc, Q2.transElt_mem r hp⟩

/-- The twins' transversals have equal length (both `= charCounts r`). -/
theorem transLenTr (r : Fin 148) (p : Nat) (hp : p < (Q2.transData.getD r.val []).length) :
    p < (transData.getD r.val []).length := by
  rw [transCard r]; rw [Q2.transCard r] at hp; exact hp

/-- The `q=1` row basis element at character position `j` of class `rK`. -/
noncomputable def rowE1 (rK : Fin 148) (j : Nat)
    (hj : j < (repChars.getD rK.val []).length) : DRing (Coordinate 1) :=
  basisElt (reps rK) (charOfVec rK ((repChars.getD rK.val []).getD j [])
    (validAt rK (listedAt rK hj)))

/-- The `q=2` row basis element at the ALIGNED character position. -/
noncomputable def rowE2 (rK : Fin 148) (j : Nat)
    (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) : DRing (Coordinate 2) :=
  basisElt (Q2.reps rK) (Q2.charOfVec2 rK
    ((Q2.repChars2.getD rK.val []).getD ((alnPos.getD rK.val []).getD j 0) [])
    (Q2.validAt rK (Q2.listedAt rK (alnCheck_rep rK hj hq).1)))

/-! ## The three off-support dispatchers -/

theorem match_zero_len (rK rH : Fin 148) (p : Nat)
    (hp : p < (Q2.transData.getD rH.val []).length) (j : Nat)
    (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true)
    (h1 : (basisAt rK).length < (basisAt rH).length)
    (h2 : (Q2.basisAt2 rK).length < (Q2.basisAt2 rH).length) :
    species (Q2.reps rH) (colE2 rH p hp) (rowE2 rK j hj hq)
      = species (reps rH) (colE1 rH p (transLenTr rH p hp)) (rowE1 rK j hj) := by
  rw [rowE2, rowE1, Q2.species_zero_of_len_lt rK rH _ _ h2, species_zero_of_len_lt rK rH _ _ h1]

theorem match_zero_fix (rK rH : Fin 148) (p : Nat)
    (hp : p < (Q2.transData.getD rH.val []).length) (j : Nat)
    (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true)
    (h1 : Fintype.card (fixedPoints (reps rH) (Coordinate 1 ⧸ reps rK)) = 0)
    (h2 : Fintype.card (fixedPoints (Q2.reps rH) (Coordinate 2 ⧸ Q2.reps rK)) = 0) :
    species (Q2.reps rH) (colE2 rH p hp) (rowE2 rK j hj hq)
      = species (reps rH) (colE1 rH p (transLenTr rH p hp)) (rowE1 rK j hj) := by
  rw [rowE2, rowE1, Q2.species_zero_of_fixCard_zero rK rH _ _ h2,
    species_zero_of_fixCard_zero rK rH _ _ h1]

theorem match_bot (rK : Fin 148) (p : Nat)
    (hp : p < (Q2.transData.getD rK0.val []).length) (j : Nat)
    (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps rK0) (colE2 rK0 p hp) (rowE2 rK j hj hq)
      = species (reps rK0) (colE1 rK0 p (transLenTr rK0 p hp)) (rowE1 rK j hj) := by
  rw [rowE2, rowE1, Q2.species_bot_column rK _ _, species_bot_column rK _ _,
    basisAt_length_eq rK]

/-! ## Fast-code extraction from the emitted all-decides -/

theorem fastcode_of_div {m : ℕ} (rK : Fin 148) (D1 D2 : List (List ℕ))
    (e : List (ZMod 25)) (hmem : e ∈ Q2.charsAt2 rK)
    (hall : ((Q2.charsAt2 rK).map (fun e => decide
      (P5CyclotomicCode.sumPowers (fastCode (colFn D2 (m := m)) (List.map ZMod.val e))
        = P5CyclotomicCode.sumPowers (fastCode (colFn D1 (m := m))
            (List.map ZMod.val e))))).all id = true) :
    P5CyclotomicCode.sumPowers (fastCode (colFn D1 (m := m)) (List.map ZMod.val e))
      = P5CyclotomicCode.sumPowers (fastCode (colFn D2 (m := m)) (List.map ZMod.val e)) := by
  have h := (List.all_eq_true.mp hall) _ (List.mem_map_of_mem hmem)
  simp only [id_eq, decide_eq_true_eq] at h
  exact h.symm

theorem fastcode_of_tau {m : ℕ} (rK : Fin 148) (D1 D2 : List (List ℕ))
    (e : List (ZMod 25)) (hmem : e ∈ Q2.charsAt2 rK)
    (hall : ((Q2.charsAt2 rK).map (fun e => decide
      (P5CyclotomicCode.sumPowers (fastCode (colFn D1 (m := m)) (List.map ZMod.val e))
        = P5CyclotomicCode.sumPowers (fastCode (colFn D2 (m := m))
            (List.map ZMod.val e))))).all id = true) :
    P5CyclotomicCode.sumPowers (fastCode (colFn D1 (m := m)) (List.map ZMod.val e))
      = P5CyclotomicCode.sumPowers (fastCode (colFn D2 (m := m)) (List.map ZMod.val e)) := by
  have h := (List.all_eq_true.mp hall) _ (List.mem_map_of_mem hmem)
  simp only [id_eq, decide_eq_true_eq] at h
  exact h

''']
    for rK in range(148):
        if rK in moved:
            continue
        n = len(D.repChars[rK])
        core.append(f'''theorem alnId_{rK} : ∀ j, j < {n} →
    (Q2.repChars2.getD {rK} []).getD ((alnPos.getD {rK} []).getD j 0) []
      = (repChars.getD {rK} []).getD j [] := by decide

''')
    for rH in range(148):
        cols = D.cols(rH)
        lst = "[" + ", ".join(str(x) for x in cols) + "]"
        core.append(f'''theorem repPos_{rH} : ∀ p, p < (Q2.transData.getD {rH} []).length →
    (Q2.cosetIsRep.getD {rH} []).getD p false = true → p ∈ ({lst} : List Nat) := by decide

''')
    core.append("end LeanDring.P5Presentation\n")

    # ---- leaves -------------------------------------------------------------
    leaves = []
    for (rK, rH, p) in triples:
        name, mod, is_div = colobj[(rK, rH, p)]
        m = trip[(rK, rH, p)]
        mods = {mod, entrymod[(rK, rH)], "LeanDring.Basic.P5MatchCore"}
        head = f'''theorem leaf_{rK}_{rH}_{p} (hp : {p} < (Q2.transData.getD {rH} []).length)
    (j : Nat) (hj : j < (repChars.getD {rK} []).length)
    (hq : (normIsRep.getD {rK} []).getD j false = true) :
    species (Q2.reps (⟨{rH}, by decide⟩ : Fin 148)) (colE2 ⟨{rH}, by decide⟩ {p} hp)
        (rowE2 (⟨{rK}, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨{rH}, by decide⟩ : Fin 148))
        (colE1 ⟨{rH}, by decide⟩ {p} (transLenTr ⟨{rH}, by decide⟩ {p} hp))
        (rowE1 (⟨{rK}, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
'''
        common = f'''  refine (species_eq_of_data_eq (⟨{rK}, by decide⟩ : Fin 148) ⟨{rH}, by decide⟩ _
      (validAt ⟨{rK}, by decide⟩ (listedAt ⟨{rK}, by decide⟩ hj))
      (colE1 ⟨{rH}, by decide⟩ {p} (transLenTr ⟨{rH}, by decide⟩ {p} hp)) T{rK}_{rH}
      hfix{rK}_{rH} hinj{rK}_{rH} hcardT{rK}_{rH}
      (fun i => conj_mem_of_fixedPoints _ _ (T{rK}_{rH} i) (hfix{rK}_{rH} i) _)
      ⟨{rK}, by decide⟩ ⟨{rH}, by decide⟩ _
      (Q2.validAt ⟨{rK}, by decide⟩ (Q2.listedAt ⟨{rK}, by decide⟩
        (alnCheck_rep ⟨{rK}, by decide⟩ hj hq).1))
      (colE2 ⟨{rH}, by decide⟩ {p} hp) Q2.T{rK}_{rH}_2 Q2.hfix{rK}_{rH}_2 Q2.hinj{rK}_{rH}_2
      Q2.hcardT{rK}_{rH}_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T{rK}_{rH}_2 i) (Q2.hfix{rK}_{rH}_2 i) _)
      {name}.hD ?_).symm
  rw [alnId_{rK} j hj]
'''
        fastc_head = f'''  refine (species_eq_of_fastcode_eq (⟨{rK}, by decide⟩ : Fin 148) ⟨{rH}, by decide⟩ _
      (validAt ⟨{rK}, by decide⟩ (listedAt ⟨{rK}, by decide⟩ hj))
      (colE1 ⟨{rH}, by decide⟩ {p} (transLenTr ⟨{rH}, by decide⟩ {p} hp)) T{rK}_{rH}
      hfix{rK}_{rH} hinj{rK}_{rH} hcardT{rK}_{rH}
      (fun i => conj_mem_of_fixedPoints _ _ (T{rK}_{rH} i) (hfix{rK}_{rH} i) _)
      ⟨{rK}, by decide⟩ ⟨{rH}, by decide⟩ _
      (Q2.validAt ⟨{rK}, by decide⟩ (Q2.listedAt ⟨{rK}, by decide⟩
        (alnCheck_rep ⟨{rK}, by decide⟩ hj hq).1))
      (colE2 ⟨{rH}, by decide⟩ {p} hp) Q2.T{rK}_{rH}_2 Q2.hfix{rK}_{rH}_2 Q2.hinj{rK}_{rH}_2
      Q2.hcardT{rK}_{rH}_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T{rK}_{rH}_2 i) (Q2.hfix{rK}_{rH}_2 i) _)
      ?_).symm
  rw [show colData1 (⟨{rK}, by decide⟩ : Fin 148)
        ((colE1 ⟨{rH}, by decide⟩ {p} (transLenTr ⟨{rH}, by decide⟩ {p} hp) : ↥(reps ⟨{rH}, by decide⟩)) : Coordinate 1)
        T{rK}_{rH} = colFn {name}.{"D1" if is_div else "D"} (m := {m}) from {name}.bind1,
    show colData2 (⟨{rK}, by decide⟩ : Fin 148)
        ((colE2 ⟨{rH}, by decide⟩ {p} hp : ↥(Q2.reps ⟨{rH}, by decide⟩)) : Coordinate 2)
        Q2.T{rK}_{rH}_2 = colFn {name}.{"D2" if is_div else "D"} (m := {m}) from {name}.bind2]
'''
        if rK in moved:
            amod = alnthm[(rK, rH, p)]
            mods.add(amod)
            body = fastc_head + f"  exact alnAll_{rK}_{rH}_{p} j hj hq\n"
        elif not is_div:
            body = common + "\n"
        else:
            if (rK, rH, p) in divthm:
                tname, tmod = divthm[(rK, rH, p)]
                helper = "fastcode_of_div"
            else:
                tname, tmod = tauthm[(rK, rH, p)]
                helper = "fastcode_of_tau"
            mods.add(tmod)
            body = fastc_head + f'''  rw [alnId_{rK} j hj]
  exact {helper} ⟨{rK}, by decide⟩ _ _ _
    ((alnId_{rK} j hj) ▸ Q2.listedAt (⟨{rK}, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨{rK}, by decide⟩ : Fin 148) hj hq).1) {tname}

'''
        leaves.append((rK, rH, p, head + body, mods))

    # ---- pair theorems ------------------------------------------------------
    pairthm = []
    for (rK, rH) in pairs:
        ps = sorted(p for (a, b, p) in triples if (a, b) == (rK, rH))
        n = len(D.transData[rH])
        cols = D.cols(rH)
        assert ps == cols, (rK, rH, ps, cols)
        body = [f'''theorem pair_{rK}_{rH} (p : Nat) (hp : p < (Q2.transData.getD {rH} []).length)
    (hrep : (Q2.cosetIsRep.getD {rH} []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD {rK} []).length)
    (hq : (normIsRep.getD {rK} []).getD j false = true) :
    species (Q2.reps (⟨{rH}, by decide⟩ : Fin 148)) (colE2 ⟨{rH}, by decide⟩ p hp)
        (rowE2 (⟨{rK}, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨{rH}, by decide⟩ : Fin 148))
        (colE1 ⟨{rH}, by decide⟩ p (transLenTr ⟨{rH}, by decide⟩ p hp))
        (rowE1 (⟨{rK}, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_{rH} p hp hrep
''']
        for p in ps:
            body.append(f"  rcases List.mem_cons.mp hm with rfl | hm\n")
            body.append(f"  · exact leaf_{rK}_{rH}_{p} hp j hj hq\n")
        body.append("  simp at hm\n\n")
        pairthm.append((rK, rH, "".join(body),
                        {f"leaf:{rK}_{rH}_{p}" for p in ps}))

    # ---- masters ------------------------------------------------------------
    masters = []
    for rH in range(148):
        if rH == 0:
            masters.append((0, f'''theorem master_0 (p : Nat) (hp : p < (Q2.transData.getD 0 []).length)
    (_hrep : (Q2.cosetIsRep.getD 0 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨0, by decide⟩ : Fin 148)) (colE2 ⟨0, by decide⟩ p hp) (rowE2 rK j hj hq)
      = species (reps (⟨0, by decide⟩ : Fin 148))
        (colE1 ⟨0, by decide⟩ p (transLenTr ⟨0, by decide⟩ p hp)) (rowE1 rK j hj) :=
  match_bot rK p hp j hj hq

''', set()))
            continue
        arms, mods = [], set()
        for rK in range(148):
            if (rK, rH) in supp:
                arms.append(f"  · exact pair_{rK}_{rH} p hp hrep j hj hq\n")
                mods.add(f"pair:{rK}_{rH}")
            elif len(D.repBases[rK]) < len(D.repBases[rH]):
                arms.append(f"  · exact match_zero_len ⟨{rK}, by decide⟩ ⟨{rH}, by decide⟩ p hp j hj hq"
                            " (by decide) (by decide)\n")
            else:
                arms.append(f"  · exact match_zero_fix ⟨{rK}, by decide⟩ ⟨{rH}, by decide⟩ p hp j hj hq"
                            f" fz1_{rK}_{rH} fz2_{rK}_{rH}\n")
                mods.add(fixmod[(1, rK, rH)]); mods.add(fixmod[(2, rK, rH)])
        head = f'''theorem master_{rH} (p : Nat) (hp : p < (Q2.transData.getD {rH} []).length)
    (hrep : (Q2.cosetIsRep.getD {rH} []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨{rH}, by decide⟩ : Fin 148)) (colE2 ⟨{rH}, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨{rH}, by decide⟩ : Fin 148))
        (colE1 ⟨{rH}, by decide⟩ p (transLenTr ⟨{rH}, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
'''
        masters.append((rH, head + "".join(arms) + "\n", mods))

    print("leaves %d, pairs %d, masters %d" % (len(leaves), len(pairthm), len(masters)))
    if dry:
        return

    # ---- write --------------------------------------------------------------
    open(os.path.join(BASIC, "P5MatchCore.lean"), "w", encoding="utf-8").write("".join(core))
    modules = ["LeanDring.Basic.P5MatchCore"]

    leafmod = {}
    for ci in range(0, len(leaves), LEAF_CHUNK):
        chunk = leaves[ci:ci + LEAF_CHUNK]
        name = "P5MatchLeaf%d" % (ci // LEAF_CHUNK)
        imps = sorted({m for it in chunk for m in it[4]})
        txt = [LIC] + ["import " + m + "\n" for m in imps] + [
            "\n/-! # Stage-5 leaves, chunk %d (auto-emitted).  -/\n\nnamespace LeanDring.P5Presentation\n\nopen MulAction Finset LeanDring.DRing LeanDring.MonGSet\n" % (ci // LEAF_CHUNK),
            OPTS] + [it[3] + "\n" for it in chunk] + ["end LeanDring.P5Presentation\n"]
        open(os.path.join(BASIC, name + ".lean"), "w", encoding="utf-8").write("".join(txt))
        for it in chunk:
            leafmod["leaf:%d_%d_%d" % (it[0], it[1], it[2])] = "LeanDring.Basic." + name
        modules.append("LeanDring.Basic." + name)

    pairmod = {}
    for ci in range(0, len(pairthm), PAIR_CHUNK):
        chunk = pairthm[ci:ci + PAIR_CHUNK]
        name = "P5MatchPair%d" % (ci // PAIR_CHUNK)
        imps = sorted({leafmod[k] for it in chunk for k in it[3]}
                      | {"LeanDring.Basic.P5MatchCore"})
        txt = [LIC] + ["import " + m + "\n" for m in imps] + [
            "\n/-! # Stage-5 per-pair theorems, chunk %d (auto-emitted).  -/\n\nnamespace LeanDring.P5Presentation\n\nopen MulAction Finset LeanDring.DRing LeanDring.MonGSet\n" % (ci // PAIR_CHUNK),
            OPTS] + [it[2] for it in chunk] + ["end LeanDring.P5Presentation\n"]
        open(os.path.join(BASIC, name + ".lean"), "w", encoding="utf-8").write("".join(txt))
        for it in chunk:
            pairmod["pair:%d_%d" % (it[0], it[1])] = "LeanDring.Basic." + name
        modules.append("LeanDring.Basic." + name)

    mastermod = {}
    for ci in range(0, len(masters), MASTER_CHUNK):
        chunk = masters[ci:ci + MASTER_CHUNK]
        name = "P5MatchMaster%d" % (ci // MASTER_CHUNK)
        imps = set(["LeanDring.Basic.P5MatchCore"])
        for it in chunk:
            for k in it[2]:
                imps.add(pairmod[k] if k.startswith("pair:") else k)
        txt = [LIC] + ["import " + m + "\n" for m in sorted(imps)] + [
            "\n/-! # Stage-5 per-column-class master theorems, chunk %d (auto-emitted).  -/\n\nnamespace LeanDring.P5Presentation\n\nopen MulAction Finset LeanDring.DRing LeanDring.MonGSet\n" % (ci // MASTER_CHUNK),
            OPTS] + [it[1] for it in chunk] + ["end LeanDring.P5Presentation\n"]
        open(os.path.join(BASIC, name + ".lean"), "w", encoding="utf-8").write("".join(txt))
        for it in chunk:
            mastermod[it[0]] = "LeanDring.Basic." + name
        modules.append("LeanDring.Basic." + name)

    # ---- the global master --------------------------------------------------
    arms = "".join("  · exact master_%d p hp hrep rK j hj hq\n" % rH for rH in range(148))
    txt = [LIC] + ["import " + m + "\n" for m in sorted(set(mastermod.values()))] + ['''
/-!
# Stage-5 — the master cell theorem

Every orbit-representative column of `Coordinate 2` agrees, on every pair-class
row, with the `Coordinate 1` column of the SAME index, the rows being matched by
the alignment `alnPos` (i.e. by `σ`).  148-way dispatch on the column class.
Auto-emitted by `python/p5_match_emit.py`.
-/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet
''', OPTS, '''theorem master (rH : Fin 148) (p : Nat) (hp : p < (Q2.transData.getD rH.val []).length)
    (hrep : (Q2.cosetIsRep.getD rH.val []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps rH) (colE2 rH p hp) (rowE2 rK j hj hq)
      = species (reps rH) (colE1 rH p (transLenTr rH p hp)) (rowE1 rK j hj) := by
  rcases rH with ⟨nH, hnH⟩; interval_cases nH
''', arms, "\nend LeanDring.P5Presentation\n"]
    open(os.path.join(BASIC, "P5MatchAll.lean"), "w", encoding="utf-8").write("".join(txt))
    modules.append("LeanDring.Basic.P5MatchAll")

    open(os.path.join(REPO, "results", "p5_match_manifest.txt"), "w").write(
        "\n".join(modules) + "\n")
    print("wrote %d modules (results/p5_match_manifest.txt)" % len(modules))


if __name__ == "__main__":
    main()
