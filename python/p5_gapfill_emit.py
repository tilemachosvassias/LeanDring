#!/usr/bin/env python3
"""Stage-5 NEW-1 — the 19 missing on-support cell pairs (rK in {13,14,15}).

The M5 cell layer and the stage-2 column manifest cover 1,500 / 1,488 of the
1,523 genuinely on-support (rK,rH) class pairs; the pilot A-block classes 13, 14
and 15 were never finished.  This emitter closes the gap:

  * `P5EntryDataGap.lean` — for each missing pair the `H`-fixed sub-transversal
    `T<rK>_<rH>` (a sub-list of the certified full transversal `R<rK>list`, twin
    shared), the three `decide`-backed hypotheses and the `cell` theorem, both
    twins;
  * `P5ColDataGap.lean` — the `ColCert` for each of the 135 missing columns.

Validated in Python before emission (`p5_stage5_common`): every one of the 135
columns is twin-COINCIDENT (`colData1 = colData2`), and all 3,375 cells satisfy
`sumPowers (fastCode D1 e) = sumPowers (fastCode D2 e)`.

Usage:  python3 python/p5_gapfill_emit.py [--dry-run]
"""
from __future__ import annotations
import glob, json, os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p5_stage5_common import (Data, REPO, BASIC, parse_flat_tuples, col_data,
                              sum_powers_fast_code)

GAP = [(13, 6), (13, 7), (13, 8), (13, 9), (13, 10),
       (14, 2), (14, 3), (14, 4), (14, 5), (14, 9), (14, 11), (14, 14),
       (15, 2), (15, 3), (15, 4), (15, 5), (15, 9), (15, 11), (15, 15)]

HDR_CELL = '''/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Basic.P5EntryDataA13
import LeanDring.Basic.P5EntryDataA14
import LeanDring.Basic.P5EntryDataA15

/-!
# M5 gap-fill (stage-5 NEW-1): the 19 on-support cells the A-block pilot missed

The true on-support set is 1,523 `(rK,rH)` class pairs (= the nonzero entries of
the certified table of marks, cross-checked against stage 0); the emitted M5 cell
layer covers all but 19 of them, all with `rK ∈ {13,14,15}`.  Each cell here is
built exactly like the emitted ones: the `H`-fixed sub-transversal is a sub-list
of the class's certified full transversal `R<rK>list`, re-verified by `decide`
through the `P5EntryTransA` adapters, in both twins (the transversal data
coincides, as everywhere else).

Emitted by `python/p5_gapfill_emit.py`.
-/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

'''

HDR_COL = '''/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Basic.P5ColCert
import LeanDring.Basic.P5EntryDataGap

/-!
# Stage-2 gap-fill (stage-5 NEW-1): the 135 missing column certificates

Per-column certified exponent-vector data for the 19 gap cell pairs of
`P5EntryDataGap`.  All 135 columns are twin-COINCIDENT, so each is a `ColCert`
with a single embedded list `D` and the two kernel bindings.

Emitted by `python/p5_gapfill_emit.py`.
-/

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

'''


def tup(t):
    return "(" + ",".join(str(x) for x in t) + ")"


def cell_block(rK, rH, T, q2):
    """The q=1 (q2=False) or q=2 (q2=True) block for one cell pair."""
    m = len(T)
    s2 = "_2" if q2 else ""
    if not q2:
        lst = (f"def T{rK}_{rH}list : List Coordinates := ["
               + ", ".join(tup(t) for t in T) + "]\n"
               + f"def T{rK}_{rH} : Fin {m} → Coordinate 1 := fun i => T{rK}_{rH}list.getD i.val (0,0,0,0,0)\n\n")
        return lst + f'''theorem hfix{rK}_{rH} : ∀ i, ((T{rK}_{rH} i : Coordinate 1) : Coordinate 1 ⧸ reps rK{rK})
    ∈ fixedPoints (reps (⟨{rH}, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK{rK}) :=
  repsFix_of_siftB rK{rK} ⟨{rH}, by decide⟩ T{rK}_{rH} (by decide)

theorem hinj{rK}_{rH} : Function.Injective
    (fun i => ((T{rK}_{rH} i : Coordinate 1) : Coordinate 1 ⧸ reps rK{rK})) :=
  repsInj_of_reduceAux rK{rK} T{rK}_{rH} (by decide)

theorem hcardT{rK}_{rH} : Fintype.card (Fin {m})
    = Fintype.card (fixedPoints (reps (⟨{rH}, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK{rK})) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK{rK} ⟨{rH}, by decide⟩ R{rK} hpxR{rK} hcardq{rK} (by decide)).symm

/-- **Cell ({rK}, {rH}).** -/
theorem cell{rK}_{rH} (e : List (ZMod 25)) (heK : charOK (basisAt rK{rK}) e = true)
    (h : ↥(reps (⟨{rH}, by decide⟩ : Fin 148))) :
    species (reps (⟨{rH}, by decide⟩ : Fin 148)) h (basisElt (reps rK{rK}) (charOfVec rK{rK} e heK))
      = ∑ i : Fin {m}, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK{rK} e (h : Coordinate 1) T{rK}_{rH} i :=
  species_entry_eq_sum rK{rK} ⟨{rH}, by decide⟩ e heK h T{rK}_{rH} hfix{rK}_{rH} hinj{rK}_{rH} hcardT{rK}_{rH}
    (fun i => conj_mem_of_fixedPoints (reps ⟨{rH}, by decide⟩) (reps rK{rK}) (T{rK}_{rH} i) (hfix{rK}_{rH} i) h)

'''
    return f'''def T{rK}_{rH}_2 : Fin {m} → Coordinate 2 := fun i => T{rK}_{rH}list.getD i.val (0,0,0,0,0)

theorem hfix{rK}_{rH}_2 : ∀ i, ((T{rK}_{rH}_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK{rK})
    ∈ fixedPoints (reps (⟨{rH}, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK{rK}) :=
  repsFix_of_siftB2 rK{rK} ⟨{rH}, by decide⟩ T{rK}_{rH}_2 (by decide)

theorem hinj{rK}_{rH}_2 : Function.Injective
    (fun i => ((T{rK}_{rH}_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK{rK})) :=
  repsInj_of_reduceAux2 rK{rK} T{rK}_{rH}_2 (by decide)

theorem hcardT{rK}_{rH}_2 : Fintype.card (Fin {m})
    = Fintype.card (fixedPoints (reps (⟨{rH}, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK{rK})) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK{rK} ⟨{rH}, by decide⟩ R{rK}_2 hpxR{rK}_2 hcardq{rK}_2 (by decide)).symm

/-- **Cell ({rK}, {rH}) twin (q=2).** -/
theorem cell{rK}_{rH}_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK{rK}) e = true)
    (h : ↥(reps (⟨{rH}, by decide⟩ : Fin 148))) :
    species (reps (⟨{rH}, by decide⟩ : Fin 148)) h (basisElt (reps rK{rK}) (charOfVec2 rK{rK} e heK))
      = ∑ i : Fin {m}, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK{rK} e (h : Coordinate 2) T{rK}_{rH}_2 i :=
  species_entry_eq_sum rK{rK} ⟨{rH}, by decide⟩ e heK h T{rK}_{rH}_2 hfix{rK}_{rH}_2 hinj{rK}_{rH}_2 hcardT{rK}_{rH}_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨{rH}, by decide⟩) (reps rK{rK}) (T{rK}_{rH}_2 i) (hfix{rK}_{rH}_2 i) h)

'''


def main():
    dry = "--dry-run" in sys.argv
    D = Data()
    Rs = {}
    for path in glob.glob(os.path.join(BASIC, "P5EntryData*.lean")):
        for m in re.finditer(r"def R(\d+)list", open(path, encoding="utf-8").read()):
            rK = int(m.group(1))
            if rK in (13, 14, 15):
                Rs[rK] = parse_flat_tuples(os.path.basename(path), "R%dlist" % rK)

    cells, cols, manifest = [], [], []
    ncells = 0
    for rK, rH in GAP:
        T = D.fixed_transversal(1, Rs[rK], rK, rH)
        T2 = D.fixed_transversal(2, Rs[rK], rK, rH)
        assert T == T2, ("transversal differs between twins", rK, rH)
        assert T, ("empty transversal", rK, rH)
        cells.append((rK, rH, T))
        for p in D.cols(rH):
            h1 = tuple(D.transData[rH][p]); h2 = tuple(D.transData2[rH][p])
            d1 = col_data(1, D.repBases[rK], T, h1)
            d2 = col_data(2, D.repBases2[rK], T2, h2)
            assert d1 == d2, ("column data diverges", rK, rH, p)
            for e in D.repChars2[rK]:
                ncells += 1
                assert sum_powers_fast_code(d1, e) == sum_powers_fast_code(d2, e)
            cols.append((rK, rH, p, len(T), h1, h2, d1))
            manifest.append({"rK": rK, "rH": rH, "p": p, "m": len(T),
                             "h1": list(h1), "h2": list(h2), "coincide": True})
    print("gap cell pairs: %d, columns: %d, cells validated: %d"
          % (len(cells), len(cols), ncells))
    if dry:
        return

    out = [HDR_CELL]
    for rK, rH, T in cells:
        out.append(f"/-! ## Cell ({rK}, {rH}): |T| = {len(T)} -/\n\n")
        out.append(cell_block(rK, rH, T, False))
    out.append("namespace Q2\n\n")
    for rK, rH, T in cells:
        out.append(f"/-! ### Cell ({rK}, {rH}) twin -/\n\n")
        out.append(cell_block(rK, rH, T, True))
    out.append("end Q2\n\nend LeanDring.P5Presentation\n")
    open(os.path.join(BASIC, "P5EntryDataGap.lean"), "w", encoding="utf-8").write("".join(out))

    out = [HDR_COL]
    for rK, rH, p, m, h1, h2, d in cols:
        out.append(f'''def colCert_{rK}_{rH}_{p} : ColCert where
  rK := ⟨{rK}, by decide⟩
  rH := ⟨{rH}, by decide⟩
  m := {m}
  T1 := T{rK}_{rH}
  T2 := Q2.T{rK}_{rH}_2
  h1 := {tup(h1)}
  h2 := {tup(h2)}
  D := {json.dumps(d)}
  bind1 := by decide
  bind2 := by decide

''')
    out.append("end LeanDring.P5Presentation\n")
    open(os.path.join(BASIC, "P5ColDataGap.lean"), "w", encoding="utf-8").write("".join(out))
    json.dump(manifest, open(os.path.join(REPO, "results", "p5_gapfill_manifest.json"), "w"),
              indent=1)
    print("wrote P5EntryDataGap.lean, P5ColDataGap.lean, results/p5_gapfill_manifest.json")


if __name__ == "__main__":
    main()
