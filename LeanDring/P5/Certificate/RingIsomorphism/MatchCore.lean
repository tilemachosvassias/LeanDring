/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.RingIsomorphism.Twin2.Sigma
import LeanDring.P5.Certificate.Support.Stage5Core
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Certificate.SpeciesTable.EntrySupport
import LeanDring.P5.Certificate.SpeciesTable.Twin1.SpeciesComplete
import LeanDring.P5.Certificate.SpeciesTable.Twin2.SpeciesComplete

/-!
# Stage-5 assembly core

Wrappers for the two column elements and the two row basis elements the master
cell theorem is stated with, the three off-support dispatchers (order bound,
empty fixed-point set, `⊥` column), the two fast-code extractors
(`LeanDring/P5/Data/SpeciesDiv.lean` /
`LeanDring/P5/Certificate/SpeciesTable/Twin2/SpeciesTau/` orientation), and the
index decides: `alnId_<rK>` (the alignment
is the identity on vectors — the 114 classes whose q1/q2 character sets agree)
and `repPos_<rH>` (the certified orbit-representative column positions).
Auto-emitted by `python/p5_match_emit.py`.
-/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false


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

theorem alnId_0 : ∀ j, j < 1 →
    (Q2.repChars2.getD 0 []).getD ((alnPos.getD 0 []).getD j 0) []
      = (repChars.getD 0 []).getD j [] := by decide

theorem alnId_1 : ∀ j, j < 5 →
    (Q2.repChars2.getD 1 []).getD ((alnPos.getD 1 []).getD j 0) []
      = (repChars.getD 1 []).getD j [] := by decide

theorem alnId_2 : ∀ j, j < 5 →
    (Q2.repChars2.getD 2 []).getD ((alnPos.getD 2 []).getD j 0) []
      = (repChars.getD 2 []).getD j [] := by decide

theorem alnId_3 : ∀ j, j < 5 →
    (Q2.repChars2.getD 3 []).getD ((alnPos.getD 3 []).getD j 0) []
      = (repChars.getD 3 []).getD j [] := by decide

theorem alnId_4 : ∀ j, j < 5 →
    (Q2.repChars2.getD 4 []).getD ((alnPos.getD 4 []).getD j 0) []
      = (repChars.getD 4 []).getD j [] := by decide

theorem alnId_5 : ∀ j, j < 5 →
    (Q2.repChars2.getD 5 []).getD ((alnPos.getD 5 []).getD j 0) []
      = (repChars.getD 5 []).getD j [] := by decide

theorem alnId_6 : ∀ j, j < 5 →
    (Q2.repChars2.getD 6 []).getD ((alnPos.getD 6 []).getD j 0) []
      = (repChars.getD 6 []).getD j [] := by decide

theorem alnId_7 : ∀ j, j < 5 →
    (Q2.repChars2.getD 7 []).getD ((alnPos.getD 7 []).getD j 0) []
      = (repChars.getD 7 []).getD j [] := by decide

theorem alnId_8 : ∀ j, j < 5 →
    (Q2.repChars2.getD 8 []).getD ((alnPos.getD 8 []).getD j 0) []
      = (repChars.getD 8 []).getD j [] := by decide

theorem alnId_9 : ∀ j, j < 5 →
    (Q2.repChars2.getD 9 []).getD ((alnPos.getD 9 []).getD j 0) []
      = (repChars.getD 9 []).getD j [] := by decide

theorem alnId_10 : ∀ j, j < 5 →
    (Q2.repChars2.getD 10 []).getD ((alnPos.getD 10 []).getD j 0) []
      = (repChars.getD 10 []).getD j [] := by decide

theorem alnId_11 : ∀ j, j < 5 →
    (Q2.repChars2.getD 11 []).getD ((alnPos.getD 11 []).getD j 0) []
      = (repChars.getD 11 []).getD j [] := by decide

theorem alnId_12 : ∀ j, j < 5 →
    (Q2.repChars2.getD 12 []).getD ((alnPos.getD 12 []).getD j 0) []
      = (repChars.getD 12 []).getD j [] := by decide

theorem alnId_13 : ∀ j, j < 25 →
    (Q2.repChars2.getD 13 []).getD ((alnPos.getD 13 []).getD j 0) []
      = (repChars.getD 13 []).getD j [] := by decide

theorem alnId_14 : ∀ j, j < 25 →
    (Q2.repChars2.getD 14 []).getD ((alnPos.getD 14 []).getD j 0) []
      = (repChars.getD 14 []).getD j [] := by decide

theorem alnId_15 : ∀ j, j < 25 →
    (Q2.repChars2.getD 15 []).getD ((alnPos.getD 15 []).getD j 0) []
      = (repChars.getD 15 []).getD j [] := by decide

theorem alnId_16 : ∀ j, j < 25 →
    (Q2.repChars2.getD 16 []).getD ((alnPos.getD 16 []).getD j 0) []
      = (repChars.getD 16 []).getD j [] := by decide

theorem alnId_17 : ∀ j, j < 25 →
    (Q2.repChars2.getD 17 []).getD ((alnPos.getD 17 []).getD j 0) []
      = (repChars.getD 17 []).getD j [] := by decide

theorem alnId_18 : ∀ j, j < 25 →
    (Q2.repChars2.getD 18 []).getD ((alnPos.getD 18 []).getD j 0) []
      = (repChars.getD 18 []).getD j [] := by decide

theorem alnId_19 : ∀ j, j < 25 →
    (Q2.repChars2.getD 19 []).getD ((alnPos.getD 19 []).getD j 0) []
      = (repChars.getD 19 []).getD j [] := by decide

theorem alnId_20 : ∀ j, j < 25 →
    (Q2.repChars2.getD 20 []).getD ((alnPos.getD 20 []).getD j 0) []
      = (repChars.getD 20 []).getD j [] := by decide

theorem alnId_21 : ∀ j, j < 25 →
    (Q2.repChars2.getD 21 []).getD ((alnPos.getD 21 []).getD j 0) []
      = (repChars.getD 21 []).getD j [] := by decide

theorem alnId_22 : ∀ j, j < 25 →
    (Q2.repChars2.getD 22 []).getD ((alnPos.getD 22 []).getD j 0) []
      = (repChars.getD 22 []).getD j [] := by decide

theorem alnId_23 : ∀ j, j < 25 →
    (Q2.repChars2.getD 23 []).getD ((alnPos.getD 23 []).getD j 0) []
      = (repChars.getD 23 []).getD j [] := by decide

theorem alnId_24 : ∀ j, j < 25 →
    (Q2.repChars2.getD 24 []).getD ((alnPos.getD 24 []).getD j 0) []
      = (repChars.getD 24 []).getD j [] := by decide

theorem alnId_25 : ∀ j, j < 25 →
    (Q2.repChars2.getD 25 []).getD ((alnPos.getD 25 []).getD j 0) []
      = (repChars.getD 25 []).getD j [] := by decide

theorem alnId_26 : ∀ j, j < 25 →
    (Q2.repChars2.getD 26 []).getD ((alnPos.getD 26 []).getD j 0) []
      = (repChars.getD 26 []).getD j [] := by decide

theorem alnId_27 : ∀ j, j < 25 →
    (Q2.repChars2.getD 27 []).getD ((alnPos.getD 27 []).getD j 0) []
      = (repChars.getD 27 []).getD j [] := by decide

theorem alnId_53 : ∀ j, j < 25 →
    (Q2.repChars2.getD 53 []).getD ((alnPos.getD 53 []).getD j 0) []
      = (repChars.getD 53 []).getD j [] := by decide

theorem alnId_54 : ∀ j, j < 25 →
    (Q2.repChars2.getD 54 []).getD ((alnPos.getD 54 []).getD j 0) []
      = (repChars.getD 54 []).getD j [] := by decide

theorem alnId_55 : ∀ j, j < 25 →
    (Q2.repChars2.getD 55 []).getD ((alnPos.getD 55 []).getD j 0) []
      = (repChars.getD 55 []).getD j [] := by decide

theorem alnId_56 : ∀ j, j < 25 →
    (Q2.repChars2.getD 56 []).getD ((alnPos.getD 56 []).getD j 0) []
      = (repChars.getD 56 []).getD j [] := by decide

theorem alnId_57 : ∀ j, j < 25 →
    (Q2.repChars2.getD 57 []).getD ((alnPos.getD 57 []).getD j 0) []
      = (repChars.getD 57 []).getD j [] := by decide

theorem alnId_58 : ∀ j, j < 25 →
    (Q2.repChars2.getD 58 []).getD ((alnPos.getD 58 []).getD j 0) []
      = (repChars.getD 58 []).getD j [] := by decide

theorem alnId_59 : ∀ j, j < 25 →
    (Q2.repChars2.getD 59 []).getD ((alnPos.getD 59 []).getD j 0) []
      = (repChars.getD 59 []).getD j [] := by decide

theorem alnId_60 : ∀ j, j < 25 →
    (Q2.repChars2.getD 60 []).getD ((alnPos.getD 60 []).getD j 0) []
      = (repChars.getD 60 []).getD j [] := by decide

theorem alnId_61 : ∀ j, j < 25 →
    (Q2.repChars2.getD 61 []).getD ((alnPos.getD 61 []).getD j 0) []
      = (repChars.getD 61 []).getD j [] := by decide

theorem alnId_62 : ∀ j, j < 25 →
    (Q2.repChars2.getD 62 []).getD ((alnPos.getD 62 []).getD j 0) []
      = (repChars.getD 62 []).getD j [] := by decide

theorem alnId_63 : ∀ j, j < 25 →
    (Q2.repChars2.getD 63 []).getD ((alnPos.getD 63 []).getD j 0) []
      = (repChars.getD 63 []).getD j [] := by decide

theorem alnId_65 : ∀ j, j < 25 →
    (Q2.repChars2.getD 65 []).getD ((alnPos.getD 65 []).getD j 0) []
      = (repChars.getD 65 []).getD j [] := by decide

theorem alnId_66 : ∀ j, j < 25 →
    (Q2.repChars2.getD 66 []).getD ((alnPos.getD 66 []).getD j 0) []
      = (repChars.getD 66 []).getD j [] := by decide

theorem alnId_68 : ∀ j, j < 25 →
    (Q2.repChars2.getD 68 []).getD ((alnPos.getD 68 []).getD j 0) []
      = (repChars.getD 68 []).getD j [] := by decide

theorem alnId_69 : ∀ j, j < 25 →
    (Q2.repChars2.getD 69 []).getD ((alnPos.getD 69 []).getD j 0) []
      = (repChars.getD 69 []).getD j [] := by decide

theorem alnId_70 : ∀ j, j < 25 →
    (Q2.repChars2.getD 70 []).getD ((alnPos.getD 70 []).getD j 0) []
      = (repChars.getD 70 []).getD j [] := by decide

theorem alnId_71 : ∀ j, j < 25 →
    (Q2.repChars2.getD 71 []).getD ((alnPos.getD 71 []).getD j 0) []
      = (repChars.getD 71 []).getD j [] := by decide

theorem alnId_72 : ∀ j, j < 25 →
    (Q2.repChars2.getD 72 []).getD ((alnPos.getD 72 []).getD j 0) []
      = (repChars.getD 72 []).getD j [] := by decide

theorem alnId_74 : ∀ j, j < 25 →
    (Q2.repChars2.getD 74 []).getD ((alnPos.getD 74 []).getD j 0) []
      = (repChars.getD 74 []).getD j [] := by decide

theorem alnId_75 : ∀ j, j < 25 →
    (Q2.repChars2.getD 75 []).getD ((alnPos.getD 75 []).getD j 0) []
      = (repChars.getD 75 []).getD j [] := by decide

theorem alnId_77 : ∀ j, j < 25 →
    (Q2.repChars2.getD 77 []).getD ((alnPos.getD 77 []).getD j 0) []
      = (repChars.getD 77 []).getD j [] := by decide

theorem alnId_78 : ∀ j, j < 25 →
    (Q2.repChars2.getD 78 []).getD ((alnPos.getD 78 []).getD j 0) []
      = (repChars.getD 78 []).getD j [] := by decide

theorem alnId_79 : ∀ j, j < 25 →
    (Q2.repChars2.getD 79 []).getD ((alnPos.getD 79 []).getD j 0) []
      = (repChars.getD 79 []).getD j [] := by decide

theorem alnId_80 : ∀ j, j < 125 →
    (Q2.repChars2.getD 80 []).getD ((alnPos.getD 80 []).getD j 0) []
      = (repChars.getD 80 []).getD j [] := by decide

theorem alnId_81 : ∀ j, j < 25 →
    (Q2.repChars2.getD 81 []).getD ((alnPos.getD 81 []).getD j 0) []
      = (repChars.getD 81 []).getD j [] := by decide

theorem alnId_82 : ∀ j, j < 25 →
    (Q2.repChars2.getD 82 []).getD ((alnPos.getD 82 []).getD j 0) []
      = (repChars.getD 82 []).getD j [] := by decide

theorem alnId_83 : ∀ j, j < 25 →
    (Q2.repChars2.getD 83 []).getD ((alnPos.getD 83 []).getD j 0) []
      = (repChars.getD 83 []).getD j [] := by decide

theorem alnId_84 : ∀ j, j < 25 →
    (Q2.repChars2.getD 84 []).getD ((alnPos.getD 84 []).getD j 0) []
      = (repChars.getD 84 []).getD j [] := by decide

theorem alnId_85 : ∀ j, j < 125 →
    (Q2.repChars2.getD 85 []).getD ((alnPos.getD 85 []).getD j 0) []
      = (repChars.getD 85 []).getD j [] := by decide

theorem alnId_86 : ∀ j, j < 25 →
    (Q2.repChars2.getD 86 []).getD ((alnPos.getD 86 []).getD j 0) []
      = (repChars.getD 86 []).getD j [] := by decide

theorem alnId_87 : ∀ j, j < 25 →
    (Q2.repChars2.getD 87 []).getD ((alnPos.getD 87 []).getD j 0) []
      = (repChars.getD 87 []).getD j [] := by decide

theorem alnId_88 : ∀ j, j < 25 →
    (Q2.repChars2.getD 88 []).getD ((alnPos.getD 88 []).getD j 0) []
      = (repChars.getD 88 []).getD j [] := by decide

theorem alnId_89 : ∀ j, j < 25 →
    (Q2.repChars2.getD 89 []).getD ((alnPos.getD 89 []).getD j 0) []
      = (repChars.getD 89 []).getD j [] := by decide

theorem alnId_91 : ∀ j, j < 25 →
    (Q2.repChars2.getD 91 []).getD ((alnPos.getD 91 []).getD j 0) []
      = (repChars.getD 91 []).getD j [] := by decide

theorem alnId_92 : ∀ j, j < 25 →
    (Q2.repChars2.getD 92 []).getD ((alnPos.getD 92 []).getD j 0) []
      = (repChars.getD 92 []).getD j [] := by decide

theorem alnId_93 : ∀ j, j < 25 →
    (Q2.repChars2.getD 93 []).getD ((alnPos.getD 93 []).getD j 0) []
      = (repChars.getD 93 []).getD j [] := by decide

theorem alnId_94 : ∀ j, j < 25 →
    (Q2.repChars2.getD 94 []).getD ((alnPos.getD 94 []).getD j 0) []
      = (repChars.getD 94 []).getD j [] := by decide

theorem alnId_96 : ∀ j, j < 25 →
    (Q2.repChars2.getD 96 []).getD ((alnPos.getD 96 []).getD j 0) []
      = (repChars.getD 96 []).getD j [] := by decide

theorem alnId_97 : ∀ j, j < 25 →
    (Q2.repChars2.getD 97 []).getD ((alnPos.getD 97 []).getD j 0) []
      = (repChars.getD 97 []).getD j [] := by decide

theorem alnId_98 : ∀ j, j < 25 →
    (Q2.repChars2.getD 98 []).getD ((alnPos.getD 98 []).getD j 0) []
      = (repChars.getD 98 []).getD j [] := by decide

theorem alnId_99 : ∀ j, j < 25 →
    (Q2.repChars2.getD 99 []).getD ((alnPos.getD 99 []).getD j 0) []
      = (repChars.getD 99 []).getD j [] := by decide

theorem alnId_101 : ∀ j, j < 25 →
    (Q2.repChars2.getD 101 []).getD ((alnPos.getD 101 []).getD j 0) []
      = (repChars.getD 101 []).getD j [] := by decide

theorem alnId_102 : ∀ j, j < 25 →
    (Q2.repChars2.getD 102 []).getD ((alnPos.getD 102 []).getD j 0) []
      = (repChars.getD 102 []).getD j [] := by decide

theorem alnId_103 : ∀ j, j < 25 →
    (Q2.repChars2.getD 103 []).getD ((alnPos.getD 103 []).getD j 0) []
      = (repChars.getD 103 []).getD j [] := by decide

theorem alnId_104 : ∀ j, j < 25 →
    (Q2.repChars2.getD 104 []).getD ((alnPos.getD 104 []).getD j 0) []
      = (repChars.getD 104 []).getD j [] := by decide

theorem alnId_106 : ∀ j, j < 25 →
    (Q2.repChars2.getD 106 []).getD ((alnPos.getD 106 []).getD j 0) []
      = (repChars.getD 106 []).getD j [] := by decide

theorem alnId_107 : ∀ j, j < 25 →
    (Q2.repChars2.getD 107 []).getD ((alnPos.getD 107 []).getD j 0) []
      = (repChars.getD 107 []).getD j [] := by decide

theorem alnId_108 : ∀ j, j < 25 →
    (Q2.repChars2.getD 108 []).getD ((alnPos.getD 108 []).getD j 0) []
      = (repChars.getD 108 []).getD j [] := by decide

theorem alnId_109 : ∀ j, j < 25 →
    (Q2.repChars2.getD 109 []).getD ((alnPos.getD 109 []).getD j 0) []
      = (repChars.getD 109 []).getD j [] := by decide

theorem alnId_111 : ∀ j, j < 25 →
    (Q2.repChars2.getD 111 []).getD ((alnPos.getD 111 []).getD j 0) []
      = (repChars.getD 111 []).getD j [] := by decide

theorem alnId_112 : ∀ j, j < 25 →
    (Q2.repChars2.getD 112 []).getD ((alnPos.getD 112 []).getD j 0) []
      = (repChars.getD 112 []).getD j [] := by decide

theorem alnId_113 : ∀ j, j < 25 →
    (Q2.repChars2.getD 113 []).getD ((alnPos.getD 113 []).getD j 0) []
      = (repChars.getD 113 []).getD j [] := by decide

theorem alnId_114 : ∀ j, j < 25 →
    (Q2.repChars2.getD 114 []).getD ((alnPos.getD 114 []).getD j 0) []
      = (repChars.getD 114 []).getD j [] := by decide

theorem alnId_115 : ∀ j, j < 25 →
    (Q2.repChars2.getD 115 []).getD ((alnPos.getD 115 []).getD j 0) []
      = (repChars.getD 115 []).getD j [] := by decide

theorem alnId_116 : ∀ j, j < 125 →
    (Q2.repChars2.getD 116 []).getD ((alnPos.getD 116 []).getD j 0) []
      = (repChars.getD 116 []).getD j [] := by decide

theorem alnId_117 : ∀ j, j < 125 →
    (Q2.repChars2.getD 117 []).getD ((alnPos.getD 117 []).getD j 0) []
      = (repChars.getD 117 []).getD j [] := by decide

theorem alnId_118 : ∀ j, j < 125 →
    (Q2.repChars2.getD 118 []).getD ((alnPos.getD 118 []).getD j 0) []
      = (repChars.getD 118 []).getD j [] := by decide

theorem alnId_119 : ∀ j, j < 125 →
    (Q2.repChars2.getD 119 []).getD ((alnPos.getD 119 []).getD j 0) []
      = (repChars.getD 119 []).getD j [] := by decide

theorem alnId_120 : ∀ j, j < 125 →
    (Q2.repChars2.getD 120 []).getD ((alnPos.getD 120 []).getD j 0) []
      = (repChars.getD 120 []).getD j [] := by decide

theorem alnId_121 : ∀ j, j < 25 →
    (Q2.repChars2.getD 121 []).getD ((alnPos.getD 121 []).getD j 0) []
      = (repChars.getD 121 []).getD j [] := by decide

theorem alnId_122 : ∀ j, j < 25 →
    (Q2.repChars2.getD 122 []).getD ((alnPos.getD 122 []).getD j 0) []
      = (repChars.getD 122 []).getD j [] := by decide

theorem alnId_123 : ∀ j, j < 25 →
    (Q2.repChars2.getD 123 []).getD ((alnPos.getD 123 []).getD j 0) []
      = (repChars.getD 123 []).getD j [] := by decide

theorem alnId_124 : ∀ j, j < 25 →
    (Q2.repChars2.getD 124 []).getD ((alnPos.getD 124 []).getD j 0) []
      = (repChars.getD 124 []).getD j [] := by decide

theorem alnId_125 : ∀ j, j < 25 →
    (Q2.repChars2.getD 125 []).getD ((alnPos.getD 125 []).getD j 0) []
      = (repChars.getD 125 []).getD j [] := by decide

theorem alnId_126 : ∀ j, j < 25 →
    (Q2.repChars2.getD 126 []).getD ((alnPos.getD 126 []).getD j 0) []
      = (repChars.getD 126 []).getD j [] := by decide

theorem alnId_127 : ∀ j, j < 25 →
    (Q2.repChars2.getD 127 []).getD ((alnPos.getD 127 []).getD j 0) []
      = (repChars.getD 127 []).getD j [] := by decide

theorem alnId_128 : ∀ j, j < 25 →
    (Q2.repChars2.getD 128 []).getD ((alnPos.getD 128 []).getD j 0) []
      = (repChars.getD 128 []).getD j [] := by decide

theorem alnId_129 : ∀ j, j < 25 →
    (Q2.repChars2.getD 129 []).getD ((alnPos.getD 129 []).getD j 0) []
      = (repChars.getD 129 []).getD j [] := by decide

theorem alnId_130 : ∀ j, j < 25 →
    (Q2.repChars2.getD 130 []).getD ((alnPos.getD 130 []).getD j 0) []
      = (repChars.getD 130 []).getD j [] := by decide

theorem alnId_131 : ∀ j, j < 25 →
    (Q2.repChars2.getD 131 []).getD ((alnPos.getD 131 []).getD j 0) []
      = (repChars.getD 131 []).getD j [] := by decide

theorem alnId_132 : ∀ j, j < 25 →
    (Q2.repChars2.getD 132 []).getD ((alnPos.getD 132 []).getD j 0) []
      = (repChars.getD 132 []).getD j [] := by decide

theorem alnId_133 : ∀ j, j < 25 →
    (Q2.repChars2.getD 133 []).getD ((alnPos.getD 133 []).getD j 0) []
      = (repChars.getD 133 []).getD j [] := by decide

theorem alnId_134 : ∀ j, j < 25 →
    (Q2.repChars2.getD 134 []).getD ((alnPos.getD 134 []).getD j 0) []
      = (repChars.getD 134 []).getD j [] := by decide

theorem alnId_135 : ∀ j, j < 25 →
    (Q2.repChars2.getD 135 []).getD ((alnPos.getD 135 []).getD j 0) []
      = (repChars.getD 135 []).getD j [] := by decide

theorem alnId_136 : ∀ j, j < 25 →
    (Q2.repChars2.getD 136 []).getD ((alnPos.getD 136 []).getD j 0) []
      = (repChars.getD 136 []).getD j [] := by decide

theorem alnId_137 : ∀ j, j < 25 →
    (Q2.repChars2.getD 137 []).getD ((alnPos.getD 137 []).getD j 0) []
      = (repChars.getD 137 []).getD j [] := by decide

theorem alnId_138 : ∀ j, j < 25 →
    (Q2.repChars2.getD 138 []).getD ((alnPos.getD 138 []).getD j 0) []
      = (repChars.getD 138 []).getD j [] := by decide

theorem alnId_139 : ∀ j, j < 25 →
    (Q2.repChars2.getD 139 []).getD ((alnPos.getD 139 []).getD j 0) []
      = (repChars.getD 139 []).getD j [] := by decide

theorem alnId_140 : ∀ j, j < 25 →
    (Q2.repChars2.getD 140 []).getD ((alnPos.getD 140 []).getD j 0) []
      = (repChars.getD 140 []).getD j [] := by decide

theorem alnId_141 : ∀ j, j < 125 →
    (Q2.repChars2.getD 141 []).getD ((alnPos.getD 141 []).getD j 0) []
      = (repChars.getD 141 []).getD j [] := by decide

theorem alnId_142 : ∀ j, j < 25 →
    (Q2.repChars2.getD 142 []).getD ((alnPos.getD 142 []).getD j 0) []
      = (repChars.getD 142 []).getD j [] := by decide

theorem alnId_143 : ∀ j, j < 25 →
    (Q2.repChars2.getD 143 []).getD ((alnPos.getD 143 []).getD j 0) []
      = (repChars.getD 143 []).getD j [] := by decide

theorem alnId_144 : ∀ j, j < 25 →
    (Q2.repChars2.getD 144 []).getD ((alnPos.getD 144 []).getD j 0) []
      = (repChars.getD 144 []).getD j [] := by decide

theorem alnId_145 : ∀ j, j < 25 →
    (Q2.repChars2.getD 145 []).getD ((alnPos.getD 145 []).getD j 0) []
      = (repChars.getD 145 []).getD j [] := by decide

theorem alnId_146 : ∀ j, j < 25 →
    (Q2.repChars2.getD 146 []).getD ((alnPos.getD 146 []).getD j 0) []
      = (repChars.getD 146 []).getD j [] := by decide

theorem alnId_147 : ∀ j, j < 125 →
    (Q2.repChars2.getD 147 []).getD ((alnPos.getD 147 []).getD j 0) []
      = (repChars.getD 147 []).getD j [] := by decide

theorem repPos_0 : ∀ p, p < (Q2.transData.getD 0 []).length →
    (Q2.cosetIsRep.getD 0 []).getD p false = true → p ∈ ([0] : List Nat) := by decide

theorem repPos_1 : ∀ p, p < (Q2.transData.getD 1 []).length →
    (Q2.cosetIsRep.getD 1 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4] : List Nat) := by decide

theorem repPos_2 : ∀ p, p < (Q2.transData.getD 2 []).length →
    (Q2.cosetIsRep.getD 2 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4] : List Nat) := by decide

theorem repPos_3 : ∀ p, p < (Q2.transData.getD 3 []).length →
    (Q2.cosetIsRep.getD 3 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4] : List Nat) := by decide

theorem repPos_4 : ∀ p, p < (Q2.transData.getD 4 []).length →
    (Q2.cosetIsRep.getD 4 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4] : List Nat) := by decide

theorem repPos_5 : ∀ p, p < (Q2.transData.getD 5 []).length →
    (Q2.cosetIsRep.getD 5 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4] : List Nat) := by decide

theorem repPos_6 : ∀ p, p < (Q2.transData.getD 6 []).length →
    (Q2.cosetIsRep.getD 6 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4] : List Nat) := by decide

theorem repPos_7 : ∀ p, p < (Q2.transData.getD 7 []).length →
    (Q2.cosetIsRep.getD 7 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4] : List Nat) := by decide

theorem repPos_8 : ∀ p, p < (Q2.transData.getD 8 []).length →
    (Q2.cosetIsRep.getD 8 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4] : List Nat) := by decide

theorem repPos_9 : ∀ p, p < (Q2.transData.getD 9 []).length →
    (Q2.cosetIsRep.getD 9 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4] : List Nat) := by decide

theorem repPos_10 : ∀ p, p < (Q2.transData.getD 10 []).length →
    (Q2.cosetIsRep.getD 10 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4] : List Nat) := by decide

theorem repPos_11 : ∀ p, p < (Q2.transData.getD 11 []).length →
    (Q2.cosetIsRep.getD 11 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4] : List Nat) := by decide

theorem repPos_12 : ∀ p, p < (Q2.transData.getD 12 []).length →
    (Q2.cosetIsRep.getD 12 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4] : List Nat) := by decide

theorem repPos_13 : ∀ p, p < (Q2.transData.getD 13 []).length →
    (Q2.cosetIsRep.getD 13 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_14 : ∀ p, p < (Q2.transData.getD 14 []).length →
    (Q2.cosetIsRep.getD 14 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_15 : ∀ p, p < (Q2.transData.getD 15 []).length →
    (Q2.cosetIsRep.getD 15 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_16 : ∀ p, p < (Q2.transData.getD 16 []).length →
    (Q2.cosetIsRep.getD 16 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_17 : ∀ p, p < (Q2.transData.getD 17 []).length →
    (Q2.cosetIsRep.getD 17 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_18 : ∀ p, p < (Q2.transData.getD 18 []).length →
    (Q2.cosetIsRep.getD 18 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_19 : ∀ p, p < (Q2.transData.getD 19 []).length →
    (Q2.cosetIsRep.getD 19 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_20 : ∀ p, p < (Q2.transData.getD 20 []).length →
    (Q2.cosetIsRep.getD 20 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_21 : ∀ p, p < (Q2.transData.getD 21 []).length →
    (Q2.cosetIsRep.getD 21 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_22 : ∀ p, p < (Q2.transData.getD 22 []).length →
    (Q2.cosetIsRep.getD 22 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_23 : ∀ p, p < (Q2.transData.getD 23 []).length →
    (Q2.cosetIsRep.getD 23 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_24 : ∀ p, p < (Q2.transData.getD 24 []).length →
    (Q2.cosetIsRep.getD 24 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_25 : ∀ p, p < (Q2.transData.getD 25 []).length →
    (Q2.cosetIsRep.getD 25 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_26 : ∀ p, p < (Q2.transData.getD 26 []).length →
    (Q2.cosetIsRep.getD 26 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_27 : ∀ p, p < (Q2.transData.getD 27 []).length →
    (Q2.cosetIsRep.getD 27 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_28 : ∀ p, p < (Q2.transData.getD 28 []).length →
    (Q2.cosetIsRep.getD 28 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_29 : ∀ p, p < (Q2.transData.getD 29 []).length →
    (Q2.cosetIsRep.getD 29 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_30 : ∀ p, p < (Q2.transData.getD 30 []).length →
    (Q2.cosetIsRep.getD 30 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_31 : ∀ p, p < (Q2.transData.getD 31 []).length →
    (Q2.cosetIsRep.getD 31 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_32 : ∀ p, p < (Q2.transData.getD 32 []).length →
    (Q2.cosetIsRep.getD 32 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_33 : ∀ p, p < (Q2.transData.getD 33 []).length →
    (Q2.cosetIsRep.getD 33 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_34 : ∀ p, p < (Q2.transData.getD 34 []).length →
    (Q2.cosetIsRep.getD 34 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_35 : ∀ p, p < (Q2.transData.getD 35 []).length →
    (Q2.cosetIsRep.getD 35 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_36 : ∀ p, p < (Q2.transData.getD 36 []).length →
    (Q2.cosetIsRep.getD 36 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_37 : ∀ p, p < (Q2.transData.getD 37 []).length →
    (Q2.cosetIsRep.getD 37 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_38 : ∀ p, p < (Q2.transData.getD 38 []).length →
    (Q2.cosetIsRep.getD 38 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_39 : ∀ p, p < (Q2.transData.getD 39 []).length →
    (Q2.cosetIsRep.getD 39 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_40 : ∀ p, p < (Q2.transData.getD 40 []).length →
    (Q2.cosetIsRep.getD 40 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_41 : ∀ p, p < (Q2.transData.getD 41 []).length →
    (Q2.cosetIsRep.getD 41 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_42 : ∀ p, p < (Q2.transData.getD 42 []).length →
    (Q2.cosetIsRep.getD 42 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_43 : ∀ p, p < (Q2.transData.getD 43 []).length →
    (Q2.cosetIsRep.getD 43 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_44 : ∀ p, p < (Q2.transData.getD 44 []).length →
    (Q2.cosetIsRep.getD 44 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_45 : ∀ p, p < (Q2.transData.getD 45 []).length →
    (Q2.cosetIsRep.getD 45 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_46 : ∀ p, p < (Q2.transData.getD 46 []).length →
    (Q2.cosetIsRep.getD 46 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_47 : ∀ p, p < (Q2.transData.getD 47 []).length →
    (Q2.cosetIsRep.getD 47 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_48 : ∀ p, p < (Q2.transData.getD 48 []).length →
    (Q2.cosetIsRep.getD 48 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_49 : ∀ p, p < (Q2.transData.getD 49 []).length →
    (Q2.cosetIsRep.getD 49 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_50 : ∀ p, p < (Q2.transData.getD 50 []).length →
    (Q2.cosetIsRep.getD 50 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_51 : ∀ p, p < (Q2.transData.getD 51 []).length →
    (Q2.cosetIsRep.getD 51 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_52 : ∀ p, p < (Q2.transData.getD 52 []).length →
    (Q2.cosetIsRep.getD 52 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_53 : ∀ p, p < (Q2.transData.getD 53 []).length →
    (Q2.cosetIsRep.getD 53 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_54 : ∀ p, p < (Q2.transData.getD 54 []).length →
    (Q2.cosetIsRep.getD 54 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_55 : ∀ p, p < (Q2.transData.getD 55 []).length →
    (Q2.cosetIsRep.getD 55 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_56 : ∀ p, p < (Q2.transData.getD 56 []).length →
    (Q2.cosetIsRep.getD 56 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_57 : ∀ p, p < (Q2.transData.getD 57 []).length →
    (Q2.cosetIsRep.getD 57 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_58 : ∀ p, p < (Q2.transData.getD 58 []).length →
    (Q2.cosetIsRep.getD 58 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_59 : ∀ p, p < (Q2.transData.getD 59 []).length →
    (Q2.cosetIsRep.getD 59 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_60 : ∀ p, p < (Q2.transData.getD 60 []).length →
    (Q2.cosetIsRep.getD 60 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_61 : ∀ p, p < (Q2.transData.getD 61 []).length →
    (Q2.cosetIsRep.getD 61 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_62 : ∀ p, p < (Q2.transData.getD 62 []).length →
    (Q2.cosetIsRep.getD 62 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_63 : ∀ p, p < (Q2.transData.getD 63 []).length →
    (Q2.cosetIsRep.getD 63 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_64 : ∀ p, p < (Q2.transData.getD 64 []).length →
    (Q2.cosetIsRep.getD 64 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 30, 35, 40, 45, 50, 55, 60, 65, 70, 75, 80, 85, 90, 95, 100, 105, 110, 115, 120] : List Nat) := by decide

theorem repPos_65 : ∀ p, p < (Q2.transData.getD 65 []).length →
    (Q2.cosetIsRep.getD 65 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_66 : ∀ p, p < (Q2.transData.getD 66 []).length →
    (Q2.cosetIsRep.getD 66 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_67 : ∀ p, p < (Q2.transData.getD 67 []).length →
    (Q2.cosetIsRep.getD 67 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 30, 35, 40, 45, 50, 55, 60, 65, 70, 75, 80, 85, 90, 95, 100, 105, 110, 115, 120] : List Nat) := by decide

theorem repPos_68 : ∀ p, p < (Q2.transData.getD 68 []).length →
    (Q2.cosetIsRep.getD 68 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_69 : ∀ p, p < (Q2.transData.getD 69 []).length →
    (Q2.cosetIsRep.getD 69 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_70 : ∀ p, p < (Q2.transData.getD 70 []).length →
    (Q2.cosetIsRep.getD 70 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_71 : ∀ p, p < (Q2.transData.getD 71 []).length →
    (Q2.cosetIsRep.getD 71 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_72 : ∀ p, p < (Q2.transData.getD 72 []).length →
    (Q2.cosetIsRep.getD 72 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_73 : ∀ p, p < (Q2.transData.getD 73 []).length →
    (Q2.cosetIsRep.getD 73 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 30, 35, 40, 45, 50, 55, 60, 65, 70, 75, 80, 85, 90, 95, 100, 105, 110, 115, 120] : List Nat) := by decide

theorem repPos_74 : ∀ p, p < (Q2.transData.getD 74 []).length →
    (Q2.cosetIsRep.getD 74 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_75 : ∀ p, p < (Q2.transData.getD 75 []).length →
    (Q2.cosetIsRep.getD 75 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_76 : ∀ p, p < (Q2.transData.getD 76 []).length →
    (Q2.cosetIsRep.getD 76 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 30, 35, 40, 45, 50, 55, 60, 65, 70, 75, 80, 85, 90, 95, 100, 105, 110, 115, 120] : List Nat) := by decide

theorem repPos_77 : ∀ p, p < (Q2.transData.getD 77 []).length →
    (Q2.cosetIsRep.getD 77 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_78 : ∀ p, p < (Q2.transData.getD 78 []).length →
    (Q2.cosetIsRep.getD 78 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_79 : ∀ p, p < (Q2.transData.getD 79 []).length →
    (Q2.cosetIsRep.getD 79 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_80 : ∀ p, p < (Q2.transData.getD 80 []).length →
    (Q2.cosetIsRep.getD 80 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20, 25, 30, 35, 40, 45, 50, 55, 60, 65, 70, 75, 80, 85, 90, 95, 100, 105, 110, 115, 120] : List Nat) := by decide

theorem repPos_81 : ∀ p, p < (Q2.transData.getD 81 []).length →
    (Q2.cosetIsRep.getD 81 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_82 : ∀ p, p < (Q2.transData.getD 82 []).length →
    (Q2.cosetIsRep.getD 82 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_83 : ∀ p, p < (Q2.transData.getD 83 []).length →
    (Q2.cosetIsRep.getD 83 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_84 : ∀ p, p < (Q2.transData.getD 84 []).length →
    (Q2.cosetIsRep.getD 84 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_85 : ∀ p, p < (Q2.transData.getD 85 []).length →
    (Q2.cosetIsRep.getD 85 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 30, 35, 40, 45, 50, 55, 60, 65, 70, 75, 80, 85, 90, 95, 100, 105, 110, 115, 120] : List Nat) := by decide

theorem repPos_86 : ∀ p, p < (Q2.transData.getD 86 []).length →
    (Q2.cosetIsRep.getD 86 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_87 : ∀ p, p < (Q2.transData.getD 87 []).length →
    (Q2.cosetIsRep.getD 87 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_88 : ∀ p, p < (Q2.transData.getD 88 []).length →
    (Q2.cosetIsRep.getD 88 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_89 : ∀ p, p < (Q2.transData.getD 89 []).length →
    (Q2.cosetIsRep.getD 89 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_90 : ∀ p, p < (Q2.transData.getD 90 []).length →
    (Q2.cosetIsRep.getD 90 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20, 25, 50, 75, 100] : List Nat) := by decide

theorem repPos_91 : ∀ p, p < (Q2.transData.getD 91 []).length →
    (Q2.cosetIsRep.getD 91 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_92 : ∀ p, p < (Q2.transData.getD 92 []).length →
    (Q2.cosetIsRep.getD 92 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_93 : ∀ p, p < (Q2.transData.getD 93 []).length →
    (Q2.cosetIsRep.getD 93 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_94 : ∀ p, p < (Q2.transData.getD 94 []).length →
    (Q2.cosetIsRep.getD 94 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_95 : ∀ p, p < (Q2.transData.getD 95 []).length →
    (Q2.cosetIsRep.getD 95 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20, 25, 50, 75, 100] : List Nat) := by decide

theorem repPos_96 : ∀ p, p < (Q2.transData.getD 96 []).length →
    (Q2.cosetIsRep.getD 96 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_97 : ∀ p, p < (Q2.transData.getD 97 []).length →
    (Q2.cosetIsRep.getD 97 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_98 : ∀ p, p < (Q2.transData.getD 98 []).length →
    (Q2.cosetIsRep.getD 98 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_99 : ∀ p, p < (Q2.transData.getD 99 []).length →
    (Q2.cosetIsRep.getD 99 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_100 : ∀ p, p < (Q2.transData.getD 100 []).length →
    (Q2.cosetIsRep.getD 100 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20, 25, 50, 75, 100] : List Nat) := by decide

theorem repPos_101 : ∀ p, p < (Q2.transData.getD 101 []).length →
    (Q2.cosetIsRep.getD 101 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_102 : ∀ p, p < (Q2.transData.getD 102 []).length →
    (Q2.cosetIsRep.getD 102 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_103 : ∀ p, p < (Q2.transData.getD 103 []).length →
    (Q2.cosetIsRep.getD 103 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_104 : ∀ p, p < (Q2.transData.getD 104 []).length →
    (Q2.cosetIsRep.getD 104 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_105 : ∀ p, p < (Q2.transData.getD 105 []).length →
    (Q2.cosetIsRep.getD 105 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20, 25, 50, 75, 100] : List Nat) := by decide

theorem repPos_106 : ∀ p, p < (Q2.transData.getD 106 []).length →
    (Q2.cosetIsRep.getD 106 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_107 : ∀ p, p < (Q2.transData.getD 107 []).length →
    (Q2.cosetIsRep.getD 107 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_108 : ∀ p, p < (Q2.transData.getD 108 []).length →
    (Q2.cosetIsRep.getD 108 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_109 : ∀ p, p < (Q2.transData.getD 109 []).length →
    (Q2.cosetIsRep.getD 109 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_110 : ∀ p, p < (Q2.transData.getD 110 []).length →
    (Q2.cosetIsRep.getD 110 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20, 25, 50, 75, 100] : List Nat) := by decide

theorem repPos_111 : ∀ p, p < (Q2.transData.getD 111 []).length →
    (Q2.cosetIsRep.getD 111 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_112 : ∀ p, p < (Q2.transData.getD 112 []).length →
    (Q2.cosetIsRep.getD 112 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_113 : ∀ p, p < (Q2.transData.getD 113 []).length →
    (Q2.cosetIsRep.getD 113 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_114 : ∀ p, p < (Q2.transData.getD 114 []).length →
    (Q2.cosetIsRep.getD 114 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_115 : ∀ p, p < (Q2.transData.getD 115 []).length →
    (Q2.cosetIsRep.getD 115 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 10, 15, 20] : List Nat) := by decide

theorem repPos_116 : ∀ p, p < (Q2.transData.getD 116 []).length →
    (Q2.cosetIsRep.getD 116 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 30, 35, 40, 45, 50, 55, 60, 65, 70, 75, 80, 85, 90, 95, 100, 105, 110, 115, 120] : List Nat) := by decide

theorem repPos_117 : ∀ p, p < (Q2.transData.getD 117 []).length →
    (Q2.cosetIsRep.getD 117 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 30, 35, 40, 45, 50, 55, 60, 65, 70, 75, 80, 85, 90, 95, 100, 105, 110, 115, 120] : List Nat) := by decide

theorem repPos_118 : ∀ p, p < (Q2.transData.getD 118 []).length →
    (Q2.cosetIsRep.getD 118 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 30, 35, 40, 45, 50, 55, 60, 65, 70, 75, 80, 85, 90, 95, 100, 105, 110, 115, 120] : List Nat) := by decide

theorem repPos_119 : ∀ p, p < (Q2.transData.getD 119 []).length →
    (Q2.cosetIsRep.getD 119 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 30, 35, 40, 45, 50, 55, 60, 65, 70, 75, 80, 85, 90, 95, 100, 105, 110, 115, 120] : List Nat) := by decide

theorem repPos_120 : ∀ p, p < (Q2.transData.getD 120 []).length →
    (Q2.cosetIsRep.getD 120 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 30, 35, 40, 45, 50, 55, 60, 65, 70, 75, 80, 85, 90, 95, 100, 105, 110, 115, 120] : List Nat) := by decide

theorem repPos_121 : ∀ p, p < (Q2.transData.getD 121 []).length →
    (Q2.cosetIsRep.getD 121 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_122 : ∀ p, p < (Q2.transData.getD 122 []).length →
    (Q2.cosetIsRep.getD 122 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_123 : ∀ p, p < (Q2.transData.getD 123 []).length →
    (Q2.cosetIsRep.getD 123 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_124 : ∀ p, p < (Q2.transData.getD 124 []).length →
    (Q2.cosetIsRep.getD 124 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_125 : ∀ p, p < (Q2.transData.getD 125 []).length →
    (Q2.cosetIsRep.getD 125 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_126 : ∀ p, p < (Q2.transData.getD 126 []).length →
    (Q2.cosetIsRep.getD 126 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_127 : ∀ p, p < (Q2.transData.getD 127 []).length →
    (Q2.cosetIsRep.getD 127 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_128 : ∀ p, p < (Q2.transData.getD 128 []).length →
    (Q2.cosetIsRep.getD 128 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_129 : ∀ p, p < (Q2.transData.getD 129 []).length →
    (Q2.cosetIsRep.getD 129 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_130 : ∀ p, p < (Q2.transData.getD 130 []).length →
    (Q2.cosetIsRep.getD 130 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_131 : ∀ p, p < (Q2.transData.getD 131 []).length →
    (Q2.cosetIsRep.getD 131 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_132 : ∀ p, p < (Q2.transData.getD 132 []).length →
    (Q2.cosetIsRep.getD 132 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_133 : ∀ p, p < (Q2.transData.getD 133 []).length →
    (Q2.cosetIsRep.getD 133 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_134 : ∀ p, p < (Q2.transData.getD 134 []).length →
    (Q2.cosetIsRep.getD 134 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_135 : ∀ p, p < (Q2.transData.getD 135 []).length →
    (Q2.cosetIsRep.getD 135 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_136 : ∀ p, p < (Q2.transData.getD 136 []).length →
    (Q2.cosetIsRep.getD 136 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_137 : ∀ p, p < (Q2.transData.getD 137 []).length →
    (Q2.cosetIsRep.getD 137 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_138 : ∀ p, p < (Q2.transData.getD 138 []).length →
    (Q2.cosetIsRep.getD 138 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_139 : ∀ p, p < (Q2.transData.getD 139 []).length →
    (Q2.cosetIsRep.getD 139 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_140 : ∀ p, p < (Q2.transData.getD 140 []).length →
    (Q2.cosetIsRep.getD 140 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_141 : ∀ p, p < (Q2.transData.getD 141 []).length →
    (Q2.cosetIsRep.getD 141 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 30, 35, 40, 45, 50, 55, 60, 65, 70, 75, 80, 85, 90, 95, 100, 105, 110, 115, 120] : List Nat) := by decide

theorem repPos_142 : ∀ p, p < (Q2.transData.getD 142 []).length →
    (Q2.cosetIsRep.getD 142 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_143 : ∀ p, p < (Q2.transData.getD 143 []).length →
    (Q2.cosetIsRep.getD 143 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_144 : ∀ p, p < (Q2.transData.getD 144 []).length →
    (Q2.cosetIsRep.getD 144 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_145 : ∀ p, p < (Q2.transData.getD 145 []).length →
    (Q2.cosetIsRep.getD 145 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_146 : ∀ p, p < (Q2.transData.getD 146 []).length →
    (Q2.cosetIsRep.getD 146 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat) := by decide

theorem repPos_147 : ∀ p, p < (Q2.transData.getD 147 []).length →
    (Q2.cosetIsRep.getD 147 []).getD p false = true → p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124] : List Nat) := by decide

end LeanDring.P5Presentation
