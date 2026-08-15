/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharCert
import LeanDring.P5.Certificate.Characters.Twin2.CharRows.Chunk01
import LeanDring.P5.Certificate.Characters.Twin2.CharRows.Chunk02
import LeanDring.P5.Certificate.Characters.Twin2.CharRows.Chunk03
import LeanDring.P5.Certificate.Characters.Twin2.CharRows.Chunk04
import LeanDring.P5.Certificate.Characters.Twin2.CharRows.Chunk05
import LeanDring.P5.Certificate.Characters.Twin2.CharRows.Chunk06
import LeanDring.P5.Certificate.Characters.Twin2.CharRows.Chunk07
import LeanDring.P5.Certificate.Characters.Twin2.CharRows.Chunk08
import LeanDring.P5.Certificate.Characters.Twin2.CharBasis.Chunk01
import LeanDring.P5.Certificate.Characters.Twin2.CharBasis.Chunk02
import LeanDring.P5.Certificate.Characters.Twin2.CharBasis.Chunk03
import LeanDring.P5.Certificate.Characters.Twin2.CharBasis.Chunk04
import LeanDring.P5.Certificate.Characters.Twin2.CharValid
import LeanDring.P5.Certificate.Characters.Twin2.CharNodup
import LeanDring.P5.Certificate.Characters.Twin2.CharCount
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.ConjClasses
import LeanDring.P5.Certificate.Characters.Twin1.CharAssembly

/-!
# Assembly of the per-representative q=2 character certification (character certification, twin q=2)

The q=2 twin of `LeanDring.P5.Certificate.Characters.Twin1.CharAssembly`. The
sibling `CharRows.Chunk01`–`Chunk08`, `CharBasis.Chunk01`–`Chunk04`, `CharValid`,
`CharNodup` and `CharCount` modules (all under
`LeanDring.P5.Certificate.Characters.Twin2`) kernel-check, chunk by chunk, that
for every representative `r` the embedded q=2 data
(`repBases2/repPR2/repCR2/repChars2 r`) is internally consistent under the q=2
group law. Here we glue the chunks into whole-range
`(List.range 148).all _ = true` facts and expose the per-`r` API
`charsAt2_valid/nodup/count`, `basisAt2_eq`, and the certified total `5236`.

The heavy sift check `checkRows2` is split into eight finer chunks (the len-4/5
representatives, `116…147`, kept to ≤ 8 per kernel `decide`); the lighter checks
follow the q=1 four-chunk layout via `all148_of_chunks`.
-/

namespace LeanDring.P5Presentation

open Fin.NatCast

set_option maxRecDepth 100000

/-! ## Gluing the chunks into whole-range checks -/

theorem checkRows2_all : (List.range 148).all Q2.checkRows2 = true := by
  rw [all_split (List.range 148) Q2.checkRows2 37,
      all_split ((List.range 148).drop 37) Q2.checkRows2 37,
      all_split (((List.range 148).drop 37).drop 37) Q2.checkRows2 26,
      all_split ((((List.range 148).drop 37).drop 37).drop 26) Q2.checkRows2 16,
      all_split (((((List.range 148).drop 37).drop 37).drop 26).drop 16) Q2.checkRows2 8,
      all_split ((((((List.range 148).drop 37).drop 37).drop 26).drop 16).drop 8) Q2.checkRows2 8,
      all_split (((((((List.range 148).drop 37).drop 37).drop 26).drop 16).drop 8).drop 8)
        Q2.checkRows2 8]
  simp only [rowsChunk2a, rowsChunk2b, rowsChunk2c, rowsChunk2d, rowsChunk2e, rowsChunk2f,
    rowsChunk2g, rowsChunk2h, Bool.and_self]

theorem checkBasis2_all : (List.range 148).all Q2.checkBasis2 = true :=
  all148_of_chunks Q2.checkBasis2 basisChunk2_0 basisChunk2_1 basisChunk2_2 basisChunk2_3

theorem checkValid2_all : (List.range 148).all Q2.checkValid2 = true :=
  all148_of_chunks Q2.checkValid2 validChunk2_0 validChunk2_1 validChunk2_2 validChunk2_3

theorem checkNodup2_all : (List.range 148).all Q2.checkNodup2 = true :=
  all148_of_chunks Q2.checkNodup2 nodupChunk2_0 nodupChunk2_1 nodupChunk2_2 nodupChunk2_3

theorem checkCount2_all : (List.range 148).all Q2.checkCount2 = true :=
  all148_of_chunks Q2.checkCount2 countChunk2_0 countChunk2_1 countChunk2_2 countChunk2_3

namespace Q2

/-! ## The per-representative API -/

/-- The q=2 echelon basis of `reps r`, as embedded. -/
def basisAt2 (r : Fin 148) : List Coordinates := repBases2.getD r.val []

/-- The q=2 linear-character exponent vectors of `reps r`, as embedded. -/
def charsAt2 (r : Fin 148) : List (List (ZMod 25)) := repChars2.getD r.val []

/-- **Validity.** Every embedded vector of `reps r` is a genuine `charOK2`-valid
q=2 character (kills every q=2 collection relator of the echelon basis). -/
theorem charsAt2_valid (r : Fin 148) : (charsAt2 r).all (charOK2 (basisAt2 r)) = true := by
  have hrows := checker_at checkRows2_all r
  have hvalid := checker_at checkValid2_all r
  simp only [checkRows2, Bool.and_eq_true, decide_eq_true_eq] at hrows
  obtain ⟨hPR, hCR⟩ := hrows
  exact all_charOK_of_rows2 (basisAt2 r) (charsAt2 r) _ _ hPR hCR hvalid

/-- **Distinctness.** The embedded q=2 character list of `reps r` is duplicate-free. -/
theorem charsAt2_nodup (r : Fin 148) : (charsAt2 r).Nodup := by
  have h := checker_at checkNodup2_all r
  simp only [checkNodup2] at h
  exact of_decide_eq_true h

/-- **Count.** The number of embedded q=2 characters of `reps r` is the aggregate
`charCounts` entry (`= |H^ab|`, twin-invariant). -/
theorem charsAt2_count (r : Fin 148) : (charsAt2 r).length = charCounts.getD r.val 0 := by
  have h := checker_at checkCount2_all r
  simp only [checkCount2] at h
  exact Nat.eq_of_beq_eq_true h

/-- **Basis identification.** The embedded basis is the genuine q=2 echelon basis of
`reps r` (`Q2.getB` at the representative's `classRepsData` index). -/
theorem basisAt2_eq (r : Fin 148) : basisAt2 r = getB (classRepsData.getD r.val 0) := by
  have h := checker_at checkBasis2_all r
  simp only [checkBasis2] at h
  exact of_decide_eq_true h

/-- `reps r` is generated by its embedded q=2 echelon basis. -/
theorem reps_eq_ofList2 (r : Fin 148) :
    reps r = ofList 2 hq2 (basisAt2 r) := by
  rw [basisAt2_eq]; rfl

/-! ## Aggregate: the total `5236` from certified per-representative counts -/

/-- **Certified headline total (q=2).** The sum over the 148 representatives of the
*certified* q=2 character counts is `5236` — each summand `(charsAt2 r).length` is
kernel-verified equal to its `charCounts` entry, and those entries sum to `5236`. -/
theorem charsTotal2_certified :
    ((List.range 148).map (fun r => (repChars2.getD r []).length)).sum = 5236 := by
  have hmap : (List.range 148).map (fun r => (repChars2.getD r []).length)
      = (List.range 148).map (fun r => charCounts.getD r 0) := by
    apply List.map_congr_left
    intro r hr
    have h := (List.all_eq_true.mp checkCount2_all) r hr
    simp only [checkCount2] at h
    exact Nat.eq_of_beq_eq_true h
  rw [hmap]
  decide

end Q2

end LeanDring.P5Presentation
