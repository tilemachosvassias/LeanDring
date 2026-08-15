/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin1.CharCert
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.ConjClasses

/-!
# `#eval` generator: linear-character data for `Coordinate 2`

**Outside the build closure.** Nothing in the library imports this file; it
carries no part of the trust base and is kept for provenance, as the script that
produced the character data embedded in
`LeanDring/P5/Certificate/Characters/Twin2/CharData.lean`. Run it by hand
(`lake env lean` on this file). Everything it emits is untrusted and is
re-checked where it is embedded by kernel `decide`.

It works over the `q = 2` echelon bases `bases2 r = Q2.getB (classRepsData r)`,
which differ from the `q = 1` bases — the subgroups are the same sets, but the
echelon reduction is performed under the second group law — and computes the pc
collection-relation rows and the linear-character exponent vectors with
`mulC 2` / `mpow 2` / `clearStep 2`. The diagnostic `#eval`s compare the result
against the `q = 1` data class by class: how many echelon bases, power rows,
commutator rows and character-vector sets differ, and that the per-class
character counts (total 5236) are unchanged.
-/

namespace LeanDring.P5Gen2Char

open LeanDring.P5Presentation
open Fin.NatCast

/-- q=2 echelon bases of the 148 reps (from the q=2 subgroup inventory). -/
def bases2 : List (List Coordinates) :=
  (LeanDring.P5Presentation.Q2.classRepsData).map (fun i => LeanDring.P5Presentation.Q2.getB i)

def expNat2 (B : List Coordinates) (x : Coordinates) : List Nat :=
  (B.foldl (fun (acc : Coordinates × List Nat) p =>
      (clearStep 2 p acc.1, acc.2 ++ [(coordAt acc.1 (pivotDepth p)).val])) (x, [])).2
def expVec2 (B : List Coordinates) (x : Coordinates) : List (ZMod 25) :=
  (expNat2 B x).map (fun n => (n : ZMod 25))
def commutatorC2 (a b : Coordinates) : Coordinates :=
  mulC 2 (mulC 2 (mulC 2 a b) (invC 2 a)) (invC 2 b)
def powRowsE2 (B : List Coordinates) : List (List (ZMod 25)) :=
  (List.range B.length).map (fun i => expVec2 B (mpow 2 (B.getD i zc) 5))
def commRowsE2 (B : List Coordinates) : List (List (ZMod 25)) :=
  (List.range B.length).flatMap (fun i =>
    ((List.range B.length).filter (fun j => Nat.blt i j)).map (fun j =>
      expVec2 B (commutatorC2 (B.getD i zc) (B.getD j zc))))
def charOK2 (B : List Coordinates) (e : List (ZMod 25)) : Bool :=
  charOKrows (powRowsE2 B) (commRowsE2 B) e

def zmodAll : List (ZMod 25) := List.finRange 25
def allVecs : Nat → List (List (ZMod 25))
  | 0 => [[]]
  | k + 1 => zmodAll.flatMap (fun a => (allVecs k).map (fun v => a :: v))
def solve2 (B : List Coordinates) : List (List (ZMod 25)) :=
  (allVecs B.length).filter (charOK2 B)

def keyOf (e : List (ZMod 25)) : List Nat := e.map (fun a => a.val)
def sortVecs (vs : List (List (ZMod 25))) : List (List Nat) :=
  (vs.map keyOf).mergeSort (fun a b => decide (a.foldl (fun s x => s*100+x) 0
    ≤ b.foldl (fun s x => s*100+x) 0))

/-! ### Structural comparison of the twin data (each on its own echelon basis) -/

-- 0. do the echelon bases themselves differ between the twins?
#eval do
  let mut basesDiff : List Nat := []
  for r in List.range 148 do
    if bases2.getD r [] ≠ repBases.getD r [] then basesDiff := basesDiff ++ [r]
  IO.println s!"BASES q2 vs q1: #different={basesDiff.length}"
  IO.println s!"  bases-diff reps={basesDiff}"

-- 1. q2 power/commutator rows (on q2 bases) vs q1 embedded rows (on q1 bases)
#eval do
  let mut prDiff : List Nat := []
  let mut crDiff : List Nat := []
  for r in List.range 148 do
    let B := bases2.getD r []
    if powRowsE2 B ≠ repPR.getD r [] then prDiff := prDiff ++ [r]
    if commRowsE2 B ≠ repCR.getD r [] then crDiff := crDiff ++ [r]
  IO.println s!"ROWS q2 vs q1: #powRow-diff={prDiff.length}, #commRow-diff={crDiff.length}"
  IO.println s!"  powRow-diff reps={prDiff}"
  IO.println s!"  commRow-diff reps={crDiff}"

-- 2. character vector SETS (k≤3): does q2's solution set match q1's repChars,
-- and do counts match?
#eval do
  let mut setEq : List Nat := []
  let mut setNe : List Nat := []
  let mut countNe : List Nat := []
  for r in List.range 148 do
    let B := bases2.getD r []
    if B.length ≤ 3 then
      let s2 := solve2 B
      let q1 := repChars.getD r []
      if s2.length ≠ q1.length then countNe := countNe ++ [r]
      if sortVecs s2 = sortVecs q1 then setEq := setEq ++ [r] else setNe := setNe ++ [r]
  let setsMsg := s!"SETS (k≤3): set-equal={setEq.length}, set-different={setNe.length}"
  IO.println s!"{setsMsg}, count-different={countNe.length}"
  IO.println s!"  set-different reps={setNe}"
  IO.println s!"  count-different reps={countNe}"

-- 3. for k≥4, is each q1 char vector still charOK2-valid on the q2 basis?
-- (count-preservation ⇒ set equality)
#eval do
  let mut ok : List Nat := []
  let mut bad : List Nat := []
  for r in List.range 148 do
    let B := bases2.getD r []
    if B.length ≥ 4 then
      if (repChars.getD r []).all (charOK2 B) then ok := ok ++ [r] else bad := bad ++ [r]
  let k4Msg := s!"k≥4: q1 chars charOK2-valid on q2 basis for {ok.length} reps"
  IO.println s!"{k4Msg}, invalid for {bad.length}"
  IO.println s!"  invalid reps={bad}"

/-! ### Literal emitters -/

def rvec (e : List (ZMod 25)) : String :=
  "[" ++ String.intercalate "," (e.map (fun a => toString a.val)) ++ "]"
def rvecs (vs : List (List (ZMod 25))) : String :=
  "[" ++ String.intercalate ", " (vs.map rvec) ++ "]"
def rbase (b : List Coordinates) : String :=
  "[" ++ String.intercalate "," (b.map (fun v =>
    s!"({v.1.val},{v.2.1.val},{v.2.2.1.val},{v.2.2.2.1.val},{v.2.2.2.2.val})")) ++ "]"

#eval do
  IO.println "=====REPBASES2====="
  for r in List.range 148 do IO.println (" " ++ rbase (bases2.getD r []) ++ ",")
#eval do
  IO.println "=====REPPR2====="
  for r in List.range 148 do IO.println (" " ++ rvecs (powRowsE2 (bases2.getD r [])) ++ ",")
#eval do
  IO.println "=====REPCR2====="
  for r in List.range 148 do IO.println (" " ++ rvecs (commRowsE2 (bases2.getD r [])) ++ ",")
#eval do
  IO.println "=====REPCHARS2====="
  for r in List.range 148 do
    let B := bases2.getD r []
    let cs := if B.length ≤ 3 then solve2 B else repChars.getD r []
    IO.println (" " ++ rvecs cs ++ ",")

-- final self-check: embedded repChars2 all charOK2-valid, nodup, count = charCounts (q1 list)
#eval do
  let mut allValid := true
  let mut allCount := true
  let mut total := 0
  for r in List.range 148 do
    let B := bases2.getD r []
    let cs := if B.length ≤ 3 then solve2 B else repChars.getD r []
    total := total + cs.length
    if !(cs.all (charOK2 B)) then allValid := false
    if cs.length ≠ charCounts.getD r 0 then allCount := false
    if cs.dedup.length ≠ cs.length then allCount := false
  IO.println s!"REPCHARS2 CHECK: allValid={allValid}, countAndNodupOK={allCount}, total={total}"

end LeanDring.P5Gen2Char
