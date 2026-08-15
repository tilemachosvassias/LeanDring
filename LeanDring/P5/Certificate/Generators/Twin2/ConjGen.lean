/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SubgroupInventory.Twin2.FrattiniCert

/-!
# `#eval` generator: subgroup-conjugacy data for `Coordinate 2`

**Outside the build closure.** Nothing in the library imports this file; it
carries no part of the trust base and is kept for provenance, as the script that
produced the conjugacy data embedded in
`LeanDring/P5/Certificate/ConjugacyClasses/Twin2/ConjData.lean` and the
`Conj2R` chunks. Run it by hand (`lake env lean` on this file) to regenerate
`conj_data2.txt`. Everything it emits is untrusted and is re-checked where it is
embedded by kernel `decide`.

It builds the 5×676 table of "conjugate base `i` by the `k`-th pc generator",
then floods that table to obtain the subgroup conjugacy classes with a BFS
spanning tree (parent generator, parent index, depth) per subgroup. The run also
prints the class statistics, which must come out as 148 classes of which 71 are
normal.
-/

namespace LeanDring.P5Presentation

open LeanDring.P5Presentation.Q2
open Fin.NatCast

def numSubs2 : Nat := 676

/-- The `k`-th standard pc generator as a raw coordinate vector. -/
def gkVec2 (k : Nat) : Coordinates :=
  match k with
  | 0 => (1,0,0,0,0)
  | 1 => (0,1,0,0,0)
  | 2 => (0,0,1,0,0)
  | 3 => (0,0,0,1,0)
  | _ => (0,0,0,0,1)

def bases2 : List (List Coordinates) := Q2.allBasesRaw

/-- Target index `j` of the conjugation move `(k, i)`: the unique inventory base
`j` of the same order into which every generator of base `i`, conjugated by the
`k`-th generator, sifts. (Exactly the datum `conjEntryOK2` re-checks.) -/
def conjMoveGen2 (k i : Nat) : Nat :=
  let src := bases2.getD i []
  let g := gkVec2 k
  let conj := src.map (fun x => conjC 2 g x)
  let len := src.length
  match bases2.zipIdx.find? (fun p => p.1.length == len && conj.all (fun x => siftB 2 p.1 x)) with
  | some p => p.2
  | none => 99999

/-- The 5×676 conjugation index table as a nested `Array`. -/
def conjTabArr2 : Array (Array Nat) := Id.run do
  let mut rows := #[]
  for k in [0:5] do
    let mut row := Array.mkEmpty numSubs2
    for i in [0:numSubs2] do
      row := row.push (conjMoveGen2 k i)
    rows := rows.push row
  return rows

/-- Class labels, representatives, BFS tree (parent gen/pred, depth), isRep. -/
def computeData2 :
    Array Nat × Array Nat × Array Bool × Array Nat × Array Nat × Array Nat × Array (Array Nat) :=
  Id.run do
  let ct := conjTabArr2
  let mut classOf : Array Nat := Array.replicate numSubs2 99999
  let mut isRep : Array Bool := Array.replicate numSubs2 false
  let mut parentK : Array Nat := Array.replicate numSubs2 0
  let mut parentJ : Array Nat := Array.replicate numSubs2 0
  let mut depth : Array Nat := Array.replicate numSubs2 0
  let mut classReps : Array Nat := #[]
  let mut nextLabel := 0
  for s in [0:numSubs2] do
    if classOf[s]! == 99999 then
      let label := nextLabel
      nextLabel := nextLabel + 1
      classReps := classReps.push s
      classOf := classOf.set! s label
      isRep := isRep.set! s true
      depth := depth.set! s 0
      let mut queue := [s]
      while !queue.isEmpty do
        let x := queue.headD 0
        queue := queue.tailD []
        for k in [0:5] do
          let y := (ct[k]!)[x]!
          if classOf[y]! == 99999 then
            classOf := classOf.set! y label
            parentK := parentK.set! y k
            parentJ := parentJ.set! y x
            depth := depth.set! y (depth[x]! + 1)
            queue := queue ++ [y]
  return (classOf, classReps, isRep, parentK, parentJ, depth, ct)

/-! ## Emission -/

def renderNat2 (n : Nat) : String := toString n
def renderNatList2 (l : List Nat) : String :=
  "[" ++ String.intercalate ", " (l.map renderNat2) ++ "]"
def renderBoolList2 (l : List Bool) : String :=
  "[" ++ String.intercalate ", " (l.map (fun b => if b then "true" else "false")) ++ "]"
def renderTab2 (t : List (List Nat)) : String :=
  "[" ++ String.intercalate ", " (t.map renderNatList2) ++ "]"

#eval do
  let (classOf, classReps, isRep, parentK, parentJ, depth, ct) := computeData2
  let ctList : List (List Nat) := (ct.toList).map (fun (a : Array Nat) => a.toList)
  -- Diagnostics
  let numClasses := classReps.size
  let anyMissing := ctList.any (fun row => row.any (fun j => j == 99999))
  let normalCount := classReps.toList.foldl (fun acc rep =>
      if (List.range 5).all (fun k => ((ct[k]!)[rep]!) == rep) then acc + 1 else acc) 0
  IO.println s!"NUM_SUBGROUPS::{numSubs2}"
  IO.println s!"NUM_CLASSES::{numClasses}"
  IO.println s!"NORMAL_COUNT::{normalCount}"
  IO.println s!"ANY_MISSING_MOVE::{anyMissing}"
  let file ← IO.FS.Handle.mk "conj_data2.txt" IO.FS.Mode.write
  file.putStrLn s!"def conjTab : List (List Nat) := {renderTab2 ctList}"
  file.putStrLn ""
  file.putStrLn s!"def classOfData : List Nat := {renderNatList2 classOf.toList}"
  file.putStrLn ""
  file.putStrLn s!"def classRepsData : List Nat := {renderNatList2 classReps.toList}"
  file.putStrLn ""
  file.putStrLn s!"def parentKData : List Nat := {renderNatList2 parentK.toList}"
  file.putStrLn ""
  file.putStrLn s!"def parentJData : List Nat := {renderNatList2 parentJ.toList}"
  file.putStrLn ""
  file.putStrLn s!"def depthData : List Nat := {renderNatList2 depth.toList}"
  file.putStrLn ""
  file.putStrLn s!"def isRepData : List Bool := {renderBoolList2 isRep.toList}"
  IO.println "emitted conj_data2.txt"

end LeanDring.P5Presentation
