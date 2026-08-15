/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.ComputableModel.Twin1.Cgs

/-!
# `#eval` generator: the subgroup inventory of `Coordinate 2`

**Outside the build closure.** Nothing in the library imports this file; it
carries no part of the trust base and is kept for provenance, as the script that
produced the subgroup-inventory data embedded in
`LeanDring/P5/Certificate/SubgroupInventory/Twin2/AllSubgroups.lean`. Everything
it emits is untrusted and is re-checked there by kernel `decide`.

Structurally identical to the `Coordinate 1` generator
(`LeanDring/P5/Certificate/Generators/Twin1/Gen.lean`), with every group
operation taken at `q = 2` (`mulC 2`, `invC 2`, `mpow 2`, `clearStep 2`) so that
the echelon reduction is performed under the second group law. The order-`5`
stratum is emitted in six blocks of 26 to keep each downstream `decide` inside
the elaborator budget.
-/

namespace LeanDring.P5Gen2

open LeanDring.P5Presentation
open Fin.NatCast

abbrev Vec := Coordinates
def z5 : Vec := (0,0,0,0,0)

def leadInv (t : Fin 5) : ℕ :=
  match t.val with | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | _ => 0

def reduceBy (pivots : List Vec) (v : Vec) : Vec :=
  pivots.foldl (fun acc p => clearStep 2 p acc) v

def commutator (a b : Vec) : Vec :=
  mulC 2 (mulC 2 (mulC 2 a b) (invC 2 a)) (invC 2 b)

def insertSorted (r1 : Vec) : List Vec → List Vec
  | [] => [r1]
  | p :: ps => if pivotDepth r1 < pivotDepth p then r1 :: p :: ps else p :: insertSorted r1 ps

partial def closeFrom (pivots : List Vec) : List Vec → List Vec
  | [] => pivots
  | v :: vs =>
    let r := reduceBy pivots v
    if r = z5 then closeFrom pivots vs
    else
      let d := pivotDepth r
      let r1 := mpow 2 r (leadInv (coordAt r d))
      let backsub := pivots.map (fun p =>
        if coordAt p d ≠ 0 then clearStep 2 r1 p else p)
      let pivots2 := insertSorted r1 backsub
      let comms := pivots.flatMap (fun p => [commutator r1 p, commutator p r1])
      closeFrom pivots2 (vs ++ (mpow 2 r1 5) :: comms)

def closure (gens : List Vec) : List Vec := closeFrom [] gens

def fin5s : List (Fin 5) := [0,1,2,3,4]

def frattini (B : List Vec) : List Vec :=
  let pows := B.map (fun b => mpow 2 b 5)
  let comms := (B.flatMap (fun b => B.map (fun b' => commutator b b')))
  closeFrom [] (pows ++ comms)

def freeGens (B Phi : List Vec) : List Vec :=
  (B.foldl (fun (acc : List Vec × List Vec) b =>
      let (span, frees) := acc
      if reduceBy span b = z5 then acc
      else (closeFrom span [b], frees ++ [b])) (Phi, [])).2

def scal (v : Vec) (c : Fin 5) : Vec := mpow 2 v c.val

def allTails : ℕ → List (List (Fin 5))
  | 0 => [[]]
  | n+1 => (allTails n).flatMap (fun t => fin5s.map (fun a => a :: t))

def functionals : ℕ → List (List (Fin 5))
  | 0 => []
  | r+1 =>
    (allTails r).map (fun t => (1 : Fin 5) :: t) ++
    (functionals r).map (fun f => (0 : Fin 5) :: f)

def maximalsOf (B : List Vec) : List (List Vec) :=
  let Phi := frattini B
  let F := freeGens B Phi
  let r := F.length
  if r = 0 then []
  else (functionals r).map (fun φ =>
    let k := (φ.zipIdx.filter (fun p => p.1 ≠ 0)).headD ((0:Fin 5),0) |>.2
    let Fk := F.getD k z5
    let kerB := (F.zipIdx.filter (fun p => p.2 < k)).map (fun p => p.1) ++
      (F.zipIdx.filter (fun p => p.2 > k)).map (fun p =>
        mulC 2 p.1 (scal (invC 2 Fk) (φ.getD p.2 0)))
    closeFrom Phi kerB)

partial def genAllDown : List (List Vec) :=
  let top : List Vec := closure [(1,0,0,0,0),(0,1,0,0,0),(0,0,1,0,0)]
  let rec loop (frontier seen : List (List Vec)) : List (List Vec) :=
    match frontier with
    | [] => seen
    | H :: rest =>
      let mem (L : List (List Vec)) (K : List Vec) : Bool := L.any (fun s => decide (s = K))
      let newSubs := (maximalsOf H).foldl (fun acc M =>
        if mem seen M || mem acc M then acc else M :: acc) []
      loop (rest ++ newSubs) (seen ++ newSubs)
  loop [top] [top]

def allData : List (List Vec) := genAllDown

def subEq (A B : List Vec) : Bool :=
  A.all (fun g => decide (reduceBy B g = z5)) && B.all (fun g => decide (reduceBy A g = z5))

def allDataSem : List (List Vec) :=
  allData.foldl (fun acc K => if acc.any (fun s => subEq s K) then acc else K :: acc) []

def renderVec (v : Vec) : String :=
  s!"({v.1},{v.2.1},{v.2.2.1},{v.2.2.2.1},{v.2.2.2.2})"

def renderBase (b : List Vec) : String :=
  "[" ++ String.intercalate "," (b.map renderVec) ++ "]"

/-- The authoritative q=2 subgroups, stratified by order 5^0..5^5. -/
def strat (k : ℕ) : List (List Vec) :=
  (allDataSem.filter (fun s => s.length = k))

-- Provenance cross-checks.
#eval allData.length
#eval allDataSem.length
#eval (List.range 6).map (fun k => (strat k).length)

/-- Render a stratum (or slice) as a comma+newline-separated list of bases. -/
def renderStratum (bs : List (List Vec)) : String :=
  String.intercalate ",\n  " (bs.map renderBase)

-- Emit each stratum. The order-5 stratum is chunked into 6 blocks of 26 so that
-- each well-formedness `decide` downstream stays inside the elaborator budget.
#eval IO.println ("SUB0::" ++ renderStratum (strat 0))
#eval IO.println ("SUB1_0::" ++ renderStratum ((strat 1).take 26))
#eval IO.println ("SUB1_1::" ++ renderStratum (((strat 1).drop 26).take 26))
#eval IO.println ("SUB1_2::" ++ renderStratum (((strat 1).drop 52).take 26))
#eval IO.println ("SUB1_3::" ++ renderStratum (((strat 1).drop 78).take 26))
#eval IO.println ("SUB1_4::" ++ renderStratum (((strat 1).drop 104).take 26))
#eval IO.println ("SUB1_5::" ++ renderStratum (((strat 1).drop 130).take 26))
#eval IO.println ("SUB2::" ++ renderStratum (strat 2))
#eval IO.println ("SUB3::" ++ renderStratum (strat 3))
#eval IO.println ("SUB4::" ++ renderStratum (strat 4))
#eval IO.println ("SUB5::" ++ renderStratum (strat 5))

end LeanDring.P5Gen2
