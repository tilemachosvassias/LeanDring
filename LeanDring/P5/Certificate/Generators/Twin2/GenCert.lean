/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SubgroupInventory.Twin2.AllSubgroups

/-!
# `#eval` generator: per-subgroup Frattini certificates for `Coordinate 2`

**Outside the build closure.** Nothing in the library imports this file; it
carries no part of the trust base and is kept for provenance, as the script that
produced the certificates embedded in
`LeanDring/P5/Certificate/SubgroupInventory/Twin2/FrattiniCert.lean`. Everything
it emits is untrusted and is re-checked there by the kernel checker `fratCertB`.

Per subgroup `H` of `Coordinate 2` it emits the inventory index of `Φ(H)`, the
indices of the maximal subgroups of `H`, and a witness word for each generator
of `Φ(H)` expressing it as a product of commutators and 5th powers of elements
of `H`. `checkEmit` verifies before emission that every word evaluates to the
generator it is recorded against.
-/

namespace LeanDring.P5Gen2Cert

open LeanDring.P5Presentation
open LeanDring.P5Presentation.Q2
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

def subEq (A B : List Vec) : Bool :=
  A.all (fun g => decide (reduceBy B g = z5)) && B.all (fun g => decide (reduceBy A g = z5))

/-- `Q2.allBases` re-typed as raw coordinate vectors (definitional). -/
def allBasesV : List (List Vec) := Q2.allBases

def baseIdx (K : List Vec) : Nat := (allBasesV.findIdx? (fun b => subEq b K)).getD 99999

/-! ### Signed-atom witness words -/
abbrev WAtom := Bool × Bool × Vec × Vec
abbrev Word := List WAtom

def atomVal : WAtom → Vec
  | (inv, isPow, a, b) =>
    let v := if isPow then mpow 2 a 5 else commutator a b
    if inv then invC 2 v else v

def wordVal (w : Word) : Vec := w.foldl (fun acc at' => mulC 2 acc (atomVal at')) z5

def wInv (w : Word) : Word := (w.reverse).map (fun (inv, p, a, b) => (!inv, p, a, b))
def wMul (w1 w2 : Word) : Word := w1 ++ w2
def wPow (w : Word) (n : Nat) : Word := (List.replicate n w).flatten

abbrev VW := Vec × Word

def mulVW (x y : VW) : VW := (mulC 2 x.1 y.1, wMul x.2 y.2)
def invVW (x : VW) : VW := (invC 2 x.1, wInv x.2)
def powVW (x : VW) (n : Nat) : VW := (mpow 2 x.1 n, wPow x.2 n)

def clearStepVW (p x : VW) : VW :=
  mulVW x (powVW (invVW p) (coordAt x.1 (pivotDepth p.1)).val)

def reduceByVW (pivots : List VW) (v : VW) : VW :=
  pivots.foldl (fun acc p => clearStepVW p acc) v

def insertSortedVW (r1 : VW) : List VW → List VW
  | [] => [r1]
  | p :: ps => if pivotDepth r1.1 < pivotDepth p.1 then r1 :: p :: ps else p :: insertSortedVW r1 ps

def commutatorVW (a b : VW) : VW :=
  mulVW (mulVW (mulVW a b) (invVW a)) (invVW b)

partial def closeFromVW (pivots : List VW) : List VW → List VW
  | [] => pivots
  | v :: vs =>
    let r := reduceByVW pivots v
    if r.1 = z5 then closeFromVW pivots vs
    else
      let d := pivotDepth r.1
      let r1 := powVW r (leadInv (coordAt r.1 d))
      let backsub := pivots.map (fun p =>
        if coordAt p.1 d ≠ 0 then clearStepVW r1 p else p)
      let pivots2 := insertSortedVW r1 backsub
      let comms := pivots.flatMap (fun p => [commutatorVW r1 p, commutatorVW p r1])
      closeFromVW pivots2 (vs ++ (powVW r1 5) :: comms)

def frattiniVW (B : List Vec) : List VW :=
  let pows : List VW := B.map (fun b => (mpow 2 b 5, [(false, true, b, z5)]))
  let comms : List VW :=
    B.flatMap (fun b => B.map (fun b' => (commutator b b', [(false, false, b, b')])))
  closeFromVW [] (pows ++ comms)

def emitCert (B : List Vec) : Nat × Nat × List Nat × List (Vec × Word) :=
  let h := baseIdx B
  let phi := frattini B
  let phiIdx := baseIdx phi
  let maxs := maximalsOf B
  let maxIdxs := maxs.map baseIdx
  let phiVW := frattiniVW B
  let wits : List (Vec × Word) := phiVW.map (fun vw => (vw.1, vw.2))
  (h, phiIdx, maxIdxs, wits)

def checkEmit (B : List Vec) : Bool :=
  let phiVW := frattiniVW B
  let phi := frattini B
  phiVW.all (fun vw => decide (wordVal vw.2 = vw.1)) &&
  subEq (phiVW.map (·.1)) phi

def renderVec (v : Vec) : String :=
  s!"({v.1},{v.2.1},{v.2.2.1},{v.2.2.2.1},{v.2.2.2.2})"

def renderAtom (a : WAtom) : String :=
  s!"({a.1},{a.2.1},{renderVec a.2.2.1},{renderVec a.2.2.2})"

def renderWord (w : Word) : String :=
  "[" ++ String.intercalate "," (w.map renderAtom) ++ "]"

def renderWit (vwit : Vec × Word) : String :=
  s!"({renderVec vwit.1},{renderWord vwit.2})"

def renderCert (B : List Vec) : String :=
  let (h, phiIdx, maxIdxs, wits) := emitCert B
  let maxs := "[" ++ String.intercalate "," (maxIdxs.map toString) ++ "]"
  let witsS := "[" ++ String.intercalate "," (wits.map renderWit) ++ "]"
  s!"  ({h}, \{ phiIdx := {phiIdx}, maxIdxs := {maxs}, wits := {witsS} })"

def renderStratum (bs : List (List Vec)) : String :=
  String.intercalate ",\n" (bs.map renderCert)

def sub0V : List (List Vec) := Q2.sub0
def sub1V : List (List Vec) := Q2.sub1
def sub2V : List (List Vec) := Q2.sub2
def sub3V : List (List Vec) := Q2.sub3
def sub4V : List (List Vec) := Q2.sub4
def sub5V : List (List Vec) := Q2.sub5

-- Sanity: all certs' witness words reproduce their Φ generators.
#eval (sub0V ++ sub1V ++ sub2V ++ sub3V ++ sub4V ++ sub5V).all checkEmit

#eval IO.println ("CERT0::" ++ renderStratum sub0V)
#eval IO.println ("CERT1::" ++ renderStratum sub1V)
#eval IO.println ("CERT2::" ++ renderStratum sub2V)
#eval IO.println ("CERT3::" ++ renderStratum sub3V)
#eval IO.println ("CERT4::" ++ renderStratum sub4V)
#eval IO.println ("CERT5::" ++ renderStratum sub5V)

end LeanDring.P5Gen2Cert
