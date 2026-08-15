/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Generators.Twin2.GenCert
import LeanDring.P5.Certificate.Characters.Twin2.CharAssembly
import LeanDring.P5.Certificate.SubgroupInventory.Twin2.FrattiniCert
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.ConjClasses

/-!
# `#eval` generator: normalizer-orbit data for `Coordinate 2`

**Outside the build closure.** Nothing in the library imports this file; it
carries no part of the trust base and is kept for provenance, as the script that
produced the normalizer-orbit data embedded in
`LeanDring/P5/Certificate/ConjugacyClasses/Twin2/NormOrbitData.lean`. Run it by
hand (`lake env lean` on this file) to regenerate `norm_data2.txt`. Everything
it emits is untrusted and is re-checked where it is embedded by kernel `decide`.

This is the `q = 2` counterpart of
`LeanDring/P5/Certificate/Generators/Twin1/NormGen.lean`. The subgroup lattice,
conjugation table and class data coincide with `q = 1`, so `normIdxData` — the
normalizer subgroup indices — comes out identical; `normGens` and `normMats`
depend on the group law and are recomputed; the character-orbit data diverges on
the 34 representatives whose character sets are reshaped by the second law. The
aggregate diagnostics printed by the run must still come out as
`Σ orbits = 2724` with the order-fibre `{1: 148, 5: 2376, 25: 200}`.
-/

namespace LeanDring.P5Presentation.Q2

open Fin.NatCast

def fin5s : List (Fin 5) := [0, 1, 2, 3, 4]

/-- All 3125 coordinate vectors. -/
def allVecs : List Coordinates :=
  fin5s.flatMap (fun a => fin5s.flatMap (fun b => fin5s.flatMap (fun c =>
    fin5s.flatMap (fun d => fin5s.map (fun e => (a, b, c, d, e))))))

/-- Elements of `G` normalizing `H` (basis `B`): `g` with `g gᵢ g⁻¹ ∈ H` ∀ gen
(q=2 group law). -/
def normElems (B : List Coordinates) : List Coordinates :=
  allVecs.filter (fun g => B.all (fun gen => siftB 2 B (conjC 2 g gen)))

/-- Echelon basis of `N_G(H)` (basis `B`), q=2 echelon reduction. -/
def normBasis (B : List Coordinates) : List Coordinates :=
  P5Gen2Cert.closeFrom [] (normElems B)

/-- The conjugation matrix of `n` on `H`'s char vectors (q=2): row `i` = expVec2
of `n⁻¹ gᵢ n` in `B`-coordinates. -/
def conjMatrix (B : List Coordinates) (n : Coordinates) : List (List (ZMod 25)) :=
  B.map (fun gi => expVec2 B (conjC 2 (invC 2 n) gi))

/-- The action of a matrix `M` on a char exponent vector `e`. -/
def actVec (M : List (List (ZMod 25))) (e : List (ZMod 25)) : List (ZMod 25) :=
  M.map (fun row => dotZ row e)

/-- Order (1, 5 or 25) of a char exponent vector over ZMod 25. -/
def charOrd (e : List (ZMod 25)) : Nat :=
  let g := e.foldl (fun acc z => Nat.gcd acc z.val) 25
  25 / g

/-! ## Orbit BFS -/

partial def bfsComp (adj : Nat → List Nat) (comp : Array Nat) (cid : Nat) :
    List Nat → Array Nat
  | [] => comp
  | x :: rest =>
    if comp[x]! != 0 then bfsComp adj comp cid rest
    else bfsComp adj (comp.set! x cid) cid (adj x ++ rest)

partial def flood (n : Nat) (adj : Nat → List Nat) : Array Nat := Id.run do
  let mut comp := Array.replicate n 0
  let mut cid := 0
  for s in [0:n] do
    if comp[s]! == 0 then
      cid := cid + 1
      comp := bfsComp adj comp cid [s]
  return comp

/-- The induced permutation position table: `actPos[k][p]` = index in `chars` of
`actVec Ms[k] chars[p]`. -/
def actPosTab (chars : List (List (ZMod 25))) (Ms : List (List (List (ZMod 25)))) :
    List (List Nat) :=
  Ms.map (fun M => chars.map (fun e => chars.idxOf (actVec M e)))

/-- BFS orbit data: per position `(label, isRep, treeGen, treePar, depth)`. -/
def orbitData (n : Nat) (actPos : List (List Nat)) :
    Array Nat × Array Bool × Array Nat × Array Nat × Array Nat := Id.run do
  let mut label := Array.replicate n n
  let mut isRep := Array.replicate n false
  let mut tGen := Array.replicate n 0
  let mut tPar := Array.replicate n 0
  let mut depth := Array.replicate n 0
  let ng := actPos.length
  for s in [0:n] do
    if label[s]! == n then
      label := label.set! s s
      isRep := isRep.set! s true
      let mut queue := [s]
      while !queue.isEmpty do
        let x := queue.headD 0
        queue := queue.tailD []
        for k in [0:ng] do
          let y := ((actPos.getD k []).getD x 0)
          if label[y]! == n then
            label := label.set! y s
            tGen := tGen.set! y k
            tPar := tPar.set! y x
            depth := depth.set! y (depth[x]! + 1)
            queue := queue ++ [y]
  return (label, isRep, tGen, tPar, depth)

/-! ## Rendering -/

def renderNat (n : Nat) : String := toString n
def renderCoord (v : Coordinates) : String :=
  s!"({v.1},{v.2.1},{v.2.2.1},{v.2.2.2.1},{v.2.2.2.2})"
def renderCoordList (l : List Coordinates) : String :=
  "[" ++ String.intercalate "," (l.map renderCoord) ++ "]"
def renderNatList (l : List Nat) : String :=
  "[" ++ String.intercalate "," (l.map renderNat) ++ "]"
def renderBoolList (l : List Bool) : String :=
  "[" ++ String.intercalate "," (l.map (fun b => if b then "true" else "false")) ++ "]"
def renderZVec (e : List (ZMod 25)) : String :=
  "[" ++ String.intercalate "," (e.map (fun z => toString z.val)) ++ "]"
def renderMat (M : List (List (ZMod 25))) : String :=
  "[" ++ String.intercalate "," (M.map renderZVec) ++ "]"
def renderMats (Ms : List (List (List (ZMod 25)))) : String :=
  "[" ++ String.intercalate "," (Ms.map renderMat) ++ "]"
def renderNatLL (l : List (List Nat)) : String :=
  "[" ++ String.intercalate "," (l.map renderNatList) ++ "]"

-- Emit all q=2 normalizer-orbit data as Lean `def` literals + diagnostics.
#eval do
  let mut normIdxs : List Nat := []
  let mut gensAll : List String := []
  let mut matsAll : List String := []
  let mut actAll : List String := []
  let mut labAll : List String := []
  let mut isRepAll : List String := []
  let mut tGenAll : List String := []
  let mut tParAll : List String := []
  let mut tDepthAll : List String := []
  let mut totalOrbits : Nat := 0
  let mut fib1 : Nat := 0
  let mut fib5 : Nat := 0
  let mut fib25 : Nat := 0
  let mut idxMatch : Nat := 0
  for r in [0:148] do
    let ri := classRepsData.getD r 0
    let B := getB ri
    let Nb := normBasis B
    let chars := repChars2.getD r []
    let Ms := Nb.map (conjMatrix B)
    let n := chars.length
    let actPos := actPosTab chars Ms
    let (label, isRep, tGen, tPar, depth) := orbitData n actPos
    let idx := P5Gen2Cert.baseIdx Nb
    normIdxs := normIdxs ++ [idx]
    gensAll := gensAll ++ [renderCoordList Nb]
    matsAll := matsAll ++ [renderMats Ms]
    actAll := actAll ++ [renderNatLL actPos]
    labAll := labAll ++ [renderNatList label.toList]
    isRepAll := isRepAll ++ [renderBoolList isRep.toList]
    tGenAll := tGenAll ++ [renderNatList tGen.toList]
    tParAll := tParAll ++ [renderNatList tPar.toList]
    tDepthAll := tDepthAll ++ [renderNatList depth.toList]
    -- diagnostics: orbit count + fibre by order of orbit-rep vector
    for p in [0:n] do
      if isRep.getD p false then
        totalOrbits := totalOrbits + 1
        let o := charOrd (chars.getD p [])
        if o == 1 then fib1 := fib1 + 1
        else if o == 5 then fib5 := fib5 + 1
        else fib25 := fib25 + 1
  let file ← IO.FS.Handle.mk "norm_data2.txt" IO.FS.Mode.write
  file.putStrLn s!"def normIdxData : List Nat := {renderNatList normIdxs}"
  file.putStrLn ""
  file.putStrLn s!"def normGens : List (List Coordinates) :=\n[{String.intercalate ",\n" gensAll}]"
  file.putStrLn ""
  let matsJoined := String.intercalate ",\n" matsAll
  file.putStrLn s!"def normMats : List (List (List (List (ZMod 25)))) :=\n[{matsJoined}]"
  file.putStrLn ""
  file.putStrLn s!"def normActPos : List (List (List Nat)) :=\n[{String.intercalate ",\n" actAll}]"
  file.putStrLn ""
  file.putStrLn s!"def normLabel : List (List Nat) :=\n[{String.intercalate ",\n" labAll}]"
  file.putStrLn ""
  file.putStrLn s!"def normIsRep : List (List Bool) :=\n[{String.intercalate ",\n" isRepAll}]"
  file.putStrLn ""
  file.putStrLn s!"def normTreeGen : List (List Nat) :=\n[{String.intercalate ",\n" tGenAll}]"
  file.putStrLn ""
  file.putStrLn s!"def normTreePar : List (List Nat) :=\n[{String.intercalate ",\n" tParAll}]"
  file.putStrLn ""
  file.putStrLn s!"def normTreeDepth : List (List Nat) :=\n[{String.intercalate ",\n" tDepthAll}]"
  IO.println s!"emitted norm_data2.txt"
  IO.println s!"TOTAL ORBITS (pairClassTotal) = {totalOrbits}   [expect 2724]"
  let fibreMsg := s!"FIBRE by order: order1 = {fib1}, order5 = {fib5}, order25 = {fib25}"
  IO.println s!"{fibreMsg}   [expect 148/2376/200]"
  -- comparison with the q=1 normIdxData: all 148 positions must agree
  let q1idx : List Nat := [
      675, 648, 608, 603, 598, 593, 647, 646, 645, 669, 644, 593, 675, 588, 593, 593, 593, 593,
      593, 675, 669, 669, 669, 669, 675, 675, 675, 675, 644, 645, 646, 647, 648, 644, 645, 646,
      647, 648, 644, 645, 646, 647, 648, 644, 645, 646, 647, 648, 644, 645, 646, 647, 648, 675,
      669, 644, 644, 644, 644, 644, 645, 645, 645, 645, 645, 646, 646, 646, 646, 646, 647, 647,
      647, 647, 647, 648, 648, 648, 648, 648, 675, 675, 675, 675, 675, 669, 669, 669, 669, 669,
      675, 675, 675, 675, 675, 675, 675, 675, 675, 675, 675, 675, 675, 675, 675, 675, 675, 675,
      675, 675, 675, 675, 675, 675, 675, 675, 675, 675, 675, 675, 675, 675, 675, 675, 675, 675,
      675, 675, 675, 675, 675, 675, 675, 675, 675, 675, 675, 675, 675, 675, 675, 675, 675, 675,
      675, 675, 675, 675
    ]
  for r in [0:148] do
    if normIdxs.getD r 0 == q1idx.getD r 0 then idxMatch := idxMatch + 1
  IO.println s!"normIdxData vs q=1: {idxMatch}/148 positions identical"

end LeanDring.P5Presentation.Q2
