/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Generators.Twin1.Gen
import LeanDring.P5.Certificate.Characters.Twin1.CharAssembly

/-!
# `#eval` generator: normalizer-orbit data for `Coordinate 1`

**Outside the build closure.** Nothing imports this file; it carries no part of
the trust base and is kept for provenance, as the script that produced the
normalizer-orbit data embedded in
`LeanDring/P5/Certificate/ConjugacyClasses/Twin1/NormOrbitData.lean`. Run it by
hand (`lake env lean` on this file) to regenerate `norm_data.txt`. Everything it
emits is untrusted and is re-checked by kernel `decide` where it is embedded.

For each of the 148 subgroup-class representatives it computes `N_G(H)`, its
echelon basis, the conjugation matrices of those generators on `H`'s certified
character vectors, and a BFS orbit partition of the characters under that
matrix action, with spanning-tree witnesses.
-/

namespace LeanDring.P5Presentation

open Fin.NatCast

/-- All 3125 coordinate vectors. -/
def allVecs : List Coordinates :=
  fin5s.flatMap (fun a => fin5s.flatMap (fun b => fin5s.flatMap (fun c =>
    fin5s.flatMap (fun d => fin5s.map (fun e => (a, b, c, d, e))))))

/-- Elements of `G` normalizing `H` (basis `B`): `g` with `g gᵢ g⁻¹ ∈ H` ∀ gen. -/
def normElems (B : List Coordinates) : List Coordinates :=
  allVecs.filter (fun g => B.all (fun gen => siftB 1 B (conjC 1 g gen)))

/-- Echelon basis of `N_G(H)` (basis `B`), from the normalizing elements. -/
def normBasis (B : List Coordinates) : List Coordinates := closeFrom [] (normElems B)

/-- The conjugation matrix of `n` on `H`'s char vectors: row `i` = expVec of
`n⁻¹ gᵢ n` in `B`-coordinates. -/
def conjMatrix (B : List Coordinates) (n : Coordinates) : List (List (ZMod 25)) :=
  B.map (fun gi => expVec B (conjC 1 (invC 1 n) gi))

/-- The action of a matrix `M` on a char exponent vector `e`. -/
def actVec (M : List (List (ZMod 25))) (e : List (ZMod 25)) : List (ZMod 25) :=
  M.map (fun row => dotZ row e)

/-- Order (1, 5 or 25) of a char exponent vector over ZMod 25. -/
def charOrd (e : List (ZMod 25)) : Nat :=
  let g := e.foldl (fun acc z => Nat.gcd acc z.val) 25
  25 / g

/-! ## Orbit flood-fill under the matrix action -/

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

/-- Per-rep orbit data: (basis, chars, matrices, component array). -/
def repOrbit (r : Nat) : List Coordinates × List (List (ZMod 25)) ×
    List (List (List (ZMod 25))) × Array Nat :=
  let ri := classRepsData.getD r 0
  let B := getB ri
  let Nb := normBasis B
  let chars := repChars.getD r []
  let Ms := Nb.map (conjMatrix B)
  let cnt := chars.length
  let adj := fun i =>
    Ms.map (fun M => chars.idxOf (actVec M (chars.getD i [])))
  (B, chars, Ms, flood cnt adj)

/-- Number of orbits for rep `r`. -/
def orbitCount (r : Nat) : Nat :=
  let (_, _, _, comp) := repOrbit r
  comp.foldl Nat.max 0

/-- Sanity of the normalizer location for rep `r`: |normElems| is a power of 5,
Nb basis has right length, and it is found in allBases. -/
def normCheck (r : Nat) : Nat × Nat × Nat × Nat :=
  let ri := classRepsData.getD r 0
  let B := getB ri
  let ne := (normElems B).length
  let Nb := normBasis B
  let idx := baseIdx Nb
  let cls := classSizeNat r
  (ne, Nb.length, idx, cls)

/-! ## Full per-rep orbit computation with BFS tree + witnesses -/

/-- The induced permutation position table: `actPos[k][p]` = index in `chars` of
`actVec Ms[k] chars[p]`. -/
def actPosTab (chars : List (List (ZMod 25))) (Ms : List (List (List (ZMod 25)))) :
    List (List Nat) :=
  Ms.map (fun M => chars.map (fun e => chars.idxOf (actVec M e)))

/-- BFS orbit data: per position `(label, isRep, treeGen, treePar, depth)`.
`label` = index of the orbit's canonical (min-index) representative. -/
def orbitData (n : Nat) (actPos : List (List Nat)) :
    Array Nat × Array Bool × Array Nat × Array Nat × Array Nat := Id.run do
  let mut label := Array.replicate n n      -- n = "unvisited"
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

/-! ## Emission -/

def renderNat (n : Nat) : String := toString n
/-- Render a coordinate vector as a Lean literal (for the link-2 `normGens`). -/
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

-- Emit all normalizer-orbit certification data as Lean `def` literals.
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
  for r in [0:148] do
    let ri := classRepsData.getD r 0
    let B := getB ri
    let Nb := normBasis B
    let chars := repChars.getD r []
    let Ms := Nb.map (conjMatrix B)
    let n := chars.length
    let actPos := actPosTab chars Ms
    let (label, isRep, tGen, tPar, depth) := orbitData n actPos
    normIdxs := normIdxs ++ [baseIdx Nb]
    gensAll := gensAll ++ [renderCoordList Nb]
    matsAll := matsAll ++ [renderMats Ms]
    actAll := actAll ++ [renderNatLL actPos]
    labAll := labAll ++ [renderNatList label.toList]
    isRepAll := isRepAll ++ [renderBoolList isRep.toList]
    tGenAll := tGenAll ++ [renderNatList tGen.toList]
    tParAll := tParAll ++ [renderNatList tPar.toList]
    tDepthAll := tDepthAll ++ [renderNatList depth.toList]
  let file ← IO.FS.Handle.mk "norm_data.txt" IO.FS.Mode.write
  file.putStrLn s!"def normIdxData : List Nat := {renderNatList normIdxs}"
  file.putStrLn ""
  -- link 2 provenance: the actual `normBasis B` generators used for `normMats`.
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
  IO.println "emitted norm_data.txt"

end LeanDring.P5Presentation
