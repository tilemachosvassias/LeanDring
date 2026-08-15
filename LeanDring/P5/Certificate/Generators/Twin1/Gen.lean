/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.ComputableModel.Twin1.Cgs
import LeanDring.P5.Certificate.SubgroupInventory.Twin1.AllSubgroups

/-!
# `#eval` generator: the subgroup inventory of `Coordinate 1`

**Outside the build closure.** Nothing imports this file, so it is not compiled
by `lake build` and carries no part of the trust base. It is kept for
provenance: it is the script that produced the subgroup-inventory data literals
embedded in `LeanDring/P5/Certificate/SubgroupInventory/Twin1/AllSubgroups.lean`,
and it is run by hand (`lake env lean` on this file) when that data must be
regenerated. Everything it emits is untrusted; the embedded copy is re-checked
in the inventory modules by kernel `decide`.

The generator enumerates the 676 subgroups of `Coordinate 1` by descending
through maximal subgroups from `⊤`, deduplicating by mutual sift, and then emits
one Frattini certificate per subgroup: the index of `Φ(H)`, the indices of the
maximal subgroups of `H`, and a witness word expressing each generator of `Φ(H)`
as a product of commutators and 5th powers of elements of `H`.
-/

namespace LeanDring.P5Presentation

open Fin.NatCast

abbrev Vec := Coordinates
def z5 : Vec := (0,0,0,0,0)

/-- Multiplicative inverse of a `Fin 5` lead coefficient (0 for 0). -/
def leadInv (t : Fin 5) : ℕ :=
  match t.val with | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | _ => 0

/-- Reduce `v` against an echelon pivot list (shallow→deep): strip every pivot. -/
def reduceBy (pivots : List Vec) (v : Vec) : Vec :=
  pivots.foldl (fun acc p => clearStep 1 p acc) v

def commutator (a b : Vec) : Vec :=
  mulC 1 (mulC 1 (mulC 1 a b) (invC 1 a)) (invC 1 b)

def insertSorted (r1 : Vec) : List Vec → List Vec
  | [] => [r1]
  | p :: ps => if pivotDepth r1 < pivotDepth p then r1 :: p :: ps else p :: insertSorted r1 ps

/-- Close a pcgs basis `pivots` under the obligations in `todo`, adding p-th
powers and commutators of every genuinely new pivot. Produces the canonical
echelon (induced pcgs) basis of the subgroup generated. -/
partial def closeFrom (pivots : List Vec) : List Vec → List Vec
  | [] => pivots
  | v :: vs =>
    let r := reduceBy pivots v
    if r = z5 then closeFrom pivots vs
    else
      let d := pivotDepth r
      let r1 := mpow 1 r (leadInv (coordAt r d))                 -- lead → 1
      let backsub := pivots.map (fun p =>
        if coordAt p d ≠ 0 then clearStep 1 r1 p else p)         -- reduce above
      let pivots2 := insertSorted r1 backsub
      let comms := pivots.flatMap (fun p => [commutator r1 p, commutator p r1])
      closeFrom pivots2 (vs ++ (mpow 1 r1 5) :: comms)

def closure (gens : List Vec) : List Vec := closeFrom [] gens

def fin5s : List (Fin 5) := [0,1,2,3,4]

/-- Frattini subgroup basis `Φ(H) = ⟨ b^5, [b,b'] ⟩` from a pcgs basis. -/
def frattini (B : List Vec) : List Vec :=
  let pows := B.map (fun b => mpow 1 b 5)
  let comms := (B.flatMap (fun b => B.map (fun b' => commutator b b')))
  closeFrom [] (pows ++ comms)

/-- The "free" generators of `H` modulo `Φ(H)`: a basis of `H/Φ(H)`. -/
def freeGens (B Phi : List Vec) : List Vec :=
  (B.foldl (fun (acc : List Vec × List Vec) b =>
      let (span, frees) := acc
      if reduceBy span b = z5 then acc
      else (closeFrom span [b], frees ++ [b])) (Phi, [])).2

/-- Scalar power `v^c`. -/
def scal (v : Vec) (c : Fin 5) : Vec := mpow 1 v c.val

/-- All length-`n` coefficient lists over `F5`. -/
def allTails : ℕ → List (List (Fin 5))
  | 0 => [[]]
  | n+1 => (allTails n).flatMap (fun t => fin5s.map (fun a => a :: t))

/-- Nonzero functionals on `F5^r` normalized so the first nonzero coordinate is
`1` (one representative per hyperplane): `(5^r-1)/4` of them, as coeff lists. -/
def functionals : ℕ → List (List (Fin 5))
  | 0 => []
  | r+1 =>
    (allTails r).map (fun t => (1 : Fin 5) :: t) ++
    (functionals r).map (fun f => (0 : Fin 5) :: f)

/-- Maximal subgroups of `H` (given by pcgs basis `B`), each as a canonical
echelon basis: preimages of the hyperplanes of `H/Φ(H)`. -/
def maximalsOf (B : List Vec) : List (List Vec) :=
  let Phi := frattini B
  let F := freeGens B Phi
  let r := F.length
  if r = 0 then []
  else (functionals r).map (fun φ =>
    -- k = index of first `1` in φ; ker basis = {F_j : j<k} ∪ {F_j·F_k^{-φ_j} : j>k}
    let k := (φ.zipIdx.filter (fun p => p.1 ≠ 0)).headD ((0:Fin 5),0) |>.2
    let Fk := F.getD k z5
    let kerB := (F.zipIdx.filter (fun p => p.2 < k)).map (fun p => p.1) ++
      (F.zipIdx.filter (fun p => p.2 > k)).map (fun p =>
        mulC 1 p.1 (scal (invC 1 Fk) (φ.getD p.2 0)))
    closeFrom Phi kerB)

/-- Downward BFS from `⊤`: every subgroup is reached by descending through
maximal subgroups. Dedup by canonical basis equality. -/
partial def genAllDown : List (List Vec) :=
  let top : List Vec := closure [(1,0,0,0,0),(0,1,0,0,0),(0,0,1,0,0)]  -- rank-3 gens
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

/-- Semantic subgroup equality via mutual sift (the proven-correct notion — a
syntactic echelon "canonical" form is NOT unique for this nonabelian group). -/
def subEq (A B : List Vec) : Bool :=
  A.all (fun g => decide (reduceBy B g = z5)) && B.all (fun g => decide (reduceBy A g = z5))

/-- Re-dedup `allData` by semantic equality: the authoritative 676 subgroups. -/
def allDataSem : List (List Vec) :=
  allData.foldl (fun acc K => if acc.any (fun s => subEq s K) then acc else K :: acc) []

-- Provenance cross-checks against GAP (`AllSubgroups(SmallGroup(3125,68))`):
#eval allData.length        -- 830 distinct echelon bases (canonical form NOT unique)
#eval allDataSem.length     -- 676  ✓ matches GAP total
#eval (List.range 6).map (fun k => (allDataSem.filter (fun s => s.length = k)).length)
                            -- [1,156,306,181,31,1]  ✓ matches GAP per-order strata

/-! ## Frattini-certificate data emission (untrusted; checked by `fratCertB`)

For the per-subgroup Frattini-certification pipeline
(`LeanDring/P5/Certificate/SubgroupInventory/Twin1/FrattiniCert.lean`), we emit,
for each subgroup `H` (given by its echelon basis, at index `h` in `allBases`):
* `phiIdx`  — index of `Φ(H)` in `allBases`;
* `maxIdxs` — indices of `H`'s maximal subgroups in `allBases`;
* signed-atom **witness words** for each generator of `Φ(H)`, expressing it as a
  product of commutators `⁅a,b⁆^±1` and 5th powers `(c^5)^±1` of elements of `H`.
All of this is untrusted data, re-verified by the kernel checker `fratCertB`.
-/

/-- `allBases` re-typed as raw coordinate vectors (definitional). -/
def allBasesV : List (List Vec) := allBases

/-- Index of the subgroup with echelon basis `K` in `allBases` (semantic match). -/
def baseIdx (K : List Vec) : Nat := (allBasesV.findIdx? (fun b => subEq b K)).getD 99999

/-! ### Signed-atom witness words

A word is a `List (Bool × Bool × Vec × Vec)`: each atom is `(inv, isPow, a, b)`
with value `(if isPow then a^5 else ⁅a,b⁆)` optionally inverted. The word's value
is the left-fold product; the generator tracks a word alongside every derived
vector so that each `Φ`-generator carries an explicit word over
commutators/5th-powers of the *original* basis elements of `H`. -/
abbrev WAtom := Bool × Bool × Vec × Vec       -- (inv?, isPow5?, a, b)
abbrev Word := List WAtom

def atomVal : WAtom → Vec
  | (inv, isPow, a, b) =>
    let v := if isPow then mpow 1 a 5 else commutator a b
    if inv then invC 1 v else v

def wordVal (w : Word) : Vec := w.foldl (fun acc at' => mulC 1 acc (atomVal at')) z5

def wInv (w : Word) : Word := (w.reverse).map (fun (inv, p, a, b) => (!inv, p, a, b))
def wMul (w1 w2 : Word) : Word := w1 ++ w2
def wPow (w : Word) (n : Nat) : Word := (List.replicate n w).flatten

/-- A vector carrying its witness word (over commutators/5th-powers of `H`-gens). -/
abbrev VW := Vec × Word

def mulVW (x y : VW) : VW := (mulC 1 x.1 y.1, wMul x.2 y.2)
def invVW (x : VW) : VW := (invC 1 x.1, wInv x.2)
def powVW (x : VW) (n : Nat) : VW := (mpow 1 x.1 n, wPow x.2 n)

/-- Clearing step at the word level: `x * p^(-coord)`. -/
def clearStepVW (p x : VW) : VW :=
  mulVW x (powVW (invVW p) (coordAt x.1 (pivotDepth p.1)).val)

def reduceByVW (pivots : List VW) (v : VW) : VW :=
  pivots.foldl (fun acc p => clearStepVW p acc) v

def insertSortedVW (r1 : VW) : List VW → List VW
  | [] => [r1]
  | p :: ps => if pivotDepth r1.1 < pivotDepth p.1 then r1 :: p :: ps else p :: insertSortedVW r1 ps

def commutatorVW (a b : VW) : VW :=
  mulVW (mulVW (mulVW a b) (invVW a)) (invVW b)

/-- Word-tracking closure: same shape as `closeFrom`, carrying words. -/
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

/-- Frattini basis of `H` (basis `B`) with a witness word per generator. -/
def frattiniVW (B : List Vec) : List VW :=
  let pows : List VW := B.map (fun b => (mpow 1 b 5, [(false, true, b, z5)]))
  let comms : List VW :=
    B.flatMap (fun b => B.map (fun b' => (commutator b b', [(false, false, b, b')])))
  closeFromVW [] (pows ++ comms)

/-- Emit the full certificate record for the subgroup with basis `B`. -/
def emitCert (B : List Vec) : Nat × Nat × List Nat × List (Vec × Word) :=
  let h := baseIdx B
  let phi := frattini B
  let phiIdx := baseIdx phi
  let maxs := maximalsOf B
  let maxIdxs := maxs.map baseIdx
  let phiVW := frattiniVW B
  let wits : List (Vec × Word) := phiVW.map (fun vw => (vw.1, vw.2))
  (h, phiIdx, maxIdxs, wits)

/-- Sanity: witness words reproduce the Frattini generators and the emitted
Frattini basis matches `frattini B` (semantic). -/
def checkEmit (B : List Vec) : Bool :=
  let phiVW := frattiniVW B
  let phi := frattini B
  -- every word evaluates to its recorded vector
  phiVW.all (fun vw => decide (wordVal vw.2 = vw.1)) &&
  -- the word-tracked basis generates the same subgroup as `frattini B`
  subEq (phiVW.map (·.1)) phi

/-- Render a `Vec` as Lean source. -/
def renderVec (v : Vec) : String :=
  s!"({v.1},{v.2.1},{v.2.2.1},{v.2.2.2.1},{v.2.2.2.2})"

def renderAtom (a : WAtom) : String :=
  s!"({a.1},{a.2.1},{renderVec a.2.2.1},{renderVec a.2.2.2})"

def renderWord (w : Word) : String :=
  "[" ++ String.intercalate "," (w.map renderAtom) ++ "]"

def renderWit (vwit : Vec × Word) : String :=
  s!"({renderVec vwit.1},{renderWord vwit.2})"

/-- Render one certificate as a `(Nat × FratCert)` Lean literal. -/
def renderCert (B : List Vec) : String :=
  let (h, phiIdx, maxIdxs, wits) := emitCert B
  let maxs := "[" ++ String.intercalate "," (maxIdxs.map toString) ++ "]"
  let witsS := "[" ++ String.intercalate "," (wits.map renderWit) ++ "]"
  s!"  ({h}, \{ phiIdx := {phiIdx}, maxIdxs := {maxs}, wits := {witsS} })"

/-- The pilot slice: `⊤` (the sole order-`5^5` base) plus all 31 order-`5^4` bases. -/
def pilotBases : List (List Vec) := (sub5 : List (List Vec)) ++ (sub4 : List (List Vec))

#eval pilotBases.length                                   -- 32
#eval pilotBases.all checkEmit                            -- expect true
#eval (pilotBases.map emitCert).map (fun c => (c.1, c.2.1, c.2.2.1.length))
-- per-H: (h, phiIdx, #maximals)  — top has 31 maximals, each 5^4 has ≤6
#eval IO.println (String.intercalate ",\n" (pilotBases.map renderCert))

end LeanDring.P5Presentation
