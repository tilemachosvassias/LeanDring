import LeanDring.P5.Certificate.Generators.Twin2.Gen
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.NormLink2Data
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.ConjData
import LeanDring.P5.Certificate.SubgroupInventory.Twin2.FrattiniCert
import LeanDring.P5.Certificate.Characters.Twin2.CharData

/-!
Species-side (Col-side) enumeration EMITTER for the q=2 twin (SmallGroup(3125,69)).
Mirror of `LeanDring/P5/Certificate/SpeciesTable/Twin1/SpeciesEmit.lean` on H'-cosets, using the
q=2 group law (`mulC 2` …) and
the Q2-namespaced inventory (getB / classRepsData / normGens / charCounts).
NOT part of the library trust base; produced lists are re-checked by `decide` in
`LeanDring/P5/Certificate/SpeciesTable/Twin2/SpeciesCosets.lean` /
`LeanDring/P5/Certificate/SpeciesTable/Twin2/SpeciesOrbitData.lean`.
Run: lake build LeanDring.P5.Certificate.SpeciesTable.Twin2.SpeciesEmit
-/

namespace LeanDring.P5Presentation.Q2
open Fin.NatCast

set_option maxRecDepth 100000

abbrev Vec := Coordinates
def z5 : Vec := (0,0,0,0,0)

/-- `g x g⁻¹` (q=2). -/
def conjBy (g x : Vec) : Vec := mulC 2 (mulC 2 g x) (invC 2 g)

/-- Derived subgroup pcgs `[H,H]` for `H` given by pcgs `B` (q=2). -/
def derivedOf (B : List Vec) : List Vec :=
  let comms := B.flatMap (fun a => B.map (fun b => LeanDring.P5Gen2.commutator a b))
  let rec go : Nat → List Vec → List Vec
    | 0, cur => cur
    | fuel+1, cur =>
      let conjs := cur.flatMap (fun p =>
        B.flatMap (fun b => [conjBy b p, conjBy (invC 2 b) p]))
      let nxt := LeanDring.P5Gen2.closeFrom [] (cur ++ conjs)
      if nxt.length = cur.length then cur else go fuel nxt
  go 12 (LeanDring.P5Gen2.closeFrom [] comms)

/-- Free pivots of `B` modulo `Hp`. -/
def freePivots (B Hp : List Vec) : List Vec :=
  let hd := Hp.map pivotDepth
  B.filter (fun b => ¬ hd.contains (pivotDepth b))

/-- Full coset transversal of `Hp` in `H = ⟨B⟩` (q=2). -/
def transversal (B Hp : List Vec) : List Vec :=
  (freePivots B Hp).foldl
    (fun acc pv => acc.flatMap (fun t => (List.range 5).map (fun c => mulC 2 t (mpow 2 pv c))))
    [z5]

/-- Reduce `x ∈ H` to its `Hp`-coset transversal index. -/
def cosetIdx (Hp T : List Vec) (x : Vec) : Nat :=
  (T.findIdx? (fun t => siftB 2 Hp (mulC 2 (invC 2 t) x))).getD 999

/-- Order of the coset `x·Hp` in `H/Hp` (∈ {1,5,25}). -/
def cosetOrder (Hp : List Vec) (x : Vec) : Nat :=
  if siftB 2 Hp x then 1
  else if siftB 2 Hp (mpow 2 x 5) then 5
  else 25

/-- Action of a normalizer generator `n` on the transversal: `Tᵢ ↦ cosetIdx (n Tᵢ n⁻¹)`. -/
def actPerm (Hp T : List Vec) (n : Vec) : List Nat :=
  T.map (fun t => cosetIdx Hp T (conjBy n t))

/-- BFS orbit labels. -/
def orbitLabels (perms : List (List Nat)) (m : Nat) : List Nat := Id.run do
  let mut lab : Array Nat := (Array.range m)
  for _ in [0:m+1] do
    for perm in perms do
      for i in [0:m] do
        let j := perm.getD i i
        let li := lab.getD i i
        let lj := lab.getD j j
        let lo := min li lj
        lab := lab.set! i lo
        lab := lab.set! j lo
    pure ()
  return (List.range m).map (fun i => lab.getD i i)

/-- Per-rep species-orbit summary. -/
def repSummary (r : Nat) : Nat × Nat × Nat × Nat × Nat × Nat × Nat := Id.run do
  let B := getB (classRepsData.getD r 0)
  let Hp := derivedOf B
  let T := transversal B Hp
  let m := T.length
  let ng := normGens.getD r []
  let perms := ng.map (actPerm Hp T)
  let lab := orbitLabels perms m
  let repIdxs := (List.range m).filter (fun i => lab.getD i i == i)
  let numOrb := repIdxs.length
  let ords := repIdxs.map (fun i => cosetOrder Hp (T.getD i z5))
  let f1 := (ords.filter (· == 1)).length
  let f5 := (ords.filter (· == 5)).length
  let f25 := (ords.filter (· == 25)).length
  return (r, 5 ^ (B.length - Hp.length), m, numOrb, f1, f5, f25)

def allSummaries : List (Nat × Nat × Nat × Nat × Nat × Nat × Nat) :=
  (List.range 148).map repSummary

def hAbCheck : List (Nat × Nat × Nat) :=
  allSummaries.map (fun s => (s.1, s.2.1, charCounts.getD s.1 0))

#eval "=== |H/H'| vs charCounts mismatches (should be empty) ==="
#eval hAbCheck.filter (fun t => t.2.1 != t.2.2)
#eval "=== transversal size = |H/H'| mismatches (should be empty) ==="
#eval allSummaries.filter (fun s => s.2.1 != s.2.2.1)
#eval "=== TOTAL orbits (want 2724) ==="
#eval (allSummaries.map (fun s => s.2.2.2.1)).sum
#eval "=== FIBRE SPLIT by coset order (o1, o5, o25) — want (148,2376,200) ==="
#eval ((allSummaries.map (fun s => s.2.2.2.2.1)).sum,
       (allSummaries.map (fun s => s.2.2.2.2.2.1)).sum,
       (allSummaries.map (fun s => s.2.2.2.2.2.2)).sum)

def rawFibre : Nat × Nat × Nat := Id.run do
  let mut f1 := 0; let mut f5 := 0; let mut f25 := 0
  for r in [0:148] do
    let B := getB (classRepsData.getD r 0)
    let Hp := derivedOf B
    let T := transversal B Hp
    for t in T do
      match cosetOrder Hp t with
      | 1 => f1 := f1 + 1
      | 5 => f5 := f5 + 1
      | _ => f25 := f25 + 1
  return (f1, f5, f25)
#eval "=== RAW element-order fibre over all cosets (o1,o5,o25) ==="
#eval rawFibre
#eval "=== per-rep orbit-count distribution (value, #reps) ==="
#eval (allSummaries.map (fun s => s.2.2.2.1)).foldl
        (fun (acc : List (Nat × Nat)) v =>
          if acc.any (fun p => p.1 == v)
          then acc.map (fun p => if p.1 == v then (p.1, p.2+1) else p)
          else acc ++ [(v,1)]) []

/-! ## Data emission -/

def renderCoord (v : Coordinates) : String :=
  s!"({v.1},{v.2.1},{v.2.2.1},{v.2.2.2.1},{v.2.2.2.2})"
def renderCoordList (l : List Coordinates) : String :=
  "[" ++ String.intercalate "," (l.map renderCoord) ++ "]"

/-- Output directory for the emitted data files (relative to the working
directory the `#eval` is run from). -/
def SCRATCH : String := "."

def emitSpeciesData : IO Unit := do
  let hpAll := (List.range 148).map (fun r =>
    renderCoordList (derivedOf (getB (classRepsData.getD r 0))))
  let trAll := (List.range 148).map (fun r =>
    let B := getB (classRepsData.getD r 0)
    renderCoordList (transversal B (derivedOf B)))
  let file ← IO.FS.Handle.mk (SCRATCH ++ "/species_data2.txt") IO.FS.Mode.write
  file.putStrLn s!"def hpData : List (List Coordinates) :=\n[{String.intercalate ",\n" hpAll}]"
  file.putStrLn ""
  file.putStrLn s!"def transData : List (List Coordinates) :=\n[{String.intercalate ",\n" trAll}]"

-- #eval emitSpeciesData  -- (re-run to regenerate species_data2.txt)

/-! ## Coset-ORBIT data emission -/

/-- `n⁻¹ · t · n` (orientation matching `normMats_realize`). -/
def conjInv (n t : Vec) : Vec := mulC 2 (mulC 2 (invC 2 n) t) n

def actPermInv (Hp T : List Vec) (n : Vec) : List Nat :=
  T.map (fun t => cosetIdx Hp T (conjInv n t))

def repCosetData (r : Nat) :
    List (List Nat) × List Nat × List Bool × List Nat × List Nat × List Nat := Id.run do
  let B := getB (classRepsData.getD r 0)
  let Hp := derivedOf B
  let T := transversal B Hp
  let m := T.length
  let ng := normGens.getD r []
  let perms := ng.map (actPermInv Hp T)
  let lab := orbitLabels perms m
  let isRep := (List.range m).map (fun i => lab.getD i i == i)
  let mut par : Array Nat := Array.replicate m 0
  let mut gen : Array Nat := Array.replicate m 0
  let mut dep : Array Nat := Array.replicate m 0
  let mut vis : Array Bool := Array.replicate m false
  let mut queue : Array Nat := #[]
  for i in [0:m] do
    if lab.getD i i == i then
      vis := vis.set! i true
      dep := dep.set! i 0
      queue := queue.push i
  let mut head := 0
  while head < queue.size do
    let u := queue.getD head 0
    head := head + 1
    let du := dep.getD u 0
    for k in [0:perms.length] do
      let v := (perms.getD k []).getD u u
      if v < m && !(vis.getD v false) then
        vis := vis.set! v true
        par := par.set! v u
        gen := gen.set! v k
        dep := dep.set! v (du + 1)
        queue := queue.push v
  return (perms, lab, isRep,
          (List.range m).map (fun i => gen.getD i 0),
          (List.range m).map (fun i => par.getD i 0),
          (List.range m).map (fun i => dep.getD i 0))

def renderNatList (l : List Nat) : String :=
  "[" ++ String.intercalate "," (l.map toString) ++ "]"
def renderNatLL (l : List (List Nat)) : String :=
  "[" ++ String.intercalate "," (l.map renderNatList) ++ "]"
def renderBoolList (l : List Bool) : String :=
  "[" ++ String.intercalate "," (l.map (fun b => if b then "true" else "false")) ++ "]"

def orbitStats : Nat × Nat × Nat × Nat := Id.run do
  let mut orbTot := 0; let mut f1 := 0; let mut f5 := 0; let mut f25 := 0
  for r in [0:148] do
    let B := getB (classRepsData.getD r 0)
    let Hp := derivedOf B
    let T := transversal B Hp
    let d := repCosetData r
    let lab := d.2.1
    for i in [0:T.length] do
      if lab.getD i i == i then
        orbTot := orbTot + 1
        match cosetOrder Hp (T.getD i z5) with
        | 1 => f1 := f1 + 1
        | 5 => f5 := f5 + 1
        | _ => f25 := f25 + 1
  return (orbTot, f1, f5, f25)

def emitCosetOrbitData : IO Unit := do
  let datas := (List.range 148).map repCosetData
  let acts := datas.map (fun d => renderNatLL d.1)
  let labs := datas.map (fun d => renderNatList d.2.1)
  let isreps := datas.map (fun d => renderBoolList d.2.2.1)
  let gens := datas.map (fun d => renderNatList d.2.2.2.1)
  let pars := datas.map (fun d => renderNatList d.2.2.2.2.1)
  let deps := datas.map (fun d => renderNatList d.2.2.2.2.2)
  let file ← IO.FS.Handle.mk (SCRATCH ++ "/coset_orbit_data2.txt") IO.FS.Mode.write
  file.putStrLn s!"def cosetActData : List (List (List Nat)) :=\n[{String.intercalate ",\n" acts}]"
  file.putStrLn ""
  file.putStrLn s!"def cosetLabel : List (List Nat) :=\n[{String.intercalate ",\n" labs}]"
  file.putStrLn ""
  file.putStrLn s!"def cosetIsRep : List (List Bool) :=\n[{String.intercalate ",\n" isreps}]"
  file.putStrLn ""
  file.putStrLn s!"def cosetTreeGen : List (List Nat) :=\n[{String.intercalate ",\n" gens}]"
  file.putStrLn ""
  file.putStrLn s!"def cosetTreePar : List (List Nat) :=\n[{String.intercalate ",\n" pars}]"
  file.putStrLn ""
  file.putStrLn s!"def cosetTreeDepth : List (List Nat) :=\n[{String.intercalate ",\n" deps}]"

#eval "=== orbit stats (orbits, o1, o5, o25) — want (2724, 148, 2376, 200) ==="
#eval orbitStats
-- #eval emitCosetOrbitData  -- (re-run to regenerate coset_orbit_data2.txt)

end LeanDring.P5Presentation.Q2
