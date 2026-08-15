/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin1.CharAssembly

/-!
# `#eval` generator: coset transversals and fixed sub-transversals

**Outside the build closure.** Nothing imports this file; it carries no part of
the trust base and is kept for provenance, as the script that produced the
transversal data embedded in the species-entry modules
`LeanDring/P5/Certificate/SpeciesTable/Twin1/EntryData.lean` and
`…/EntryFix.lean`. Everything it emits is untrusted, and is re-verified there by
kernel `decide` against two proven bridges:

* `coset_eq_iff_reduceAux` — injectivity of `fun i ↦ ⟦R i⟧` is `decide`-able via
  the canonical `reduceAux` proxy, so an emitted `R` of the right length
  (`[G:K] = 5^(5-|gK|)`) is a full transversal (`transversalMod_bijective`).
* `coset_fixed_iff_siftB` — `H`-fixedness of a coset is a per-generator `siftB`
  Bool, so the fixed sub-transversal `T(H,K)` is `R.filter (isFixed gH)` and the
  count feeds `card_fixedPoints_eq_of_filter_card` for `hcard`.

The full coset transversal `R` of `K = ⟨gK⟩` is the set of canonical `reduceAux`
normal forms `{reduceAux gK x : x ∈ G}` (deduplicated).  `reduceAux gK` is
constant on left cosets and canonical, so this is a genuine transversal.

## Transversal sizes

Per `K`-class of order `5^k` the transversal has `[G:K] = 5^(5-k)` elements:
`k ∈ {0,1,2,3,4,5} → |R| ∈ {3125,625,125,25,5,1}`.  The order-`25` `A`-block
(`k=2`, `[G:K]=125`) is where the twins' species entries differ, so it carries
the bulk of the emitted data: a `125`-element transversal per `K`-class,
filtered by `H`-fixedness for each `H` with `|H| ≤ 25`.  The `k=0` (`K=⊥`)
transversal is the full `3125` carrier and is fixed only under `H=⊥`.

The emission `#eval`s are commented out: uncomment the one wanted and run
`lake env lean` on this file.
-/

namespace LeanDring.P5Presentation

open Fin.NatCast

/-- The five `Fin 5` values. -/
def fin5s : List (Fin 5) := [0, 1, 2, 3, 4]

/-- All 3125 coordinate vectors. -/
def allVecs : List Coordinates :=
  fin5s.flatMap (fun a => fin5s.flatMap (fun b => fin5s.flatMap (fun c =>
    fin5s.flatMap (fun d => fin5s.map (fun e => (a, b, c, d, e))))))

/-- The canonical left-coset transversal of `K = ⟨gK⟩` in `G`: the deduplicated
image of the whole group under the canonical normal form `reduceAux gK`. -/
def cosetTransversal (gK : List Coordinates) : List Coordinates :=
  (allVecs.map (fun x => reduceAux 1 gK x)).dedup

/-- The return element `t⁻¹·g·t`, matching `P5EntryData.retConj`. -/
def retConjE (t g : Coordinates) : Coordinates :=
  mulC 1 (mulC 1 (invC 1 t) g) t

/-- Is the coset `⟦t⟧` fixed by `H = ⟨gH⟩`? — every generator's return element
sifts into `K = ⟨gK⟩`.  (Mirrors `coset_fixed_iff_siftB`.) -/
def isFixedCoset (gK gH : List Coordinates) (t : Coordinates) : Bool :=
  gH.all (fun g => siftB 1 gK (retConjE t g))

/-- The `H`-fixed sub-transversal `T(H,K) = R.filter (isFixed)`. -/
def fixedTransversal (gK gH : List Coordinates) : List Coordinates :=
  (cosetTransversal gK).filter (isFixedCoset gK gH)

/-- Render one transversal as a Lean list literal of coordinate tuples. -/
def renderVecs (vs : List Coordinates) : String :=
  "[" ++ String.intercalate ", "
    (vs.map (fun v => s!"({v.1.val},{v.2.1.val},{v.2.2.1.val},{v.2.2.2.1.val},{v.2.2.2.2.val})"))
    ++ "]"

/-! ## Self-checks / volume probes (run with `#eval`) -/

-- Index sanity: |R(reps k)| must equal 5^(5 - |basisAt k|) = [G:K].
-- Prints the 148 transversal lengths for q=1 (paste + kernel-check downstream).
-- #eval IO.println <| String.intercalate "," <|
--   (List.range 148).map (fun k => toString (cosetTransversal (basisAt ⟨k, by decide⟩)).length)

-- A-block probe: for K a chosen order-25 class rK, print the fixed-count of every
-- H-class of order ≤ 25 (the |T(H,K)| = |(G/K)^H| the entry layer certifies).
-- #eval do
--   let rK := 60          -- an order-25 A-block class index
--   let gK := basisAt ⟨rK, by decide⟩
--   for rH in List.range 148 do
--     let gH := basisAt ⟨rH, by decide⟩
--     if gH.length ≤ (5 - gK.length) + gK.length then   -- |H| ≤ |K| prune
--       IO.println s!"({rH},{rK}) |T| = {(fixedTransversal gK gH).length}"

-- Emit the full order-25 K-block transversals:
-- #eval IO.println <| String.intercalate ",\n" <|
--   ((List.range 148).filter (fun k => (basisAt ⟨k, by decide⟩).length = 2)).map
--     (fun k => renderVecs (cosetTransversal (basisAt ⟨k, by decide⟩)))

end LeanDring.P5Presentation
