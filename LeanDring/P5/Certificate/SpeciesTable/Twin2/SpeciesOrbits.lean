/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.SpeciesOrbitChunk.C002
import LeanDring.P5.Data.SpeciesOrbitChunk.C004
import LeanDring.P5.Data.SpeciesOrbitChunk.C006
import LeanDring.P5.Data.SpeciesOrbitChunk.C008
import LeanDring.P5.Data.SpeciesOrbitChunk.C010
import LeanDring.P5.Data.SpeciesOrbitChunk.C012
import LeanDring.P5.Data.SpeciesOrbitChunk.C014
import LeanDring.P5.Data.SpeciesOrbitChunk.C016
import LeanDring.P5.Data.SpeciesOrbitChunk.C018
import LeanDring.P5.Data.SpeciesOrbitChunk.C020
import LeanDring.P5.Data.SpeciesOrbitChunk.C022
import LeanDring.P5.Data.SpeciesOrbitChunk.C024
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.NormLink

/-!
# Species-side coset-orbit partition (species-side coset orbits, part D — the column analogue of the
normalizer-orbit partition)

Assembly of the twelve chunked kernel checks (`LeanDring/P5/Data/SpeciesOrbitChunk/C001.lean`–`11`)
into
whole-range facts, and the headline aggregate counts of the `N_G(H)`-orbit
partition of the certified `H'`-coset transversals `transData r`.

For each of the 148 subgroup-class reps `H = reps r`, with `H' = [H,H]` (certified
in `Twin2/SpeciesLink.lean`, `hpSub_eq_derived`) and transversal `T = transData r` (certified
a genuine transversal, `transCard`), the emitter produces the `N_G(H)`-action on
cosets and a BFS orbit partition. The kernel certifies (one `siftB` per `(r,k,p)`):

* `cosetOrbCheck_all` — the emitted index tables are genuine coset actions
  (`(T[tab])⁻¹ · nₖ⁻¹ · T[p] · nₖ ∈ H'`), labels are generator-invariant, and every
  coset reaches its orbit representative along a valid BFS spanning tree.

From these:

* `speciesOrbitTotal` — `Σ_r cosetOrbitCountR r = 2724`, the pair-class transversal
  size (`= rank D(G)` for `q = 2`), **matching the character side** (`pairClassTotal`);
* `speciesOrbitCount_distribution` — the per-rep orbit counts realise the same
  fingerprint `{1:1, 5:12, 9:61, 13:5, 25:56, 29:1, 45:11, 125:1}` as the normalizer-orbit
  partition;
* `speciesOrbitFibre` — the fibre split of the **orbits** by the order of the coset
  `hH'` in `H/H'` is `{1 : 148, 5 : 2376, 25 : 200}`, **identical** to the character
  side (`orbitFibre_by_order`) by Pontryagin duality; the raw split is `{148,3688,1400}`.

## Semantic grounding

The combinatorial Prop API (`CosetReach`, `cosetLabel_stable`, `cosetReach_from_rep`)
follows the normalizer-orbit partition's `MatReach` layer on positions.
`speciesOrbit_semantically_closed`
grounds it: every orbit-connected pair of cosets is transported by a genuine element
of `N_G(reps r)` — the ordered product of the certified normalizer generators
`normGens r` (`normGens_generate`,
`LeanDring/P5/Certificate/ConjugacyClasses/Twin2/NormLink.lean`) over the connecting word. The
per-step realization (table entry = conjugate coset) is `cosetActOK` in the data file.
-/

namespace LeanDring.P5Presentation

namespace Q2

open Fin.NatCast

set_option maxRecDepth 100000
-- file-level maxHeartbeats: dozens of decide-heavy declarations below need it
set_option linter.style.setOption false
set_option maxHeartbeats 4000000

/-! ## Whole-range check from the twelve chunks -/

/-- **Coset-action + label-invariance + spanning-tree validity for all 148 reps.** -/
theorem cosetOrbCheck_all : (List.range 148).all cosetOrbCheck = true := by
  have e : List.range 148 =
      List.range' 0 64 ++ List.range' 64 8 ++ List.range' 72 8 ++ List.range' 80 8 ++
      List.range' 88 8 ++ List.range' 96 8 ++ List.range' 104 8 ++ List.range' 112 8 ++
      List.range' 120 8 ++ List.range' 128 8 ++ List.range' 136 8 ++ List.range' 144 4 := by decide
  have h0 := cosetOrbChunk0; have h1 := cosetOrbChunk1; have h2 := cosetOrbChunk2
  have h3 := cosetOrbChunk3; have h4 := cosetOrbChunk4; have h5 := cosetOrbChunk5
  have h6 := cosetOrbChunk6; have h7 := cosetOrbChunk7; have h8 := cosetOrbChunk8
  have h9 := cosetOrbChunk9; have h10 := cosetOrbChunk10; have h11 := cosetOrbChunk11
  simp only [cosetOrbCheckRange] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  rw [e]
  simp only [List.all_append, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    Bool.and_self]

/-- Extract `cosetOrbCheck r = true` per representative. -/
theorem cosetOrbCheck_at (r : Fin 148) : cosetOrbCheck r.val = true :=
  (List.all_eq_true.mp cosetOrbCheck_all) r.val (List.mem_range.mpr r.isLt)

/-- Per-rep coset-action + label-invariance certificate. -/
theorem checkCosetAct_at (r : Fin 148) : checkCosetAct r.val = true := by
  have h := cosetOrbCheck_at r; simp only [cosetOrbCheck, Bool.and_eq_true] at h; exact h.1.1

/-- Per-rep spanning-tree certificate. -/
theorem checkCosetTree_at (r : Fin 148) : checkCosetTree r.val = true := by
  have h := cosetOrbCheck_at r; simp only [cosetOrbCheck, Bool.and_eq_true] at h; exact h.1.2

/-! ## Aggregate: the 2724 pair-class transversal (species side) -/

/-- **The pair-class transversal size, species side.** Summed over the 148
subgroup classes, the number of `N_G(H)`-orbits of `H'`-cosets is `2724` — the same
`rank D(G)` (`q = 2`) obtained on the character side (`pairClassTotal`). -/
theorem speciesOrbitTotal : ((List.range 148).map cosetOrbitCountR).sum = 2724 := by decide

/-- **The per-representative orbit-count distribution** `{1:1, 5:12, 9:61, 13:5,
25:56, 29:1, 45:11, 125:1}`, identical to the character side's fingerprint. -/
theorem speciesOrbitCount_distribution :
    ((List.range 148).filter (fun r => Nat.beq (cosetOrbitCountR r) 1)).length = 1 ∧
    ((List.range 148).filter (fun r => Nat.beq (cosetOrbitCountR r) 5)).length = 12 ∧
    ((List.range 148).filter (fun r => Nat.beq (cosetOrbitCountR r) 9)).length = 61 ∧
    ((List.range 148).filter (fun r => Nat.beq (cosetOrbitCountR r) 13)).length = 5 ∧
    ((List.range 148).filter (fun r => Nat.beq (cosetOrbitCountR r) 25)).length = 56 ∧
    ((List.range 148).filter (fun r => Nat.beq (cosetOrbitCountR r) 29)).length = 1 ∧
    ((List.range 148).filter (fun r => Nat.beq (cosetOrbitCountR r) 45)).length = 11 ∧
    ((List.range 148).filter (fun r => Nat.beq (cosetOrbitCountR r) 125)).length = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The orbit fibre split by coset order.** The `2724` orbits split by the order
of the representative coset `hH'` in `H/H'` as `{1 : 148, 5 : 2376, 25 : 200}` —
identical to the character side (`orbitFibre_by_order`) by Pontryagin duality. -/
theorem speciesOrbitFibre :
    ((List.range 148).map cosetFibreO1).sum = 148 ∧
    ((List.range 148).map cosetFibreO5).sum = 2376 ∧
    ((List.range 148).map cosetFibreO25).sum = 200 := by
  refine ⟨by decide, by decide, by decide⟩

/-- The three order-fibres of the orbits total `2724`, cross-checking
`speciesOrbitTotal`. -/
theorem speciesOrbitFibre_total :
    ((List.range 148).map cosetFibreO1).sum +
      ((List.range 148).map cosetFibreO5).sum +
      ((List.range 148).map cosetFibreO25).sum = 2724 := by decide

/-! ## Prop-level packaging: coset-orbit reachability (combinatorial API)

Purely at the level of the transversal *positions* and the emitted index action —
the column analogue of the normalizer-orbit `MatReach`. Every coset reaches its orbit representative
along the spanning tree, and its label is stable under every generator's action. -/

/-- The action of `N`'s `k`-th generator on a coset position of rep `r`
(out-of-range default `0`, consistent with the emitter's tables). -/
def cosetGenAct (r k p : Nat) : Nat := ((cosetActData.getD r []).getD k []).getD p 0

/-- `p'` is reachable from `p` by a word of generator actions of rep `r`. -/
def CosetReach (r : Nat) (p p' : Nat) : Prop :=
  ∃ w : List Nat, w.foldl (fun x k => cosetGenAct r k x) p = p'

theorem CosetReach.refl (r p : Nat) : CosetReach r p p := ⟨[], rfl⟩

theorem CosetReach.step {r p p' : Nat} (k : Nat) (h : CosetReach r p p') :
    CosetReach r p (cosetGenAct r k p') := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w ++ [k], ?_⟩
  rw [List.foldl_append, hw]; rfl

/-- The per-`(k,p)` label-invariance fact of rep `r`, from `checkCosetAct_at`. -/
theorem cosetAct_fact (r : Fin 148) (k p : Nat)
    (hk : k < (cosetActData.getD r.val []).length) (hp : p < (transData.getD r.val []).length) :
    (cosetLabel.getD r.val []).getD (((cosetActData.getD r.val []).getD k []).getD p 0) 0 =
      (cosetLabel.getD r.val []).getD p 0 := by
  have hrow := (List.all_eq_true.mp (checkCosetAct_at r)) k (List.mem_range.mpr hk)
  have hp' := (List.all_eq_true.mp hrow) p (List.mem_range.mpr hp)
  simp only [cosetActOK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hp'
  exact hp'.2

/-- **Label stability.** Applying any generator to a coset keeps it in the same
orbit label — the coset action respects the emitted partition. -/
theorem cosetLabel_stable (r : Fin 148) (k p : Nat)
    (hk : k < (cosetActData.getD r.val []).length) (hp : p < (transData.getD r.val []).length) :
    (cosetLabel.getD r.val []).getD (cosetGenAct r.val k p) 0 =
      (cosetLabel.getD r.val []).getD p 0 :=
  cosetAct_fact r k p hk hp

/-- **Reachability from the representative.** Every coset of rep `r` is reachable,
along the spanning tree, from the coset at its orbit label. -/
theorem cosetReach_from_rep (r : Fin 148) : ∀ (dep p : Nat),
    p < (transData.getD r.val []).length →
    (cosetTreeDepth.getD r.val []).getD p 0 = dep →
    CosetReach r.val ((cosetLabel.getD r.val []).getD p 0) p := by
  intro dep
  induction dep using Nat.strong_induction_on with
  | _ dep IH =>
    intro p hp hdep
    have ht := (List.all_eq_true.mp (checkCosetTree_at r)) p (List.mem_range.mpr hp)
    by_cases hr : (cosetIsRep.getD r.val []).getD p false = true
    · simp only [cosetTreeOK, hr, Bool.not_true, Bool.false_and, Bool.or_false, Bool.true_and,
        Bool.and_eq_true, Nat.beq_eq] at ht
      rw [ht.2]; exact CosetReach.refl _ _
    · have hrf : (cosetIsRep.getD r.val []).getD p false = false := by
        cases h : (cosetIsRep.getD r.val []).getD p false with
        | false => rfl
        | true => exact absurd h hr
      simp only [cosetTreeOK, hrf, Bool.not_false, Bool.false_and, Bool.false_or, Bool.true_and,
        Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at ht
      obtain ⟨⟨⟨⟨_, hparlt⟩, hdlt⟩, hmove⟩, hlab⟩ := ht
      have hpardep : (cosetTreeDepth.getD r.val []).getD
          ((cosetTreePar.getD r.val []).getD p 0) 0 < dep := hdep ▸ hdlt
      have hIH := IH _ hpardep ((cosetTreePar.getD r.val []).getD p 0) hparlt rfl
      rw [hlab] at hIH
      have hstep := hIH.step ((cosetTreeGen.getD r.val []).getD p 0)
      rwa [show cosetGenAct r.val ((cosetTreeGen.getD r.val []).getD p 0)
        ((cosetTreePar.getD r.val []).getD p 0) = p from hmove] at hstep

/-- **Orbit ⟺ label.** Two cosets of rep `r` sharing an orbit label are each
reachable from their common representative — the labels are a complete, achieved
invariant of the coset action. -/
theorem cosetReach_of_sameLabel (r : Fin 148) (p p' : Nat)
    (hp : p < (transData.getD r.val []).length) (hp' : p' < (transData.getD r.val []).length)
    (hlab : (cosetLabel.getD r.val []).getD p 0 = (cosetLabel.getD r.val []).getD p' 0) :
    CosetReach r.val ((cosetLabel.getD r.val []).getD p 0) p ∧
      CosetReach r.val ((cosetLabel.getD r.val []).getD p 0) p' :=
  ⟨cosetReach_from_rep r _ p hp rfl, hlab ▸ cosetReach_from_rep r _ p' hp' rfl⟩

/-! ## Semantic closure of the coset orbits under genuine normalizer elements -/

/-- **Orbit closure, semantically (species side).** Whenever the emitted coset action
carries a coset position `p` of rep `r` to `p'` (`CosetReach` — a word `w` of
per-generator moves), the transport is realized by a genuine element of
`N_G(reps r)`: the ordered product `n = ∏ₖ (normGens r)[k]` over `w`. The per-step
content (each table move is conjugation by a normalizer generator) is `cosetActOK`;
`normGens_generate` (`LeanDring/P5/Certificate/ConjugacyClasses/Twin2/NormLink.lean`) certifies
`normGens r` generate `N_G(reps r)`.
This is the exact analogue of `orbit_semantically_closed`. -/
theorem speciesOrbit_semantically_closed (r : Fin 148) {p p' : Nat}
    (h : CosetReach r.val p p') :
    ∃ (w : List Nat) (n : Coordinate 2),
      n ∈ Subgroup.normalizer ((reps r : Subgroup (Coordinate 2)) : Set (Coordinate 2)) ∧
      n = w.foldl (fun acc k => acc * normGenAt r.val k) (1 : Coordinate 2) ∧
      w.foldl (fun x k => cosetGenAct r.val k x) p = p' := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, _, foldl_normGen_mem r w, rfl, hw⟩

end Q2

end LeanDring.P5Presentation
