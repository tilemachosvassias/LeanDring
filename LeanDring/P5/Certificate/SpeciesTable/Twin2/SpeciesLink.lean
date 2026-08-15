/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin2.SpeciesCosets
import LeanDring.P5.Certificate.Characters.Twin2.CharCompleteFull
import LeanDring.P5.Certificate.SubgroupInventory.Twin2.FratDischarge

/-!
# Species-side enumeration: the `H' = [H,H]` semantic squeeze (species-side coset orbits, part B)

Turns the eight boolean certificates of `Twin2/SpeciesCosets.lean` into the group-theoretic
identity they encode: the emitted per-rep candidate `hpData r` genuinely presents
the derived subgroup `[H,H]` of `H = reps r`.

The squeeze is by **cardinality**, using the character-data bridge
`card_abelianization_reps_all` (`|H^ab| = charCounts r`) — no witness words:

* `commutator_reps_le_hpSub` — `[H,H] ≤ H'` (the abelian-quotient direction),
  from `commInCheck` (generator-commutators sift into `H'`) + `hpNormalCheck`
  (`H` normalizes `H'`) via `commutator_gens_mem`;
* `card` count — `|H'| = |H| / |H^ab| = |[H,H]|`, from `cardCheck`
  (`charCounts r · |H'| = |H|`) + Lagrange for `[H,H]` + the abelianization bridge;
* `hpSub_eq_derived` — `[H,H] ≤ H'` together with equal cardinality forces
  `(commutator ↥H).map H.subtype = H'`, i.e. `H'` **is** the ambient derived
  subgroup of `reps r`.

The transversal certificates (`transMemCheck`/`transDistinctCheck`/`transCountCheck`)
give: `transData r ⊆ H`, pairwise-distinct mod `H'`, of size `charCounts r = |H/H'|`
— a genuine coset transversal of `H'` in `H`.
-/

namespace LeanDring.P5Presentation

namespace Q2

open Fin.NatCast
open scoped commutatorElement

set_option maxRecDepth 100000
-- file-level maxHeartbeats: dozens of decide-heavy declarations below need it
set_option linter.style.setOption false
set_option maxHeartbeats 4000000

/-! ## Combine the four chunks -/

/-- The whole-range species certificate, from the four chunked `decide`s. -/
theorem speciesCheck_all : (List.range 148).all speciesCheck = true := by
  have e : List.range 148 =
      List.range' 0 37 ++ List.range' 37 37 ++ List.range' 74 37 ++ List.range' 111 37 := by decide
  have h0 := speciesChunk0; have h1 := speciesChunk1
  have h2 := speciesChunk2; have h3 := speciesChunk3
  simp only [speciesCheckRange] at h0 h1 h2 h3
  rw [e]
  simp only [List.all_append, h0, h1, h2, h3, Bool.and_self]

theorem speciesCheck_at (r : Fin 148) : speciesCheck r.val = true :=
  (List.all_eq_true.mp speciesCheck_all) r.val (List.mem_range.mpr r.isLt)

/-! ## Component extraction -/

theorem hpWf_at (r : Fin 148) : wfB' 2 (hpData.getD r.val []) = true := by
  have h := speciesCheck_at r; simp only [speciesCheck, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1

theorem hpSub_at (r : Fin 148) : hpSubCheck r.val = true := by
  have h := speciesCheck_at r; simp only [speciesCheck, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.2

theorem commIn_at (r : Fin 148) : commInCheck r.val = true := by
  have h := speciesCheck_at r; simp only [speciesCheck, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.2

theorem hpNormal_at (r : Fin 148) : hpNormalCheck r.val = true := by
  have h := speciesCheck_at r; simp only [speciesCheck, Bool.and_eq_true] at h
  exact h.1.1.1.1.2

theorem card_at (r : Fin 148) : cardCheck r.val = true := by
  have h := speciesCheck_at r; simp only [speciesCheck, Bool.and_eq_true] at h
  exact h.1.1.1.2

theorem transCount_at (r : Fin 148) : transCountCheck r.val = true := by
  have h := speciesCheck_at r; simp only [speciesCheck, Bool.and_eq_true] at h
  exact h.2

/-! ## The ambient derived subgroup -/

/-- The emitted derived-subgroup candidate `H' = hpData r`, as an ambient subgroup. -/
def hpSub (r : Nat) : Subgroup (Coordinate 2) := ofList 2 hq2 (hpData.getD r [])

/-- `H'` is a well-formed echelon pcgs. -/
theorem hpSub_wf (r : Fin 148) : WF 2 hq2 (hpData.getD r.val []) :=
  wf_of_wfB' hq2 _ (hpWf_at r)

/-- `|H'| = 5 ^ (length of its pcgs)`. -/
theorem card_hpSub (r : Fin 148) :
    Nat.card (hpSub r.val) = 5 ^ (hpData.getD r.val []).length :=
  card_ofList hq2 _ (hpSub_wf r)

/-- Every generator of `H'` sifts into `H = reps r`. -/
theorem hpSub_le_reps (r : Fin 148) : hpSub r.val ≤ reps r := by
  refine (Subgroup.closure_le _).mpr ?_
  intro g hg
  have h := hpSub_at r
  simp only [hpSubCheck, spIdx, List.all_eq_true] at h
  have hs : siftB 2 (getB (classRepsData.getD r.val 0)) g = true := h g hg
  exact (siftB_getB_iff (classReps_lt r.val r.isLt) g).mp hs

/-- `H = reps r` normalizes `H'`. -/
theorem reps_le_normalizer_hpSub (r : Fin 148) :
    reps r ≤ Subgroup.normalizer (hpSub r.val) := by
  change subAt (classRepsData.getD r.val 0) ≤ _
  rw [subAt_eq_closure]
  refine (Subgroup.closure_le _).mpr ?_
  intro b hb
  have h := hpNormal_at r
  simp only [hpNormalCheck, spIdx, List.all_eq_true, Bool.and_eq_true] at h
  change b ∈ Subgroup.normalizer (Subgroup.closure {x : Coordinate 2 | x ∈ hpData.getD r.val []})
  apply normalizes_closure hq2 b {x : Coordinate 2 | x ∈ hpData.getD r.val []}
  · intro g hg
    have hs : siftB 2 (hpData.getD r.val []) (conjByC b g) = true := (h g hg b hb).1
    have hmem : conjByC b g ∈ ofList 2 hq2 (hpData.getD r.val []) :=
      (sift_mem_iff hq2 _ (hpSub_wf r) _).mp hs
    rwa [show conjByC b g = conjC 2 b g from rfl, conjC_eq hq2 b g] at hmem
  · intro g hg
    have hs : siftB 2 (hpData.getD r.val []) (conjByC (invC 2 b) g) = true := (h g hg b hb).2
    have hmem : conjByC (invC 2 b) g ∈ ofList 2 hq2 (hpData.getD r.val []) :=
      (sift_mem_iff hq2 _ (hpSub_wf r) _).mp hs
    rw [show conjByC (invC 2 b) g = conjC 2 (invC 2 b) g from rfl, conjC_eq hq2 (invC 2 b) g,
      show invC 2 b = b⁻¹ from rfl, inv_inv] at hmem
    exact hmem

/-- Generator-commutators of `H` land in `H'`. -/
theorem gen_comm_mem_hpSub (r : Fin 148) :
    ∀ a ∈ {x : Coordinate 2 | x ∈ getB (classRepsData.getD r.val 0)},
      ∀ b ∈ {x : Coordinate 2 | x ∈ getB (classRepsData.getD r.val 0)},
      ⁅a, b⁆ ∈ hpSub r.val := by
  intro a ha b hb
  simp only [Set.mem_setOf_eq] at ha hb
  have h := commIn_at r
  simp only [commInCheck, spIdx, List.all_eq_true] at h
  have hs : siftB 2 (hpData.getD r.val []) (commutatorC a b) = true := h a ha b hb
  have hmem : commutatorC a b ∈ ofList 2 hq2 (hpData.getD r.val []) :=
    (sift_mem_iff hq2 _ (hpSub_wf r) _).mp hs
  rwa [commutatorC_eq] at hmem

/-- **`[H,H] ≤ H'`** — the abelian-quotient direction. -/
theorem commutator_reps_le_hpSub (r : Fin 148) :
    _root_.commutator (reps r) ≤ (hpSub r.val).subgroupOf (reps r) := by
  apply commutator_le_of_comm_mem (h := classRepsData.getD r.val 0)
  refine commutator_gens_mem
    (S := {x : Coordinate 2 | x ∈ getB (classRepsData.getD r.val 0)})
    ?_ (gen_comm_mem_hpSub r)
  intro z hz g hg
  have : z ∈ Subgroup.normalizer (hpSub r.val) := reps_le_normalizer_hpSub r hz
  exact (Subgroup.mem_normalizer_iff.mp this g).mp hg

/-! ## The cardinality squeeze -/

/-- **`H' = [H,H]`.** The emitted candidate equals the ambient image of the derived
subgroup of `reps r`. -/
theorem hpSub_eq_derived (r : Fin 148) :
    (_root_.commutator (reps r)).map (reps r).subtype = hpSub r.val := by
  -- Lagrange for [H,H] inside H, tied to the abelianization order = charCounts.
  have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup (_root_.commutator (reps r))
  have hab : Nat.card (Abelianization (reps r)) = charCounts.getD r.val 0 :=
    card_abelianization_reps_all2 r
  have hcardH : Nat.card (reps r) = 5 ^ (getB (classRepsData.getD r.val 0)).length := by
    change Nat.card (subAt (classRepsData.getD r.val 0)) = _
    exact card_subAt (classReps_lt r.val r.isLt)
  have hcc : charCounts.getD r.val 0 * 5 ^ (hpData.getD r.val []).length
      = 5 ^ (getB (classRepsData.getD r.val 0)).length :=
    Nat.eq_of_beq_eq_true (card_at r)
  have hpos : 0 < charCounts.getD r.val 0 := by
    rcases Nat.eq_zero_or_pos (charCounts.getD r.val 0) with h0 | h
    · exfalso; rw [h0, Nat.zero_mul] at hcc
      exact (pow_pos (by norm_num : (0:ℕ) < 5) _).ne' hcc.symm
    · exact h
  -- key: |H| = charCounts · |[H,H]|  (Abelianization is defeq the commutator quotient)
  have hq : Nat.card (↥(reps r) ⧸ _root_.commutator (reps r)) = charCounts.getD r.val 0 := hab
  have key : Nat.card (reps r)
      = charCounts.getD r.val 0 * Nat.card (_root_.commutator (reps r)) := by
    rw [hlag, hq]
  -- hence |[H,H]| = |H'| = 5 ^ hpLen
  have hcardComm : Nat.card (_root_.commutator (reps r)) = 5 ^ (hpData.getD r.val []).length := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc charCounts.getD r.val 0 * Nat.card (_root_.commutator (reps r))
        = Nat.card (reps r) := key.symm
      _ = 5 ^ (getB (classRepsData.getD r.val 0)).length := hcardH
      _ = charCounts.getD r.val 0 * 5 ^ (hpData.getD r.val []).length := hcc.symm
  -- the derived image has the same card, and sits inside H'
  have hdmap_card :
      Nat.card ((_root_.commutator (reps r)).map (reps r).subtype)
        = Nat.card (_root_.commutator (reps r)) :=
    (Nat.card_congr
      (Subgroup.equivMapOfInjective (_root_.commutator (reps r)) (reps r).subtype
        (reps r).subtype_injective).toEquiv).symm
  have hle : (_root_.commutator (reps r)).map (reps r).subtype ≤ hpSub r.val :=
    Subgroup.map_le_iff_le_comap.mpr (commutator_reps_le_hpSub r)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_hpSub r, hdmap_card, hcardComm]

/-! ## Transversal semantics -/

/-- The certified transversal has `|H/H'| = charCounts r` elements. -/
theorem transCard (r : Fin 148) :
    (transData.getD r.val []).length = charCounts.getD r.val 0 :=
  Nat.eq_of_beq_eq_true (transCount_at r)

end Q2

end LeanDring.P5Presentation
