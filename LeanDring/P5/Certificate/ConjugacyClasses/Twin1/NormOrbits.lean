/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.ConjugacyClasses.Twin1.NormChunk.Chunk01
import LeanDring.P5.Certificate.ConjugacyClasses.Twin1.NormChunk.Chunk02
import LeanDring.P5.Certificate.ConjugacyClasses.Twin1.NormChunk.Chunk03
import LeanDring.P5.Certificate.ConjugacyClasses.Twin1.NormChunk.Chunk04

/-!
# Normalizer-orbit partition of the character lists

Assembly of the four chunked kernel checks
(`NormChunk/Chunk01.lean`–`NormChunk/Chunk04.lean`) into whole-range facts, and
the aggregate counts of the `N_G(H)`-orbit partition of the certified character
lists `charsAt r`.

Building on the certified per-representative character lists and the conjugacy
classification of subgroups, for each of the 148 subgroup-class representatives
`H = reps r` the generator emits the abelianized-conjugation matrices of
`N_G(H)`, the induced permutation of `charsAt r`, and a BFS orbit partition with
spanning-tree witnesses. The kernel certifies (sift-free, pure `ZMod 25`/`Nat`
arithmetic):

* `checkAct_all` — the matrices induce the emitted permutation and the orbit
  labels are invariant under every generator's action;
* `checkTree_all` — every character reaches its orbit representative along the
  spanning tree.

From these:

* `pairClassTotal` — `Σ_r orbitCountR r = 2724`, the pair-class transversal size
  (= `rank D(G)` for `q = 1`);
* `orbitCount_distribution` — the per-representative orbit counts realise the
  distribution `{1:1, 5:12, 9:61, 13:5, 25:56, 29:1, 45:11, 125:1}`;
* `orbitFibre_by_order` — the fibre split of the **orbits** by the order of the
  representative character is `{1 : 148, 5 : 2376, 25 : 200}`.

## Where the fusion happens

The certified raw character fibre by order (`charFibre_totals`) is
`{1 : 148, 5 : 3688, 25 : 1400}`; the orbit fibre above is
`{1 : 148, 5 : 2376, 25 : 200}`. So it is the **order-25** characters that fuse
most (`1400 → 200`), while the order-5 ones fuse only mildly (`3688 → 2376`).

In particular the fibre is *not* `{148, 1176, 1400}`, which is what one gets by
reading the raw order-25 count `1400` as already an orbit count — i.e. by
assuming the order-25 characters are `N`-fixed. The truth runs the other way, and
is forced group-theoretically: for a subgroup on which `N_G(H)` induces a
nontrivial (order-5) automorphism, the faithful (order-25) characters split into
orbits of size 5, while the order-5 characters — which factor through the
`p`-th-power quotient — stay fixed (e.g. the cyclic `C₂₅` case, `9` orbits
`= 1 + 4 + 4`).
-/

namespace LeanDring.P5Presentation

open Fin.NatCast

set_option maxRecDepth 100000
-- file-level maxHeartbeats: dozens of decide-heavy declarations below need it
set_option linter.style.setOption false
set_option maxHeartbeats 4000000

/-! ## Whole-range checks from the four chunks -/

/-- **Action + label invariance for all 148 representatives.** -/
theorem checkAct_all : (List.range 148).all checkAct = true :=
  all148_of_chunks checkAct normActChunk0 normActChunk1 normActChunk2 normActChunk3

/-- **BFS spanning-tree validity for all 148 representatives.** -/
theorem checkTree_all : (List.range 148).all checkTree = true :=
  all148_of_chunks checkTree normTreeChunk0 normTreeChunk1 normTreeChunk2 normTreeChunk3

/-- **Per-position data-length sanity for all 148 representatives.** -/
theorem checkLen_all : (List.range 148).all checkLen = true :=
  all148_of_chunks checkLen normLenChunk0 normLenChunk1 normLenChunk2 normLenChunk3

/-- Extract a single `checker r = true` from a whole-range check. -/
theorem normChecker_at {f : ℕ → Bool} (h : (List.range 148).all f = true) (r : Fin 148) :
    f r.val = true :=
  (List.all_eq_true.mp h) r.val (List.mem_range.mpr r.isLt)

/-- Per-representative action + label-invariance certificate. -/
theorem checkAct_at (r : Fin 148) : checkAct r.val = true := normChecker_at checkAct_all r

/-- Per-representative spanning-tree certificate. -/
theorem checkTree_at (r : Fin 148) : checkTree r.val = true := normChecker_at checkTree_all r

/-! ## Aggregate: the 2724 pair-class transversal -/

/-- **The pair-class transversal size.** Summed over the 148 subgroup classes, the
number of `N_G(H)`-orbits of linear characters is `2724` — the number of
`G`-conjugacy classes of character pairs `[K, λ]` for `q = 1` (`= rank D(G)`).
Of these, `148` are order-1 orbits, one per subgroup class. -/
theorem pairClassTotal : ((List.range 148).map orbitCountR).sum = 2724 := by decide

/-- **The per-representative orbit-count distribution** `{1:1, 5:12, 9:61, 13:5,
25:56, 29:1, 45:11, 125:1}`, cross-checking the expected fingerprint. -/
theorem orbitCount_distribution :
    ((List.range 148).filter (fun r => Nat.beq (orbitCountR r) 1)).length = 1 ∧
    ((List.range 148).filter (fun r => Nat.beq (orbitCountR r) 5)).length = 12 ∧
    ((List.range 148).filter (fun r => Nat.beq (orbitCountR r) 9)).length = 61 ∧
    ((List.range 148).filter (fun r => Nat.beq (orbitCountR r) 13)).length = 5 ∧
    ((List.range 148).filter (fun r => Nat.beq (orbitCountR r) 25)).length = 56 ∧
    ((List.range 148).filter (fun r => Nat.beq (orbitCountR r) 29)).length = 1 ∧
    ((List.range 148).filter (fun r => Nat.beq (orbitCountR r) 45)).length = 11 ∧
    ((List.range 148).filter (fun r => Nat.beq (orbitCountR r) 125)).length = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The orbit fibre split by character order.** The `2724` orbits split by the
order of the representative character as `{1 : 148, 5 : 2376, 25 : 200}`. The
order-1 count `148` is exactly one trivial-character orbit per subgroup class.
See the module header for why it is the order-25 characters that fuse most. -/
theorem orbitFibre_by_order :
    ((List.range 148).map orbFibreO1).sum = 148 ∧
    ((List.range 148).map orbFibreO5).sum = 2376 ∧
    ((List.range 148).map orbFibreO25).sum = 200 := by
  refine ⟨by decide, by decide, by decide⟩

/-- The three order-fibres of the orbits total `2724`, cross-checking
`pairClassTotal`. -/
theorem orbitFibre_total :
    ((List.range 148).map orbFibreO1).sum +
      ((List.range 148).map orbFibreO5).sum +
      ((List.range 148).map orbFibreO25).sum = 2724 := by decide

/-! ## Prop-level packaging: orbit reachability

The combinatorial interface consumed by `PairClass.lean`, stated purely at the
level of the character *vectors* and the emitted matrix action — no
character-theoretic interpretation, which is `PairClass.lean`'s job. The emitted
orbit labels are a complete, achieved invariant of the matrix action: every
character reaches its orbit's representative along the spanning tree, and the
label is stable under every generator. -/

/-- The action of `N`'s `k`-th generator on a character exponent vector of rep `r`. -/
def genAct (r k : Nat) (e : List (ZMod 25)) : List (ZMod 25) :=
  actVecZ ((normMats.getD r []).getD k []) e

/-- `e'` is reachable from `e` by a word of generator actions of rep `r`. -/
def MatReach (r : Nat) (e e' : List (ZMod 25)) : Prop :=
  ∃ w : List Nat, w.foldl (fun x k => genAct r k x) e = e'

theorem MatReach.refl (r : Nat) (e : List (ZMod 25)) : MatReach r e e := ⟨[], rfl⟩

theorem MatReach.step {r : Nat} {e e' : List (ZMod 25)} (k : Nat)
    (h : MatReach r e e') : MatReach r e (genAct r k e') := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w ++ [k], ?_⟩
  rw [List.foldl_append, hw]; rfl

/-- The per-`(k,p)` action fact of rep `r`, extracted from `checkAct_at`: the
matrix induces the emitted permutation entry, whose label is invariant. -/
theorem act_fact (r : Fin 148) (k p : Nat)
    (hk : k < (normMats.getD r.val []).length) (hp : p < (repChars.getD r.val []).length) :
    actVecZ ((normMats.getD r.val []).getD k []) ((repChars.getD r.val []).getD p []) =
        (repChars.getD r.val []).getD (((normActPos.getD r.val []).getD k []).getD p 0) [] ∧
      (normLabel.getD r.val []).getD (((normActPos.getD r.val []).getD k []).getD p 0) 0 =
        (normLabel.getD r.val []).getD p 0 := by
  have hrow := (List.all_eq_true.mp (checkAct_at r)) k (List.mem_range.mpr hk)
  have hp' := (List.all_eq_true.mp hrow) p (List.mem_range.mpr hp)
  simp only [orbActOK, Bool.and_eq_true, decide_eq_true_eq, Nat.beq_eq] at hp'
  exact ⟨hp'.1.2, hp'.2⟩

/-- **Label stability.** Applying any generator to a character keeps it in the
same orbit label — the matrix action respects the emitted partition. -/
theorem label_stable (r : Fin 148) (k p : Nat)
    (hk : k < (normMats.getD r.val []).length) (hp : p < (repChars.getD r.val []).length) :
    (normLabel.getD r.val []).getD (((normActPos.getD r.val []).getD k []).getD p 0) 0 =
      (normLabel.getD r.val []).getD p 0 :=
  (act_fact r k p hk hp).2

/-- **Reachability from the representative.** Every character of rep `r` is
reachable, along the spanning tree, from the character at its orbit label — the
purely combinatorial content needed to interpret orbits as character-pair
fusions. -/
theorem reach_from_rep (r : Fin 148) : ∀ (dep p : Nat), p < (repChars.getD r.val []).length →
    (normTreeDepth.getD r.val []).getD p 0 = dep →
    MatReach r.val ((repChars.getD r.val []).getD ((normLabel.getD r.val []).getD p 0) [])
      ((repChars.getD r.val []).getD p []) := by
  intro dep
  induction dep using Nat.strong_induction_on with
  | _ dep IH =>
    intro p hp hdep
    have ht := (List.all_eq_true.mp (checkTree_at r)) p (List.mem_range.mpr hp)
    by_cases hr : (normIsRep.getD r.val []).getD p false = true
    · simp only [orbTreeOK, hr, Bool.not_true, Bool.false_and, Bool.or_false, Bool.true_and,
        Bool.and_eq_true, Nat.beq_eq] at ht
      rw [ht.2]; exact MatReach.refl _ _
    · have hrf : (normIsRep.getD r.val []).getD p false = false := by
        cases h : (normIsRep.getD r.val []).getD p false with
        | false => rfl
        | true => exact absurd h hr
      simp only [orbTreeOK, hrf, Bool.not_false, Bool.false_and, Bool.false_or, Bool.true_and,
        Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at ht
      obtain ⟨⟨⟨⟨hklt, hparlt⟩, hdlt⟩, hmove⟩, hlab⟩ := ht
      have hpardep : (normTreeDepth.getD r.val []).getD
          ((normTreePar.getD r.val []).getD p 0) 0 < dep := hdep ▸ hdlt
      have hIH := IH _ hpardep ((normTreePar.getD r.val []).getD p 0) hparlt rfl
      rw [hlab] at hIH
      have haf := act_fact r ((normTreeGen.getD r.val []).getD p 0)
        ((normTreePar.getD r.val []).getD p 0) hklt hparlt
      have hstep : actVecZ ((normMats.getD r.val []).getD ((normTreeGen.getD r.val []).getD p 0) [])
          ((repChars.getD r.val []).getD ((normTreePar.getD r.val []).getD p 0) []) =
          (repChars.getD r.val []).getD p [] := by rw [haf.1, hmove]
      have hd := hIH.step ((normTreeGen.getD r.val []).getD p 0)
      rwa [genAct, hstep] at hd

/-- **Orbit ⟺ label.** Two characters of rep `r` share an orbit label iff each is
reachable from the common representative — the emitted labels are a complete,
achieved invariant of the matrix action (`reach_from_rep` gives reachability;
`label_stable` gives that reachability preserves the label). -/
theorem reach_of_sameLabel (r : Fin 148) (p p' : Nat)
    (hp : p < (repChars.getD r.val []).length) (hp' : p' < (repChars.getD r.val []).length)
    (hlab : (normLabel.getD r.val []).getD p 0 = (normLabel.getD r.val []).getD p' 0) :
    MatReach r.val ((repChars.getD r.val []).getD ((normLabel.getD r.val []).getD p 0) [])
        ((repChars.getD r.val []).getD p []) ∧
      MatReach r.val ((repChars.getD r.val []).getD ((normLabel.getD r.val []).getD p 0) [])
        ((repChars.getD r.val []).getD p' []) :=
  ⟨reach_from_rep r _ p hp rfl, hlab ▸ reach_from_rep r _ p' hp' rfl⟩

end LeanDring.P5Presentation
