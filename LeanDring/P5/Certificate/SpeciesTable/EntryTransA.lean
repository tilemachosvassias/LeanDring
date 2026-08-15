/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryData
import LeanDring.P5.Certificate.Characters.Twin1.CharExtend
import LeanDring.P5.Certificate.Characters.Twin2.CharExtend
import LeanDring.P5.Certificate.SubgroupInventory.Twin1.AllSubgroups
import LeanDring.P5.Certificate.SubgroupInventory.Twin2.AllSubgroups
import LeanDring.P5.Certificate.ConjugacyClasses.Twin1.NormCard
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.NormCard

/-!
# Species-table cells, data layer — the per-`K` / per-`(H,K)` certified transversal machinery

This module turns the *generic proven bridges* of
`LeanDring/P5/Certificate/SpeciesTable/Twin1/EntryFix.lean` /
`LeanDring/P5/Certificate/SpeciesTable/Twin1/EntryData.lean`
into **reusable, data-parameterized builders** that discharge, for a concrete
coordinate-vector transversal, exactly the three non-`decide` hypotheses that
`P5EntryCore.species_entry_eq_sum` / `entryCode_eq_species` consume per species
cell `φ_{H,h}[K,λ]`:

* `hinj`  — the transversal is injective mod `K`;
* `hfix`  — every representative names an `H`-fixed coset;
* `hcard` — the transversal length equals `|(G/K)^H|`.

Everything here is **generic over `q ∈ {1,2}`**, so *one* set of definitions
serves **both twins** (`Coordinate 1` and `Coordinate 2`): the group law, the
sift, and `reduceAux` are all the `q`-parameterized computable operations, and the
twins differ only in the *embedded data* (the transversals `R`), which is supplied
downstream.

## Cardinal numerals (all `K`, both twins)

`card_quotient_ofList` gives `|G/K| = 5^(5-|gK|)` for every well-formed echelon
list — pure Lagrange arithmetic (`card_ofList` + `card_subgroup_dvd_card`), no
carrier scan.  Specialised to the class representatives this is `card_quotient_reps`
(q=1) and `Q2.card_quotient_reps2` (q=2).  For the order-`25` **A-block**
(`|gK| = 2`) this reads `|G/K| = 125`.

## The A-block priority slice

The order-`25` A-block comprises the **42** length-2 echelon classes (indices
`13 … 54` in `repBases`), where the twins' `552` differing GAP species entries
live.  The structural fixed-point pruning is `|H| ≤ |K|`: a coset `⟦t⟧` is
`H`-fixed iff `t⁻¹Ht ⊆ K`, and `t⁻¹Ht ≅ H`, so `|H| > |K|` forces
`(G/K)^H = ∅`.  For `|K| = 25` the surviving columns are the **55** H-classes with
`|H| ≤ 25` (`|gH| ≤ 2`: the 1 trivial + 12 order-5 + 42 order-25 classes).

## The per-cell builders

* `cosetFun_inj_of_reduceAux` — `hinj` from a `decide`-able `reduceAux`-proxy
  injectivity (`Fintype.decidableInjectiveFintype` over `Fin n`, `n = [G:K]`).
* `cosetFun_fix_of_siftB` — `hfix` from the per-generator `siftB` bool
  (`coset_fixed_iff_siftB`), one kernel `decide` per representative.
* `fixedCard_eq_of_filter` — `hcard` from the filter-count identity over the full
  transversal `R` (`card_fixedPoints_eq_of_filter_card`), a single `decide` over
  the `[G:K]` cosets (`125` for the A-block — **no `3125`-carrier scan**).

The class-rep adapters `repsFix_of_siftB` / `repsInj_of_reduceAux` / `repsFixedCard`
(q=1) and their `Q2.*2` twins produce the exact `species_entry_eq_sum` /
`entryCode_eq_species` inputs for a concrete `(rK, rH)` cell by one application
each (the membership `hb` is then free — `LeanDring.conj_mem_of_fixedPoints`
applied to `hfix`).
-/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring

/-! ## Cardinal numerals: `|G/K| = 5^(5-|gK|)` (generic, both twins) -/

/-- **The quotient-card numeral.** For a well-formed echelon generator list `gK`
of length `k`, the coset space `G/⟨gK⟩` has `5^(5-k)` elements.  Pure Lagrange:
`|⟨gK⟩| = 5^k` (`card_ofList`) divides `|G| = 3125 = 5^5`, and the quotient card is
the complementary power.  No carrier scan. -/
theorem card_quotient_ofList {q : ℕ} (hq : q = 1 ∨ q = 2)
    (gK : List (Coordinate q)) (hwf : WF q hq gK) :
    letI := coordinateGroup q hq
    Nat.card (Coordinate q ⧸ ofList q hq gK) = 5 ^ (5 - gK.length) := by
  letI := coordinateGroup q hq
  have hcardG : Nat.card (Coordinate q) = 3125 := by
    rw [Nat.card_eq_fintype_card]; exact card_coordinates
  have hsub : Nat.card (ofList q hq gK) = 5 ^ gK.length := card_ofList hq gK hwf
  have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup (ofList q hq gK)
  have hlen : gK.length ≤ 5 := by
    have hdvd : Nat.card (ofList q hq gK) ∣ Nat.card (Coordinate q) :=
      Subgroup.card_subgroup_dvd_card _
    rw [hsub, hcardG, show (3125 : ℕ) = 5 ^ 5 by norm_num] at hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  have e1 : Nat.card (Coordinate q ⧸ ofList q hq gK) * 5 ^ gK.length = 3125 := by
    rw [← hsub, ← hlag, hcardG]
  have e2 : 5 ^ (5 - gK.length) * 5 ^ gK.length = 3125 := by
    rw [← pow_add, Nat.sub_add_cancel hlen]; norm_num
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) _) (e1.trans e2.symm)

/-- **Decidable membership in `⟨gK⟩`** for a well-formed echelon list, via the
`siftB` bool (`sift_mem_iff`).  This is the instance that lets `QuotientGroup.fintype`
build a genuine (computable) `Fintype (Coordinate q ⧸ ⟨gK⟩)` under the `letI`
group — auto-synthesis fails because the group is a `let`, not a real instance. -/
@[reducible]
def decMemOfList {q : ℕ} (hq : q = 1 ∨ q = 2) (gK : List (Coordinate q)) (hwf : WF q hq gK) :
    letI := coordinateGroup q hq
    DecidablePred (· ∈ ofList q hq gK) :=
  letI := coordinateGroup q hq
  fun x => decidable_of_iff _ (sift_mem_iff hq gK hwf x)

/-- **q=1 class-rep specialisation.** `|G/reps r| = 5^(5-|basisAt r|)`; `= 125`
for every order-`25` A-block class (`|basisAt r| = 2`). -/
theorem card_quotient_reps (r : Fin 148) :
    Nat.card (Coordinate 1 ⧸ reps r) = 5 ^ (5 - (basisAt r).length) := by
  rw [reps_eq_ofList r]
  exact card_quotient_ofList hq1 (basisAt r) (wf_basisAt r)

/-! ## Per-cell builders (generic over `q ∈ {1,2}`) -/

/-- **`hinj` from a `reduceAux`-proxy.** Injectivity of `i ↦ ⟦R i⟧` follows from
injectivity of the computable canonical form `i ↦ reduceAux gK (R i)`, which is a
`decide` for a concrete `R : Fin n → Coordinate q`. -/
theorem cosetFun_inj_of_reduceAux {q : ℕ} (hq : q = 1 ∨ q = 2)
    (gK : List (Coordinate q)) (hwf : WF q hq gK) {n : ℕ} (R : Fin n → Coordinate q)
    (hpx : Function.Injective (fun i => reduceAux q gK (R i))) :
    letI := coordinateGroup q hq
    Function.Injective
      (fun i => (QuotientGroup.mk (R i) : Coordinate q ⧸ ofList q hq gK)) := by
  letI := coordinateGroup q hq
  intro i j hij
  exact hpx ((coset_eq_iff_reduceAux hq gK hwf (R i) (R j)).mp hij)

/-- **`hfix` from per-generator `siftB`.** Every representative `T i` names an
`H = ⟨gH⟩`-fixed coset of `K = ⟨gK⟩`, provided each generator's return element
`(T i)⁻¹·g·(T i)` sifts into `K` — a kernel `decide` per representative. -/
theorem cosetFun_fix_of_siftB {q : ℕ} (hq : q = 1 ∨ q = 2)
    (gK gH : List (Coordinate q)) (hwfK : WF q hq gK) {m : ℕ} (T : Fin m → Coordinate q)
    (hfx : ∀ i, gH.all (fun g => siftB q gK (retConj q (T i) g)) = true) :
    letI := coordinateGroup q hq
    ∀ i, (QuotientGroup.mk (T i) : Coordinate q ⧸ ofList q hq gK)
        ∈ fixedPoints (ofList q hq gH) (Coordinate q ⧸ ofList q hq gK) := by
  letI := coordinateGroup q hq
  intro i
  exact (coset_fixed_iff_siftB hq gK gH hwfK (T i)).mpr (hfx i)

/-- **`hcard` from the filter count over a full transversal.** Given a full coset
transversal `R : Fin n → G` of `K` (bijective mod `K`, certified by the index
count `n = |G/K|` and the `reduceAux`-proxy injectivity), the number of
`H`-fixed cosets equals the number of transversal indices whose coset is
`H`-fixed — the `siftB`-filter count, a single `decide` over the `[G:K]` cosets. -/
theorem fixedCard_eq_of_filter {q : ℕ} (hq : q = 1 ∨ q = 2)
    (gK gH : List (Coordinate q)) (hwfK : WF q hq gK) {n : ℕ} (R : Fin n → Coordinate q)
    (hpx : Function.Injective (fun i => reduceAux q gK (R i)))
    (hcardq :
      Nat.card (letI := coordinateGroup q hq; Coordinate q ⧸ ofList q hq gK) = n)
    {m : ℕ}
    (hm : (Finset.univ.filter
        fun i => gH.all (fun g => siftB q gK (retConj q (R i) g)) = true).card = m) :
    letI := coordinateGroup q hq
    Nat.card
        (fixedPoints (ofList q hq gH) (Coordinate q ⧸ ofList q hq gK)) = m := by
  letI := coordinateGroup q hq
  letI : DecidablePred (· ∈ ofList q hq gK) := decMemOfList hq gK hwfK
  letI : Fintype (Coordinate q ⧸ ofList q hq gK) := QuotientGroup.fintype (ofList q hq gK)
  have hcardF : Fintype.card (Coordinate q ⧸ ofList q hq gK) = n := by
    rw [← Nat.card_eq_fintype_card]; exact hcardq
  letI : DecidablePred
      (fun i => (QuotientGroup.mk (R i) : Coordinate q ⧸ ofList q hq gK)
        ∈ fixedPoints (ofList q hq gH) (Coordinate q ⧸ ofList q hq gK)) :=
    fun i => decidable_of_iff _ (coset_fixed_iff_siftB hq gK gH hwfK (R i)).symm
  have hbij := transversalMod_bijective (ofList q hq gK) R hcardF
    (cosetFun_inj_of_reduceAux hq gK hwfK R hpx)
  have hfilt : (Finset.univ.filter
      fun i => (QuotientGroup.mk (R i) : Coordinate q ⧸ ofList q hq gK)
        ∈ fixedPoints (ofList q hq gH) (Coordinate q ⧸ ofList q hq gK)).card = m := by
    rw [Finset.filter_congr (fun i _ => coset_fixed_iff_siftB hq gK gH hwfK (R i))]
    exact hm
  have hF := card_fixedPoints_eq_of_filter_card (ofList q hq gH) (ofList q hq gK) R hbij hfilt
  rw [← Nat.card_eq_fintype_card] at hF
  exact hF

/-! ## q=1 concrete cell adapters — the `species_entry_eq_sum` inputs, one apply each

For a species cell `φ_{H,h}[K,λ]` with `K = reps rK`, `H = reps rH`, the three
non-`decide` hypotheses of `P5Presentation.species_entry_eq_sum` /
`entryCode_eq_species` are produced from the emitted `siftB`-data by exactly one
application each of the lemmas below.  The remaining membership `hb` is *free*
(`LeanDring.conj_mem_of_fixedPoints` applied to `hfix`).  `reps_eq_ofList`
mediates between the class-rep subgroup and its echelon `ofList` presentation. -/

/-- **`hfix` at the class-rep level (q=1).** Every representative of the emitted
fixed sub-transversal `T` names a `reps rH`-fixed coset of `reps rK`, given the
per-generator `siftB` bool. -/
theorem repsFix_of_siftB (rK rH : Fin 148) {m : ℕ} (T : Fin m → Coordinate 1)
    (hfxT : ∀ i, (basisAt rH).all
      (fun g => siftB 1 (basisAt rK) (retConj 1 (T i) g)) = true) :
    ∀ i, ((T i : Coordinate 1) : Coordinate 1 ⧸ reps rK)
        ∈ fixedPoints (reps rH) (Coordinate 1 ⧸ reps rK) := by
  have h := cosetFun_fix_of_siftB hq1 (basisAt rK) (basisAt rH) (wf_basisAt rK) T hfxT
  rw [reps_eq_ofList rK, reps_eq_ofList rH]; exact h

/-- **`hinj` at the class-rep level (q=1).** The emitted transversal is injective
mod `reps rK`, from the `decide`-able `reduceAux`-proxy injectivity. -/
theorem repsInj_of_reduceAux (rK : Fin 148) {m : ℕ} (T : Fin m → Coordinate 1)
    (hpxT : Function.Injective (fun i => reduceAux 1 (basisAt rK) (T i))) :
    Function.Injective (fun i => ((T i : Coordinate 1) : Coordinate 1 ⧸ reps rK)) := by
  have h := cosetFun_inj_of_reduceAux hq1 (basisAt rK) (wf_basisAt rK) T hpxT
  rw [reps_eq_ofList rK]; exact h

/-- **`hcard` at the class-rep level (q=1).** The fixed-point count of `reps rH`
on `G/reps rK` equals the `siftB`-filter count over the full transversal `R`
(`n = |G/reps rK| = 5^(5-|basisAt rK|)`, cf. `card_quotient_reps`). -/
theorem repsFixedCard (rK rH : Fin 148) {n : ℕ} (R : Fin n → Coordinate 1)
    (hpx : Function.Injective (fun i => reduceAux 1 (basisAt rK) (R i)))
    (hcardq : Nat.card (Coordinate 1 ⧸ reps rK) = n)
    {m : ℕ}
    (hm : (Finset.univ.filter fun i => (basisAt rH).all
        (fun g => siftB 1 (basisAt rK) (retConj 1 (R i) g)) = true).card = m) :
    Fintype.card (fixedPoints (reps rH) (Coordinate 1 ⧸ reps rK)) = m := by
  have h := fixedCard_eq_of_filter hq1 (basisAt rK) (basisAt rH) (wf_basisAt rK) R hpx
    (by rw [← reps_eq_ofList rK]; exact hcardq) hm
  rw [← Nat.card_eq_fintype_card, reps_eq_ofList rK, reps_eq_ofList rH]; exact h

/-! ## q=2 (twin) class-rep specialisation + cell adapters -/

namespace Q2

/-- **q=2 class-rep specialisation.** `|G/reps r| = 5^(5-|basisAt2 r|)`; `= 125`
for every order-`25` A-block class.  Twin of `card_quotient_reps`. -/
theorem card_quotient_reps2 (r : Fin 148) :
    Nat.card (Coordinate 2 ⧸ reps r) = 5 ^ (5 - (basisAt2 r).length) := by
  rw [reps_eq_ofList2 r]
  exact card_quotient_ofList hq2 (basisAt2 r) (wf_basisAt2 r)

/-- **`hfix` at the class-rep level (q=2 twin).** -/
theorem repsFix_of_siftB2 (rK rH : Fin 148) {m : ℕ} (T : Fin m → Coordinate 2)
    (hfxT : ∀ i, (basisAt2 rH).all
      (fun g => siftB 2 (basisAt2 rK) (retConj 2 (T i) g)) = true) :
    ∀ i, ((T i : Coordinate 2) : Coordinate 2 ⧸ reps rK)
        ∈ fixedPoints (reps rH) (Coordinate 2 ⧸ reps rK) := by
  have h := cosetFun_fix_of_siftB hq2 (basisAt2 rK) (basisAt2 rH) (wf_basisAt2 rK) T hfxT
  rw [reps_eq_ofList2 rK, reps_eq_ofList2 rH]; exact h

/-- **`hinj` at the class-rep level (q=2 twin).** -/
theorem repsInj_of_reduceAux2 (rK : Fin 148) {m : ℕ} (T : Fin m → Coordinate 2)
    (hpxT : Function.Injective (fun i => reduceAux 2 (basisAt2 rK) (T i))) :
    Function.Injective (fun i => ((T i : Coordinate 2) : Coordinate 2 ⧸ reps rK)) := by
  have h := cosetFun_inj_of_reduceAux hq2 (basisAt2 rK) (wf_basisAt2 rK) T hpxT
  rw [reps_eq_ofList2 rK]; exact h

/-- **`hcard` at the class-rep level (q=2 twin).** -/
theorem repsFixedCard2 (rK rH : Fin 148) {n : ℕ} (R : Fin n → Coordinate 2)
    (hpx : Function.Injective (fun i => reduceAux 2 (basisAt2 rK) (R i)))
    (hcardq : Nat.card (Coordinate 2 ⧸ reps rK) = n)
    {m : ℕ}
    (hm : (Finset.univ.filter fun i => (basisAt2 rH).all
        (fun g => siftB 2 (basisAt2 rK) (retConj 2 (R i) g)) = true).card = m) :
    Fintype.card (fixedPoints (reps rH) (Coordinate 2 ⧸ reps rK)) = m := by
  have h := fixedCard_eq_of_filter hq2 (basisAt2 rK) (basisAt2 rH) (wf_basisAt2 rK) R hpx
    (by rw [← reps_eq_ofList2 rK]; exact hcardq) hm
  rw [← Nat.card_eq_fintype_card, reps_eq_ofList2 rK, reps_eq_ofList2 rH]; exact h

end Q2

end LeanDring.P5Presentation
