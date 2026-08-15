/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.SpeciesColumn
import LeanDring.P5.Certificate.SpeciesTable.Twin1.SpeciesLink
import LeanDring.P5.Certificate.SpeciesTable.Twin1.SpeciesOrbits

/-!
# `SpeciesColsComplete` for `Coordinate 1`: the concrete `q = 1` coverage

Assembles the three concrete reductions that show the `2724` orbit-representative
columns `(reps r, T[p])` (`p` a `cosetIsRep` transversal position) form a
*complete* family of species columns:

* **Step 1** (`species_col_conj_to_reps`, `Twin1/SpeciesColumn.lean`) — conjugate any column
  onto one of the `148` subgroup-class reps `reps r`.
* **Step 2** (`exists_trans_pos`) — reduce `h ∈ reps r` modulo `H' = [H,H]` to a
  certified `H'`-coset transversal position `T[p]`.  The transversal is complete
  because `reduceAux` is a canonical left-coset transversal (`reduceAux_mul_mem`),
  making `p ↦ Abelianization.of ⟨T[p]⟩` an injection from `Fin |T|` (card
  `charCounts r`, `transCard`) into `H^ab` (card `charCounts r`,
  `card_abelianization_reps_all`), hence a bijection.
* **Step 3** (`species_reduces_to_rep`) — normalise a transversal position to its
  `N_G(reps r)`-orbit representative along the certified BFS spanning tree
  (`cosetReach_from_rep`), each step a genuine conjugation by a normalizer
  generator (`cosetActOK`), composed by the single-step lemma `species_cosetStep`.

The capstone `speciesColsComplete_coordinate1` packages the orbit-representative
columns and discharges `SpeciesColsComplete`.
-/

namespace LeanDring.P5Presentation

open Fin.NatCast
open scoped commutatorElement

-- file-level maxHeartbeats: dozens of decide-heavy declarations below need it
set_option linter.style.setOption false
set_option maxHeartbeats 4000000

/-! ## Certificate extraction: transversal membership and distinctness -/

theorem transMem_at (r : Fin 148) : transMemCheck r.val = true := by
  have h := speciesCheck_at r; simp only [speciesCheck, Bool.and_eq_true] at h
  exact h.1.1.2

theorem transDistinct_at (r : Fin 148) : transDistinctCheck r.val = true := by
  have h := speciesCheck_at r; simp only [speciesCheck, Bool.and_eq_true] at h
  exact h.1.2

/-- Every certified transversal element lies in `H = reps r`. -/
theorem transElt_mem (r : Fin 148) {p : Nat}
    (hp : p < (transData.getD r.val []).length) :
    ((transData.getD r.val []).getD p zc) ∈ reps r := by
  have h := transMem_at r
  simp only [transMemCheck, spIdx, List.all_eq_true] at h
  have hmem : ((transData.getD r.val []).getD p zc) ∈ transData.getD r.val [] := by
    rw [List.getD_eq_getElem _ zc hp]; exact List.getElem_mem hp
  have hs : siftB 1 (getB (classRepsData.getD r.val 0))
      ((transData.getD r.val []).getD p zc) = true :=
    h _ hmem
  exact (siftB_getB_iff (classReps_lt r.val r.isLt) _).mp hs

/-! ## `reduceAux` decides the `H'`-coset of a transversal element -/

/-- If `a⁻¹ b ∈ H'` then `a` and `b` have the same `reduceAux` normal form. -/
theorem hpSub_reduceAux (r : Fin 148) (a b : Coordinate 1)
    (hab : a⁻¹ * b ∈ hpSub r.val) :
    reduceAux 1 (hpData.getD r.val []) a = reduceAux 1 (hpData.getD r.val []) b := by
  have hthis := reduceAux_mul_mem hq1 (hpData.getD r.val []) (hpSub_wf r) a (a⁻¹ * b) hab
  rw [show a * (a⁻¹ * b) = b from by group] at hthis
  exact hthis.symm

/-- Distinct transversal positions have distinct `reduceAux` normal forms. -/
theorem reduceAux_trans_inj (r : Fin 148) {p p' : Nat}
    (hp : p < (transData.getD r.val []).length)
    (hp' : p' < (transData.getD r.val []).length)
    (h : reduceAux 1 (hpData.getD r.val []) ((transData.getD r.val []).getD p zc)
       = reduceAux 1 (hpData.getD r.val []) ((transData.getD r.val []).getD p' zc)) :
    p = p' := by
  set red := (transData.getD r.val []).map (reduceAux 1 (hpData.getD r.val [])) with hred
  have hnodup : red.Nodup := by
    have hd := transDistinct_at r
    simp only [transDistinctCheck, Nat.beq_eq] at hd
    have hlen : red.dedup.length = red.length := by rw [hred, hd, List.length_map]
    have heq : red.dedup = red := (List.dedup_sublist red).eq_of_length hlen
    rw [← heq]; exact List.nodup_dedup red
  have hpl : p < red.length := by rw [hred, List.length_map]; exact hp
  have hpl' : p' < red.length := by rw [hred, List.length_map]; exact hp'
  have hgp : red[p] =
      reduceAux 1 (hpData.getD r.val []) ((transData.getD r.val []).getD p zc) := by
    simp only [hred, List.getElem_map, List.getD_eq_getElem _ zc hp]
  have hgp' : red[p'] =
      reduceAux 1 (hpData.getD r.val []) ((transData.getD r.val []).getD p' zc) := by
    simp only [hred, List.getElem_map, List.getD_eq_getElem _ zc hp']
  have hpp2 : red[p] = red[p'] := by rw [hgp, hgp', h]
  exact hnodup.getElem_inj_iff.mp hpp2

end LeanDring.P5Presentation

/-! ## Species-level helpers and the three concrete steps -/

namespace LeanDring.DRing

open MonGSet MulAction SpeciesTableEncoding
open P5Presentation
open scoped commutatorElement

-- the decide-heavy proofs over the embedded certificate data need the raise
set_option linter.style.setOption false
set_option maxHeartbeats 4000000

/-- **The ambient `H'`-invariance of species.** If `(a : G)⁻¹ * (b : G) ∈ H'` for
`a b : ↥(reps r)`, then `φ_{reps r, a} = φ_{reps r, b}`.  Combines
`hpSub_eq_derived` (`H'` is the ambient image of `[H,H]`) with the abstract
`species_eq_of_abelianization_eq`. -/
theorem species_eq_of_hpSub (r : Fin 148) (a b : ↥(reps r))
    (hab : (a : Coordinate 1)⁻¹ * (b : Coordinate 1) ∈ hpSub r.val) :
    species (reps r) a = species (reps r) b := by
  have hsubcoe : (reps r).subtype (a⁻¹ * b) = (a : Coordinate 1)⁻¹ * (b : Coordinate 1) := by
    rw [map_mul, map_inv]; rfl
  have hmap : (reps r).subtype (a⁻¹ * b)
      ∈ (_root_.commutator ↥(reps r)).map (reps r).subtype := by
    rw [hpSub_eq_derived r, hsubcoe]; exact hab
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hmap
  have hyc : y = a⁻¹ * b := (reps r).subtype_injective hyeq
  have hc : a⁻¹ * b ∈ _root_.commutator ↥(reps r) := hyc ▸ hy
  refine species_eq_of_abelianization_eq (reps r) a b ?_
  have hof : Abelianization.of (a⁻¹ * b) = 1 := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker] at hc; exact hc
  rw [map_mul, map_inv] at hof
  exact inv_mul_eq_one.mp hof

/-! ## Step 2: transversal completeness -/

/-- **Step 2.** Every `h ∈ reps r` is `H'`-coset-equal to a certified transversal
position `T[p]`, hence has the same species. -/
theorem exists_trans_pos (r : Fin 148) (h : ↥(reps r)) :
    ∃ (p : Nat) (hp : p < (transData.getD r.val []).length),
      species (reps r) h
        = species (reps r) ⟨(transData.getD r.val []).getD p zc, transElt_mem r hp⟩ := by
  classical
  haveI : Fintype ↥(reps r) := Fintype.ofFinite _
  haveI : Finite ↥(reps r) := Finite.of_fintype _
  haveI : Finite (Abelianization ↥(reps r)) := Quotient.finite _
  haveI : Fintype (Abelianization ↥(reps r)) := Fintype.ofFinite _
  set L := (transData.getD r.val []).length with hL
  let f : Fin L → Abelianization ↥(reps r) :=
    fun p => Abelianization.of ⟨(transData.getD r.val []).getD p.val zc, transElt_mem r p.isLt⟩
  have hcard : Fintype.card (Fin L) = Fintype.card (Abelianization ↥(reps r)) := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, card_abelianization_reps_all, hL, transCard]
  have hinj : Function.Injective f := by
    intro p p' hpp
    apply Fin.ext
    have hof : Abelianization.of
        ((⟨(transData.getD r.val []).getD p.val zc, transElt_mem r p.isLt⟩ : ↥(reps r))⁻¹
          * ⟨(transData.getD r.val []).getD p'.val zc, transElt_mem r p'.isLt⟩) = 1 := by
      rw [map_mul, map_inv]
      change (f p)⁻¹ * f p' = 1
      rw [hpp]; exact inv_mul_cancel _
    have hc :
        (⟨(transData.getD r.val []).getD p.val zc, transElt_mem r p.isLt⟩ : ↥(reps r))⁻¹
        * ⟨(transData.getD r.val []).getD p'.val zc, transElt_mem r p'.isLt⟩
        ∈ _root_.commutator ↥(reps r) := by
      rw [← Abelianization.ker_of, MonoidHom.mem_ker]; exact hof
    have hmap : ((⟨(transData.getD r.val []).getD p.val zc, transElt_mem r p.isLt⟩ :
            ↥(reps r)) : Coordinate 1)⁻¹
        * ((⟨(transData.getD r.val []).getD p'.val zc, transElt_mem r p'.isLt⟩ :
            ↥(reps r)) : Coordinate 1) ∈ hpSub r.val := by
      rw [← hpSub_eq_derived r]
      refine Subgroup.mem_map.mpr ⟨_, hc, ?_⟩
      rw [map_mul, map_inv]; rfl
    exact reduceAux_trans_inj r p.isLt p'.isLt (hpSub_reduceAux r _ _ hmap)
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩
  obtain ⟨p, hp⟩ := hbij.2 (Abelianization.of h)
  exact ⟨p.val, p.isLt, species_eq_of_abelianization_eq (reps r) h _ hp.symm⟩

/-! ## Step 3: normalise a transversal position to its orbit representative -/

/-- `n = normGenAt r k` normalizes `reps r`, packaged as a conjugation
automorphism fixing `reps r`. -/
theorem map_conj_normGen (r : Fin 148) (k : Nat) :
    (reps r).map (MulAut.conj (normGenAt r.val k)).toMonoidHom = reps r := by
  set n := normGenAt r.val k with hn
  have hnmem : n ∈
      Subgroup.normalizer ((reps r : Subgroup (Coordinate 1)) : Set (Coordinate 1)) := by
    rw [hn]; exact normGen_getD_mem r k
  have hnormiff : ∀ y : Coordinate 1, y ∈ reps r ↔ n⁻¹ * y * n ∈ reps r := by
    intro y
    have h := (Subgroup.mem_normalizer_iff''.mp hnmem) y
    simpa only [SetLike.mem_coe] using h
  ext z
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine (hnormiff (n * w * n⁻¹)).mpr ?_
    rw [show n⁻¹ * (n * w * n⁻¹) * n = w from by group]; exact hw
  · intro hz
    exact ⟨n⁻¹ * z * n, (hnormiff z).mp hz, by group⟩

/-- **The single normaliser step (species side).** If the coset action carries `p`
to `p' = cosetGenAct r k p`, the two transversal columns carry the same species:
`φ_{reps r, T[p']} = φ_{reps r, T[p]}`.  The move is conjugation by
`n = normGenAt r k ∈ N_G(reps r)` (`species_of_conjSub`) followed by the residual
`H'`-shift certified in `cosetActOK` (`species_eq_of_hpSub`). -/
theorem species_cosetStep (r : Fin 148) (k p : Nat)
    (hk : k < (cosetActData.getD r.val []).length)
    (hp : p < (transData.getD r.val []).length)
    (memp : ((transData.getD r.val []).getD p zc) ∈ reps r)
    (memp' : ((transData.getD r.val []).getD (cosetGenAct r.val k p) zc) ∈ reps r) :
    species (reps r) ⟨_, memp'⟩ = species (reps r) ⟨_, memp⟩ := by
  set n := normGenAt r.val k with hn
  -- Genuine `Coordinate 1` handles for the two transversal columns, so every group
  -- operation below is elaborated at `Coordinate 1` (via the subtype coercion `↑a`).
  set a : ↥(reps r) := ⟨(transData.getD r.val []).getD p zc, memp⟩ with ha
  set a' : ↥(reps r) :=
    ⟨(transData.getD r.val []).getD (cosetGenAct r.val k p) zc, memp'⟩ with ha'
  -- extract the coset-action fact
  have hrow := (List.all_eq_true.mp (checkCosetAct_at r)) k (List.mem_range.mpr hk)
  have hcell := (List.all_eq_true.mp hrow) p (List.mem_range.mpr hp)
  simp only [cosetActOK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hcell
  obtain ⟨⟨_, hsift⟩, _⟩ := hcell
  -- `n⁻¹ · T[p] · n ∈ reps r`
  have hnmem : n ∈
      Subgroup.normalizer ((reps r : Subgroup (Coordinate 1)) : Set (Coordinate 1)) := by
    rw [hn]; exact normGen_getD_mem r k
  have hnormiff : ∀ y : Coordinate 1, y ∈ reps r ↔ n⁻¹ * y * n ∈ reps r := by
    intro y
    have h := (Subgroup.mem_normalizer_iff''.mp hnmem) y
    simpa only [SetLike.mem_coe] using h
  have wmem : n⁻¹ * (a : Coordinate 1) * n ∈ reps r := (hnormiff _).mp a.2
  -- the certified `H'`-membership, as `T[p']⁻¹ · (n⁻¹ · T[p] · n) ∈ H'`
  have hmemHp : (a' : Coordinate 1)⁻¹ * (n⁻¹ * (a : Coordinate 1) * n) ∈ hpSub r.val :=
    (sift_mem_iff hq1 _ (hpSub_wf r) _).mp hsift
  -- conjugation move
  have hg : (reps r).map (MulAut.conj n).toMonoidHom = reps r := map_conj_normGen r k
  have hconj : species (reps r) a
      = species (reps r) (⟨n⁻¹ * (a : Coordinate 1) * n, wmem⟩) :=
    species_of_conjSub (reps r) ⟨n⁻¹ * (a : Coordinate 1) * n, wmem⟩ n hg a (by group)
  -- residual `H'`-shift
  have hshift : species (reps r) a'
      = species (reps r) (⟨n⁻¹ * (a : Coordinate 1) * n, wmem⟩) :=
    species_eq_of_hpSub r a' ⟨n⁻¹ * (a : Coordinate 1) * n, wmem⟩ hmemHp
  rw [hshift, ← hconj]

/-- **Step 3.** Every transversal position `p` reduces, along the certified BFS
spanning tree, to its orbit representative `q` (`cosetIsRep q = true`), with equal
species — mirroring `cosetReach_from_rep` and composing `species_cosetStep`. -/
theorem species_reduces_to_rep (r : Fin 148) : ∀ (dep p : Nat)
    (hp : p < (transData.getD r.val []).length)
    (_hdep : (cosetTreeDepth.getD r.val []).getD p 0 = dep),
    ∃ (q : Nat) (hq : q < (transData.getD r.val []).length),
      (cosetIsRep.getD r.val []).getD q false = true ∧
      species (reps r) ⟨(transData.getD r.val []).getD p zc, transElt_mem r hp⟩
        = species (reps r) ⟨(transData.getD r.val []).getD q zc, transElt_mem r hq⟩ := by
  intro dep
  induction dep using Nat.strong_induction_on with
  | _ dep IH =>
    intro p hp hdep
    have ht := (List.all_eq_true.mp (checkCosetTree_at r)) p (List.mem_range.mpr hp)
    by_cases hr : (cosetIsRep.getD r.val []).getD p false = true
    · exact ⟨p, hp, hr, rfl⟩
    · have hrf : (cosetIsRep.getD r.val []).getD p false = false := by
        cases h : (cosetIsRep.getD r.val []).getD p false with
        | false => rfl
        | true => exact absurd h hr
      simp only [cosetTreeOK, hrf, Bool.not_false, Bool.false_and, Bool.false_or, Bool.true_and,
        Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at ht
      obtain ⟨⟨⟨⟨hklt, hparlt⟩, hdlt⟩, hmove⟩, _hlab⟩ := ht
      set k := (cosetTreeGen.getD r.val []).getD p 0 with hk_def
      set j := (cosetTreePar.getD r.val []).getD p 0 with hj_def
      have hpardep : (cosetTreeDepth.getD r.val []).getD j 0 < dep := hdep ▸ hdlt
      obtain ⟨q, hq, hqrep, hIH⟩ := IH _ hpardep j hparlt rfl
      -- `cosetGenAct r k j` is definitionally the certified move value `T`-index, `= p`
      have hcga : cosetGenAct r.val k j = p := hmove
      have memcga : ((transData.getD r.val []).getD (cosetGenAct r.val k j) zc) ∈ reps r := by
        rw [hcga]; exact transElt_mem r hp
      -- single step: T[cosetGenAct r k j] ~ T[j]
      have hstep := species_cosetStep r k j hklt hparlt (transElt_mem r hparlt) memcga
      -- convert the value `cosetGenAct r k j` back to `p`
      have hpp' : species (reps r) ⟨(transData.getD r.val []).getD p zc, transElt_mem r hp⟩
          = species (reps r)
              ⟨(transData.getD r.val []).getD (cosetGenAct r.val k j) zc, memcga⟩ := by
        congr 1
        apply Subtype.ext
        change (transData.getD r.val []).getD p zc
          = (transData.getD r.val []).getD (cosetGenAct r.val k j) zc
        rw [hcga]
      refine ⟨q, hq, hqrep, ?_⟩
      rw [hpp', hstep, hIH]

end LeanDring.DRing

/-! ## The capstone: `SpeciesColsComplete` for the orbit-representative columns -/

namespace LeanDring.DRing

open P5Presentation
open MonGSet

/-- The `2724` orbit-representative species columns of `Coordinate 1`, indexed by a
subgroup-class rep `r` together with a `cosetIsRep` transversal position `p`. -/
def orbitRepColumns :
    (Σ r : Fin 148, {p : Nat //
        p < (transData.getD r.val []).length ∧ (cosetIsRep.getD r.val []).getD p false = true})
      → SpeciesColumn (Coordinate 1) :=
  fun x =>
    ⟨reps x.1, ⟨(transData.getD x.1.val []).getD x.2.val zc, transElt_mem x.1 x.2.2.1⟩⟩

/-- **The capstone.** The orbit-representative columns form a complete family of
species columns for `Coordinate 1`: every species column `(H, h)` has the same
species ring homomorphism as one of them. -/
theorem speciesColsComplete_coordinate1 :
    SpeciesColsComplete orbitRepColumns := by
  intro col
  obtain ⟨H, h⟩ := col
  obtain ⟨r, h', e1⟩ := species_col_conj_to_reps H h
  obtain ⟨p, hp, e2⟩ := exists_trans_pos r h'
  obtain ⟨q, hq, hqrep, e3⟩ := species_reduces_to_rep r _ p hp rfl
  refine ⟨⟨r, ⟨q, ⟨hq, hqrep⟩⟩⟩, ?_⟩
  rw [e1, e2]
  exact e3

/-- **The glue (column half).** Whenever a source family `colsG` and a row
bijection `σ` reproduce the `2724` orbit-representative columns of
`Coordinate 1`, the column-completeness proved here
(`speciesColsComplete_coordinate1`) upgrades that match to an abstract `D`-ring
isomorphism `DRing G ≃+* DRing (Coordinate 1)`.

The row-side hypotheses `σ` and `hmatch` are discharged by
`P5Presentation.sigmaEquiv` and `P5Presentation.hmatch`
(`LeanDring/P5/Certificate/RingIsomorphism/Twin1/Assembly.lean`), which
instantiate the `Coordinate 2` twin of this lemma to give the unconditional
`dring_equiv_coordinate12`. -/
theorem dringEquiv_of_rowMatch_coordinate1 {G : Type} [Group G] [Fintype G]
    {ι : Type*} (colsG : ι → SpeciesColumn G)
    (σ : CharPairClass G ℂˣ ≃ CharPairClass (Coordinate 1) ℂˣ)
    (hmatch : ∀ i' : (Σ r : Fin 148, {p : Nat //
          p < (transData.getD r.val []).length ∧
            (cosetIsRep.getD r.val []).getD p false = true}),
        ∃ i : ι, ∀ c : CharPairClass G ℂˣ,
          species (orbitRepColumns i').1 (orbitRepColumns i').2 (classElt (σ c)) =
            species (colsG i).1 (colsG i).2 (classElt c)) :
    Nonempty (DRing G ≃+* DRing (Coordinate 1)) :=
  nonempty_dringEquiv_of_reduced colsG orbitRepColumns
    speciesColsComplete_coordinate1 σ hmatch

end LeanDring.DRing
