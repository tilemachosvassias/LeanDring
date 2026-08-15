/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharExtend
import LeanDring.P5.Certificate.Characters.Twin2.CharCompleteFull
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.NormLink1
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.NormLink
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.ConjClasses
import LeanDring.Theory.DRing.FreeBasis

/-!
# The `CharPairClass` bridge for `Coordinate 2` (the pair-class bridge)

The final step: connect the certified concrete data (the 148 certified subgroup-class
representatives `reps`, Step-2's certified character lists `charsAt2`, and the normalizer-orbit
partition) to the *abstract* D-ring basis index type
`CharPairClass (Coordinate 2) ℂˣ`.

This file assembles, in stages:

* `exists_charOfVec2_eq` — Step-2 **completeness as surjectivity**: every linear
  character of `reps r` is one of the certified listed characters `charOfVec2 r e`
  (from `charsAt_complete_all2` + `charOfVec2_inj`, a Nodup list of full length).
* `isConjPair_reps_transport` — **subgroup-conjugation transport**: for
  `conjSub g (reps r) = K` and any `l : K →* ℂˣ`, the pair `(K, l)` is conjugate
  to a pair `(reps r, μ)` on the representative subgroup.
* `pairClass_realized_by_listed` — **surjectivity onto the pair classes**: every
  `c : CharPairClass (Coordinate 2) ℂˣ` equals `⟦(reps r, charOfVec2 r e)⟧` for
  some representative `r` and some *listed* certified character `e ∈ charsAt2 r`.
  Hence `CharPairClass (Coordinate 2) ℂˣ` is finite.
* `charForm2_genAct` — **the character↔vector dictionary** (the technical heart):
  applying the `k`-th normalizer-generator matrix `M_k` to a certified vector `e`
  computes the character of `e` precomposed with conjugation by `n = normGens r[k]`
  — `charForm2 B (M_k e) x = charForm2 B e (n⁻¹ x n)` for all `x ∈ reps r`, by closure
  induction using Step-1 additivity, `normMats_realize` and `dotZ_comm`.
* `class_genAct_eq` — **one normalizer step fuses two pair classes**: a `genAct`
  step preserves the `CharPairClass` (conjugation by `n ∈ N_G(reps r)` is an
  `IsConjPair` move fixing `reps r`).
* `class_reduces_to_rep` / `pairClass_realized_by_orbitRep` — **sharpened
  surjectivity**: iterating `class_genAct_eq` along the certified BFS spanning tree
  (`Twin2/NormOrbits.lean`, `reach_from_rep`), every pair class equals the class of the
  character at some *orbit-representative* position (`normIsRep q = true`). Since the
  orbit representatives number `Σ_r orbitCountR r = 2724` (`pairClassTotal`), this is
  the surjection realizing `|CharPairClass| ≤ 2724`.
* `rank_dring_coordinate2_of_card` — the rank corollary, conditional on the pair
  count: `Nat.card (CharPairClass …) = 2724 ⟹ Module.rank ℤ (DRing (Coordinate 2)) = 2724`.

## Closing the unconditional `= 2724` (both pieces done in `Twin2/PairClassInj.lean`)

Two pieces close `Nat.card (CharPairClass (Coordinate 2) ℂˣ) = 2724` (and hence the
unconditional rank via `rank_dring_coordinate2_of_card`): (i) the routine count that
the orbit-representative index type has cardinality `2724` (`pairClassTotal` +
`checkLen`); and (ii) **injectivity** — distinct orbit representatives give distinct
classes. (ii) is the harder converse of `class_genAct_eq`: an `IsConjPair` between
two orbit-rep pairs forces the conjugator into `N_G(reps r)` (`reps_pairwise_nonconj`
for the cross-representative case), and a `normGens`-closure induction reusing
`charForm2_genAct` identifies its action with a `MatReach` path, so the two positions
carry the same `normLabel` — contradiction. It reuses this file's dictionary.
-/

namespace LeanDring.P5Presentation

namespace Q2

open LeanDring LeanDring.MonGSet LeanDring.DRing

-- file-level maxHeartbeats: dozens of decide-heavy declarations below need it
set_option linter.style.setOption false
set_option maxHeartbeats 4000000

/-! ## Step-2 completeness as a surjectivity statement -/

/-- The certified finiteness of `Hom(reps r, ℂˣ)` (replicated from the count
bound proof), packaged as a `Fintype`. -/
noncomputable instance homFintype (r : Fin 148) : Fintype (↥(reps r) →* ℂˣ) := by
  classical
  haveI : Fintype ↥(reps r) := Fintype.ofFinite _
  haveI : Finite (Abelianization ↥(reps r)) := Quotient.finite _
  have hcard : Nat.card (↥(reps r) →* ℂˣ) = Nat.card (Abelianization ↥(reps r)) :=
    LeanDring.DRing.card_charHom_eq_card_abelianization
  haveI : Finite (↥(reps r) →* ℂˣ) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  exact Fintype.ofFinite _

/-- The list of all certified realized characters of `reps r`. -/
noncomputable def realizedChars (r : Fin 148) : List (↥(reps r) →* ℂˣ) :=
  (charsAt2 r).attach.map (fun p => charOfVec2 r p.1 (validAt r p.2))

theorem realizedChars_nodup (r : Fin 148) : (realizedChars r).Nodup := by
  apply List.Nodup.map_on ?_ (List.nodup_attach.mpr (charsAt2_nodup r))
  rintro ⟨a, ha⟩ _ ⟨b, hb⟩ _ hab
  exact Subtype.ext (charOfVec2_inj r ha hb hab)

theorem realizedChars_length (r : Fin 148) :
    (realizedChars r).length = Fintype.card (↥(reps r) →* ℂˣ) := by
  rw [realizedChars, List.length_map, List.length_attach, charsAt2_count r,
    ← charsAt_complete_all2 r, Nat.card_eq_fintype_card]

/-- **Step-2 completeness as surjectivity.** Every linear character of `reps r`
is realized by one of the certified listed exponent vectors. -/
theorem exists_charOfVec2_eq (r : Fin 148) (χ : ↥(reps r) →* ℂˣ) :
    ∃ e, ∃ he : e ∈ charsAt2 r, χ = charOfVec2 r e (validAt r he) := by
  classical
  have hmem : χ ∈ realizedChars r := by
    have hcard : (realizedChars r).toFinset = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [List.toFinset_card_of_nodup (realizedChars_nodup r), realizedChars_length r]
    rw [← List.mem_toFinset, hcard]
    exact Finset.mem_univ _
  obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hmem
  exact ⟨p.1, p.2, hpe.symm⟩

/-! ## Subgroup-conjugation transport of a character pair -/

/-- Membership: conjugating an element of `reps r` by `g` lands in `K`. -/
theorem conj_mem_transport (r : Fin 148) (g : Coordinate 2)
    {K : Subgroup (Coordinate 2)} (hK : conjSub g (reps r) = K)
    {k : Coordinate 2} (hk : k ∈ reps r) : g * k * g⁻¹ ∈ K := by
  rw [← hK, conjSub]
  exact Subgroup.mem_map.mpr
    ⟨k, hk, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩

/-- The reverse: a preimage of `K` under `g`-conjugation lies in `reps r`. -/
theorem mem_reps_of_conj (r : Fin 148) (g : Coordinate 2)
    {K : Subgroup (Coordinate 2)} (hK : conjSub g (reps r) = K)
    {k : Coordinate 2} (hk : g * k * g⁻¹ ∈ K) : k ∈ reps r := by
  rw [← hK, conjSub] at hk
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hk
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyeq
  have hyk : y = k := mul_left_cancel (mul_right_cancel hyeq)
  rwa [hyk] at hy

/-- The character on `reps r` transported from `l : K →* ℂˣ` along a conjugation
`conjSub g (reps r) = K`. -/
noncomputable def transportChar (r : Fin 148) (g : Coordinate 2)
    {K : Subgroup (Coordinate 2)} (hK : conjSub g (reps r) = K) (l : K →* ℂˣ) :
    ↥(reps r) →* ℂˣ where
  toFun x := l ⟨g * (x : Coordinate 2) * g⁻¹, conj_mem_transport r g hK x.2⟩
  map_one' :=
    (congrArg l (Subtype.ext (by simp only [Subgroup.coe_one]; group))).trans (map_one l)
  map_mul' x y := by
    rw [← map_mul l]
    exact congrArg l (Subtype.ext (by simp only [Subgroup.coe_mul]; group))

/-- **Subgroup-conjugation transport.** For `conjSub g (reps r) = K`, the pair
`(reps r, transportChar …)` is conjugate to `(K, l)` — realized by `a = g`. -/
theorem isConjPair_reps_transport (r : Fin 148) (g : Coordinate 2)
    {K : Subgroup (Coordinate 2)} (hK : conjSub g (reps r) = K) (l : K →* ℂˣ) :
    IsConjPair (reps r) K (transportChar r g hK l) l := by
  refine ⟨g, fun k => ⟨fun hkr => conj_mem_transport r g hK hkr,
    fun hkK => mem_reps_of_conj r g hK hkK⟩, fun k hk => rfl⟩

/-! ## Surjectivity onto the pair classes: every class is realized by a listed char -/

/-- **Surjectivity (unconditional).** Every `G`-conjugacy class of character pairs
of `Coordinate 2` is realized by a certified *listed* character on one of the 148
subgroup-class representatives: `c = ⟦(reps r, charOfVec2 r e)⟧` for some `r` and
some `e ∈ charsAt2 r`. -/
theorem pairClass_realized_by_listed (c : CharPairClass (Coordinate 2) ℂˣ) :
    ∃ (r : Fin 148) (e : List (ZMod 25)) (he : e ∈ charsAt2 r),
      c = (⟦⟨reps r, charOfVec2 r e (validAt r he)⟩⟧ : CharPairClass (Coordinate 2) ℂˣ) := by
  induction c using Quotient.inductionOn with
  | h p =>
    obtain ⟨K, l⟩ := p
    obtain ⟨r, g, hg⟩ := reps_complete K
    obtain ⟨e, he, hμe⟩ := exists_charOfVec2_eq r (transportChar r g hg l)
    refine ⟨r, e, he, Quotient.sound ?_⟩
    -- `(K, l) ≈ (reps r, charOfVec2 r e)` : symmetric of the transport, with `μ = charOfVec2`
    have hcp : IsConjPair (reps r) K (charOfVec2 r e (validAt r he)) l := by
      rw [← hμe]; exact isConjPair_reps_transport r g hg l
    exact hcp.symm

/-! ## The character↔vector dictionary: a generator step is a conjugation -/

/-- Symmetry of the `ZMod 25` dot product used by the matrix action. -/
theorem dotZ_comm : ∀ (a b : List (ZMod 25)), dotZ a b = dotZ b a
  | [], [] => rfl
  | [], (_ :: _) => by simp [dotZ]
  | (_ :: _), [] => by simp [dotZ]
  | (x :: a), (y :: b) => by
      simp only [dotZ, List.zipWith_cons_cons, List.sum_cons]
      have ih := dotZ_comm a b
      simp only [dotZ] at ih
      rw [mul_comm x y, ih]

/-- **The per-generator dictionary (pointwise).** Applying the `k`-th
normalizer-generator matrix to a certified vector `e` computes the character of
`e` precomposed with conjugation by `n = normGens r [k]`: for every `x ∈ reps r`,
`charForm2 B (M_k e) x = charForm2 B e (n⁻¹ x n)`. Proven by closure induction on
`x`, using Step-1 additivity for both `e` and `M_k e`, the per-entry realization
`normMats_realize`, and `dotZ_comm`. -/
theorem charForm2_genAct (r : Fin 148) (k : Nat)
    (hk : k < (normGens.getD r.val []).length)
    {e : List (ZMod 25)} (he : charOK2 (basisAt2 r) e = true)
    (he' : charOK2 (basisAt2 r) (genAct r.val k e) = true)
    {x : Coordinate 2} (hx : x ∈ reps r) :
    charForm2 (basisAt2 r) (genAct r.val k e) x
      = charForm2 (basisAt2 r) e
          (((normGenAt r.val k)⁻¹ * x * (normGenAt r.val k) : Coordinate 2)) := by
  set B := basisAt2 r with hB
  set e' := genAct r.val k e with he'def
  obtain ⟨a, ha_def⟩ : ∃ a : Coordinate 2, a = normGenAt r.val k := ⟨_, rfl⟩
  rw [← ha_def]
  -- normalizer facts
  have hnmem : a ∈
      Subgroup.normalizer ((reps r : Subgroup (Coordinate 2)) : Set (Coordinate 2)) := by
    rw [ha_def]; exact normGen_getD_mem r k
  have hnormiff : ∀ y : Coordinate 2, y ∈ reps r ↔ a⁻¹ * y * a ∈ reps r := by
    intro y
    have h := (Subgroup.mem_normalizer_iff''.mp hnmem) y
    simpa only [SetLike.mem_coe] using h
  have hconjmem : ∀ {y : Coordinate 2}, y ∈ reps r → a⁻¹ * y * a ∈ reps r :=
    fun hy => (hnormiff _).mp hy
  -- charForm2 additivity helpers on `reps r`
  have haddE : ∀ (v : List (ZMod 25)), charOK2 B v = true → ∀ {c d : Coordinate 2},
      c ∈ reps r → d ∈ reps r →
      charForm2 B v ((c * d : Coordinate 2)) = charForm2 B v c + charForm2 B v d := by
    intro v hv c d hc hd
    exact charExtendsAt2_basisAt r v hv c d (siftB_of_mem r ⟨c, hc⟩) (siftB_of_mem r ⟨d, hd⟩)
  have hone : ∀ (v : List (ZMod 25)), charOK2 B v = true →
      charForm2 B v (1 : Coordinate 2) = 0 := by
    intro v hv
    have h1 := charOfVec2_apply r v hv (1 : ↥(reps r))
    rw [map_one, Subgroup.coe_one] at h1
    exact zexp_inj (h1.symm.trans zexp_zero.symm)
  have hnegE : ∀ (v : List (ZMod 25)), charOK2 B v = true → ∀ {c : Coordinate 2},
      c ∈ reps r → charForm2 B v ((c⁻¹ : Coordinate 2)) = - charForm2 B v c := by
    intro v hv c hc
    have h := haddE v hv (inv_mem hc) hc
    rw [inv_mul_cancel, hone v hv] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  -- the conjugation-by-`a` group identities
  have hsplit : ∀ x y : Coordinate 2, a⁻¹ * (x * y) * a = (a⁻¹ * x * a) * (a⁻¹ * y * a) := by
    intro x y; group
  have hinvsplit : ∀ x : Coordinate 2, a⁻¹ * x⁻¹ * a = (a⁻¹ * x * a)⁻¹ := by
    intro x; group
  have honesplit : a⁻¹ * (1 : Coordinate 2) * a = 1 := by group
  -- generator-evaluation of a valid vector
  have hgenEval : ∀ (v : List (ZMod 25)), charOK2 B v = true → ∀ i (hi : i < B.length),
      charForm2 B v (B.getD i zc) = v.getD i 0 := by
    intro v hv i hi
    have hmem : ((B.getD i zc : Coordinate 2)) ∈ reps r := by
      rw [reps_eq_ofList2 r, ← hB, List.getD_eq_getElem B zc hi]
      exact Subgroup.subset_closure (List.getElem_mem hi)
    have hg := charOfVec2_gen r v hv i hi hmem
    rw [charOfVec2_apply] at hg
    exact zexp_inj hg
  -- matrix-row length: each `normMats` row has `B.length` entries
  have hMlen : ((normMats.getD r.val []).getD k []).length = B.length := by
    have hklt : k < ((normGens.getD r.val []).map
        (conjMatrixL2 (getB (classRepsData.getD r.val 0)))).length := by
      rw [List.length_map]; exact hk
    rw [normRealize_at r, List.getD_eq_getElem _ [] hklt, List.getElem_map, conjMatrixL2,
      List.length_map, ← basisAt2_eq r, ← hB]
  -- the matrix action reads a dot product
  have hei : ∀ i, i < B.length →
      e'.getD i 0 = dotZ (((normMats.getD r.val []).getD k []).getD i []) e := by
    intro i hi
    have hlt : i < ((normMats.getD r.val []).getD k []).length := by rw [hMlen]; exact hi
    rw [he'def, genAct, actVecZ]
    rw [List.getD_eq_getElem _ 0 (by rw [List.length_map]; exact hlt)]
    rw [List.getElem_map]
    rw [List.getD_eq_getElem _ [] hlt]
  -- the conjC→group bridge (used once, in the base case)
  have hbridge : ∀ g : Coordinate 2,
      (conjC 2 (invC 2 ((normGens.getD r.val []).getD k zc)) g : Coordinate 2)
        = a⁻¹ * g * a := by
    intro g
    rw [conjC_eq hq2]
    have h1 : (invC 2 ((normGens.getD r.val []).getD k zc) : Coordinate 2) = a⁻¹ := by
      rw [ha_def]; rfl
    rw [h1, inv_inv]
  -- closure induction
  have toReps : ∀ {c : Coordinate 2},
      c ∈ Subgroup.closure {y : Coordinate 2 | y ∈ B} → c ∈ reps r := by
    intro c hc; rw [reps_eq_ofList2 r, ← hB]; exact hc
  have hxc : x ∈ Subgroup.closure {y : Coordinate 2 | y ∈ B} := by
    rw [reps_eq_ofList2 r, ← hB] at hx; exact hx
  refine Subgroup.closure_induction
    (p := fun (z : Coordinate 2) _ =>
      charForm2 B e' z = charForm2 B e ((a⁻¹ * z * a : Coordinate 2)))
    (fun z hz => ?_) ?_ (fun c d hc hd pc pd => ?_) (fun c hc pc => ?_) hxc
  · -- generator base case
    obtain ⟨i, hi, hzeq⟩ := List.getElem_of_mem hz
    have hzB : z = B.getD i zc := by rw [List.getD_eq_getElem B zc hi, hzeq]
    subst hzB
    rw [hgenEval e' he' i hi, hei i hi, normMats_realize r hk hi, ← hB, hbridge]
    simp only [charForm2]
    exact dotZ_comm _ _
  · -- one
    rw [honesplit, hone e' he', hone e he]
  · -- mul
    rw [haddE e' he' (toReps hc) (toReps hd), hsplit,
      haddE e he (hconjmem (toReps hc)) (hconjmem (toReps hd)), pc, pd]
  · -- inv
    rw [hnegE e' he' (toReps hc), hinvsplit, hnegE e he (hconjmem (toReps hc)), pc]

/-- **A generator step fuses the pair classes.** If `genAct r k e` is again a
listed character, then `(reps r, charOfVec2 (genAct r k e))` and
`(reps r, charOfVec2 e)` are `G`-conjugate pairs (via the normalizer generator
`normGens r [k]`), so they define the *same* `CharPairClass`. -/
theorem class_genAct_eq (r : Fin 148) (k : Nat)
    (hk : k < (normGens.getD r.val []).length)
    {e : List (ZMod 25)} (he : e ∈ charsAt2 r) (he' : genAct r.val k e ∈ charsAt2 r) :
    (⟦⟨reps r, charOfVec2 r (genAct r.val k e) (validAt r he')⟩⟧ :
        CharPairClass (Coordinate 2) ℂˣ)
      = ⟦⟨reps r, charOfVec2 r e (validAt r he)⟩⟧ := by
  refine Quotient.sound ?_
  obtain ⟨a, ha_def⟩ : ∃ a : Coordinate 2, a = normGenAt r.val k := ⟨_, rfl⟩
  have hnmem : a ∈
      Subgroup.normalizer ((reps r : Subgroup (Coordinate 2)) : Set (Coordinate 2)) := by
    rw [ha_def]; exact normGen_getD_mem r k
  refine ⟨a⁻¹, fun k0 => ?_, fun k0 hk0 => ?_⟩
  · -- conjugacy of the subgroup (both are `reps r`)
    rw [inv_inv]
    have h := (Subgroup.mem_normalizer_iff''.mp hnmem) k0
    simpa only [SetLike.mem_coe] using h
  · -- the character transports along the conjugation
    have hcf := charForm2_genAct r k hk (validAt r he) (validAt r he') (x := k0) hk0
    rw [← ha_def] at hcf
    rw [charOfVec2_apply, charOfVec2_apply]
    change zexp (charForm2 (basisAt2 r) e (a⁻¹ * k0 * (a⁻¹)⁻¹))
      = zexp (charForm2 (basisAt2 r) (genAct r.val k e) k0)
    rw [inv_inv, hcf]

/-- A position `p < |charsAt2 r|` reads a listed character. -/
theorem listedAt (r : Fin 148) {p : Nat} (hp : p < (repChars2.getD r.val []).length) :
    (repChars2.getD r.val []).getD p [] ∈ charsAt2 r := by
  change (repChars2.getD r.val []).getD p [] ∈ repChars2.getD r.val []
  rw [List.getD_eq_getElem _ [] hp]; exact List.getElem_mem hp

/-- The pair class of a listed character depends only on the vector (proof
irrelevance of the validity witness). -/
theorem class_charOfVec2_congr (r : Fin 148) {v w : List (ZMod 25)}
    (hv : v ∈ charsAt2 r) (hw : w ∈ charsAt2 r) (h : v = w) :
    (⟦⟨reps r, charOfVec2 r v (validAt r hv)⟩⟧ : CharPairClass (Coordinate 2) ℂˣ)
      = ⟦⟨reps r, charOfVec2 r w (validAt r hw)⟩⟧ := by
  subst h; rfl

/-- **Orbit reduction.** Every listed character of `reps r` is `G`-conjugate (as a
character pair) to the character at *some* orbit-representative position `q`
(`normIsRep q = true`) — reached along the certified BFS spanning tree, fusing
one normalizer-generator step at a time via `class_genAct_eq`. -/
theorem class_reduces_to_rep (r : Fin 148) : ∀ (dep p : Nat)
    (hp : p < (repChars2.getD r.val []).length)
    (_hdep : (normTreeDepth.getD r.val []).getD p 0 = dep),
    ∃ q, ∃ hq : q < (repChars2.getD r.val []).length,
      (normIsRep.getD r.val []).getD q false = true ∧
      (⟦⟨reps r, charOfVec2 r ((repChars2.getD r.val []).getD p []) (validAt r (listedAt r hp))⟩⟧ :
          CharPairClass (Coordinate 2) ℂˣ)
        = ⟦⟨reps r, charOfVec2 r ((repChars2.getD r.val []).getD q [])
            (validAt r (listedAt r hq))⟩⟧ := by
  intro dep
  induction dep using Nat.strong_induction_on with
  | _ dep IH =>
    intro p hp hdep
    have ht := (List.all_eq_true.mp (checkTree_at r)) p (List.mem_range.mpr hp)
    by_cases hr : (normIsRep.getD r.val []).getD p false = true
    · exact ⟨p, hp, hr, rfl⟩
    · have hrf : (normIsRep.getD r.val []).getD p false = false := by
        cases h : (normIsRep.getD r.val []).getD p false with
        | false => rfl
        | true => exact absurd h hr
      simp only [orbTreeOK, hrf, Bool.not_false, Bool.false_and, Bool.false_or, Bool.true_and,
        Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at ht
      obtain ⟨⟨⟨⟨hklt, hparlt⟩, hdlt⟩, hmove⟩, _hlab⟩ := ht
      set k := (normTreeGen.getD r.val []).getD p 0 with hk_def
      set j := (normTreePar.getD r.val []).getD p 0 with hj_def
      have hpardep : (normTreeDepth.getD r.val []).getD j 0 < dep := hdep ▸ hdlt
      obtain ⟨q, hq, hqrep, hIH⟩ := IH _ hpardep j hparlt rfl
      have haf := act_fact r k j hklt hparlt
      have hgenActeq : genAct r.val k ((repChars2.getD r.val []).getD j []) =
          (repChars2.getD r.val []).getD p [] := by rw [genAct, haf.1, hmove]
      have hnglen : k < (normGens.getD r.val []).length := by
        have hlen : (normMats.getD r.val []).length = (normGens.getD r.val []).length := by
          rw [normRealize_at r, List.length_map]
        rw [← hlen]; exact hklt
      have he' : genAct r.val k ((repChars2.getD r.val []).getD j []) ∈ charsAt2 r := by
        rw [hgenActeq]; exact listedAt r hp
      have hstep := (class_charOfVec2_congr r (listedAt r hp) he' hgenActeq.symm).trans
        (class_genAct_eq r k hnglen (listedAt r hparlt) he')
      exact ⟨q, hq, hqrep, hstep.trans hIH⟩

/-- **Sharpened surjectivity: every pair class is an orbit representative.** Every
`G`-conjugacy class of character pairs of `Coordinate 2` equals the class of the
character at an orbit-representative position `q` (`normIsRep q = true`) on one of
the 148 subgroup-class representatives. The orbit representatives number
`Σ_r orbitCountR r = 2724` (`pairClassTotal`), so this is the surjection realizing
`|CharPairClass| ≤ 2724`. -/
theorem pairClass_realized_by_orbitRep (c : CharPairClass (Coordinate 2) ℂˣ) :
    ∃ (r : Fin 148) (q : Nat) (hq : q < (repChars2.getD r.val []).length),
      (normIsRep.getD r.val []).getD q false = true ∧
      c = ⟦⟨reps r, charOfVec2 r ((repChars2.getD r.val []).getD q [])
        (validAt r (listedAt r hq))⟩⟧ := by
  obtain ⟨r, e, he, hce⟩ := pairClass_realized_by_listed c
  have hmem : e ∈ repChars2.getD r.val [] := he
  obtain ⟨p, hp, hpe⟩ := List.getElem_of_mem hmem
  have hpe' : (repChars2.getD r.val []).getD p [] = e := by
    rw [List.getD_eq_getElem _ [] hp, hpe]
  obtain ⟨q, hq, hqrep, hred⟩ := class_reduces_to_rep r _ p hp rfl
  refine ⟨r, q, hq, hqrep, ?_⟩
  rw [hce]
  exact (class_charOfVec2_congr r he (listedAt r hp) hpe'.symm).trans hred

/-! ## Finiteness of the pair-class index and the rank corollary -/

/-- The pair classes of `Coordinate 2` form a finite type (surjective image of the
finite set of `(representative, listed character)` pairs). -/
noncomputable instance : Finite (CharPairClass (Coordinate 2) ℂˣ) := by
  classical
  -- surjection from `Σ r, {e // e ∈ charsAt2 r}` (a finite type) onto the classes
  apply Finite.of_surjective
    (f := fun p : (Σ r : Fin 148, {e : List (ZMod 25) // e ∈ charsAt2 r}) =>
      (⟦⟨reps p.1, charOfVec2 p.1 p.2.1 (validAt p.1 p.2.2)⟩⟧ :
        CharPairClass (Coordinate 2) ℂˣ))
  intro c
  obtain ⟨r, e, he, hc⟩ := pairClass_realized_by_listed c
  exact ⟨⟨r, ⟨e, he⟩⟩, hc.symm⟩

/-- **The rank corollary (conditional on the pair count).** If the pair-class
index has cardinality `2724`, then `rank_ℤ D(Coordinate 2) = 2724`. Composes
`DRing.basisOfCharPairClass` with `rank_eq_card_basis`. -/
theorem rank_dring_coordinate2_of_card
    (h : Nat.card (CharPairClass (Coordinate 2) ℂˣ) = 2724) :
    Module.rank ℤ (DRing (Coordinate 2)) = 2724 := by
  classical
  haveI : Fintype (CharPairClass (Coordinate 2) ℂˣ) := Fintype.ofFinite _
  have hcard : Fintype.card (CharPairClass (Coordinate 2) ℂˣ) = 2724 := by
    rw [← Nat.card_eq_fintype_card]; exact h
  rw [rank_eq_card_basis (DRing.basisOfCharPairClass (G := Coordinate 2)), hcard]
  norm_cast

end Q2

end LeanDring.P5Presentation
