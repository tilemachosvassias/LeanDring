/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.ConjugacyClasses.Twin1.PairClass

/-!
# Injectivity of the orbit-representative enumeration (pair-class enumeration, final step)

`LeanDring/P5/Certificate/ConjugacyClasses/Twin1/PairClass.lean` delivered the **surjection**
`pairClass_realized_by_orbitRep`: every
`c : CharPairClass (Coordinate 1) ℂˣ` is the class of the character at some
orbit-representative position (`normIsRep q = true`) on one of the 148 subgroup
representatives. This file closes the converse — **injectivity** — and the routine
count, yielding the unconditional

* `card_charPairClass_coordinate1 : Nat.card (CharPairClass (Coordinate 1) ℂˣ) = 2724`
* `rank_dring_coordinate1 : Module.rank ℤ (DRing (Coordinate 1)) = 2724`.

## The route

* `conjSub_of_isConjPair` — an `IsConjPair` between two subgroup-character pairs
  yields a subgroup conjugation `conjSub a K = K'`. For the **cross-representative**
  case this collides with `reps_pairwise_nonconj`, forcing `r = r'`.
* `ConjLabelProp` + `conjLabelProp_of_mem_N` — the **character↔vector dictionary
  as a closure induction**: for every `a ∈ N_G(reps r)` and every character
  position `p`, there is a position `p'` in the *same normalizer orbit*
  (`normLabel p' = normLabel p`) whose character is `charForm … p` precomposed with
  conjugation by `a`. The generator step is `charForm_genAct`; the induction is
  closed under products, and under **inverses via the finite-order identity**
  `a⁻¹ = a ^ (orderOf a - 1)` (`Coordinate 1` is finite), sidestepping any need for
  an inverse-step matrix.
* `orbitRep_class_inj_same` — the **same-representative** case: an `IsConjPair` on a
  fixed `reps r` puts the conjugator in `N_G(reps r)`, so `conjLabelProp_of_mem_N`
  identifies the two orbit-rep positions' characters, `charOfVec_inj` + `Nodup`
  collapse them to a single position, and `normLabel` invariance (`= p` at a rep)
  gives `q = q'`.
* `card_fibre_eq` / `orbRepSigma` — the orbit-representative index type has
  `Σ_r orbitCountR r = 2724` elements (`pairClassTotal`), and `orbRepClass` is a
  bijection onto the pair classes.
-/

namespace LeanDring.P5Presentation

open LeanDring LeanDring.MonGSet LeanDring.DRing

-- file-level maxHeartbeats: dozens of decide-heavy declarations below need it
set_option linter.style.setOption false
set_option maxHeartbeats 4000000

/-! ## Subgroup conjugation extracted from a character-pair conjugation -/

/-- An `IsConjPair` yields a genuine subgroup conjugation of the underlying
subgroups. -/
theorem conjSub_of_isConjPair {K K' : Subgroup (Coordinate 1)}
    {l : K →* ℂˣ} {l' : K' →* ℂˣ}
    (h : IsConjPair K K' l l') : ∃ a : Coordinate 1, conjSub a K = K' := by
  obtain ⟨a, hmem, _⟩ := h
  refine ⟨a, ?_⟩
  ext y
  simp only [conjSub, mem_map_conj_iff]
  constructor
  · intro hy
    have h2 := (hmem (a⁻¹ * y * a)).mp hy
    rwa [show a * (a⁻¹ * y * a) * a⁻¹ = y by group] at h2
  · intro hy
    apply (hmem (a⁻¹ * y * a)).mpr
    rwa [show a * (a⁻¹ * y * a) * a⁻¹ = y by group]

/-! ## The conjugation-orbit dictionary as a closure induction -/

/-- **The inductive property.** For a normalizer element `a`, every character
position `p` of `reps r` has a partner `p'` in the *same normalizer orbit* whose
character is the `p`-character conjugated by `a`. -/
def ConjLabelProp (r : Fin 148) (a : Coordinate 1) : Prop :=
  a ∈ Subgroup.normalizer ((reps r : Subgroup (Coordinate 1)) : Set (Coordinate 1)) ∧
    ∀ (p : Nat), p < (repChars.getD r.val []).length →
      ∃ p', ∃ _ : p' < (repChars.getD r.val []).length,
        (normLabel.getD r.val []).getD p' 0 = (normLabel.getD r.val []).getD p 0 ∧
        ∀ x : Coordinate 1, x ∈ reps r →
          charForm (basisAt r) ((repChars.getD r.val []).getD p' []) x
            = charForm (basisAt r) ((repChars.getD r.val []).getD p [])
                ((a⁻¹ * x * a : Coordinate 1))

/-- The action position of generator `k` on character position `p` is in range. -/
theorem actPos_lt (r : Fin 148) (k p : Nat)
    (hk : k < (normMats.getD r.val []).length) (hp : p < (repChars.getD r.val []).length) :
    ((normActPos.getD r.val []).getD k []).getD p 0 < (repChars.getD r.val []).length := by
  have hrow := (List.all_eq_true.mp (checkAct_at r)) k (List.mem_range.mpr hk)
  have hp' := (List.all_eq_true.mp hrow) p (List.mem_range.mpr hp)
  simp only [orbActOK, Bool.and_eq_true, decide_eq_true_eq, Nat.blt_eq, Nat.beq_eq] at hp'
  exact hp'.1.1

theorem ConjLabelProp.one (r : Fin 148) : ConjLabelProp r 1 := by
  refine ⟨Subgroup.one_mem _, fun p hp => ⟨p, hp, rfl, fun x _ => ?_⟩⟩
  rw [inv_one, mul_one, one_mul]

/-- **Base case.** Each normalizer generator satisfies `ConjLabelProp`, via
`charForm_genAct` and the certified orbit action `act_fact` / `label_stable`. -/
theorem ConjLabelProp.base (r : Fin 148) (k : Nat)
    (hk : k < (normGens.getD r.val []).length) : ConjLabelProp r (normGenAt r.val k) := by
  refine ⟨normGen_getD_mem r k, fun p hp => ?_⟩
  have hk_mats : k < (normMats.getD r.val []).length := by
    rw [normRealize_at r, List.length_map]; exact hk
  set p' := ((normActPos.getD r.val []).getD k []).getD p 0 with hp'def
  have hp'lt : p' < (repChars.getD r.val []).length := actPos_lt r k p hk_mats hp
  have genActeq : genAct r.val k ((repChars.getD r.val []).getD p [])
      = (repChars.getD r.val []).getD p' [] := (act_fact r k p hk_mats hp).1
  have he' : charOK (basisAt r) (genAct r.val k ((repChars.getD r.val []).getD p [])) = true := by
    rw [genActeq]; exact validAt r (listedAt r hp'lt)
  refine ⟨p', hp'lt, label_stable r k p hk_mats hp, fun x hx => ?_⟩
  have hcf := charForm_genAct r k hk (validAt r (listedAt r hp)) he' hx
  rw [genActeq] at hcf
  exact hcf

theorem ConjLabelProp.mul (r : Fin 148) {a b : Coordinate 1}
    (ha : ConjLabelProp r a) (hb : ConjLabelProp r b) : ConjLabelProp r (a * b) := by
  refine ⟨(Subgroup.normalizer _).mul_mem ha.1 hb.1, fun p hp => ?_⟩
  obtain ⟨pb, hpb, hlabb, hcharb⟩ := hb.2 p hp
  obtain ⟨p', hp', hlaba, hchara⟩ := ha.2 pb hpb
  refine ⟨p', hp', hlaba.trans hlabb, fun x hx => ?_⟩
  have hax : a⁻¹ * x * a ∈ reps r := ((Subgroup.mem_normalizer_iff''.mp ha.1) x).mp hx
  rw [hchara x hx, hcharb _ hax,
    show b⁻¹ * (a⁻¹ * x * a) * b = (a * b)⁻¹ * x * (a * b) by group]

theorem ConjLabelProp.pow (r : Fin 148) {a : Coordinate 1} (ha : ConjLabelProp r a) :
    ∀ n : Nat, ConjLabelProp r (a ^ n)
  | 0 => by rw [pow_zero]; exact ConjLabelProp.one r
  | n + 1 => by rw [pow_succ]; exact ConjLabelProp.mul r (ConjLabelProp.pow r ha n) ha

theorem ConjLabelProp.inv (r : Fin 148) {a : Coordinate 1} (ha : ConjLabelProp r a) :
    ConjLabelProp r a⁻¹ := by
  have hord : 0 < orderOf a := orderOf_pos a
  have hmul1 : a * a ^ (orderOf a - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hord, pow_orderOf_eq_one]
  have hinv : a⁻¹ = a ^ (orderOf a - 1) := inv_eq_of_mul_eq_one_right hmul1
  rw [hinv]; exact ConjLabelProp.pow r ha (orderOf a - 1)

/-- **The dictionary, for every normalizer element.** Closure induction on
`a ∈ N_G(reps r)`: generators (`base`), one (`one`), products (`mul`) and inverses
(`inv`, via the finite-order power identity). -/
theorem conjLabelProp_of_mem_N (r : Fin 148) {a : Coordinate 1}
    (ha : a ∈ Subgroup.normalizer ((reps r : Subgroup (Coordinate 1)) : Set (Coordinate 1))) :
    ConjLabelProp r a := by
  have ha' : a ∈ Subgroup.closure {x : Coordinate 1 | x ∈ normGens.getD r.val []} := by
    have hof : ofList 1 hq1 (normGens.getD r.val [])
        = Subgroup.closure {x : Coordinate 1 | x ∈ normGens.getD r.val []} := rfl
    rw [← hof, normGens_generate r]; exact ha
  clear ha
  induction ha' using Subgroup.closure_induction with
  | mem x hx =>
      simp only [Set.mem_setOf_eq] at hx
      obtain ⟨k, hk, hxk⟩ := List.getElem_of_mem hx
      have hgen : normGenAt r.val k = x :=
        (congrArg (fun c : Coordinates => (c : Coordinate 1))
          (List.getD_eq_getElem (normGens.getD r.val []) (0, 0, 0, 0, 0) hk)).trans hxk
      exact hgen ▸ ConjLabelProp.base r k hk
  | one => exact ConjLabelProp.one r
  | mul x y _ _ Px Py => exact ConjLabelProp.mul r Px Py
  | inv x _ Px => exact ConjLabelProp.inv r Px

/-! ## Orbit-representative facts: `normLabel` at a representative is itself -/

/-- At an orbit-representative position, the orbit label is the position itself. -/
theorem normLabel_rep (r : Fin 148) (p : Nat) (hp : p < (repChars.getD r.val []).length)
    (hrep : (normIsRep.getD r.val []).getD p false = true) :
    (normLabel.getD r.val []).getD p 0 = p := by
  have ht := (List.all_eq_true.mp (checkTree_at r)) p (List.mem_range.mpr hp)
  simp only [orbTreeOK, hrep, Bool.not_true, Bool.false_and, Bool.or_false, Bool.true_and,
    Bool.and_eq_true, Nat.beq_eq] at ht
  exact ht.2

/-! ## Same-representative injectivity -/

/-- **Same-representative injectivity.** Two orbit-representative positions on the
same subgroup representative that give equal pair classes are the same position. -/
theorem orbitRep_class_inj_same (r : Fin 148) {q q' : Nat}
    (hq : q < (repChars.getD r.val []).length) (hq' : q' < (repChars.getD r.val []).length)
    (hqrep : (normIsRep.getD r.val []).getD q false = true)
    (hq'rep : (normIsRep.getD r.val []).getD q' false = true)
    (h : (⟦⟨reps r, charOfVec r ((repChars.getD r.val []).getD q [])
            (validAt r (listedAt r hq))⟩⟧ : CharPairClass (Coordinate 1) ℂˣ)
        = ⟦⟨reps r, charOfVec r ((repChars.getD r.val []).getD q' [])
            (validAt r (listedAt r hq'))⟩⟧) :
    q = q' := by
  set B := basisAt r with hB
  set vq := (repChars.getD r.val []).getD q [] with hvq
  set vq' := (repChars.getD r.val []).getD q' [] with hvq'
  obtain ⟨a, hmem, hchar⟩ := Quotient.exact h
  -- `a` normalizes `reps r`
  have haN : a ∈ Subgroup.normalizer ((reps r : Subgroup (Coordinate 1)) : Set (Coordinate 1)) :=
    Subgroup.mem_normalizer_iff.mpr hmem
  have hconjmem : ∀ {x : Coordinate 1}, x ∈ reps r → a⁻¹ * x * a ∈ reps r := by
    intro x hx
    exact ((Subgroup.mem_normalizer_iff''.mp haN) x).mp hx
  -- transported character equality: `charForm vq' (a k a⁻¹) = charForm vq k`
  have hval : ∀ k : Coordinate 1, (hk : k ∈ reps r) →
      charForm B vq' (a * k * a⁻¹) = charForm B vq k := by
    intro k hk
    have hc := hchar k hk
    rw [charOfVec_apply, charOfVec_apply] at hc
    exact zexp_inj hc
  have hstar : ∀ x : Coordinate 1, x ∈ reps r →
      charForm B vq' x = charForm B vq (a⁻¹ * x * a) := by
    intro x hx
    have hkk := hconjmem hx
    have hv := hval (a⁻¹ * x * a) hkk
    rwa [show a * (a⁻¹ * x * a) * a⁻¹ = x by group] at hv
  -- the dictionary partner of `q`
  obtain ⟨p', hp', hlab, hcharP⟩ := (conjLabelProp_of_mem_N r haN).2 q hq
  -- `charForm (repChars p') = charForm vq'` on `reps r`, so the characters agree
  have heqChar : charOfVec r ((repChars.getD r.val []).getD p' []) (validAt r (listedAt r hp'))
      = charOfVec r vq' (validAt r (listedAt r hq')) := by
    refine MonoidHom.ext (fun z => ?_)
    obtain ⟨x, hx⟩ := z
    rw [charOfVec_apply, charOfVec_apply]
    congr 1
    rw [hcharP x hx, hstar x hx]
  have hvv : (repChars.getD r.val []).getD p' [] = vq' :=
    charOfVec_inj r (listedAt r hp') (listedAt r hq') heqChar
  -- `Nodup` collapses positions
  have hpq : p' = q' := by
    rw [hvq', List.getD_eq_getElem _ _ hp', List.getD_eq_getElem _ _ hq'] at hvv
    exact (charsAt_nodup r).getElem_inj_iff.mp hvv
  -- `normLabel` at both reps is the position itself
  have hlq := normLabel_rep r q hq hqrep
  have hlq' := normLabel_rep r q' hq' hq'rep
  have h1 : (normLabel.getD r.val []).getD q' 0 = (normLabel.getD r.val []).getD q 0 := by
    rw [← hpq]; exact hlab
  rw [hlq', hlq] at h1
  exact h1.symm

/-! ## The orbit-representative index type and its enumeration -/

/-- The orbit-representative index type: a subgroup class `r` together with an
orbit-representative character position on it. -/
def orbRepSigma : Type :=
  Σ r : Fin 148, {q : Fin (repChars.getD r.val []).length //
    (normIsRep.getD r.val []).getD q.val false = true}

noncomputable instance : Fintype orbRepSigma := by
  unfold orbRepSigma; infer_instance

/-- The pair class carried by an orbit-representative index. -/
noncomputable def orbRepClass (i : orbRepSigma) : CharPairClass (Coordinate 1) ℂˣ :=
  ⟦⟨reps i.1, charOfVec i.1 ((repChars.getD i.1.val []).getD i.2.1.val [])
    (validAt i.1 (listedAt i.1 i.2.1.isLt))⟩⟧

theorem orbRepClass_surjective : Function.Surjective orbRepClass := by
  intro c
  obtain ⟨r, q, hq, hqrep, hc⟩ := pairClass_realized_by_orbitRep c
  exact ⟨⟨r, ⟨⟨q, hq⟩, hqrep⟩⟩, hc.symm⟩

theorem orbRepClass_injective : Function.Injective orbRepClass := by
  rintro ⟨r, ⟨q, hqrep⟩⟩ ⟨r', ⟨q', hq'rep⟩⟩ h
  simp only [orbRepClass] at h
  -- cross-representative: force `r = r'`
  have hrr : r = r' := by
    by_contra hne
    obtain ⟨a, hconj⟩ := conjSub_of_isConjPair (Quotient.exact h)
    exact reps_pairwise_nonconj r r' hne ⟨a, hconj⟩
  subst hrr
  -- same representative: force `q = q'`
  have hqq : q.val = q'.val :=
    orbitRep_class_inj_same r q.isLt q'.isLt hqrep hq'rep h
  have : q = q' := Fin.ext hqq
  subst this
  rfl

theorem orbRepClass_bijective : Function.Bijective orbRepClass :=
  ⟨orbRepClass_injective, orbRepClass_surjective⟩

/-! ## The count of the orbit-representative index -/

/-- The number of orbit-representative positions of `reps r` equals the certified
orbit count `orbitCountR r`. -/
theorem card_fibre_eq (r : Fin 148) :
    Nat.card {q : Fin (repChars.getD r.val []).length //
        (normIsRep.getD r.val []).getD q.val false = true} = orbitCountR r.val := by
  have hlen : (normIsRep.getD r.val []).length = (repChars.getD r.val []).length := by
    have hcl := (List.all_eq_true.mp checkLen_all) r.val (List.mem_range.mpr r.isLt)
    simp only [checkLen, Bool.and_eq_true, Nat.beq_eq] at hcl
    obtain ⟨⟨⟨⟨⟨_, hb⟩, _⟩, _⟩, _⟩, _⟩ := hcl
    exact hb
  have hmap : (List.finRange (repChars.getD r.val []).length).map
      (fun q : Fin (repChars.getD r.val []).length => (normIsRep.getD r.val []).getD q.val false)
      = normIsRep.getD r.val [] := by
    apply List.ext_getElem
    · rw [List.length_map, List.length_finRange]; exact hlen.symm
    · intro k h1 h2
      rw [List.getElem_map, List.getElem_finRange]
      exact List.getD_eq_getElem _ _ _
  rw [card_subtype_fin_eq, ← List.countP_eq_length_filter]
  unfold orbitCountR
  rw [← List.countP_eq_length_filter]
  conv_rhs => rw [← hmap, List.countP_map]
  rfl

/-- The orbit-representative index has `2724` elements. -/
theorem card_orbRepSigma : Nat.card orbRepSigma = 2724 := by
  have hbridge : ∀ (f : ℕ → ℕ) (n : ℕ),
      ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
    intro f n
    induction n with
    | zero => simp
    | succ m ih =>
        rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
        simp
  rw [orbRepSigma, Nat.card_sigma]
  simp only [card_fibre_eq]
  rw [Fin.sum_univ_eq_sum_range orbitCountR 148, ← hbridge orbitCountR 148, pairClassTotal]

/-! ## The unconditional pair count and rank -/

/-- **The pair count.** `Nat.card (CharPairClass (Coordinate 1) ℂˣ) = 2724`. -/
theorem card_charPairClass_coordinate1 :
    Nat.card (CharPairClass (Coordinate 1) ℂˣ) = 2724 := by
  rw [← Nat.card_eq_of_bijective orbRepClass orbRepClass_bijective, card_orbRepSigma]

/-- **The rank of `D(Coordinate 1)`.** Unconditional, via the conditional corollary
`rank_dring_coordinate1_of_card` fed the pair count. -/
theorem rank_dring_coordinate1 :
    Module.rank ℤ (DRing (Coordinate 1)) = 2724 :=
  rank_dring_coordinate1_of_card card_charPairClass_coordinate1

end LeanDring.P5Presentation
