/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign

/-!
# Stage 5 step 4a — the row equivalence `σ`

`dringEquiv_of_rowMatch_coordinate2` needs a bijection
`σ : CharPairClass (Coordinate 1) ℂˣ ≃ CharPairClass (Coordinate 2) ℂˣ`.
It is assembled here as the transport, along the two proved index bijections
`orbRepClass`
(`LeanDring/P5/Certificate/ConjugacyClasses/Twin{1,2}/PairClassInj.lean`),
of the purely combinatorial index map

```
ψ ⟨r, q⟩ = ⟨r, alnLab r q⟩,   alnLab r q = Q2.normLabel[r][alnPos[r][q]]
```

certified by `alnCheck` (`LeanDring/P5/Certificate/Characters/Twin2/CharAlign.lean`).  `ψ` is
injective because `alnInv`
inverts it, hence bijective by the two proved counts (`2724` both sides).

Two facts make the assembly usable downstream:

* `class_pos_eq_orbRepClass` — the q2 pair class of *any* character position is
  the class of its certified orbit label, the label-tracking refinement of
  `Q2.class_reduces_to_rep` (the BFS certificate `orbTreeOK` carries
  `normLabel[parent p] = normLabel[p]`, and `normLabel_rep` closes the base case);
* `classElt_sigmaEquiv_orbRepClass` — `classElt (σ c)` for `c` at the q1
  orbit-representative position `q` is the *basis element of the aligned q2
  character* `repChars2[r][alnPos[r][q]]`, i.e. exactly the row the stage-2/3/4
  column certificates compare against.
-/

namespace LeanDring.P5Presentation

open LeanDring LeanDring.MonGSet LeanDring.DRing

-- file-level maxHeartbeats: dozens of decide-heavy declarations below need it
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Q2

/-! ## The label-tracking orbit reduction -/

/-- **Orbit reduction, with the label.** Refinement of `class_reduces_to_rep`:
the orbit representative reached from position `p` along the BFS spanning tree is
*the certified label* `normLabel[r][p]`. -/
theorem class_reduces_to_label (r : Fin 148) : ∀ (dep p : Nat)
    (hp : p < (repChars2.getD r.val []).length)
    (_hdep : (normTreeDepth.getD r.val []).getD p 0 = dep),
    ∃ q, ∃ hq : q < (repChars2.getD r.val []).length,
      (normIsRep.getD r.val []).getD q false = true ∧
      q = (normLabel.getD r.val []).getD p 0 ∧
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
    · exact ⟨p, hp, hr, (normLabel_rep r p hp hr).symm, rfl⟩
    · have hrf : (normIsRep.getD r.val []).getD p false = false := by
        cases h : (normIsRep.getD r.val []).getD p false with
        | false => rfl
        | true => exact absurd h hr
      simp only [orbTreeOK, hrf, Bool.not_false, Bool.false_and, Bool.false_or, Bool.true_and,
        Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at ht
      obtain ⟨⟨⟨⟨hklt, hparlt⟩, hdlt⟩, hmove⟩, hlab⟩ := ht
      set k := (normTreeGen.getD r.val []).getD p 0 with hk_def
      set j := (normTreePar.getD r.val []).getD p 0 with hj_def
      have hpardep : (normTreeDepth.getD r.val []).getD j 0 < dep := hdep ▸ hdlt
      obtain ⟨q, hq, hqrep, hqlab, hIH⟩ := IH _ hpardep j hparlt rfl
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
      exact ⟨q, hq, hqrep, hqlab.trans hlab, hstep.trans hIH⟩

/-- **The class of a character position is the class of its orbit label.** -/
theorem class_pos_eq_orbRepClass (r : Fin 148) (p : Nat)
    (hp : p < (repChars2.getD r.val []).length)
    (q : Fin (repChars2.getD r.val []).length)
    (hq : (normIsRep.getD r.val []).getD q.val false = true)
    (hqv : q.val = (normLabel.getD r.val []).getD p 0) :
    orbRepClass ⟨r, ⟨q, hq⟩⟩
      = (⟦⟨reps r, charOfVec2 r ((repChars2.getD r.val []).getD p [])
          (validAt r (listedAt r hp))⟩⟧ : CharPairClass (Coordinate 2) ℂˣ) := by
  obtain ⟨q', hq', hq'rep, hq'lab, hcls⟩ := class_reduces_to_label r _ p hp rfl
  have hqq : q.val = q' := by rw [hqv, hq'lab]
  rw [hcls, orbRepClass]
  exact class_charOfVec2_congr r (listedAt r q.isLt) (listedAt r hq') (by rw [hqq])

end Q2

/-! ## The index map `ψ` and the row equivalence -/

/-- The combinatorial row map: the q1 orbit representative at position `q` of
class `r` goes to the q2 orbit representative labelled by the aligned q2
character position. -/
def psi (i : orbRepSigma) : Q2.orbRepSigma :=
  ⟨i.1, ⟨⟨alnLab i.1.val i.2.1.val, (alnCheck_rep i.1 i.2.1.isLt i.2.2).2.1⟩,
    (alnCheck_rep i.1 i.2.1.isLt i.2.2).2.2.1⟩⟩

theorem psi_injective : Function.Injective psi := by
  rintro ⟨r, ⟨q, hq⟩⟩ ⟨r', ⟨q', hq'⟩⟩ h
  obtain ⟨hr, hrest⟩ := Sigma.mk.inj_iff.mp h
  subst hr
  have h2 := eq_of_heq hrest
  have hval : alnLab r q.val = alnLab r q'.val := congrArg (fun x => x.1.val) h2
  have e1 := (alnCheck_rep r q.isLt hq).2.2.2
  have e2 := (alnCheck_rep r q'.isLt hq').2.2.2
  have : q.val = q'.val := by rw [← e1, ← e2, hval]
  have hqq : q = q' := Fin.ext this
  subst hqq
  rfl

theorem psi_bijective : Function.Bijective psi := by
  classical
  haveI : Fintype orbRepSigma := Fintype.ofFinite _
  haveI : Fintype Q2.orbRepSigma := Fintype.ofFinite _
  refine (Fintype.bijective_iff_injective_and_card psi).mpr ⟨psi_injective, ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_orbRepSigma,
    Q2.card_orbRepSigma]

/-- **The row equivalence σ.** -/
noncomputable def sigmaEquiv :
    CharPairClass (Coordinate 1) ℂˣ ≃ CharPairClass (Coordinate 2) ℂˣ :=
  (Equiv.ofBijective orbRepClass orbRepClass_bijective).symm.trans
    ((Equiv.ofBijective psi psi_bijective).trans
      (Equiv.ofBijective Q2.orbRepClass Q2.orbRepClass_bijective))

theorem sigmaEquiv_orbRepClass (i : orbRepSigma) :
    sigmaEquiv (orbRepClass i) = Q2.orbRepClass (psi i) := by
  have h : (Equiv.ofBijective orbRepClass orbRepClass_bijective).symm (orbRepClass i) = i :=
    (Equiv.ofBijective orbRepClass orbRepClass_bijective).symm_apply_apply i
  simp only [sigmaEquiv, Equiv.trans_apply, h, Equiv.ofBijective_apply]

/-- **The row that `σ` selects.** For the pair class at the q1 orbit-representative
position `q` of class `r`, `classElt (σ c)` is the basis element of the *aligned*
q2 character `repChars2[r][alnPos[r][q]]` — exactly the row the stage-2/3/4 column
certificates compare against.

(Stated with the index destructured: definitional unfolding of a `Σ`-valued
definition at an *opaque* index forces the kernel to compare the dependent type
family `fun r => Fin (repChars2.getD r []).length`, which blows up on the
148-row literal. With explicit components everything is iota-reduction.) -/
theorem classElt_sigmaEquiv_orbRepClass (r : Fin 148)
    (q : Fin (repChars.getD r.val []).length)
    (hq : (normIsRep.getD r.val []).getD q.val false = true)
    (hlt : (alnPos.getD r.val []).getD q.val 0 < (Q2.repChars2.getD r.val []).length) :
    classElt (sigmaEquiv (orbRepClass ⟨r, ⟨q, hq⟩⟩))
      = basisElt (Q2.reps r) (Q2.charOfVec2 r
          ((Q2.repChars2.getD r.val []).getD ((alnPos.getD r.val []).getD q.val 0) [])
          (Q2.validAt r (Q2.listedAt r hlt))) := by
  rw [sigmaEquiv_orbRepClass]
  rw [show Q2.orbRepClass (psi ⟨r, ⟨q, hq⟩⟩)
      = (⟦⟨Q2.reps r, Q2.charOfVec2 r
          ((Q2.repChars2.getD r.val []).getD ((alnPos.getD r.val []).getD q.val 0) [])
          (Q2.validAt r (Q2.listedAt r hlt))⟩⟧ : CharPairClass (Coordinate 2) ℂˣ) from
    Q2.class_pos_eq_orbRepClass r ((alnPos.getD r.val []).getD q.val 0) hlt
      ⟨alnLab r.val q.val, (alnCheck_rep r q.isLt hq).2.1⟩
      (alnCheck_rep r q.isLt hq).2.2.1 rfl]
  rw [classElt_mk]

end LeanDring.P5Presentation
