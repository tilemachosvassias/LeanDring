/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Even.ConductorDictionaryGalois
import LeanDring.Theory.DRing.Induced
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Item (1) of the conductor dictionary: `SpeciesPairSeparation`, proven

**EVEN-ORDER LAYER.** Inside the root module's build closure and audit:
no `sorry`, three standard axioms. The results here are
verified *implications*; their hypotheses are named `Prop`s (see §7.6 of
the paper).

`LeanDring/Even/ConductorDictionaryGalois.lean` left exactly one named hypothesis,
`SpeciesPairSeparation`: if `φ_{H,h} = φ_{H,k}` as ring homomorphisms
`D(G) →+* ℂ`, then `k` is conjugate to `h` by an element of `N_G(H)`, modulo
`⁅H, H⁆`.  This file discharges it.

## The proof

Test the two species on the *induced basis elements* `[H, λ]` of
`LeanDring/Theory/DRing/Induced.lean` — the monomial `G`-set `G/H` twisted by a linear
character `λ: H →* ℂˣ`.  Müller's formula (`DRing.species_basisElt`) gives

`φ_{H,m}[H, λ] = ∑_{q ∈ (G/H)^H} λ(s(q)⁻¹ · m · s(q))`,

a sum over the `H`-fixed cosets, `s = Quotient.out`.  Two facts about the
index set:

* the representative `s(q)` of an `H`-fixed coset **normalizes** `H`
  (`inv_out_mem_normalizer`) — this is where `N_G(H)` enters;
* the identity coset is `H`-fixed, and its contribution is `λ(m)` up to a
  conjugation by an element of `H` (`of_conjRep_one`).

So the hypothesis says: the two families of characters
`λ ↦ λ(s(q)⁻¹ h s(q))` and `λ ↦ λ(s(q)⁻¹ k s(q))`, indexed by `q`, have equal
value sums at every `λ`.  Passing to `A:= Abelianization ↥H` (legitimate:
each `λ` kills `⁅H,H⁆`) and dualizing — the index `q` now names the
*evaluation* character `ev_a: (A →* ℂˣ) →* ℂˣ` — this is exactly the input of
`count_eq_of_sum_eq` (**Dedekind's linear independence of characters**, already
in `LeanDring/Theory/DRing/SpeciesInjectivity.lean`).  Multiplicities therefore agree:
`ev_{h mod ⁅H,H⁆}` occurs on the `k`-side (via the identity coset), hence also
on the `h`-side, i.e. `s(q)⁻¹ h s(q) ≡ k (mod ⁅H,H⁆)` for some `H`-fixed coset
`q`.  Injectivity of `a ↦ ev_a` is duality for the finite abelian group `A`
(`CommGroup.forall_apply_eq_apply_iff`, ℂ being algebraically closed).

Consequence: `Even.fullyFused_of_intPoint` and everything downstream of it in
`ConductorDictionaryGalois.lean` become unconditional
(`fullyFused_of_intPoint'`).

No `sorry`, no custom axiom.
-/

set_option linter.unusedFintypeInType false

namespace LeanDring

open MulAction Finset

universe u

namespace Even

/-! ## Evaluation characters of a finite abelian group -/

section Duality

variable (A : Type*) [CommGroup A]

/-- Evaluation at `a: A`, as a character of the dual group `A →* ℂˣ`. -/
def evalChar (a : A) : (A →* ℂˣ) →* ℂˣ where
  toFun l := l a
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem evalChar_apply (a : A) (l : A →* ℂˣ) : evalChar A a l = l a := rfl

variable [Finite A]

/-- **Duality for finite abelian groups**: `a ↦ ev_a` is injective.  (ℂ is
algebraically closed, hence has enough roots of unity.) -/
theorem evalChar_injective : Function.Injective (evalChar A) := by
  intro a b hab
  refine (CommGroup.forall_apply_eq_apply_iff (M := ℂ) A).mp fun l => ?_
  exact DFunLike.congr_fun hab l

end Duality

/-! ## The `H`-fixed cosets of `G ⧸ H` -/

section FixCoset

variable {G : Type u} [Group G] [Fintype G] (H : Subgroup G)

/-- The `H`-fixed points of the coset space `G ⧸ H` — the index set of
Müller's species formula for the basis element `[H, λ]`. -/
abbrev FixCoset : Type u := fixedPoints ↥H (G ⧸ H)

/-- The representative of an `H`-fixed coset normalizes `H` (we record the
inverse, which is the conjugator appearing in `SpeciesPairSeparation`). -/
theorem inv_out_mem_normalizer (q : FixCoset H) :
    (q.1.out)⁻¹ ∈ Subgroup.normalizer H := by
  refine Subgroup.mem_normalizer_fintype (S := (H : Set G)) fun n hn => ?_
  have hfix : (⟨n, hn⟩ : ↥H) • q.1 = q.1 := q.2 ⟨n, hn⟩
  have h1 : ((n * q.1.out : G) : G ⧸ H) = ((q.1.out : G) : G ⧸ H) := by
    change (n : G) • ((q.1.out : G) : G ⧸ H) = _
    rw [QuotientGroup.out_eq']
    exact hfix
  have h2 : (n * q.1.out)⁻¹ * q.1.out ∈ H := QuotientGroup.eq.mp h1
  have h3 : (q.1.out⁻¹ * n⁻¹ * q.1.out) ∈ H := by
    have he : (n * q.1.out)⁻¹ * q.1.out = q.1.out⁻¹ * n⁻¹ * q.1.out := by group
    rwa [he] at h2
  have h4 : (q.1.out)⁻¹ * n * ((q.1.out)⁻¹)⁻¹ ∈ H := by
    have he : (q.1.out)⁻¹ * n * ((q.1.out)⁻¹)⁻¹ =
        (q.1.out⁻¹ * n⁻¹ * q.1.out)⁻¹ := by group
    rw [he]
    exact H.inv_mem h3
  exact h4

/-- The conjugate `s(q)⁻¹ · m · s(q) ∈ H` attached to an `H`-fixed coset `q`
and an element `m ∈ H`. -/
noncomputable def conjRep (m : H) (q : FixCoset H) : H :=
  ⟨q.1.out⁻¹ * m * q.1.out, MonGSet.sectionConj_mem H H m q.1 (q.2 m)⟩

omit [Fintype G] in
/-- The identity coset is `H`-fixed. -/
theorem one_mem_fixCoset : ((1 : G) : G ⧸ H) ∈ fixedPoints ↥H (G ⧸ H) := by
  intro u
  change ((u : G) * (1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H)
  rw [mul_one]
  exact QuotientGroup.eq.mpr (by simp)

/-- The identity coset, as an element of `FixCoset H`. -/
def oneFixCoset : FixCoset H := ⟨((1 : G) : G ⧸ H), one_mem_fixCoset H⟩

omit [Fintype G] in
/-- At the identity coset, the conjugate is `m` up to conjugation *inside* `H`
— hence equal to `m` in the abelianization. -/
theorem of_conjRep_one (m : H) :
    Abelianization.of (conjRep H m (oneFixCoset H)) = Abelianization.of m := by
  set a : G := ((1 : G) : G ⧸ H).out with ha
  have haH : a ∈ H := by
    have h0 : ((a : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := QuotientGroup.out_eq' _
    have h1 : a⁻¹ ∈ H := by simpa using QuotientGroup.eq.mp h0
    simpa using H.inv_mem h1
  have hrep : conjRep H m (oneFixCoset H) = (⟨a, haH⟩ : H)⁻¹ * m * ⟨a, haH⟩ := by
    apply Subtype.ext
    rfl
  rw [hrep, map_mul, map_mul, map_inv]
  rw [mul_comm (Abelianization.of (⟨a, haH⟩ : H))⁻¹ (Abelianization.of m),
    mul_assoc, inv_mul_cancel, mul_one]

end FixCoset

/-! ## Müller's formula at `[H, λ]`, in the shape used below -/

section Formula

variable {G : Type u} [Group G] [Fintype G]

/-- `φ_{H,m}[H, λ] = ∑_{q ∈ (G/H)^H} λ(s(q)⁻¹ · m · s(q))`. -/
theorem species_basisElt_self (H : Subgroup G) (l : H →* ℂˣ) (m : H) :
    DRing.species H m (DRing.basisElt H l) =
      ∑ q : FixCoset H, ((l (conjRep H m q) : ℂˣ) : ℂ) := by
  rw [DRing.species_basisElt]
  exact Fintype.sum_equiv (Equiv.refl _) _ _ fun _ => rfl

end Formula

/-! ## The separation theorem -/

/-- **Item (1), proven**: the species table is indexed by pair classes.  If
`φ_{H,h} = φ_{H,k}` then `k` is `N_G(H)`-conjugate to `h` modulo `⁅H, H⁆`. -/
theorem speciesPairSeparation : SpeciesPairSeparation.{u} := by
  classical
  intro G _ _ H h k hspec
  -- (1) Test the species equality on the basis elements `[H, λ]`.
  have hsum : ∀ l : H →* ℂˣ,
      ∑ q : FixCoset H, ((l (conjRep H h q) : ℂˣ) : ℂ) =
        ∑ q : FixCoset H, ((l (conjRep H k q) : ℂˣ) : ℂ) := by
    intro l
    rw [← species_basisElt_self H l h, ← species_basisElt_self H l k]
    exact DFunLike.congr_fun hspec (DRing.basisElt H l)
  -- (2) Push the characters through the abelianization of `↥H`.
  set A := Abelianization (H : Type u) with hA
  set f : FixCoset H → A := fun q => Abelianization.of (conjRep H h q) with hf
  set g : FixCoset H → A := fun q => Abelianization.of (conjRep H k q) with hg
  -- (3) Dedekind counting in the dual group `A →* ℂˣ`.
  have hdual : ∀ m : (A →* ℂˣ),
      ∑ q : FixCoset H, ((evalChar A (f q) m : ℂˣ) : ℂ) =
        ∑ q : FixCoset H, ((evalChar A (g q) m : ℂˣ) : ℂ) :=
    fun m => hsum (m.comp Abelianization.of)
  have hcount := count_eq_of_sum_eq (M := (A →* ℂˣ))
    (fun q : FixCoset H => evalChar A (f q))
    (fun q : FixCoset H => evalChar A (g q)) hdual (evalChar A (Abelianization.of k))
  -- (4) The identity coset puts `k` on the right-hand family …
  have hmemk : oneFixCoset H ∈
      univ.filter (fun q : FixCoset H => evalChar A (g q) =
        evalChar A (Abelianization.of k)) := by
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    exact congrArg (evalChar A) (of_conjRep_one H k)
  -- … hence also on the left-hand family.
  have hpos : 0 < (univ.filter (fun q : FixCoset H => evalChar A (f q) =
      evalChar A (Abelianization.of k))).card := by
    rw [hcount]
    exact card_pos.mpr ⟨_, hmemk⟩
  obtain ⟨q, hq⟩ := card_pos.mp hpos
  rw [mem_filter] at hq
  -- (5) Duality: equal evaluation characters means equal group elements.
  have hfq : Abelianization.of (conjRep H h q) = Abelianization.of k :=
    evalChar_injective A hq.2
  -- (6) Translate back into `G`.
  have hker : (conjRep H h q) * k⁻¹ ∈ commutator (H : Type u) := by
    have hone : Abelianization.of ((conjRep H h q) * k⁻¹) = 1 := by
      rw [map_mul, map_inv, hfq, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff _).mp hone
  refine ⟨(q.1.out)⁻¹, inv_out_mem_normalizer H q, ?_⟩
  have hmap : (((conjRep H h q) * k⁻¹ : H) : G) ∈ ⁅H, H⁆ := by
    rw [← map_commutator_subtype H]
    exact Subgroup.mem_map_of_mem H.subtype hker
  have hval : (((conjRep H h q) * k⁻¹ : H) : G) =
      ((q.1.out)⁻¹ * (h : G) * ((q.1.out)⁻¹)⁻¹) * ((k : G))⁻¹ := by
    simp [conjRep]
  rwa [hval] at hmap

/-- **`fullyFused_of_intPoint`, unconditional**: the `SpeciesPairSeparation`
hypothesis of `ConductorDictionaryGalois.lean` is now discharged. -/
theorem fullyFused_of_intPoint' {G : Type u} [Group G] [Fintype G]
    (H : Subgroup G) (h : H) {p : DRing G →+* ℤ}
    (hp : complexify (DRing G) p = DRing.species H h) :
    FullyFused H h :=
  fullyFused_of_intPoint speciesPairSeparation H h hp

end Even

end LeanDring

/-! ## Axiom audit -/

#print axioms LeanDring.Even.evalChar_injective
#print axioms LeanDring.Even.inv_out_mem_normalizer
#print axioms LeanDring.Even.one_mem_fixCoset
#print axioms LeanDring.Even.of_conjRep_one
#print axioms LeanDring.Even.species_basisElt_self
#print axioms LeanDring.Even.speciesPairSeparation
#print axioms LeanDring.Even.fullyFused_of_intPoint'
