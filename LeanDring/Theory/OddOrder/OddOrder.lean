/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.DtoB
import LeanDring.Theory.DRing.FreeBasis
import LeanDring.Theory.DRing.Induced
import LeanDring.Theory.DRing.Unipotent
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The odd-order `D ⇒ B` theorem

This module formalizes Müller's theorem that an isomorphism of monomial
representation rings of finite odd-order groups induces an isomorphism of
their Burnside rings.

Müller's proof (Satz 2.5.3--2.5.4; the theorem appeared as [Mueller2012]
Thm. 2.4) recognizes the primitive idempotents with
trivial fibre intrinsically: their species are exactly those which take
integer values on the integral D-ring.  A nontrivial fibre in odd order
produces a cyclotomic orbit sum which is not an integer.  An abstract ring
isomorphism therefore preserves the trivial-fibre idempotents, and Müller's
projection argument induces an isomorphism of Burnside rings.

This file develops that proof in layers.  The first definitions below make
"integer-valued on the integral D-ring" ring-theoretic and prove the easy
trivial-fibre direction.  The parity lemmas are the arithmetic core used in
the nontrivial-fibre direction.  The spectrum layer
(`everyComplexPointIsSpecies`) and Satz 2.5.3
(`nontrivialSpeciesNotIntegerValued_of_odd`) are both proved, and the
`D ⇒ B` conclusion itself is `burnsideEquivOfOddOrder`, which assumes only
that the two groups have odd order.
-/

namespace LeanDring

namespace OddOrder

universe u v

open MonGSet

noncomputable instance complexHasEnoughRootsOfUnity (n : ℕ) [NeZero n] :
    HasEnoughRootsOfUnity ℂ n := {
  prim := ⟨_, Complex.isPrimitiveRoot_exp n NeZero.out⟩
  cyc := rootsOfUnity.isCyclic ℂ n }

noncomputable instance complexCharacterFintype
    (A : Type u) [CommGroup A] [Finite A] : Fintype (A →* ℂˣ) := by
  letI : NeZero (Monoid.exponent A) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  exact Fintype.ofFinite _

noncomputable instance complexRestrictionKernelFintype
    (A : Type u) [CommGroup A] [Finite A] (K : Subgroup A) :
    Fintype (MonoidHom.restrictHom K ℂˣ).ker := Fintype.ofFinite _

instance abelianizationFinite (A : Type u) [Group A] [Finite A] :
    Finite (Abelianization A) :=
  Finite.of_surjective Abelianization.of
    (QuotientGroup.mk'_surjective (commutator A))

noncomputable instance cosetFixedPointsFintype
    (G : Type u) [Group G] [Fintype G] (H : Subgroup G) :
    Fintype (MulAction.fixedPoints H (G ⧸ H)) := Fintype.ofFinite _

/-- A complex-valued ring homomorphism on an integral ring is integer-valued
if every value lies in the canonical copy of `ℤ ⊆ ℂ`.  This formulation is
intrinsic under precomposition by a ring isomorphism. -/
def IsIntegerValued {R : Type*} [Ring R] (s : R →+* ℂ) : Prop :=
  ∀ x, ∃ z : ℤ, s x = (z : ℂ)

/-- Integer-valuedness is preserved by precomposition with a surjective ring
homomorphism (in particular, by a ring equivalence). -/
theorem isIntegerValued_comp_of_surjective
    {R S : Type*} [Ring R] [Ring S] (s : S →+* ℂ) (f : R →+* S)
    (hs : IsIntegerValued s) : IsIntegerValued (s.comp f) := by
  intro x
  simpa using hs (f x)

/-- For a surjective change of rings, integer-valuedness can also be detected
after precomposition. -/
theorem isIntegerValued_iff_comp_of_surjective
    {R S : Type*} [Ring R] [Ring S] (s : S →+* ℂ) (f : R →+* S)
    (hf : Function.Surjective f) :
    IsIntegerValued (s.comp f) ↔ IsIntegerValued s := by
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := hf y
    exact h x
  · exact isIntegerValued_comp_of_surjective s f

/-- The trivial-fibre species is integer-valued.  Indeed it is the ordinary
Burnside mark of the underlying monomial set (Müller, the easy half of
Satz 2.5.3). -/
theorem species_one_isIntegerValued
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    IsIntegerValued (DRing.species H 1) := by
  letI := Fintype.ofFinite G
  intro x
  refine ⟨BurnsideRing.mark H (MonRing.forget x), ?_⟩
  have hx := DFunLike.congr_fun (DRing.species_one_eq_mark_forget H) x
  change DRing.species H 1 x =
    Int.castRingHom ℂ (BurnsideRing.mark H (MonRing.forget x))
  simpa only [RingHom.coe_comp, Function.comp_apply] using hx

/-- Integer-valuedness of a species is transported exactly across a ring
equivalence.  This is the ring-theoretic sentence used in Satz 2.5.4. -/
theorem species_isIntegerValued_iff_comp_equiv
    {G : Type u} {G' : Type v} [Group G] [Finite G]
    [Group G'] [Finite G'] (Phi : DRing G ≃+* DRing G')
    (H' : Subgroup G') (h' : H') :
    IsIntegerValued ((DRing.species H' h').comp Phi.toRingHom) ↔
      IsIntegerValued (DRing.species H' h') :=
  isIntegerValued_iff_comp_of_surjective _ _ Phi.surjective

/-- Complex points of a ring are transported contravariantly by a ring
equivalence.  This is the intrinsic spectrum permutation used by Müller. -/
noncomputable def complexPointsEquiv
    {R S : Type*} [Ring R] [Ring S] (Phi : R ≃+* S) :
    (S →+* ℂ) ≃ (R →+* ℂ) where
  toFun s := s.comp Phi.toRingHom
  invFun r := r.comp Phi.symm.toRingHom
  left_inv s := by
    ext y
    simp
  right_inv r := by
    ext x
    simp

@[simp] theorem complexPointsEquiv_apply
    {R S : Type*} [Ring R] [Ring S] (Phi : R ≃+* S)
    (s : S →+* ℂ) (x : R) :
    complexPointsEquiv Phi s x = s (Phi x) := rfl

/-- The spectrum permutation induced by a ring equivalence preserves the
integer-valued locus in both directions. -/
theorem complexPointsEquiv_preserves_integerValued
    {R S : Type*} [Ring R] [Ring S] (Phi : R ≃+* S) (s : S →+* ℂ) :
    IsIntegerValued (complexPointsEquiv Phi s) ↔ IsIntegerValued s :=
  isIntegerValued_iff_comp_of_surjective s Phi.toRingHom Phi.surjective

/-- The common zero locus of all integer-valued complex points of a ring. -/
def IntegerKernel {R : Type*} [Ring R] (x : R) : Prop :=
  ∀ s : R →+* ℂ, IsIntegerValued s → s x = 0

/-- Ring equivalences preserve the common kernel of integer-valued points. -/
theorem integerKernel_equiv_iff
    {R S : Type*} [Ring R] [Ring S] (Phi : R ≃+* S) (x : R) :
    IntegerKernel (Phi x) ↔ IntegerKernel x := by
  constructor
  · intro hx s hs
    let t : S →+* ℂ := s.comp Phi.symm.toRingHom
    have ht : IsIntegerValued t :=
      isIntegerValued_comp_of_surjective s Phi.symm.toRingHom hs
    have := hx t ht
    simpa [t] using this
  · intro hx s hs
    have hs' : IsIntegerValued (complexPointsEquiv Phi s) :=
      (complexPointsEquiv_preserves_integerValued Phi s).2 hs
    exact hx _ hs'

/-- The spectrum statement needed from the species classification and the
odd-order cyclotomic argument: every integer-valued complex point is a
trivial-fibre species. -/
def AllIntegerPointsAreMarks (G : Type u) [Group G] [Fintype G] : Prop :=
  ∀ s : DRing G →+* ℂ, IsIntegerValued s →
    ∃ H : Subgroup G, s = DRing.species H 1

/-- Every complex point of the integral D-ring is one of Müller's species.
This is the spectrum/primitive-idempotent classification, independent of
the odd-order hypothesis. -/
def EveryComplexPointIsSpecies (G : Type u) [Group G] [Fintype G] : Prop :=
  ∀ s : DRing G →+* ℂ, ∃ (H : Subgroup G) (h : H), s = DRing.species H h

/-- Scalar extension of the integral D-ring to its complex species
algebra. -/
abbrev ComplexifiedDRing (G : Type u) [Group G] [Fintype G] :=
  TensorProduct ℤ ℂ (DRing G)

/-- Every integral complex point extends canonically across scalar
extension. -/
noncomputable def extendComplexPoint
    {G : Type u} [Group G] [Fintype G] (s : DRing G →+* ℂ) :
    ComplexifiedDRing G →ₐ[ℂ] ℂ := {
  toRingHom := (Algebra.TensorProduct.lift (AlgHom.id ℤ ℂ)
    s.toIntAlgHom (fun _ _ => Commute.all _ _)).toRingHom
  commutes' z := by simp }

@[simp] theorem extendComplexPoint_tmul
    {G : Type u} [Group G] [Fintype G] (s : DRing G →+* ℂ)
    (z : ℂ) (x : DRing G) :
    extendComplexPoint s (z ⊗ₜ[ℤ] x) = z * s x := by
  simp [extendComplexPoint]

@[simp] theorem extendComplexPoint_includeRight
    {G : Type u} [Group G] [Fintype G] (s : DRing G →+* ℂ)
    (x : DRing G) :
    extendComplexPoint s (Algebra.TensorProduct.includeRight x) = s x := by
  change extendComplexPoint s ((1 : ℂ) ⊗ₜ[ℤ] x) = s x
  simp

/-- The complex extension of a species restricts to the original species
on the integral lattice. -/
theorem extendSpecies_includeRight
    {G : Type u} [Group G] [Fintype G] (H : Subgroup G) (h : H)
    (x : DRing G) :
    extendComplexPoint (DRing.species H h)
        (Algebra.TensorProduct.includeRight x) = DRing.species H h x := by
  simp

/-- Scalar extension does not identify distinct integral complex points. -/
theorem extendComplexPoint_injective
    {G : Type u} [Group G] [Fintype G] :
    Function.Injective (extendComplexPoint (G := G)) := by
  intro s t h
  ext x
  have hx := DFunLike.congr_fun h (Algebra.TensorProduct.includeRight x)
  simpa using hx

/-- A column of the complex species table, indexed without choosing orbit
representatives on the species side. -/
noncomputable def complexSpeciesColumn
    {G : Type u} [Group G] [Fintype G]
    (c : CharPairClass G ℂˣ) : (Σ H : Subgroup G, H) → ℂ :=
  fun p => DRing.species p.1 p.2 (DRing.classElt c)

/-- Evaluation of a finite linear combination of species-table columns at
one species. -/
theorem sum_complexSpeciesColumn_apply
    {G : Type u} [Group G] [Fintype G]
    (S : Finset (CharPairClass G ℂˣ))
    (g : CharPairClass G ℂˣ → ℂ) (H : Subgroup G) (h : H) :
    (∑ c ∈ S, g c • complexSpeciesColumn c) ⟨H, h⟩ =
      ∑ c ∈ S, g c * DRing.species H h (DRing.classElt c) := by
  simp [complexSpeciesColumn]

/-- The columns of the complex species table remain linearly independent
after extending coefficients from `ℤ` to `ℂ`.  This is the strengthened
ghost-map injectivity needed for the spectrum theorem. -/
theorem complexSpeciesColumn_linearIndependent
    {G : Type u} [Group G] [Fintype G] :
    LinearIndependent ℂ (complexSpeciesColumn (G := G)) := by
  classical
  rw [linearIndependent_iff']
  intro S g hrel i hi
  by_contra hgi
  let T := S.filter (fun c => g c ≠ 0)
  have hTne : T.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  obtain ⟨cS, hcST, hcSmax⟩ :=
    T.exists_max_image (fun c => Nat.card c.out.1) hTne
  let K₀ := cS.out.1
  let M := Nat.card K₀
  let topSupp := T.filter (fun c => Nat.card c.out.1 = M)
  have hcStop : cS ∈ topSupp := by
    exact Finset.mem_filter.mpr ⟨hcST, rfl⟩
  have hcardTop : ∀ c ∈ topSupp, Nat.card K₀ = Nat.card c.out.1 := by
    intro c hc
    exact (Finset.mem_filter.mp hc).2.symm
  have hspec : ∀ h : K₀,
      ∑ c ∈ topSupp, ∑ q : MulAction.fixedPoints K₀
          (MonGSet.induced c.out.1 c.out.2 : MonGSet G ℂˣ).carrier,
        g c * (((DRing.conjChar K₀ c.out.1 c.out.2 q.1 q.2 h : ℂˣ) : ℂ)) = 0 := by
    intro h
    have hev := congrFun hrel ⟨K₀, h⟩
    rw [sum_complexSpeciesColumn_apply] at hev
    simp only [Pi.zero_apply] at hev
    rw [← Finset.sum_filter_add_sum_filter_not S (fun c => g c ≠ 0)] at hev
    have hzero : ∑ c ∈ S.filter (fun c => ¬ g c ≠ 0),
        g c * DRing.species K₀ h (DRing.classElt c) = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      rw [Finset.mem_filter] at hc
      rw [show g c = 0 from not_ne_iff.mp hc.2, zero_mul]
    rw [hzero, add_zero] at hev
    change (∑ c ∈ T, g c * DRing.species K₀ h (DRing.classElt c)) = 0 at hev
    rw [← Finset.sum_filter_add_sum_filter_not T
      (fun c => Nat.card c.out.1 = M)] at hev
    have hlower : ∑ c ∈ T.filter (fun c => ¬ Nat.card c.out.1 = M),
        g c * DRing.species K₀ h (DRing.classElt c) = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      rw [Finset.mem_filter] at hc
      have hlt : Nat.card c.out.1 < M :=
        lt_of_le_of_ne (hcSmax c hc.1) hc.2
      rw [DRing.species_classElt_eq_zero_of_card_lt K₀ h c hlt, mul_zero]
    rw [hlower, add_zero] at hev
    change (∑ c ∈ topSupp,
      g c * DRing.species K₀ h (DRing.classElt c)) = 0 at hev
    rw [← hev]
    apply Finset.sum_congr rfl
    intro c hc
    rw [DRing.species_classElt_eq_sum_conjChar, Finset.mul_sum]
  let N : (K₀ →* ℂˣ) →₀ ℂ :=
    ∑ c ∈ topSupp, ∑ q : MulAction.fixedPoints K₀
      (MonGSet.induced c.out.1 c.out.2 : MonGSet G ℂˣ).carrier,
      Finsupp.single (DRing.conjChar K₀ c.out.1 c.out.2 q.1 q.2) (g c)
  have hNzero : N = 0 := by
    have hLI : LinearIndependent ℂ
        (fun ξ : K₀ →* ℂˣ => (unitsCharToC ξ : K₀ → ℂ)) :=
      (linearIndependent_monoidHom K₀ ℂ).comp unitsCharToC
        unitsCharToC_injective
    apply (linearIndependent_iff.mp hLI)
    funext h
    simpa [N, unitsCharToC, Finsupp.linearCombination_apply]
      using hspec h
  have hFixne : Nonempty (MulAction.fixedPoints K₀
      (MonGSet.induced cS.out.1 cS.out.2 : MonGSet G ℂˣ).carrier) := by
    subst K₀
    refine ⟨⟨((1 : G) : G ⧸ cS.out.1), ?_⟩⟩
    intro k
    change ((((k : G) * 1 : G) : G ⧸ cS.out.1)) =
      ((1 : G) : G ⧸ cS.out.1)
    simp [QuotientGroup.eq, k.2]
  obtain ⟨qS⟩ := hFixne
  let ξS : K₀ →* ℂˣ :=
    DRing.conjChar K₀ cS.out.1 cS.out.2 qS.1 qS.2
  have hcSrec : (⟦(⟨K₀, ξS⟩ : CharPair G ℂˣ)⟧ : CharPairClass G ℂˣ) = cS := by
    change (⟦(⟨K₀, DRing.conjChar K₀ cS.out.1 cS.out.2 qS.1 qS.2⟩ :
      CharPair G ℂˣ)⟧ : CharPairClass G ℂˣ) = cS
    rw [DRing.classElt_conjChar_eq K₀ cS.out.1 cS.out.2 qS.1 qS.2
      (hcardTop cS hcStop)]
    exact Quotient.out_eq cS
  have hNval : N ξS =
      ∑ q : MulAction.fixedPoints K₀
        (MonGSet.induced cS.out.1 cS.out.2 : MonGSet G ℂˣ).carrier,
        if DRing.conjChar K₀ cS.out.1 cS.out.2 q.1 q.2 = ξS
          then g cS else 0 := by
    simp only [N, Finsupp.finsetSum_apply, Finsupp.single_apply]
    apply Finset.sum_eq_single_of_mem cS hcStop
    intro c hc hne
    apply Finset.sum_eq_zero
    intro q hq
    rw [if_neg]
    intro heq
    apply hne
    have hclass : (⟦(⟨K₀,
        DRing.conjChar K₀ c.out.1 c.out.2 q.1 q.2⟩ : CharPair G ℂˣ)⟧ :
        CharPairClass G ℂˣ) = c :=
      (DRing.classElt_conjChar_eq K₀ c.out.1 c.out.2 q.1 q.2
        (hcardTop c hc)).trans (Quotient.out_eq c)
    rw [heq] at hclass
    exact hclass.symm.trans hcSrec
  have hcount_pos : 0 < (Finset.univ.filter (fun q : MulAction.fixedPoints K₀
      (MonGSet.induced cS.out.1 cS.out.2 : MonGSet G ℂˣ).carrier =>
        DRing.conjChar K₀ cS.out.1 cS.out.2 q.1 q.2 = ξS)).card := by
    rw [Finset.card_pos]
    exact ⟨qS, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have hprod : ((Finset.univ.filter (fun q : MulAction.fixedPoints K₀
      (MonGSet.induced cS.out.1 cS.out.2 : MonGSet G ℂˣ).carrier =>
        DRing.conjChar K₀ cS.out.1 cS.out.2 q.1 q.2 = ξS)).card : ℂ) * g cS = 0 := by
    have := congrArg (fun F => F ξS) hNzero
    rw [hNval] at this
    simpa [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] using this
  have hgcs : g cS ≠ 0 := (Finset.mem_filter.mp hcST).2
  rcases mul_eq_zero.mp hprod with hc | hg
  · have hcne : ((Finset.univ.filter (fun q : MulAction.fixedPoints K₀
        (MonGSet.induced cS.out.1 cS.out.2 : MonGSet G ℂˣ).carrier =>
          DRing.conjChar K₀ cS.out.1 cS.out.2 q.1 q.2 = ξS)).card : ℂ) ≠ 0 := by
      exact_mod_cast hcount_pos.ne'
    exact hcne hc
  · exact hgcs hg

/-- The simultaneous complex species map on the scalar-extended D-ring. -/
noncomputable def complexTotalSpecies
    {G : Type u} [Group G] [Fintype G] :
    ComplexifiedDRing G →ₗ[ℂ] ((Σ H : Subgroup G, H) → ℂ) where
  toFun x := fun p => extendComplexPoint (DRing.species p.1 p.2) x
  map_add' x y := by ext p; simp
  map_smul' z x := by ext p; simp

/-- The simultaneous species map as a complex algebra homomorphism. -/
noncomputable def complexTotalSpeciesAlgHom
    {G : Type u} [Group G] [Fintype G] :
    ComplexifiedDRing G →ₐ[ℂ] ((Σ H : Subgroup G, H) → ℂ) where
  toFun x := fun p => extendComplexPoint (DRing.species p.1 p.2) x
  map_one' := by ext p; simp
  map_mul' x y := by ext p; simp
  map_zero' := by ext p; simp
  map_add' x y := by ext p; simp
  commutes' z := by ext p; simp

@[simp] theorem complexTotalSpecies_baseChangeBasis
    {G : Type u} [Group G] [Fintype G] (c : CharPairClass G ℂˣ) :
    complexTotalSpecies
        ((DRing.basisOfCharPairClass (G := G)).baseChange ℂ c) =
      complexSpeciesColumn c := by
  ext p
  have hb : ⇑(DRing.basisOfCharPairClass (G := G)) = DRing.classElt :=
    Module.Basis.coe_mk _ _
  simp [complexTotalSpecies, complexSpeciesColumn,
    Module.Basis.baseChange_apply, hb]

/-- The complex ghost map is injective.  Unlike integral species
injectivity, this rules out linear dependencies with arbitrary complex
coefficients. -/
theorem complexTotalSpecies_injective
    {G : Type u} [Group G] [Fintype G] :
    Function.Injective (complexTotalSpecies (G := G)) := by
  classical
  let b := (DRing.basisOfCharPairClass (G := G)).baseChange ℂ
  intro x y hxy
  apply sub_eq_zero.mp
  let z := x - y
  have hz : complexTotalSpecies z = 0 := by
    rw [map_sub, hxy, sub_self]
  have hexp : z = (b.repr z).sum (fun c a => a • b c) := by
    exact (b.linearCombination_repr z).symm
  have hcomb : ∑ c ∈ (b.repr z).support,
      (b.repr z c) • complexSpeciesColumn c = 0 := by
    calc
      _ = complexTotalSpecies ((b.repr z).sum (fun c a => a • b c)) := by
        rw [Finsupp.sum, map_sum]
        apply Finset.sum_congr rfl
        intro c hc
        rw [map_smul, complexTotalSpecies_baseChangeBasis]
      _ = complexTotalSpecies z := congrArg complexTotalSpecies hexp.symm
      _ = 0 := hz
  have hcoeff : ∀ c, b.repr z c = 0 := by
    intro c
    by_cases hc : c ∈ (b.repr z).support
    · exact (linearIndependent_iff'.mp complexSpeciesColumn_linearIndependent
        (b.repr z).support (fun c => b.repr z c) hcomb c hc)
    · exact Finsupp.notMem_support_iff.mp hc
  have hz0 : z = 0 := by
    apply b.repr.injective
    ext c
    simp [hcoeff]
  exact hz0

theorem complexTotalSpeciesAlgHom_injective
    {G : Type u} [Group G] [Fintype G] :
    Function.Injective (complexTotalSpeciesAlgHom (G := G)) := by
  intro x y h
  apply complexTotalSpecies_injective
  exact h

/-- A complex algebra character of a subalgebra of functions on a finite
nonempty set is evaluation at one of the points.  The proof uses the
finite-product trick: if every point supplied a function vanishing there
but not under the character, their normalized product would be both zero
and mapped to one. -/
theorem Subalgebra.exists_algHom_eq_eval
    {I : Type*} [Finite I] [Nonempty I]
    (A : Subalgebra ℂ (I → ℂ)) (φ : A →ₐ[ℂ] ℂ) :
    ∃ i : I, ∀ f : A, φ f = f.1 i := by
  classical
  letI := Fintype.ofFinite I
  by_contra hnone
  have hbad : ∀ i : I, ∃ f : A, f.1 i = 0 ∧ φ f ≠ 0 := by
    intro i
    by_contra hi
    push Not at hi
    apply hnone
    refine ⟨i, fun f => ?_⟩
    let c : A := algebraMap ℂ A (f.1 i)
    have hz : (f - c).1 i = 0 := by simp [c]
    have hφz : φ (f - c) = 0 := hi (f - c) hz
    have heq : φ f - f.1 i = 0 := by simpa [c] using hφz
    exact sub_eq_zero.mp heq
  let f : I → A := fun i => (hbad i).choose
  have hf0 : ∀ i, (f i).1 i = 0 := fun i => (hbad i).choose_spec.1
  have hfφ : ∀ i, φ (f i) ≠ 0 := fun i => (hbad i).choose_spec.2
  let g : I → A := fun i => (φ (f i))⁻¹ • f i
  have hg0 : ∀ i, (g i).1 i = 0 := by
    intro i
    simp [g, hf0]
  have hgφ : ∀ i, φ (g i) = 1 := by
    intro i
    simp [g, hfφ i]
  let P : A := ∏ i, g i
  have hP0 : P = 0 := by
    dsimp only [P]
    apply Subtype.ext
    funext i
    change A.val (∏ j, g j) i = A.val 0 i
    rw [map_prod, map_zero]
    simp only [Finset.prod_apply, Pi.zero_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hg0 i)
  have hPφ : φ P = 1 := by
    simp [P, hgφ]
  rw [hP0, map_zero] at hPφ
  exact zero_ne_one hPφ

/-- **Complex spectrum classification.** Every complex-valued ring point
of the integral D-ring is one of Müller's species. -/
theorem everyComplexPointIsSpecies
    (G : Type u) [Group G] [Fintype G] : EveryComplexPointIsSpecies G := by
  classical
  intro s
  let F := complexTotalSpeciesAlgHom (G := G)
  let e : ComplexifiedDRing G ≃ₐ[ℂ] F.range :=
    AlgEquiv.ofInjective F complexTotalSpeciesAlgHom_injective
  let φ : F.range →ₐ[ℂ] ℂ :=
    (extendComplexPoint s).comp e.symm.toAlgHom
  letI : Nonempty (Σ H : Subgroup G, H) := ⟨⟨⊥, 1⟩⟩
  obtain ⟨p, hp⟩ := Subalgebra.exists_algHom_eq_eval F.range φ
  refine ⟨p.1, p.2, ?_⟩
  apply extendComplexPoint_injective
  ext x
  let xC : ComplexifiedDRing G := Algebra.TensorProduct.includeRight x
  let fx : F.range := ⟨F xC, ⟨xC, rfl⟩⟩
  have hpx := hp fx
  have hefx : e.symm fx = xC := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    rfl
  change extendComplexPoint s xC =
    extendComplexPoint (DRing.species p.1 p.2) xC
  calc
    extendComplexPoint s xC = φ fx := by
      simp [φ, hefx]
    _ = fx.1 p := hpx
    _ = extendComplexPoint (DRing.species p.1 p.2) xC := rfl

/-- A species has trivial fibre when the class of `h` in `H/H'` is the
identity. -/
def IsTrivialFibre {G : Type u} [Group G] {H : Subgroup G} (h : H) : Prop :=
  Abelianization.of h = 1

/-- Species only depend on the class `hH'`: if `h` is trivial in the
abelianization, its species is the ordinary mark species `(H,1)`. -/
theorem species_eq_one_of_trivialFibre
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) (h : H)
    (hh : IsTrivialFibre h) :
    DRing.species H h = DRing.species H 1 := by
  letI := Fintype.ofFinite G
  refine GrothendieckRing.hom_ext fun a => ?_
  obtain ⟨X⟩ := a
  simp only [DRing.species, MonRing.species, GrothendieckRing.lift_of]
  change MonGSet.speciesSum (Units.coeHom ℂ) H h X =
    MonGSet.speciesSum (Units.coeHom ℂ) H 1 X
  apply Finset.sum_congr rfl
  intro x hx
  have hcomm : h ∈ commutator H := by
    rw [← Abelianization.ker_of]
    exact hh
  have hker := Abelianization.commutator_subset_ker
    (X.fixedWeight H x) hcomm
  rw [MonoidHom.mem_ker] at hker
  have hw1 : X.fixedWeight H x 1 = 1 := (X.fixedWeight H x).map_one
  rw [hker, hw1]

/-- Subgroups of a finite odd-order group again have odd order. -/
theorem odd_card_subgroup
    {G : Type u} [Group G] [Finite G] (hG : Odd (Nat.card G))
    (H : Subgroup G) : Odd (Nat.card H) :=
  hG.of_dvd_nat H.card_subgroup_dvd_card

/-- The abelianization of a finite odd-order group has odd order. -/
theorem odd_card_abelianization
    {G : Type u} [Group G] [Finite G] (hG : Odd (Nat.card G)) :
    Odd (Nat.card (Abelianization G)) := by
  apply hG.of_dvd_nat
  exact Subgroup.card_quotient_dvd_card (commutator G)

/-- A nontrivial fibre in an odd-order group has an odd prime divisor in
its order.  This selects the prime `p` used in Müller's cyclotomic witness. -/
theorem exists_odd_prime_dvd_fibre_order
    {G : Type u} [Group G] [Finite G] (hG : Odd (Nat.card G))
    {H : Subgroup G} (h : H) (hh : ¬ IsTrivialFibre h) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ orderOf (Abelianization.of h) := by
  have hord_ne : orderOf (Abelianization.of h) ≠ 1 := by
    intro hord
    apply hh
    exact orderOf_eq_one_iff.mp hord
  obtain ⟨p, hp, hpord⟩ := Nat.exists_prime_and_dvd hord_ne
  have hord_card : orderOf (Abelianization.of h) ∣
      Nat.card (Abelianization H) := orderOf_dvd_natCard _
  have hp_card : p ∣ Nat.card (Abelianization H) := hpord.trans hord_card
  have hoddH : Odd (Nat.card H) := odd_card_subgroup hG H
  have hoddAb : Odd (Nat.card (Abelianization H)) :=
    odd_card_abelianization hoddH
  exact ⟨p, hp, hoddAb.ne_two_of_dvd_nat hp_card, hpord⟩

/-- A prime divisor of the fibre order yields a character taking a
primitive `p`-th-root value on the corresponding prime-order element. -/
theorem exists_primitive_character_on_fibre_prime_part
    {G : Type u} [Group G] [Finite G] {H : Subgroup G} (h : H)
    {p : ℕ} (hp : p.Prime) (hpord : p ∣ orderOf (Abelianization.of h)) :
    ∃ chi : Abelianization H →* ℂˣ,
      IsPrimitiveRoot
        (((chi ((Abelianization.of h) ^
          (orderOf (Abelianization.of h) / p)) : ℂˣ) : ℂ)) p := by
  letI : Finite (Abelianization H) :=
    Finite.of_surjective Abelianization.of
      (QuotientGroup.mk'_surjective (commutator H))
  let a : Abelianization H := Abelianization.of h
  let k : Abelianization H := a ^ (orderOf a / p)
  have ha0 : orderOf a ≠ 0 := orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite a)
  have hkord : orderOf k = p := orderOf_pow_orderOf_div ha0 hpord
  have hk_ne : k ≠ 1 := by
    intro hk
    have : orderOf k = 1 := orderOf_eq_one_iff.mpr hk
    apply hp.ne_one
    rw [← hkord]
    exact this
  letI : NeZero (Monoid.exponent (Abelianization H)) :=
    ⟨Monoid.exponent_ne_zero_of_finite⟩
  letI : HasEnoughRootsOfUnity ℂ (Monoid.exponent (Abelianization H)) := {
    prim := ⟨_, Complex.isPrimitiveRoot_exp _ NeZero.out⟩
    cyc := rootsOfUnity.isCyclic ℂ _ }
  obtain ⟨chi, hchi⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
      (Abelianization H) ℂ hk_ne
  have hord_dvd : orderOf (chi k) ∣ p := by
    rw [← hkord]
    exact orderOf_map_dvd chi k
  have hchiord : orderOf (chi k) = p := by
    rcases (Nat.dvd_prime hp).mp hord_dvd with hone | hp'
    · exact False.elim (hchi (orderOf_eq_one_iff.mp hone))
    · exact hp'
  refine ⟨chi, ?_⟩
  rw [IsPrimitiveRoot.iff_orderOf]
  change orderOf (((chi k : ℂˣ) : ℂ)) = p
  rw [orderOf_units, hchiord]

/-- Character orthogonality for the annihilator of a subgroup: if `y` is
outside `K`, the sum of `eta(y)` over all characters trivial on `K` is zero.
This is the cancellation step in Müller's induced-character construction. -/
theorem sum_restrictionKernel_apply_eq_zero_of_not_mem
    {A : Type u} [CommGroup A] [Finite A] (K : Subgroup A)
    (y : A) (hy : y ∉ K) :
    ∑ eta : (MonoidHom.restrictHom K ℂˣ).ker,
      (((eta.1 y : ℂˣ) : ℂ)) = 0 := by
  let ev : (MonoidHom.restrictHom K ℂˣ).ker →* ℂ := {
    toFun eta := ((eta.1 y : ℂˣ) : ℂ)
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hev_ne : ev ≠ 1 := by
    have hsep := (CommGroup.forall_monoidHom_apply_eq_one_iff
      (G := A) (ℂ) K y).not.mpr hy
    simp only [not_forall] at hsep
    obtain ⟨eta, hetaK, hetay⟩ := hsep
    let eta0 : (MonoidHom.restrictHom K ℂˣ).ker := ⟨eta, by
      apply MonoidHom.ext
      intro k
      exact hetaK k k.2⟩
    intro hev
    have := DFunLike.congr_fun hev eta0
    apply hetay
    exact Units.ext this
  simpa [ev] using sum_hom_units_eq_zero ev hev_ne

/-- On the subgroup itself every character in the restriction kernel is
trivial, so the same sum is its cardinality. -/
theorem sum_restrictionKernel_apply_eq_card_of_mem
    {A : Type u} [CommGroup A] [Finite A] (K : Subgroup A)
    (y : A) (hy : y ∈ K) :
    ∑ eta : (MonoidHom.restrictHom K ℂˣ).ker,
      (((eta.1 y : ℂˣ) : ℂ)) =
      (Nat.card (MonoidHom.restrictHom K ℂˣ).ker : ℂ) := by
  have heta : ∀ eta : (MonoidHom.restrictHom K ℂˣ).ker,
      (((eta.1 y : ℂˣ) : ℂ)) = 1 := by
    intro eta
    have hk := DFunLike.congr_fun eta.2 ⟨y, hy⟩
    exact congrArg Units.val hk
  rw [Finset.sum_congr rfl (fun eta _ => heta eta), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]

/-- Sum of all character extensions of a fixed character: it vanishes off
`K`, and on `K` equals the base value times the size of the annihilator. -/
theorem sum_character_coset_apply
    {A : Type u} [CommGroup A] [Finite A] (K : Subgroup A)
    [DecidablePred (fun y : A => y ∈ K)]
    (l : A →* ℂˣ) (y : A) :
    ∑ eta : (MonoidHom.restrictHom K ℂˣ).ker,
      (((((l * eta.1) y) : ℂˣ) : ℂ)) =
      if y ∈ K then
        (Nat.card (MonoidHom.restrictHom K ℂˣ).ker : ℂ) *
          (((l y : ℂˣ) : ℂ))
      else 0 := by
  classical
  have hfactor :
      (((l y : ℂˣ) : ℂ)) *
          (∑ eta : (MonoidHom.restrictHom K ℂˣ).ker,
            (((eta.1 y : ℂˣ) : ℂ))) =
        ∑ eta : (MonoidHom.restrictHom K ℂˣ).ker,
          (((((l * eta.1) y) : ℂˣ) : ℂ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro eta heta
    rfl
  rw [← hfactor]
  by_cases hy : y ∈ K
  · rw [if_pos hy, sum_restrictionKernel_apply_eq_card_of_mem K y hy]
    ring
  · rw [if_neg hy]
    rw [sum_restrictionKernel_apply_eq_zero_of_not_mem K y hy, mul_zero]

/-- The D-ring element obtained by summing the basis elements associated to
one coset of the annihilator of `K` in the character group. -/
noncomputable def extensionOrbitElt
    {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    (K : Subgroup (Abelianization H)) (l : Abelianization H →* ℂˣ) :
    DRing G :=
  ∑ eta : (MonoidHom.restrictHom K ℂˣ).ker,
    DRing.basisElt H ((l * eta.1).comp Abelianization.of)

/-- Expand the species of `extensionOrbitElt` as a double sum over fixed
cosets and the character-extension coset. -/
theorem species_extensionOrbitElt
    {G : Type u} [Group G] [Fintype G] (H : Subgroup G) (h : H)
    (K : Subgroup (Abelianization H)) (l : Abelianization H →* ℂˣ) :
    DRing.species H h (extensionOrbitElt H K l) =
      ∑ q : MulAction.fixedPoints H (G ⧸ H),
        ∑ eta : (MonoidHom.restrictHom K ℂˣ).ker,
          (((((l * eta.1)
            (Abelianization.of
              ⟨q.1.out⁻¹ * h * q.1.out,
                MonGSet.sectionConj_mem H H h q.1 (q.2 h)⟩)) : ℂˣ) : ℂ)) := by
  rw [extensionOrbitElt, map_sum]
  simp_rw [DRing.species_basisElt]
  rw [Finset.sum_comm]
  simp only [MonoidHom.coe_comp, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro eta heta
  apply Finset.sum_congr rfl
  intro q hq
  rfl

/-- Character orthogonality collapses the extension sum: only fixed cosets
whose conjugate of `hH'` lies in `K` survive. -/
theorem species_extensionOrbitElt_collapse
    {G : Type u} [Group G] [Fintype G] (H : Subgroup G) (h : H)
    (K : Subgroup (Abelianization H))
    [DecidablePred (fun y : Abelianization H => y ∈ K)]
    (l : Abelianization H →* ℂˣ) :
    DRing.species H h (extensionOrbitElt H K l) =
      (Nat.card (MonoidHom.restrictHom K ℂˣ).ker : ℂ) *
        ∑ q : MulAction.fixedPoints H (G ⧸ H),
          if Abelianization.of
              ⟨q.1.out⁻¹ * h * q.1.out,
                MonGSet.sectionConj_mem H H h q.1 (q.2 h)⟩ ∈ K then
            ((l (Abelianization.of
              ⟨q.1.out⁻¹ * h * q.1.out,
                MonGSet.sectionConj_mem H H h q.1 (q.2 h)⟩) : ℂˣ) : ℂ)
          else 0 := by
  classical
  rw [species_extensionOrbitElt, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  let y : Abelianization H := Abelianization.of
    ⟨q.1.out⁻¹ * h * q.1.out,
      MonGSet.sectionConj_mem H H h q.1 (q.2 h)⟩
  rw [sum_character_coset_apply K l y]
  by_cases hy : y ∈ K
  · simp [hy, y]
  · simp [hy, y]

/-- Bucket a finite odd collection of nontrivial `p`-th roots by their
exponents.  The resulting integral coefficient vector has zero constant
coefficient and odd total mass. -/
theorem exists_odd_cyclotomic_coefficients
    {Q : Type*} [Fintype Q] {p : ℕ} (hp : p.Prime)
    {zeta : ℂ} (f : Q → ℂ) (hQ : Odd (Fintype.card Q))
    (hf : ∀ q : Q, ∃ i : Fin p, i ≠ ⟨0, hp.pos⟩ ∧ f q = zeta ^ i.val) :
    ∃ b : Fin p → ℤ,
      b ⟨0, hp.pos⟩ = 0 ∧ Odd (∑ i, b i) ∧
        ∑ q, f q = ∑ i, (b i : ℂ) * zeta ^ i.val := by
  classical
  let idx : Q → Fin p := fun q => (hf q).choose
  have hidx_ne : ∀ q, idx q ≠ ⟨0, hp.pos⟩ := fun q => (hf q).choose_spec.1
  have hfidx : ∀ q, f q = zeta ^ (idx q).val := fun q => (hf q).choose_spec.2
  let b : Fin p → ℤ := fun i =>
    (Finset.univ.filter (fun q => idx q = i)).card
  have hb0 : b ⟨0, hp.pos⟩ = 0 := by
    simp only [b, Nat.cast_eq_zero]
    rw [Finset.card_eq_zero]
    apply Finset.filter_eq_empty_iff.mpr
    intro q hq
    exact hidx_ne q
  have hcard : ∑ i, (Finset.univ.filter (fun q => idx q = i)).card =
      Fintype.card Q := by
    exact (Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset Q)) (t := (Finset.univ : Finset (Fin p)))
      (fun _ _ => Finset.mem_univ _)).symm
  have hbsum : ∑ i, b i = (Fintype.card Q : ℤ) := by
    change (∑ i, ((Finset.univ.filter (fun q => idx q = i)).card : ℤ)) = _
    exact_mod_cast hcard
  refine ⟨b, hb0, ?_, ?_⟩
  · rw [hbsum]
    exact_mod_cast hQ
  · calc
      ∑ q, f q = ∑ q, zeta ^ (idx q).val :=
        Finset.sum_congr rfl (fun q _ => hfidx q)
      _ = ∑ q, ∑ i : Fin p,
          if i = idx q then zeta ^ i.val else 0 := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [Finset.sum_ite_eq' Finset.univ (idx q)]
        simp
      _ = ∑ i : Fin p, ∑ q : Q,
          if i = idx q then zeta ^ i.val else 0 := Finset.sum_comm
      _ = ∑ i, (b i : ℂ) * zeta ^ i.val := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [b, Int.cast_natCast]
        rw [← Finset.sum_filter]
        simp [Finset.sum_const, nsmul_eq_mul, eq_comm]

/-- Conjugation by `N_G(H)` descends functorially to automorphisms of
`H/H'`. -/
noncomputable def abelianizationNormalizerMonoidHom
    {G : Type u} [Group G] (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) →* MulAut (Abelianization H) where
  toFun n := (H.normalizerMonoidHom n).abelianizationCongr
  map_one' := by
    ext x
    obtain ⟨x⟩ := x
    simp
  map_mul' n m := by
    ext x
    obtain ⟨x⟩ := x
    simp

/-- The normalizer action on subsets of the abelianization, by direct image
under the descended automorphism. -/
@[reducible] noncomputable def normalizerAbelianizationSetAction
    {G : Type u} [Group G] (H : Subgroup G) :
    MulAction (Subgroup.normalizer (H : Set G))
      (Set (Abelianization H)) := by
  let rho := abelianizationNormalizerMonoidHom H
  exact {
    smul n S := rho n '' S
    one_smul S := by
      ext x
      constructor
      · rintro ⟨y, hy, hxy⟩
        have hone : rho 1 = 1 := map_one rho
        rw [hone] at hxy
        simpa using hxy ▸ hy
      · intro hx
        refine ⟨x, hx, ?_⟩
        rw [map_one]
        rfl
    mul_smul n m S := by
      ext x
      constructor
      · rintro ⟨y, hy, hxy⟩
        refine ⟨rho m y, ⟨y, hy, rfl⟩, ?_⟩
        rw [map_mul] at hxy
        exact hxy
      · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
        refine ⟨y, hy, ?_⟩
        rw [map_mul]
        rfl }

/-- Stabilizer in `N_G(H)` of the cyclic fibre subgroup generated by
`hH'`. -/
noncomputable def fibreStabilizer
    {G : Type u} [Group G] (H : Subgroup G) (h : H) :
    Subgroup (Subgroup.normalizer (H : Set G)) := by
  letI := normalizerAbelianizationSetAction H
  exact MulAction.stabilizer (Subgroup.normalizer (H : Set G))
    (Subgroup.zpowers (Abelianization.of h) : Set (Abelianization H))

/-- Membership in the fibre stabilizer is detected on the chosen generator
of the cyclic fibre. -/
theorem mem_fibreStabilizer_iff
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) (h : H)
    (n : Subgroup.normalizer (H : Set G)) :
    n ∈ fibreStabilizer H h ↔
      abelianizationNormalizerMonoidHom H n (Abelianization.of h) ∈
        Subgroup.zpowers (Abelianization.of h) := by
  let rho := abelianizationNormalizerMonoidHom H
  let K := Subgroup.zpowers (Abelianization.of h)
  letI := normalizerAbelianizationSetAction H
  change (rho n '' (K : Set (Abelianization H)) = (K : Set (Abelianization H))) ↔
    rho n (Abelianization.of h) ∈ K
  constructor
  · intro hset
    have haK : Abelianization.of h ∈ K := by
      exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
    have himg : rho n (Abelianization.of h) ∈
        rho n '' (K : Set (Abelianization H)) :=
      ⟨Abelianization.of h, haK, rfl⟩
    rwa [hset] at himg
  · intro hgen
    have hle : K.map (rho n).toMonoidHom ≤ K := by
      rw [MonoidHom.map_zpowers]
      exact Subgroup.zpowers_le.mpr hgen
    have hcard : Nat.card K ≤ Nat.card (K.map (rho n).toMonoidHom) := by
      exact le_of_eq (Subgroup.card_map_of_injective
        (K := K) (f := (rho n).toMonoidHom) (rho n).injective).symm
    have heq : K.map (rho n).toMonoidHom = K :=
      Subgroup.eq_of_le_of_card_ge hle hcard
    ext x
    change x ∈ K.map (rho n).toMonoidHom ↔ x ∈ K
    rw [heq]

/-- Inner conjugations act trivially on `H/H'`, so the canonical copy of
`H` in its normalizer lies in the fibre stabilizer. -/
theorem subgroupOf_le_fibreStabilizer
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) (h : H) :
    H.comap (Subgroup.normalizer (H : Set G)).subtype ≤
      fibreStabilizer H h := by
  intro n hn
  rw [mem_fibreStabilizer_iff]
  let k : H := ⟨n, hn⟩
  have heq : abelianizationNormalizerMonoidHom H n
      (Abelianization.of h) = Abelianization.of h := by
    change Abelianization.of
      ⟨(n : G) * h * (n : G)⁻¹, _⟩ = Abelianization.of h
    change Abelianization.of (k * h * k⁻¹) = Abelianization.of h
    rw [map_mul, map_mul, map_inv]
    rw [mul_comm (Abelianization.of k) (Abelianization.of h),
      mul_assoc, mul_inv_cancel, mul_one]
  rw [heq]
  exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩

/-- The annihilator of a subgroup of a finite odd-order abelian group has
odd cardinality. -/
theorem odd_card_restrictionKernel
    {A : Type u} [CommGroup A] [Finite A] (hA : Odd (Nat.card A))
    (K : Subgroup A) :
    Odd (Nat.card (MonoidHom.restrictHom K ℂˣ).ker) := by
  letI : NeZero (Monoid.exponent A) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  rw [CommGroup.card_restrictHom_ker (M := ℂ) K]
  exact hA.of_dvd_nat (Subgroup.card_quotient_dvd_card K)

/-- The quotient of the fibre stabilizer by the inner copy of `H` has odd
cardinality in an odd-order ambient group. -/
theorem odd_card_fibreStabilizer_quotient
    {G : Type u} [Group G] [Finite G] (hG : Odd (Nat.card G))
    (H : Subgroup G) (h : H) :
    Odd (Nat.card (fibreStabilizer H h ⧸
      (H.comap (Subgroup.normalizer (H : Set G)).subtype).comap
        (fibreStabilizer H h).subtype)) := by
  have hS : Odd (Nat.card (fibreStabilizer H h)) :=
    odd_card_subgroup (odd_card_subgroup hG (Subgroup.normalizer (H : Set G)))
      (fibreStabilizer H h)
  exact hS.of_dvd_nat (Subgroup.card_quotient_dvd_card _)

/-- If a character is primitive of prime order on one generator of a finite
cyclic subgroup, it is primitive of the same order on every other generator
of that subgroup. -/
theorem primitive_character_on_cyclic_generator
    {A : Type u} [CommGroup A] [Finite A] (a y : A)
    (l : A →* ℂˣ) {p : ℕ} (hp : p.Prime)
    (ha : IsPrimitiveRoot (((l a : ℂˣ) : ℂ)) p)
    (hy : y ∈ Subgroup.zpowers a) (hord : orderOf y = orderOf a) :
    IsPrimitiveRoot (((l y : ℂˣ) : ℂ)) p := by
  have hle : Subgroup.zpowers y ≤ Subgroup.zpowers a :=
    Subgroup.zpowers_le.mpr hy
  have hcard : Nat.card (Subgroup.zpowers a) ≤
      Nat.card (Subgroup.zpowers y) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hord]
  have heq : Subgroup.zpowers y = Subgroup.zpowers a :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  have hay : a ∈ Subgroup.zpowers y := by
    rw [heq]
    exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hy
  obtain ⟨w, hw⟩ := Subgroup.mem_zpowers_iff.mp hay
  have hly_mem : l y ∈ Subgroup.zpowers (l a) := by
    refine Subgroup.mem_zpowers_iff.mpr ⟨z, ?_⟩
    rw [← map_zpow]
    exact congrArg l hz
  have hla_order : orderOf (l a) = p := by
    have hcorder : orderOf (((l a : ℂˣ) : ℂ)) = p :=
      IsPrimitiveRoot.iff_orderOf.mp ha
    rwa [orderOf_units] at hcorder
  have horder_dvd : orderOf (l y) ∣ p := by
    rw [← hla_order]
    exact orderOf_dvd_of_mem_zpowers hly_mem
  have hly_ne : l y ≠ 1 := by
    intro hly
    have hla : l a = 1 := by
      rw [← hw, map_zpow, hly, one_zpow]
    have hlaC : (((l a : ℂˣ) : ℂ)) = 1 := congrArg Units.val hla
    exact (ha.ne_one hp.one_lt) hlaC
  have horder : orderOf (l y) = p := by
    rcases (Nat.dvd_prime hp).mp horder_dvd with hone | hp'
    · exact False.elim (hly_ne (orderOf_eq_one_iff.mp hone))
    · exact hp'
  rw [IsPrimitiveRoot.iff_orderOf, orderOf_units, horder]

/-- Cosets of `H` in the normalizer whose representatives stabilize the
cyclic fibre are canonically the quotient of the fibre stabilizer by `H`. -/
noncomputable def fibreQuotientEquiv
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) (h : H) :
    {q : Subgroup.normalizer (H : Set G) ⧸
        H.comap (Subgroup.normalizer (H : Set G)).subtype //
      q.out ∈ fibreStabilizer H h} ≃
      fibreStabilizer H h ⧸
        (H.comap (Subgroup.normalizer (H : Set G)).subtype).comap
          (fibreStabilizer H h).subtype := by
  let N := Subgroup.normalizer (H : Set G)
  let K0 := H.comap N.subtype
  let S := fibreStabilizer H h
  apply @Equiv.subtypeQuotientEquivQuotientSubtype N (fun n => n ∈ S)
    (QuotientGroup.leftRel K0)
    (QuotientGroup.leftRel (K0.comap S.subtype))
    (fun q => q.out ∈ S)
  · intro n
    have hd : ((n : N ⧸ K0).out)⁻¹ * n ∈ K0 :=
      QuotientGroup.eq.mp (QuotientGroup.out_eq' (n : N ⧸ K0))
    have hdS : ((n : N ⧸ K0).out)⁻¹ * n ∈ S :=
      subgroupOf_le_fibreStabilizer H h hd
    constructor
    · intro hn
      have hm := S.mul_mem hn (S.inv_mem hdS)
      have heq : n * (((n : N ⧸ K0).out)⁻¹ * n)⁻¹ =
          (n : N ⧸ K0).out := by group
      rwa [heq] at hm
    · intro hout
      have hm := S.mul_mem hout hdS
      have heq : (n : N ⧸ K0).out *
          (((n : N ⧸ K0).out)⁻¹ * n) = n := by group
      rwa [heq] at hm
  · intro x y
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    rfl

/-- Under the standard fixed-coset/normalizer-quotient equivalence, the
surviving cyclic-fibre condition is precisely membership in the fibre
stabilizer. -/
theorem fixedCoset_fibre_mem_iff
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) (h : H)
    (q : MulAction.fixedPoints H (G ⧸ H)) :
    Abelianization.of
        ⟨q.1.out⁻¹ * h * q.1.out,
          MonGSet.sectionConj_mem H H h q.1 (q.2 h)⟩ ∈
        Subgroup.zpowers (Abelianization.of h) ↔
      (Sylow.fixedPointsMulLeftCosetsEquivQuotient H q).out ∈
        fibreStabilizer H h := by
  letI := Fintype.ofFinite G
  let N := Subgroup.normalizer (H : Set G)
  let K0 := H.comap N.subtype
  have hgN : q.1.out ∈ N := by
    apply (Sylow.mem_fixedPoints_mul_left_cosets_iff_mem_normalizer).mp
    simpa only [QuotientGroup.out_eq' q.1] using q.2
  let n : N := ⟨q.1.out, hgN⟩
  have hclass : Sylow.fixedPointsMulLeftCosetsEquivQuotient H q =
      (n : N ⧸ K0) := by
    apply (Sylow.fixedPointsMulLeftCosetsEquivQuotient H).symm.injective
    rw [(Sylow.fixedPointsMulLeftCosetsEquivQuotient H).symm_apply_apply]
    apply Subtype.ext
    exact (QuotientGroup.out_eq' q.1).symm
  have hout : (Sylow.fixedPointsMulLeftCosetsEquivQuotient H q).out ∈
      fibreStabilizer H h ↔ n ∈ fibreStabilizer H h := by
    have hd : ((Sylow.fixedPointsMulLeftCosetsEquivQuotient H q).out)⁻¹ * n ∈ K0 := by
      apply QuotientGroup.eq.mp
      rw [QuotientGroup.out_eq', hclass]
    have hdS := subgroupOf_le_fibreStabilizer H h hd
    constructor
    · intro ho
      have hm := (fibreStabilizer H h).mul_mem ho hdS
      convert hm using 1
      all_goals group
    · intro hn
      have hm := (fibreStabilizer H h).mul_mem hn
        ((fibreStabilizer H h).inv_mem hdS)
      convert hm using 1
      all_goals group
  rw [hout, ← (fibreStabilizer H h).inv_mem_iff,
    mem_fibreStabilizer_iff]
  change Abelianization.of
      ⟨q.1.out⁻¹ * h * q.1.out,
        MonGSet.sectionConj_mem H H h q.1 (q.2 h)⟩ ∈
        Subgroup.zpowers (Abelianization.of h) ↔
    Abelianization.of ((H.normalizerMonoidHom n⁻¹) h) ∈
      Subgroup.zpowers (Abelianization.of h)
  have hel : (⟨q.1.out⁻¹ * h * q.1.out,
      MonGSet.sectionConj_mem H H h q.1 (q.2 h)⟩ : H) =
      (H.normalizerMonoidHom n⁻¹) h := by
    apply Subtype.ext
    change q.1.out⁻¹ * (h : G) * q.1.out =
      (n⁻¹ : G) * h * (n⁻¹ : G)⁻¹
    simp [n]
  rw [hel]

/-- Fixed cosets which survive character orthogonality for the cyclic
subgroup generated by the chosen fibre. -/
def FibreFixedCosets
    {G : Type u} [Group G] [Fintype G] (H : Subgroup G) (h : H) :=
  {q : MulAction.fixedPoints H (G ⧸ H) //
    Abelianization.of
      ⟨q.1.out⁻¹ * h * q.1.out,
        MonGSet.sectionConj_mem H H h q.1 (q.2 h)⟩ ∈
      Subgroup.zpowers (Abelianization.of h)}

/-- The surviving fixed cosets are exactly the fibre-stabilizer quotient. -/
noncomputable def fibreFixedCosetsEquiv
    {G : Type u} [Group G] [Fintype G] (H : Subgroup G) (h : H) :
    FibreFixedCosets H h ≃
      fibreStabilizer H h ⧸
        (H.comap (Subgroup.normalizer (H : Set G)).subtype).comap
          (fibreStabilizer H h).subtype :=
  (Equiv.subtypeEquiv
    (Sylow.fixedPointsMulLeftCosetsEquivQuotient H)
    (fixedCoset_fibre_mem_iff H h)).trans
      (fibreQuotientEquiv H h)

noncomputable instance fibreFixedCosetsFintype
    {G : Type u} [Group G] [Fintype G] (H : Subgroup G) (h : H) :
    Fintype (FibreFixedCosets H h) := by
  classical
  unfold FibreFixedCosets
  infer_instance

/-- In odd order, the collection of surviving fixed cosets has odd size. -/
theorem odd_card_fibreFixedCosets
    {G : Type u} [Group G] [Fintype G] (hG : Odd (Fintype.card G))
    (H : Subgroup G) (h : H) :
    Odd (Nat.card (FibreFixedCosets H h)) := by
  rw [Nat.card_congr (fibreFixedCosetsEquiv H h)]
  exact odd_card_fibreStabilizer_quotient (by simpa using hG) H h

theorem odd_fintypeCard_fibreFixedCosets
    {G : Type u} [Group G] [Fintype G] (hG : Odd (Fintype.card G))
    (H : Subgroup G) (h : H) :
    Odd (Fintype.card (FibreFixedCosets H h)) := by
  rw [← Nat.card_eq_fintype_card]
  exact odd_card_fibreFixedCosets hG H h

/-- Every surviving conjugate generates the same cyclic subgroup of the
abelianization as the original fibre. -/
theorem orderOf_fibreFixedCoset
    {G : Type u} [Group G] [Fintype G] (H : Subgroup G) (h : H)
    (q : FibreFixedCosets H h) :
    orderOf (Abelianization.of
      (⟨q.1.1.out⁻¹ * h * q.1.1.out,
        MonGSet.sectionConj_mem H H h q.1.1 (q.1.2 h)⟩ : H)) =
      orderOf (Abelianization.of h) := by
  let N := Subgroup.normalizer (H : Set G)
  have hgN : q.1.1.out ∈ N := by
    apply (Sylow.mem_fixedPoints_mul_left_cosets_iff_mem_normalizer).mp
    simpa only [QuotientGroup.out_eq' q.1.1] using q.1.2
  let n : N := ⟨q.1.1.out, hgN⟩
  have hel : (⟨q.1.1.out⁻¹ * h * q.1.1.out,
      MonGSet.sectionConj_mem H H h q.1.1 (q.1.2 h)⟩ : H) =
      (H.normalizerMonoidHom n⁻¹) h := by
    apply Subtype.ext
    change q.1.1.out⁻¹ * (h : G) * q.1.1.out =
      (n⁻¹ : G) * h * (n⁻¹ : G)⁻¹
    simp [n]
  rw [hel]
  change orderOf ((abelianizationNormalizerMonoidHom H n⁻¹)
    (Abelianization.of h)) = orderOf (Abelianization.of h)
  exact MulEquiv.orderOf_eq (abelianizationNormalizerMonoidHom H n⁻¹) _

private theorem sum_ite_eq_sum_subtype
    {A M : Type*} [Fintype A] [AddCommMonoid M]
    (p : A → Prop) [DecidablePred p] (f : A → M) :
    (∑ a, if p a then f a else 0) = ∑ a : {a // p a}, f a := by
  rw [← Finset.sum_filter]
  simpa using Eq.symm
    (Finset.sum_subtype_eq_sum_filter (p := p)
      (s := (Finset.univ : Finset A)) f)

/-- Orthogonality collapse rewritten as a sum over precisely the surviving
fixed cosets. -/
theorem species_extensionOrbitElt_collapse_subtype
    {G : Type u} [Group G] [Fintype G] (H : Subgroup G) (h : H)
    (l : Abelianization H →* ℂˣ) :
    DRing.species H h
        (extensionOrbitElt H (Subgroup.zpowers (Abelianization.of h)) l) =
      (Nat.card (MonoidHom.restrictHom
        (Subgroup.zpowers (Abelianization.of h)) ℂˣ).ker : ℂ) *
        ∑ q : FibreFixedCosets H h,
          ((l (Abelianization.of
            (⟨q.1.1.out⁻¹ * h * q.1.1.out,
              MonGSet.sectionConj_mem H H h q.1.1 (q.1.2 h)⟩ : H)) : ℂˣ) : ℂ) := by
  classical
  rw [species_extensionOrbitElt_collapse]
  congr 1
  exact sum_ite_eq_sum_subtype _ _

/-- Values of a character which is primitive on the chosen fibre are
nontrivial `p`-th powers of one fixed primitive root on every survivor. -/
theorem fibreFixedCoset_value_is_nontrivial_power
    {G : Type u} [Group G] [Fintype G] (H : Subgroup G) (h : H)
    {p : ℕ} (hp : p.Prime) (l : Abelianization H →* ℂˣ)
    {zeta : ℂ} (hzeta : IsPrimitiveRoot zeta p)
    (hl : IsPrimitiveRoot (((l (Abelianization.of h) : ℂˣ) : ℂ)) p)
    (q : FibreFixedCosets H h) :
    ∃ i : Fin p, i ≠ ⟨0, hp.pos⟩ ∧
      (((l (Abelianization.of
        (⟨q.1.1.out⁻¹ * h * q.1.1.out,
          MonGSet.sectionConj_mem H H h q.1.1 (q.1.2 h)⟩ : H)) : ℂˣ) : ℂ)) =
        zeta ^ i.val := by
  let y : Abelianization H := Abelianization.of
    (⟨q.1.1.out⁻¹ * h * q.1.1.out,
      MonGSet.sectionConj_mem H H h q.1.1 (q.1.2 h)⟩ : H)
  have hyprim : IsPrimitiveRoot (((l y : ℂˣ) : ℂ)) p :=
    primitive_character_on_cyclic_generator (Abelianization.of h) y l hp hl
      q.2 (orderOf_fibreFixedCoset H h q)
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, hi, hiz⟩ := hzeta.eq_pow_of_pow_eq_one hyprim.pow_eq_one
  let j : Fin p := ⟨i, hi⟩
  refine ⟨j, ?_, ?_⟩
  · intro hj
    have hi0 : i = 0 := congrArg Fin.val hj
    have hvalue : (((l y : ℂˣ) : ℂ)) = 1 := by
      rw [← hiz, hi0, pow_zero]
    exact (hyprim.ne_one hp.one_lt) hvalue
  · exact hiz.symm

def NontrivialSpeciesNotIntegerValued
    (G : Type u) [Group G] [Fintype G] : Prop :=
  ∀ (H : Subgroup G) (h : H), ¬ IsTrivialFibre h →
    ¬ IsIntegerValued (DRing.species H h)

/-- Spectrum classification plus Satz 2.5.3 identifies the intrinsic
integer-valued locus with the trivial-fibre species. -/
theorem allIntegerPointsAreMarks_of_spectrum_of_nontrivial
    {G : Type u} [Group G] [Fintype G]
    (hspectrum : EveryComplexPointIsSpecies G)
    (hnontrivial : NontrivialSpeciesNotIntegerValued G) :
    AllIntegerPointsAreMarks G := by
  intro s hs
  obtain ⟨H, h, rfl⟩ := hspectrum s
  have hh : IsTrivialFibre h := by
    by_contra hnon
    exact hnontrivial H h hnon hs
  exact ⟨H, species_eq_one_of_trivialFibre H h hh⟩

/-- **Cyclotomic parity lemma.** Let `p` be an odd prime and `zeta` a
primitive `p`-th root.  An integral combination of the nonconstant powers
of `zeta` whose coefficient sum is odd cannot be an integer.

This is the exact final contradiction in Müller's proof of Satz 2.5.3. -/
theorem cyclotomic_sum_not_integer_of_odd
    {K : Type*} [Field K] [CharZero K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {zeta : K} (hzeta : IsPrimitiveRoot zeta p)
    (b : Fin p → ℤ) (hb0 : b ⟨0, hp.pos⟩ = 0) (hbodd : Odd (∑ i, b i)) :
    ¬ ∃ z : ℤ, ∑ i, (b i : K) * zeta ^ i.val = (z : K) := by
  rintro ⟨z, hz⟩
  let i0 : Fin p := ⟨0, hp.pos⟩
  let a : Fin p → ℤ := fun i => if i = i0 then -z else b i
  have haeval : ∑ i, (a i : K) * zeta ^ i.val = 0 := by
    rw [← Finset.sum_erase_add Finset.univ
      (fun i => (a i : K) * zeta ^ i.val) (by simp : i0 ∈ Finset.univ)]
    simp only [a, if_pos, i0, pow_zero, mul_one, Int.cast_neg]
    have hz' : ∑ i ∈ Finset.univ.erase i0, (b i : K) * zeta ^ i.val = (z : K) := by
      have hzsplit := hz
      rw [← Finset.sum_erase_add Finset.univ
        (fun i => (b i : K) * zeta ^ i.val) (by simp : i0 ∈ Finset.univ)] at hzsplit
      simpa [i0, hb0] using hzsplit
    have heq : (∑ i ∈ Finset.univ.erase i0, (a i : K) * zeta ^ i.val) =
        ∑ i ∈ Finset.univ.erase i0, (b i : K) * zeta ^ i.val := by
      refine Finset.sum_congr rfl fun i hi => ?_
      simp [a, Finset.ne_of_mem_erase hi]
    rw [heq, hz']
    simp
  have hall : ∀ i j, a i = a j :=
    (hzeta.sum_eq_zero_iff_forall_eq_int hp a).mp haeval
  have hbval : ∀ i : Fin p, i ≠ i0 → b i = -z := by
    intro i hi
    simpa [a, hi] using hall i i0
  have hsum : ∑ i, b i = (p - 1 : ℕ) * (-z) := by
    rw [← Finset.sum_erase_add Finset.univ b (by simp : i0 ∈ Finset.univ), show b i0 = 0 by
      simpa [i0] using hb0,
      add_zero, Finset.sum_congr rfl (fun i hi => hbval i (Finset.ne_of_mem_erase hi)),
      Finset.sum_const, Finset.card_erase_of_mem (by simp), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  obtain ⟨q, hq⟩ := hp.odd_of_ne_two hp2
  have hpminus : p - 1 = 2 * q := by omega
  have heven : Even (∑ i, b i) := by
    refine ⟨(q : ℤ) * (-z), ?_⟩
    rw [hsum, hpminus]
    push_cast
    ring
  exact (Int.not_even_iff_odd.mpr hbodd) heven

/-- A single odd cyclotomic orbit-sum value witnesses failure of
integer-valuedness.  This is the interface between the group/character
construction in Satz 2.5.3 and its cyclotomic parity conclusion. -/
theorem not_integerValued_of_odd_cyclotomic_value
    {R : Type*} [Ring R] (s : R →+* ℂ) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {zeta : ℂ} (hzeta : IsPrimitiveRoot zeta p)
    (b : Fin p → ℤ) (hb0 : b ⟨0, hp.pos⟩ = 0)
    (hbodd : Odd (∑ i, b i)) (x : R)
    (hx : s x = ∑ i, (b i : ℂ) * zeta ^ i.val) :
    ¬ IsIntegerValued s := by
  intro hs
  obtain ⟨z, hz⟩ := hs x
  apply cyclotomic_sum_not_integer_of_odd hp hp2 hzeta b hb0 hbodd
  exact ⟨z, hx.symm.trans hz⟩

/-- **Müller, Satz 2.5.3.** For a finite group of odd order, every species
on a nontrivial fibre takes a nonintegral value on an explicit integral
D-ring element. -/
theorem nontrivialSpeciesNotIntegerValued_of_odd
    {G : Type u} [Group G] [Fintype G] (hG : Odd (Fintype.card G)) :
    NontrivialSpeciesNotIntegerValued G := by
  intro H h hh
  have hGnat : Odd (Nat.card G) := by simpa using hG
  obtain ⟨p, hp, hp2, hpord⟩ :=
    exists_odd_prime_dvd_fibre_order hGnat h hh
  obtain ⟨chi, hchi⟩ :=
    exists_primitive_character_on_fibre_prime_part h hp hpord
  let a : Abelianization H := Abelianization.of h
  let d : ℕ := orderOf a / p
  let l : Abelianization H →* ℂˣ := chi ^ d
  let zeta : ℂ := (((chi (a ^ d) : ℂˣ) : ℂ))
  have hzeta : IsPrimitiveRoot zeta p := by
    simpa [a, d, zeta] using hchi
  have hl : IsPrimitiveRoot (((l a : ℂˣ) : ℂ)) p := by
    simpa [l, zeta, map_pow] using hzeta
  let f : FibreFixedCosets H h → ℂ := fun q =>
    ((l (Abelianization.of
      (⟨q.1.1.out⁻¹ * h * q.1.1.out,
        MonGSet.sectionConj_mem H H h q.1.1 (q.1.2 h)⟩ : H)) : ℂˣ) : ℂ)
  have hf : ∀ q : FibreFixedCosets H h,
      ∃ i : Fin p, i ≠ ⟨0, hp.pos⟩ ∧ f q = zeta ^ i.val := by
    intro q
    exact fibreFixedCoset_value_is_nontrivial_power H h hp l hzeta
      (by simpa [a] using hl) q
  obtain ⟨b, hb0, hbodd, hbval⟩ :=
    exists_odd_cyclotomic_coefficients hp f
      (odd_fintypeCard_fibreFixedCosets hG H h) hf
  let K := Subgroup.zpowers a
  let c : ℕ := Nat.card (MonoidHom.restrictHom K ℂˣ).ker
  let b' : Fin p → ℤ := fun i => (c : ℤ) * b i
  have hcodd : Odd c := by
    exact odd_card_restrictionKernel
      (odd_card_abelianization (odd_card_subgroup hGnat H)) K
  have hb0' : b' ⟨0, hp.pos⟩ = 0 := by simp [b', hb0]
  have hbsum : ∑ i, b' i = (c : ℤ) * ∑ i, b i := by
    simp [b', Finset.mul_sum]
  have hbodd' : Odd (∑ i, b' i) := by
    rw [hbsum]
    exact (by exact_mod_cast hcodd : Odd (c : ℤ)).mul hbodd
  let x : DRing G := extensionOrbitElt H K l
  have hx : DRing.species H h x =
      ∑ i, (b' i : ℂ) * zeta ^ i.val := by
    dsimp only [x]
    rw [show K = Subgroup.zpowers (Abelianization.of h) by rfl,
      species_extensionOrbitElt_collapse_subtype]
    change (c : ℂ) * ∑ q, f q = _
    rw [hbval, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [b', mul_assoc]
  exact not_integerValued_of_odd_cyclotomic_value
    (DRing.species H h) hp hp2 hzeta b' hb0' hbodd' x hx

/-- If the integer-valued complex points are exactly mark species, their
common kernel is exactly the kernel of `forget : D(G) → B(G)`. -/
theorem integerKernel_iff_forget_eq_zero
    {G : Type u} [Group G] [Fintype G]
    (hpoints : AllIntegerPointsAreMarks G) (x : DRing G) :
    IntegerKernel x ↔ MonRing.forget x = 0 := by
  constructor
  · intro hx
    apply BurnsideRing.mark_injective
    funext H
    have hs0 := hx (DRing.species H 1) (species_one_isIntegerValued H)
    have hs := DFunLike.congr_fun (DRing.species_one_eq_mark_forget H) x
    simp only [RingHom.coe_comp, Function.comp_apply] at hs
    change BurnsideRing.mark H (MonRing.forget x) = BurnsideRing.mark H 0
    rw [map_zero]
    have hc : ((BurnsideRing.mark H (MonRing.forget x) : ℤ) : ℂ) = 0 :=
      hs.symm.trans hs0
    exact_mod_cast hc
  · intro hforget s hs
    obtain ⟨H, rfl⟩ := hpoints s hs
    have hmark := DFunLike.congr_fun (DRing.species_one_eq_mark_forget H) x
    simp only [RingHom.coe_comp, Function.comp_apply] at hmark
    rw [hforget, map_zero, map_zero] at hmark
    exact hmark

/-- **Kernel form of Müller's transport lemma.**  If a D-ring equivalence
preserves the kernel of the canonical projection `forget : D → B` in both
directions, then `forget ∘ Phi ∘ eta` is a Burnside-ring equivalence.

The odd-order argument will supply the kernel hypotheses intrinsically:
`ker(forget)` is the common kernel of all integer-valued complex points. -/
noncomputable def burnsideEquivOfKerForget
    {G : Type u} {G' : Type v} [Group G] [Fintype G]
    [Group G'] [Fintype G'] (Phi : DRing G ≃+* DRing G')
    (hfwd : ∀ x : DRing G, MonRing.forget x = 0 →
      MonRing.forget (Phi x) = 0)
    (hbwd : ∀ y : DRing G', MonRing.forget y = 0 →
      MonRing.forget (Phi.symm y) = 0) :
    BurnsideRing G ≃+* BurnsideRing G' := by
  let f : BurnsideRing G →+* BurnsideRing G' :=
    (MonRing.forget.comp Phi.toRingHom).comp MonRing.eta
  let g : BurnsideRing G' →+* BurnsideRing G :=
    (MonRing.forget.comp Phi.symm.toRingHom).comp MonRing.eta
  refine RingEquiv.ofRingHom f g ?_ ?_
  · ext b
    let x : DRing G := Phi.symm (MonRing.eta b)
    have hker : MonRing.forget (MonRing.eta (MonRing.forget x) - x) = 0 := by
      simp
    have hforw := hfwd _ hker
    have hx : Phi x = MonRing.eta b := Phi.apply_symm_apply _
    change MonRing.forget (Phi (MonRing.eta (MonRing.forget x))) = b
    simp only [map_sub] at hforw
    rw [sub_eq_zero] at hforw
    rw [hforw, hx, MonRing.forget_eta]
  · ext b
    let y : DRing G' := Phi (MonRing.eta b)
    have hker : MonRing.forget (MonRing.eta (MonRing.forget y) - y) = 0 := by
      simp
    have hback := hbwd _ hker
    have hy : Phi.symm y = MonRing.eta b := Phi.symm_apply_apply _
    change MonRing.forget (Phi.symm (MonRing.eta (MonRing.forget y))) = b
    simp only [map_sub] at hback
    rw [sub_eq_zero] at hback
    rw [hback, hy, MonRing.forget_eta]

/-- Once the odd-order spectrum theorem identifies all integer-valued points
with mark species, an arbitrary D-ring equivalence induces a Burnside-ring
equivalence.  This packages the final ring-theoretic step of Satz 2.5.4. -/
noncomputable def burnsideEquivOfAllIntegerPointsAreMarks
    {G : Type u} {G' : Type v} [Group G] [Fintype G]
    [Group G'] [Fintype G'] (Phi : DRing G ≃+* DRing G')
    (hG : AllIntegerPointsAreMarks G)
    (hG' : AllIntegerPointsAreMarks G') :
    BurnsideRing G ≃+* BurnsideRing G' :=
  burnsideEquivOfKerForget Phi
    (fun x hx =>
      (integerKernel_iff_forget_eq_zero hG' (Phi x)).mp
        ((integerKernel_equiv_iff Phi x).mpr
          ((integerKernel_iff_forget_eq_zero hG x).mpr hx)))
    (fun y hy =>
      (integerKernel_iff_forget_eq_zero hG (Phi.symm y)).mp
        ((integerKernel_equiv_iff Phi.symm y).mpr
          ((integerKernel_iff_forget_eq_zero hG' y).mpr hy)))

/-- In odd order, the intrinsically integer-valued complex points are
exactly the ordinary mark species. -/
theorem allIntegerPointsAreMarks_of_odd
    {G : Type u} [Group G] [Fintype G] (hG : Odd (Fintype.card G)) :
    AllIntegerPointsAreMarks G :=
  allIntegerPointsAreMarks_of_spectrum_of_nontrivial
    (everyComplexPointIsSpecies G)
    (nontrivialSpeciesNotIntegerValued_of_odd hG)

/-- **Müller's odd-order theorem (Satz 2.5.4 = [Mueller2012] Thm. 2.4).** An arbitrary ring
isomorphism between the monomial representation rings of two finite
odd-order groups canonically induces an isomorphism of their Burnside
rings. -/
noncomputable def burnsideEquivOfOddOrder
    {G : Type u} {G' : Type v} [Group G] [Fintype G]
    [Group G'] [Fintype G'] (Phi : DRing G ≃+* DRing G')
    (hG : Odd (Fintype.card G)) (hG' : Odd (Fintype.card G')) :
    BurnsideRing G ≃+* BurnsideRing G' :=
  burnsideEquivOfAllIntegerPointsAreMarks Phi
    (allIntegerPointsAreMarks_of_odd hG)
    (allIntegerPointsAreMarks_of_odd hG')

/-- If `f > 2`, Euler's totient `φ(f)` cannot divide an odd number.

This is the parity contradiction at the end of the rational-species argument
in Müller's odd-order theorem. -/
theorem not_totient_dvd_of_odd {f n : ℕ} (hf : 2 < f) (hn : Odd n) :
    ¬f.totient ∣ n := by
  intro hdiv
  have htwo_totient : 2 ∣ f.totient := even_iff_two_dvd.mp (Nat.totient_even hf)
  have htwo_n : 2 ∣ n := dvd_trans htwo_totient hdiv
  exact (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr htwo_n)

/-- Equivalently, a totient divisor of an odd number can only come from a
fibre of order at most two. -/
theorem le_two_of_totient_dvd_odd {f n : ℕ} (hn : Odd n)
    (hdiv : f.totient ∣ n) : f ≤ 2 := by
  by_contra hf
  exact not_totient_dvd_of_odd (by omega) hn hdiv

/-- If both the fibre order and its full power-automorphism order divide an
odd number, then the fibre is trivial. The first divisibility eliminates
`f = 2`; the totient divisibility eliminates every `f > 2`. -/
theorem eq_one_of_dvd_odd_of_totient_dvd {f n : ℕ} (hf : 0 < f)
    (hn : Odd n) (hfn : f ∣ n) (hφ : f.totient ∣ n) :
    f = 1 := by
  have hle : f ≤ 2 := le_two_of_totient_dvd_odd hn hφ
  obtain ⟨k, hk⟩ := hn
  obtain ⟨q, hq⟩ := hfn
  have hf_cases : f = 1 ∨ f = 2 := by omega
  rcases hf_cases with rfl | rfl
  · rfl
  · omega

/-- A faithful action of the full power automorphism group `(ZMod f)ˣ`
on a finite group forces `φ(f)` to divide the order of that group. This is
the abstract divisibility statement used when a fibre is fully fused. -/
theorem totient_dvd_card_of_injective {f : ℕ} [NeZero f]
    {Q : Type*} [Group Q] [Finite Q] (ρ : (ZMod f)ˣ →* Q)
    (hρ : Function.Injective ρ) :
    f.totient ∣ Nat.card Q := by
  rw [← ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card]
  exact Subgroup.card_dvd_of_injective ρ hρ

/-- Consequently, the full power automorphism group of a fibre of order
greater than two cannot embed in a finite group of odd order. -/
theorem not_injective_units_to_odd_group {f : ℕ} [NeZero f]
    {Q : Type*} [Group Q] [Finite Q] (hf : 2 < f)
    (hQ : Odd (Nat.card Q)) (ρ : (ZMod f)ˣ →* Q) :
    ¬Function.Injective ρ := by
  intro hρ
  exact not_totient_dvd_of_odd hf hQ (totient_dvd_card_of_injective ρ hρ)

/-- Quotient form of `totient_dvd_card_of_injective`: if a finite group
surjects onto all power automorphisms of a fibre of order `f`, then `φ(f)`
divides its order. This is the form supplied by a fully fused normalizer
action. -/
theorem totient_dvd_card_of_surjective {f : ℕ} [NeZero f]
    {Q : Type*} [Group Q] [Finite Q] (ρ : Q →* (ZMod f)ˣ)
    (hρ : Function.Surjective ρ) :
    f.totient ∣ Nat.card Q := by
  rw [← ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card]
  exact Subgroup.card_dvd_of_surjective ρ hρ

/-- A finite odd-order group cannot have the full power automorphism group
of a fibre of order greater than two as a quotient. -/
theorem not_surjective_odd_group_to_units {f : ℕ} [NeZero f]
    {Q : Type*} [Group Q] [Finite Q] (hf : 2 < f)
    (hQ : Odd (Nat.card Q)) (ρ : Q →* (ZMod f)ˣ) :
    ¬Function.Surjective ρ := by
  intro hρ
  exact not_totient_dvd_of_odd hf hQ (totient_dvd_card_of_surjective ρ hρ)

/-- **Full-fusion parity interface.** Suppose `f` is a fibre order in an
ambient object of odd order `n`. If

* the fibre order divides `n`;
* a finite acting group `Q` has order dividing `n`; and
* the power action of `Q` on the fibre is onto `(ZMod f)ˣ`;

then the fibre is trivial. In the application, `Q` is the image (or an
appropriate quotient) of a normalizer action. -/
theorem fibre_eq_one_of_full_power_action {f n : ℕ} [NeZero f]
    {Q : Type*} [Group Q] [Finite Q] (hn : Odd n)
    (hfn : f ∣ n) (hQn : Nat.card Q ∣ n)
    (ρ : Q →* (ZMod f)ˣ) (hρ : Function.Surjective ρ) :
    f = 1 := by
  have hφQ : f.totient ∣ Nat.card Q :=
    totient_dvd_card_of_surjective ρ hρ
  exact eq_one_of_dvd_odd_of_totient_dvd (NeZero.pos f) hn hfn
    (dvd_trans hφQ hQn)

/-- **Cyclic-fibre form of the full-fusion interface.** A surjective action
of a finite group `Q` on a finite cyclic fibre `C` realizes every
automorphism of `C`. If both `|C|` and `|Q|` divide an odd ambient order,
then `C` is trivial.

This avoids choosing a generator or identifying `C` with `ZMod |C|`; that
identification is supplied internally by `IsCyclic.card_mulAut`. -/
theorem card_cyclic_fibre_eq_one_of_full_action
    {C Q : Type*} [Group C] [Finite C] [IsCyclic C]
    [Group Q] [Finite Q] {n : ℕ} (hn : Odd n)
    (hCn : Nat.card C ∣ n) (hQn : Nat.card Q ∣ n)
    (ρ : Q →* MulAut C) (hρ : Function.Surjective ρ) :
    Nat.card C = 1 := by
  have hAutQ : Nat.card (MulAut C) ∣ Nat.card Q :=
    Subgroup.card_dvd_of_surjective ρ hρ
  have hφQ : (Nat.card C).totient ∣ Nat.card Q := by
    rw [← IsCyclic.card_mulAut C]
    exact hAutQ
  exact eq_one_of_dvd_odd_of_totient_dvd Nat.card_pos hn hCn
    (dvd_trans hφQ hQn)

/-- **Normalizer-fusion parity theorem.** Let `C` be a cyclic subgroup of
a finite group `G` of odd order. If conjugation by the normalizer of `C`
realizes every automorphism of `C`, then `C` is trivial.

This is the group-theoretic parity core of Müller's odd-order argument:
full fusion gives the surjection `N_G(C) → Aut(C)`, while Lagrange gives
both divisibilities into `|G|`. -/
theorem cyclic_subgroup_eq_bot_of_normalizer_action_surjective
    {G : Type*} [Group G] [Finite G] (hG : Odd (Nat.card G))
    (C : Subgroup G) [IsCyclic C]
    (hfull : Function.Surjective C.normalizerMonoidHom) :
    C = ⊥ := by
  have hcard : Nat.card C = 1 :=
    card_cyclic_fibre_eq_one_of_full_action hG
      C.card_subgroup_dvd_card
      (Subgroup.card_subgroup_dvd_card (Subgroup.normalizer (C : Set G)))
      C.normalizerMonoidHom hfull
  exact C.eq_bot_of_card_eq hcard

end OddOrder

end LeanDring
