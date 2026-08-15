/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.Units
import LeanDring.Theory.DRing.FreeBasis
import LeanDring.Theory.DRing.SplitTorsionUnits
import LeanDring.Theory.DRing.BridgeCounts

-- The `[Fintype _]` binders below are unused in several *statements* but are
-- load-bearing in their *proofs* (instance synthesis for cardinality and basis
-- constructions), so they cannot be `omit`ted.  The linter's suggested rewrite
-- to `[Finite _]` + `Fintype.ofFinite` is a genuine refactor, not a cleanup.
set_option linter.unusedFintypeInType false

/-!
# The split-ring structure of `D(G)`: `D(G) = ℤĜ ⊕ I`

Instantiation of Müller's Lemma 2.6.1 for the D-ring (step 1 of
Satz 2.6.3). Main results (sorry-free):

* `basisElt_top_eq_charElt` — the top classes `[G,λ]` are the character
  elements: `basisElt ⊤ m = charElt (m ∘ topHom)`;
* `basisElt_mul_basisElt_mem_smallSpan` — **the grading**: a product with
  a proper factor lies in the ℤ-span of proper classes (census of the
  product monomial `G`-set: all stabilizers sit inside a conjugate of the
  proper factor);
* `topSubring` (`S ≅ ℤĜ`) and `properIdeal` (`I`) with
  `smallSpan_inf_topSpan` and `exists_small_add_top` — the split
  `D(G) = S ⊕ I`;
* `torsion_unit_factorization` — **every torsion unit of `D(G)` factors
  as `u = b(1 + a)`** with `b` a torsion unit of the character subring
  and `a ∈ I` (Müller 2.6.1 applied to `D(G)`).
-/

namespace LeanDring

open MulAction Finset

universe u

namespace DRing

open MonGSet MonRing

variable {G : Type u} [Group G] [Fintype G]

/-! ## Top classes are characters -/

variable (G) in
/-- The tautological isomorphism-hom `G →* ⊤`. -/
def topHom : G →* (⊤ : Subgroup G) where
  toFun g := ⟨g, trivial⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `[⊤, m] = [G, m ∘ topHom]`: top basis classes are character
elements. -/
theorem basisElt_top_eq_charElt (m : (⊤ : Subgroup G) →* ℂˣ) :
    basisElt ⊤ m = charElt (m.comp (topHom G)) := by
  refine congrArg GrothendieckRing.of (Quotient.sound ?_)
  -- explicit iso with gauge `φ(q) = m⟨q.out⟩`
  haveI : Subsingleton (G ⧸ (⊤ : Subgroup G)) :=
    QuotientGroup.subsingleton_quotient_top
  haveI : Subsingleton ((charMon (m.comp (topHom G)) :
      MonGSet G ℂˣ).carrier) := inferInstanceAs (Subsingleton PUnit)
  haveI : Subsingleton ((induced (⊤ : Subgroup G) m :
      MonGSet G ℂˣ).carrier) :=
    inferInstanceAs (Subsingleton (G ⧸ (⊤ : Subgroup G)))
  refine ⟨equivOfSubsingletonOfSubsingleton
    (fun _ => PUnit.unit) (fun _ => (((1 : G) : G ⧸ (⊤ : Subgroup G)))),
    fun q => m ⟨q.out, trivial⟩, ?_, ?_⟩
  · intro g x
    exact Subsingleton.elim _ _
  · intro g q
    -- `weight_charMon g = m⟨g⟩`; `weight_induced g q = m⟨(g•q).out⁻¹ g q.out⟩`
    change (m.comp (topHom G)) g * m ⟨q.out, trivial⟩ =
      m ⟨(g • q).out, trivial⟩ *
        m ⟨(g • q).out⁻¹ * g * q.out, induced_mem ⊤ g q⟩
    have hsplit : (⟨(g • q).out⁻¹ * g * q.out,
        induced_mem (⊤ : Subgroup G) g q⟩ : (⊤ : Subgroup G)) =
        (⟨(g • q).out, trivial⟩ : (⊤ : Subgroup G))⁻¹ *
          ⟨g, trivial⟩ * ⟨q.out, trivial⟩ := rfl
    rw [hsplit, map_mul, map_mul, map_inv]
    change m ⟨g, trivial⟩ * m ⟨q.out, trivial⟩ = _
    group

/-! ## The grading: products with a proper factor are proper -/

/-- Conjugate pairs have subgroups of equal order. -/
theorem card_eq_of_conjPair {K K' : Subgroup G} {l : K →* ℂˣ}
    {l' : K' →* ℂˣ} (h : IsConjPair K K' l l') :
    Nat.card K = Nat.card K' := by
  obtain ⟨a, hmem, -⟩ := h
  have h1 : Nat.card K ≤ Nat.card K' := by
    refine card_le_of_subconj (g := a⁻¹) fun x hx => ?_
    have h2 : a⁻¹⁻¹ * x * a⁻¹ = a * x * a⁻¹ := by rw [inv_inv]
    rw [h2]
    exact (hmem x).mp hx
  have h2 : Nat.card K' ≤ Nat.card K := by
    refine card_le_of_subconj (g := a) fun y hy => ?_
    refine (hmem (a⁻¹ * y * a)).mpr ?_
    have h3 : a * (a⁻¹ * y * a) * a⁻¹ = y := by group
    rw [h3]
    exact hy
  omega

variable (G) in
/-- The generating set of the proper ideal: basis elements at proper
subgroups. -/
def smallSet : Set (DRing G) :=
  {x | ∃ p : (K : Subgroup G) × (K →* ℂˣ),
    Nat.card p.1 < Nat.card G ∧ x = basisElt p.1 p.2}

variable (G) in
/-- The ℤ-span of the proper classes. -/
noncomputable def smallSpan : Submodule ℤ (DRing G) :=
  Submodule.span ℤ (smallSet G)

/-- **The grading lemma**: a product with a proper left factor lies in
the proper span. -/
theorem basisElt_mul_basisElt_mem_smallSpan {K : Subgroup G}
    (hK : Nat.card K < Nat.card G) (l : K →* ℂˣ) (K' : Subgroup G)
    (l' : K' →* ℂˣ) :
    basisElt K l * basisElt K' l' ∈ smallSpan G := by
  classical
  -- the product is the skeleton of the product monomial `G`-set
  have hprod : basisElt K l * basisElt K' l' =
      GrothendieckRing.of
        (Skel.mk ((induced K l).prod (induced K' l'))) := by
    rw [basisElt, basisElt, ← GrothendieckRing.of_mul, Skel.mk_prod]
  -- decompose the skeleton and identify the classes by census
  obtain ⟨s, hs⟩ := Skel.exists_decomposition
    (Skel.mk ((induced K l).prod (induced K' l')))
  have hcensus : s.map (fun p => (⟦(⟨p.1, p.2⟩ : CharPair G ℂˣ)⟧ :
      CharPairClass G ℂˣ)) =
      census ((induced K l).prod (induced K' l')) := by
    have h1 := congrArg Skel.censusSkel hs
    rw [Skel.censusSkel_mk, Skel.censusSkel_sum_induced] at h1
    exact h1.symm
  -- census classes have stabilizer-sized (hence proper) subgroups
  have hsmall : ∀ c ∈ census ((induced K l).prod (induced K' l')),
      ∃ q : CharPair G ℂˣ, Nat.card q.1 < Nat.card G ∧ c = ⟦q⟧ := by
    intro c hc
    rw [census, Multiset.mem_map] at hc
    obtain ⟨ω, -, rfl⟩ := hc
    refine ⟨pointPair _ ω.out, ?_, rfl⟩
    change Nat.card (stabilizer G ω.out) < Nat.card G
    -- the stabilizer of a product point is inside a conjugate of `K`
    set z := ω.out with hz
    have hle : stabilizer G z ≤ stabilizer G z.1 := by
      intro g hg
      have h1 : g • z = z := hg
      have h2 : g • z.1 = z.1 := congrArg Prod.fst h1
      exact h2
    have hsub : ∀ g ∈ stabilizer G z.1,
        (z.1.out)⁻¹ * g * z.1.out ∈ K := by
      intro g hg
      have h1 : g ∈ stabilizer G (((z.1.out : G) : G ⧸ K)) := by
        have h2 : ((z.1.out : G) : G ⧸ K) = z.1 :=
          QuotientGroup.out_eq' z.1
        rw [h2]
        exact hg
      exact mem_stabilizer_coset.mp h1
    calc Nat.card (stabilizer G z)
        ≤ Nat.card (stabilizer G z.1) := Subgroup.card_le_of_le hle
      _ ≤ Nat.card K := card_le_of_subconj hsub
      _ < Nat.card G := hK
  -- pass to the sum of basis elements
  have hofs : GrothendieckRing.of
      ((s.map fun p => Skel.mk (induced p.1 p.2)).sum) =
      (s.map fun p => basisElt p.1 p.2).sum := by
    rw [← GrothendieckRing.ofHom_apply,
      map_multiset_sum GrothendieckRing.ofHom, Multiset.map_map]
    refine congrArg Multiset.sum ?_
    refine Multiset.map_congr rfl fun p _ => ?_
    rfl
  rw [hprod, (congrArg GrothendieckRing.of hs).trans hofs]
  -- each summand is a proper basis element (its class is small)
  have hmem : ∀ x ∈ s.map fun p => basisElt p.1 p.2, x ∈ smallSpan G := by
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    have hcls : (⟦(⟨p.1, p.2⟩ : CharPair G ℂˣ)⟧ : CharPairClass G ℂˣ) ∈
        census ((induced K l).prod (induced K' l')) := by
      rw [← hcensus]
      exact Multiset.mem_map_of_mem _ hp
    obtain ⟨q, hq, hqc⟩ := hsmall _ hcls
    have hconj : IsConjPair p.1 q.1 p.2 q.2 := by
      have h1 : ((⟨p.1, p.2⟩ : CharPair G ℂˣ)) ≈ q := Quotient.eq.mp hqc
      exact h1
    have hcard : Nat.card p.1 < Nat.card G := by
      rw [card_eq_of_conjPair hconj]
      exact hq
    exact Submodule.subset_span ⟨⟨p.1, p.2⟩, hcard, rfl⟩
  -- multiset sums of members lie in the span
  exact AddSubmonoid.multiset_sum_mem
    (smallSpan G).toAddSubmonoid _ hmem

/-! ## The split `D(G) = ℤĜ ⊕ I` -/

variable (G) in
/-- The ℤ-span of the character elements. -/
noncomputable def topSpan : Submodule ℤ (DRing G) :=
  Submodule.span ℤ (Set.range (charElt (G := G)))

/-- The reverse bridge: `charElt l = [⊤, l ∘ subtype]`. -/
theorem charElt_eq_basisElt_top (l : G →* ℂˣ) :
    charElt l = basisElt ⊤ (l.comp (⊤ : Subgroup G).subtype) := by
  rw [basisElt_top_eq_charElt]
  congr 1

variable (G) in
/-- The character subring `ℤĜ ⊆ D(G)`. -/
noncomputable def topSubring : Subring (DRing G) where
  carrier := topSpan G
  zero_mem' := Submodule.zero_mem _
  add_mem' := fun ha hb => Submodule.add_mem _ ha hb
  neg_mem' := fun ha => Submodule.neg_mem _ ha
  one_mem' := Submodule.subset_span ⟨1, charElt_one⟩
  mul_mem' := by
    intro a b ha hb
    have h1 : a * b ∈ topSpan G * topSpan G := Submodule.mul_mem_mul ha hb
    have h2 : topSpan G * topSpan G ≤ topSpan G := by
      rw [topSpan, Submodule.span_mul_span]
      refine Submodule.span_le.mpr ?_
      rintro x ⟨y, ⟨l, rfl⟩, z, ⟨l', rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨l * l', (charElt_mul l l').symm⟩
    exact h2 h1

/-- Multiplication by anything preserves the proper span. -/
theorem mul_mem_smallSpan (r : DRing G) {x : DRing G}
    (hx : x ∈ smallSpan G) : r * x ∈ smallSpan G := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨p, hp, rfl⟩ := hy
    obtain ⟨s, t, hst⟩ := exists_basisElt_decomposition r
    rw [hst, sub_mul]
    refine Submodule.sub_mem _ ?_ ?_ <;>
    · rw [← Multiset.sum_map_mul_right]
      refine AddSubmonoid.multiset_sum_mem (smallSpan G).toAddSubmonoid _
        ?_
      intro y hy
      rw [Multiset.mem_map] at hy
      obtain ⟨q, -, rfl⟩ := hy
      rw [mul_comm]
      exact basisElt_mul_basisElt_mem_smallSpan hp p.2 q.1 q.2
  | zero =>
    rw [mul_zero]
    exact Submodule.zero_mem _
  | add a b ha hb iha ihb =>
    rw [mul_add]
    exact Submodule.add_mem _ iha ihb
  | smul n a ha iha =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ n iha

variable (G) in
/-- The proper ideal `I ⊆ D(G)`. -/
noncomputable def properIdeal : Ideal (DRing G) where
  carrier := smallSpan G
  zero_mem' := Submodule.zero_mem _
  add_mem' := fun ha hb => Submodule.add_mem _ ha hb
  smul_mem' := fun r _x hx => mul_mem_smallSpan r hx

/-! ## Disjointness and totality -/

variable (G) in
/-- The class-level smallness predicate. -/
def SmallClass (c : CharPairClass G ℂˣ) : Prop :=
  Nat.card c.out.1 < Nat.card G

/-- The proper span sits inside the span of small classes. -/
theorem smallSpan_le :
    smallSpan G ≤ Submodule.span ℤ
      (classElt '' {c : CharPairClass G ℂˣ | SmallClass G c}) := by
  refine Submodule.span_le.mpr ?_
  rintro x ⟨p, hp, rfl⟩
  refine Submodule.subset_span ⟨⟦(⟨p.1, p.2⟩ : CharPair G ℂˣ)⟧, ?_, ?_⟩
  · change Nat.card (Quotient.out
      (⟦(⟨p.1, p.2⟩ : CharPair G ℂˣ)⟧ : CharPairClass G ℂˣ)).1 <
      Nat.card G
    have hconj : IsConjPair
        (Quotient.out (⟦(⟨p.1, p.2⟩ : CharPair G ℂˣ)⟧ :
          CharPairClass G ℂˣ)).1 p.1
        (Quotient.out (⟦(⟨p.1, p.2⟩ : CharPair G ℂˣ)⟧ :
          CharPairClass G ℂˣ)).2 p.2 :=
      Quotient.mk_out (⟨p.1, p.2⟩ : CharPair G ℂˣ)
    rw [card_eq_of_conjPair hconj]
    exact hp
  · exact classElt_mk _

/-- The character span sits inside the span of top classes. -/
theorem topSpan_le :
    topSpan G ≤ Submodule.span ℤ
      (classElt '' {c : CharPairClass G ℂˣ | ¬ SmallClass G c}) := by
  refine Submodule.span_le.mpr ?_
  rintro x ⟨l, rfl⟩
  rw [charElt_eq_basisElt_top]
  refine Submodule.subset_span
    ⟨⟦(⟨⊤, l.comp (⊤ : Subgroup G).subtype⟩ : CharPair G ℂˣ)⟧, ?_, ?_⟩
  · intro hlt
    have hconj := Quotient.mk_out (s := charPairSetoid G ℂˣ)
      (⟨(⊤ : Subgroup G), l.comp (⊤ : Subgroup G).subtype⟩ :
        CharPair G ℂˣ)
    rw [SmallClass, card_eq_of_conjPair hconj] at hlt
    have hfst : ((⟨(⊤ : Subgroup G), l.comp (⊤ : Subgroup G).subtype⟩ :
        CharPair G ℂˣ)).1 = (⊤ : Subgroup G) := rfl
    rw [hfst] at hlt
    have htop : Nat.card ((⊤ : Subgroup G)) = Nat.card G :=
      Subgroup.card_top
    omega
  · exact classElt_mk _

/-- **Disjointness**: `I ∩ ℤĜ = 0`. -/
theorem smallSpan_inf_topSpan {x : DRing G}
    (hI : x ∈ smallSpan G) (hS : x ∈ topSpan G) : x = 0 := by
  have hdisj : Disjoint
      (Submodule.span ℤ (classElt ''
        {c : CharPairClass G ℂˣ | SmallClass G c}))
      (Submodule.span ℤ (classElt ''
        {c : CharPairClass G ℂˣ | ¬ SmallClass G c})) := by
    refine LinearIndependent.disjoint_span_image linearIndependent_classElt
      ?_
    exact Set.disjoint_left.mpr fun c hc hc' => hc' hc
  have h1 := smallSpan_le hI
  have h2 := topSpan_le hS
  have h3 := hdisj.le_bot ⟨h1, h2⟩
  simpa using h3

/-- **Totality**: every element splits as proper + character parts. -/
theorem exists_small_add_top (r : DRing G) :
    ∃ a ∈ smallSpan G, ∃ b ∈ topSpan G, r = a + b := by
  classical
  have key : ∀ s : Multiset ((K : Subgroup G) × (K →* ℂˣ)),
      ∃ a ∈ smallSpan G, ∃ b ∈ topSpan G,
        (s.map fun p => basisElt p.1 p.2).sum = a + b := by
    intro s
    induction s using Multiset.induction_on with
    | empty =>
      exact ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, by simp⟩
    | cons p s ih =>
      obtain ⟨K₀, l₀⟩ := p
      obtain ⟨a, ha, b, hb, hab⟩ := ih
      rw [Multiset.map_cons, Multiset.sum_cons, hab]
      by_cases hp : Nat.card K₀ < Nat.card G
      · exact ⟨basisElt K₀ l₀ + a,
          Submodule.add_mem _
            (Submodule.subset_span ⟨⟨K₀, l₀⟩, hp, rfl⟩) ha,
          b, hb, by ring⟩
      · have hcard : Nat.card K₀ = Nat.card G := by
          have hle : Nat.card K₀ ≤ Nat.card G :=
            Subgroup.card_le_card_group K₀
          omega
        have htop : K₀ = ⊤ := Subgroup.eq_top_of_card_eq K₀ hcard
        subst htop
        refine ⟨a, ha, basisElt ⊤ l₀ + b, ?_, by ring⟩
        refine Submodule.add_mem _ ?_ hb
        rw [basisElt_top_eq_charElt]
        exact Submodule.subset_span ⟨_, rfl⟩
  obtain ⟨sP, sN, hr⟩ := exists_basisElt_decomposition r
  obtain ⟨a1, ha1, b1, hb1, h1⟩ := key sP
  obtain ⟨a2, ha2, b2, hb2, h2⟩ := key sN
  refine ⟨a1 - a2, Submodule.sub_mem _ ha1 ha2,
    b1 - b2, Submodule.sub_mem _ hb1 hb2, ?_⟩
  rw [hr, h1, h2]
  ring

/-! ## Müller 2.6.1 for `D(G)` -/

/-- **Every torsion unit of `D(G)` factors** as `u = b(1 + a)` with `b`
a torsion element of the character subring `ℤĜ` and `a` in the proper
ideal. -/
theorem torsion_unit_factorization {u : DRing G} {n : ℕ} (hn : 0 < n)
    (hu : u ^ n = 1) :
    ∃ b a : DRing G, b ∈ topSpan G ∧ a ∈ smallSpan G ∧ b ^ n = 1 ∧
      (1 + a) ^ n = 1 ∧ u = b * (1 + a) := by
  have hdisj : ∀ x ∈ properIdeal G, x ∈ topSubring G → x = 0 :=
    fun x hI hS => smallSpan_inf_topSpan hI hS
  have hspan : ∀ r : DRing G,
      ∃ a ∈ properIdeal G, ∃ b ∈ topSubring G, r = a + b :=
    fun r => exists_small_add_top r
  obtain ⟨b, a, hb, ha, hbn, han, hfact⟩ :=
    SplitRing.exists_factorization (properIdeal G) (topSubring G) hdisj
      hspan hn hu
  exact ⟨b, a, hb, ha, hbn, han, hfact⟩

end DRing

end LeanDring
