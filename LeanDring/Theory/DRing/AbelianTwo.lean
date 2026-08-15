/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.FreeBasis
import LeanDring.Theory.DRing.GabCount
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.Divisors

-- Several statements below do not mention the section's `[Fintype _]` /
-- group binders, but their proofs need them for instance synthesis, so the
-- binders cannot be `omit`ted.  The linters' suggested rewrite to `[Finite _]`
-- plus `Fintype.ofFinite` is a genuine refactor, not a cleanup.
set_option linter.unusedFintypeInType false

/-!
# The cyclic slice of the abelian 2-group `D ⇒ B` theorem

For abelian 2-groups, `D(G) ≅ D(H) ⇒ B(G) ≅ B(H)` follows on paper from the
closed-form Smith normal form of the fused-rational ghost lattice. That route
— Möbius unitriangularity, Sylvester–Hadamard Kronecker divisors, and the
triangular extraction of the group type from the divisor multiplicities — is
a formalization programme of its own and is not attempted here.

This file settles the **cyclic** case using the coarsest SNF invariant, the
one already available in the formalization: the rank of `D(G)`
(`DRing.rank_dring`, the number of elementary divisors). For finite
*commutative* groups that rank is the subgroup-order sum `∑_{K ≤ G} |K|`
(`card_charPairClass_of_comm`), and the sum is a ring-isomorphism invariant of
`D(G)` for every finite commutative group
(`sum_card_subgroups_eq_of_dringEquiv`). On a cyclic 2-group of order `2^r`
the sum evaluates to `2^(r+1) - 1` (`sum_card_subgroups_cyclic_two`), which
determines `r`; two cyclic groups of equal order are isomorphic, and Burnside
rings are functorial in group isomorphisms (`burnsideRingCongr`). Hence:

* `AbelianTwo.burnsideEquivOfCyclicTwoGroup` —
  `D(G) ≃+* D(H)` implies `B(G) ≃+* B(H)` for cyclic 2-groups (indeed
  `G ≃* H`, via `AbelianTwo.mulEquivOfCyclicTwoGroup`).

The rank alone does not separate general abelian 2-groups; that needs the
finer divisor multiplicities of the SNF theorem, so the general abelian case
is not covered here.
-/

namespace LeanDring

open MulAction

universe u v

/-! ## Burnside rings are functorial in group isomorphisms -/

namespace FinGSet

-- The pullback keeps the carrier, so both groups must live in one universe.
variable {G : Type u} [Group G] {G' : Type u} [Group G']

/-- Pull back a finite `G'`-set along a homomorphism `e : G →* G'`. -/
def comap (e : G →* G') (X : FinGSet G') : FinGSet G where
  carrier := X.carrier
  fintype := X.fintype
  action := MulAction.compHom X.carrier e

/-- Pulling back preserves equivariant isomorphism. -/
theorem IsIso.comap {e : G →* G'} {X Y : FinGSet G'} (h : IsIso X Y) :
    IsIso (comap e X) (comap e Y) := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun g x => hf (e g) x⟩

/-- The pullback ring homomorphism on Burnside semirings. -/
def comapSkelHom (e : G →* G') : Skel G' →+* Skel G where
  toFun := Quotient.map (comap e) fun _ _ h => h.comap
  map_zero' := Quotient.sound ⟨Equiv.refl _, fun g x => x.elim⟩
  map_one' := Quotient.sound ⟨Equiv.refl _, fun g x => rfl⟩
  map_add' a b := by
    refine Quotient.ind₂ (fun X Y => ?_) a b
    refine Quotient.sound ⟨Equiv.refl _, ?_⟩
    rintro g (x | y) <;> rfl
  map_mul' a b := by
    refine Quotient.ind₂ (fun X Y => ?_) a b
    exact Quotient.sound ⟨Equiv.refl _, fun g p => rfl⟩

/-- Pulling back along a composite is the composite of pullbacks (the
equivariance is definitional). -/
theorem comap_comap_isIso {G'' : Type u} [Group G''] (f : G →* G')
    (g' : G' →* G'') (X : FinGSet G'') :
    IsIso (comap f (comap g' X)) (comap (g'.comp f) X) :=
  ⟨Equiv.refl _, fun _ _ => rfl⟩

theorem comap_id_isIso (X : FinGSet G) :
    IsIso (comap (MonoidHom.id G) X) X :=
  ⟨Equiv.refl _, fun _ _ => rfl⟩

theorem comapSkelHom_comp_apply (e : G ≃* G') (a : Skel G) :
    comapSkelHom e.toMonoidHom (comapSkelHom e.symm.toMonoidHom a) = a := by
  obtain ⟨X⟩ := a
  have hhom : (e.symm.toMonoidHom).comp e.toMonoidHom = MonoidHom.id G := by
    ext g
    simp
  calc (⟦comap e.toMonoidHom (comap e.symm.toMonoidHom X)⟧ : Skel G)
      = ⟦comap ((e.symm.toMonoidHom).comp e.toMonoidHom) X⟧ :=
        Quotient.sound (comap_comap_isIso _ _ X)
    _ = ⟦comap (MonoidHom.id G) X⟧ := by rw [hhom]
    _ = ⟦X⟧ := Quotient.sound (comap_id_isIso X)

/-- Burnside semirings are functorial in group isomorphisms. -/
noncomputable def skelCongr (e : G ≃* G') : Skel G ≃+* Skel G' :=
  RingEquiv.ofRingHom (comapSkelHom e.symm.toMonoidHom)
    (comapSkelHom e.toMonoidHom)
    (RingHom.ext fun a => comapSkelHom_comp_apply e.symm a)
    (RingHom.ext fun a => comapSkelHom_comp_apply e a)

end FinGSet

namespace GrothendieckRing

variable {S : Type*} {T : Type*} [CommSemiring S] [CommSemiring T]

/-- Grothendieck rings are functorial in semiring isomorphisms. -/
noncomputable def congr (f : S ≃+* T) :
    GrothendieckRing S ≃+* GrothendieckRing T := by
  refine RingEquiv.ofRingHom (map (f : S →+* T)) (map (f.symm : T →+* S))
    ?_ ?_ <;>
  · refine hom_ext fun a => ?_
    rw [RingHom.comp_apply, map_of, map_of]
    simp

end GrothendieckRing

/-- **Burnside rings are functorial in group isomorphisms.** -/
noncomputable def burnsideRingCongr {G : Type u} [Group G] {G' : Type u}
    [Group G'] (e : G ≃* G') : BurnsideRing G ≃+* BurnsideRing G' :=
  GrothendieckRing.congr (FinGSet.skelCongr e)

/-! ## The class count is a ring-isomorphism invariant of `D(G)` -/

namespace DRing

open MonGSet

variable {G : Type u} [Group G] [Fintype G]

-- hypotheses kept: needed to synthesize `Fintype G` for
-- `card_charPairClass_eq_of_dringEquiv`.
/-- `Nat.card` form of `card_charPairClass_eq_of_dringEquiv`. -/
theorem natCard_charPairClass_eq_of_dringEquiv {G' : Type u} [Group G']
    [Fintype G'] (Φ : DRing G ≃+* DRing G') :
    Nat.card (CharPairClass G ℂˣ) = Nat.card (CharPairClass G' ℂˣ) :=
  congrArg Cardinal.toNat (card_charPairClass_eq_of_dringEquiv Φ)

section CommCount

variable {H : Type u} [CommGroup H] [Fintype H]

omit [Fintype H] in
/-- In a commutative group, conjugacy of character pairs is trivial. -/
theorem charPair_mk_injective :
    Function.Injective (Quotient.mk (charPairSetoid H ℂˣ)) := by
  rintro ⟨K, l⟩ ⟨K', l'⟩ h
  obtain ⟨a, hmem, hl⟩ := Quotient.exact h
  have hconj : ∀ k : H, a * k * a⁻¹ = k := fun k => by
    rw [mul_comm a k, mul_assoc, mul_inv_cancel, mul_one]
  have hK : K = K' := by
    ext k
    rw [hmem k, hconj k]
  subst hK
  have hchar : l = l' := by
    ext k
    have h1 := hl k.1 k.2
    have h2 : l' ⟨a * k.1 * a⁻¹, (hmem k.1).mp k.2⟩ = l' k :=
      congrArg l' (Subtype.ext (hconj k.1))
    have h3 : l k = l' k := by
      calc l k = l ⟨k.1, k.2⟩ := rfl
        _ = l' ⟨a * k.1 * a⁻¹, (hmem k.1).mp k.2⟩ := h1.symm
        _ = l' k := h2
    exact congrArg Units.val h3
  subst hchar
  rfl

-- hypothesis kept: needed to synthesize `Fintype ↥K` for
-- `card_charHom_eq_card_abelianization`.
/-- Finiteness of the character group (from `|Ĝ| = |G^ab|`). -/
theorem finite_charHom (K : Subgroup H) : Finite (↥K →* ℂˣ) := by
  classical
  have h := card_charHom_eq_card_abelianization (G := ↥K)
  have hpos : Nat.card (Abelianization ↥K) ≠ 0 := by
    haveI : Finite (Abelianization ↥K) := Quotient.finite _
    exact Nat.card_pos.ne'
  rw [← h] at hpos
  exact (Nat.card_ne_zero.mp hpos).2

/-- **The commutative class count**: `#classes = ∑_{K ≤ G} |K|`. This is
the free rank of `D(G)` for commutative `G`. -/
theorem card_charPairClass_of_comm :
    Nat.card (CharPairClass H ℂˣ) = ∑ K : Subgroup H, Nat.card ↥K := by
  classical
  haveI : ∀ K : Subgroup H, Finite (↥K →* ℂˣ) := finite_charHom
  have hbij : Function.Bijective (Quotient.mk (charPairSetoid H ℂˣ)) :=
    ⟨charPair_mk_injective, Quotient.mk_surjective⟩
  calc Nat.card (CharPairClass H ℂˣ)
      = Nat.card (CharPair H ℂˣ) :=
        (Nat.card_congr (Equiv.ofBijective _ hbij :
          CharPair H ℂˣ ≃ CharPairClass H ℂˣ)).symm
    _ = ∑ K : Subgroup H, Nat.card (↥K →* ℂˣ) := Nat.card_sigma
    _ = ∑ K : Subgroup H, Nat.card ↥K := by
        refine Finset.sum_congr rfl fun K _ => ?_
        rw [card_charHom_eq_card_abelianization]
        exact Nat.card_congr (Abelianization.equivOfComm (H := ↥K)).symm.toEquiv

end CommCount

/-- **The subgroup-order sum is a `D`-ring invariant** of finite
commutative groups: `D(G) ≅ D(G') ⇒ ∑_{K ≤ G} |K| = ∑_{K ≤ G'} |K|`.
(The coarsest invariant of the ghost-lattice SNF — its number of
elementary divisors.) -/
theorem sum_card_subgroups_eq_of_dringEquiv
    {H : Type u} [CommGroup H] [Fintype H] {H' : Type u} [CommGroup H']
    [Fintype H'] (Φ : DRing H ≃+* DRing H') :
    ∑ K : Subgroup H, Nat.card ↥K = ∑ K : Subgroup H', Nat.card ↥K := by
  rw [← card_charPairClass_of_comm, ← card_charPairClass_of_comm]
  exact natCard_charPairClass_eq_of_dringEquiv Φ

end DRing

/-! ## The subgroup-order sum of a cyclic 2-group -/

namespace AbelianTwo

variable {G : Type u} [Group G] [Fintype G]

open scoped Classical in
/-- The elements of a subgroup, as a filtered finset of the ambient
group; its cardinality is `|K|`. -/
theorem card_filter_mem (K : Subgroup G) :
    (Finset.univ.filter (fun a : G => a ∈ K)).card = Nat.card ↥K := by
  classical
  rw [← Fintype.card_subtype, Nat.card_eq_fintype_card]

open scoped Classical in
/-- In a cyclic group, a subgroup consists exactly of the `|K|`-torsion. -/
theorem filter_mem_eq_filter_pow (hG : IsCyclic G) (K : Subgroup G) :
    Finset.univ.filter (fun a : G => a ∈ K) =
      Finset.univ.filter (fun a : G => a ^ (Nat.card ↥K) = 1) := by
  classical
  have hd0 : 0 < Nat.card ↥K := Nat.card_pos
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have h1 : (⟨x, hx.2⟩ : ↥K) ^ (Nat.card ↥K) = 1 := pow_card_eq_one'
    have h3 := congrArg (K.subtype) h1
    rw [map_pow, map_one] at h3
    simpa using h3
  · rw [card_filter_mem]
    exact IsCyclic.card_pow_eq_one_le hd0

-- hypothesis kept: needed to synthesize `Fintype G` for
-- `filter_mem_eq_filter_pow`/`card_filter_mem`.
/-- In a cyclic group, a subgroup is determined by its order. -/
theorem subgroup_card_injective (hG : IsCyclic G) :
    Function.Injective fun K : Subgroup G => Nat.card ↥K := by
  classical
  intro K L h
  simp only at h
  have hKL := (filter_mem_eq_filter_pow hG K).trans
    (h ▸ (filter_mem_eq_filter_pow hG L).symm)
  ext x
  have := Finset.ext_iff.mp hKL x
  simpa using this

/-- A cyclic group has a subgroup of every order dividing the group
order. -/
theorem exists_subgroup_card_eq (hG : IsCyclic G) {d : ℕ}
    (hd : d ∣ Fintype.card G) :
    ∃ K : Subgroup G, Nat.card ↥K = d := by
  obtain ⟨g, hg⟩ := hG.exists_generator
  have hord : orderOf g = Fintype.card G := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  obtain ⟨c, hc⟩ := hd
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hc
    exact (Fintype.card_pos (α := G)).ne' hc
  refine ⟨Subgroup.zpowers (g ^ c), ?_⟩
  rw [Nat.card_zpowers, orderOf_pow, hord, hc,
    Nat.gcd_eq_right ⟨d, by ring⟩, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hc0)]

/-- Geometric sum: `∑_{i<n} 2^i = 2^n - 1`. -/
theorem sum_range_two_pow (n : ℕ) :
    ∑ i ∈ Finset.range n, 2 ^ i = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
    omega

/-- **The subgroup-order sum of a cyclic 2-group**:
`∑_{K ≤ G} |K| = 2^(r+1) - 1`. -/
theorem sum_card_subgroups_cyclic_two (hG : IsCyclic G) {r : ℕ}
    (hcard : Fintype.card G = 2 ^ r) :
    ∑ K : Subgroup G, Nat.card ↥K = 2 ^ (r + 1) - 1 := by
  classical
  have hsum : ∑ K : Subgroup G, Nat.card ↥K =
      ∑ d ∈ (2 ^ r).divisors, d := by
    refine Finset.sum_bij (fun K _ => Nat.card ↥K) ?_ ?_ ?_ ?_
    · intro K _
      rw [Nat.mem_divisors]
      refine ⟨?_, by positivity⟩
      rw [← hcard, ← Nat.card_eq_fintype_card]
      exact Subgroup.card_subgroup_dvd_card K
    · intro K _ L _ h
      exact subgroup_card_injective hG h
    · intro d hd
      rw [Nat.mem_divisors, ← hcard] at hd
      obtain ⟨K, hK⟩ := exists_subgroup_card_eq hG hd.1
      exact ⟨K, Finset.mem_univ _, hK⟩
    · intro K _
      rfl
  rw [hsum, Nat.divisors_prime_pow Nat.prime_two, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  exact sum_range_two_pow (r + 1)

/-! ## The headline: the cyclic slice of the abelian 2-group theorem -/

variable {G' : Type u} [Group G'] [Fintype G']

/-- **D-rigidity of cyclic 2-groups**: a ring isomorphism
`D(G) ≃+* D(G')` between cyclic 2-groups forces `G ≃* G'`. -/
noncomputable def mulEquivOfCyclicTwoGroup
    (hGc : IsCyclic G) (hG'c : IsCyclic G') {r s : ℕ}
    (hG : Fintype.card G = 2 ^ r) (hG' : Fintype.card G' = 2 ^ s)
    (Φ : DRing G ≃+* DRing G') : G ≃* G' := by
  letI : CommGroup G := hGc.commGroup
  letI : CommGroup G' := hG'c.commGroup
  have hsum := DRing.sum_card_subgroups_eq_of_dringEquiv Φ
  rw [sum_card_subgroups_cyclic_two hGc hG,
    sum_card_subgroups_cyclic_two hG'c hG'] at hsum
  have hr : r = s := by
    have hr1 : 1 ≤ (2 : ℕ) ^ (r + 1) := Nat.one_le_two_pow
    have hs1 : 1 ≤ (2 : ℕ) ^ (s + 1) := Nat.one_le_two_pow
    have h1 : (2 : ℕ) ^ (r + 1) = 2 ^ (s + 1) := by omega
    have h2 := Nat.pow_right_injective (le_refl 2) h1
    omega
  exact mulEquivOfCyclicCardEq (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hG, hG', hr])

/-- **The cyclic slice of the abelian 2-group `D ⇒ B` theorem**: a ring
isomorphism `D(G) ≃+* D(G')` between cyclic 2-groups induces a ring
isomorphism of Burnside rings `B(G) ≃+* B(G')`. -/
noncomputable def burnsideEquivOfCyclicTwoGroup
    (hGc : IsCyclic G) (hG'c : IsCyclic G') {r s : ℕ}
    (hG : Fintype.card G = 2 ^ r) (hG' : Fintype.card G' = 2 ^ s)
    (Φ : DRing G ≃+* DRing G') : BurnsideRing G ≃+* BurnsideRing G' :=
  burnsideRingCongr (mulEquivOfCyclicTwoGroup hGc hG'c hG hG' Φ)

end AbelianTwo

end LeanDring
