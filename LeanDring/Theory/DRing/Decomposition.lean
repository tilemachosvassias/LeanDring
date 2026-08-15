/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.Induced

/-!
# The decomposition theorem: `D(G)` is spanned by the `[K, λ]`

Every monomial `G`-set decomposes as a disjoint union of induced basis
elements `[K, λ]` (Müller, Satz 2.1.1, the spanning half): the monomial
orbit of any point `x₀` is isomorphic to `[Stab x₀, fixedWeight x₀]` — via
the gauge-matched orbit isomorphism from `SpeciesInjectivity` applied
against the identity coset of the induced model — and induction peels the
orbits off.

Main results (sorry-free):

* `MonGSet.isIso_orbit_induced` — the monomial orbit of `x₀` is `≅ [K, λ]`
  with `K = Stab x₀`, `λ = fixedWeight x₀`.
* `MonGSet.Skel.exists_decomposition` — every iso class is a finite sum of
  classes of induced monomial `G`-sets.
* `DRing.exists_basisElt_decomposition` — every element of `D(G)` is a
  difference of sums of basis elements `[K, λ]`: the `[K, λ]` **span**
  `D(G)`.
-/

namespace LeanDring

open MulAction

universe u v

variable {G : Type u} [Group G] {A : Type v} [CommGroup A]

namespace MonGSet

/-- An invariant subset that is everything gives back the whole monomial
`G`-set. -/
theorem isIso_ofInvariant_of_univ (X : MonGSet G A) {S : Set X.carrier}
    (hS : ∀ (g : G) (x : X.carrier), x ∈ S → g • x ∈ S) (huniv : ∀ z, z ∈ S) :
    IsIso (X.ofInvariant S hS) X :=
  isIso_of_weight_eq (Equiv.subtypeUnivEquiv huniv) (fun _ _ => rfl) (fun _ _ => rfl)

section OrbitInduced

variable [Fintype G] (X : MonGSet G A) (x₀ : X.carrier)

omit [Fintype G] in
/-- `x₀` is fixed by its own stabilizer. -/
theorem self_mem_fixedPoints_stabilizer :
    x₀ ∈ fixedPoints (stabilizer G x₀) X.carrier :=
  fun m => mem_stabilizer_iff.mp m.2

/-- The character of `x₀`: its weight cocycle restricted to the stabilizer. -/
noncomputable def pointChar : stabilizer G x₀ →* A :=
  X.fixedWeight (stabilizer G x₀) ⟨x₀, self_mem_fixedPoints_stabilizer X x₀⟩

/-- The identity coset of `induced K λ` carries exactly the character `λ`
(commutativity of `A` kills the conjugation by the section). -/
theorem weight_induced_one (K : Subgroup G) (l : K →* A) {k : G} (hk : k ∈ K) :
    (induced K l).weight k ((1 : G) : G ⧸ K) = l ⟨k, hk⟩ := by
  have ht : ((1 : G) : G ⧸ K).out ∈ K := by
    have := QuotientGroup.eq.mp (QuotientGroup.out_eq' ((1 : G) : G ⧸ K))
    simpa using this
  have harg : (⟨(k • ((1 : G) : G ⧸ K)).out⁻¹ * k * ((1 : G) : G ⧸ K).out,
      induced_mem K k _⟩ : K) =
      ⟨((1 : G) : G ⧸ K).out, ht⟩⁻¹ * ⟨k, hk⟩ * ⟨((1 : G) : G ⧸ K).out, ht⟩ := by
    refine Subtype.ext ?_
    change (k • ((1 : G) : G ⧸ K)).out⁻¹ * k * ((1 : G) : G ⧸ K).out =
      ((1 : G) : G ⧸ K).out⁻¹ * k * ((1 : G) : G ⧸ K).out
    have hfix : k • ((1 : G) : G ⧸ K) = ((1 : G) : G ⧸ K) := by
      rw [← mem_stabilizer_iff, MulAction.stabilizer_quotient]
      exact hk
    rw [hfix]
  change l _ = l ⟨k, hk⟩
  rw [harg, map_mul, map_mul, map_inv, mul_assoc, mul_comm (l ⟨k, hk⟩),
    ← mul_assoc, inv_mul_cancel, one_mul]

/-- **The monomial orbit is an induced basis element**: the orbit of `x₀`
with its restricted weights is isomorphic to `[Stab x₀, fixedWeight x₀]`. -/
theorem isIso_orbit_induced :
    IsIso (X.ofInvariant (orbit G x₀) (FinGSet.orbit_invariant x₀))
      (induced (stabilizer G x₀) (pointChar X x₀)) := by
  set K := stabilizer G x₀ with hK
  -- match `x₀` against the identity coset of the induced model
  have hstab : stabilizer G x₀ =
      stabilizer G (((1 : G) : G ⧸ K) : (induced K (pointChar X x₀)).carrier) := by
    rw [← hK]
    exact (MulAction.stabilizer_quotient K).symm
  have hchar : ∀ k ∈ stabilizer G x₀,
      X.weight k x₀ = (induced K (pointChar X x₀)).weight k ((1 : G) : G ⧸ K) := by
    intro k hk
    rw [weight_induced_one K (pointChar X x₀) hk]
    rfl
  refine (isIso_orbit_matched hstab hchar).trans ?_
  -- the orbit of the identity coset is everything
  refine isIso_ofInvariant_of_univ _ _ fun q => ?_
  refine QuotientGroup.induction_on q fun a => ?_
  refine mem_orbit_iff.mpr ⟨a, ?_⟩
  change ((a * 1 : G) : G ⧸ K) = _
  rw [mul_one]

end OrbitInduced

namespace Skel

variable [Fintype G]

/-- **The decomposition theorem** (bounded-cardinality induction): every iso
class of monomial `G`-sets is a finite sum of induced classes `[K, λ]`. -/
theorem exists_decomposition_aux :
    ∀ (n : ℕ) (X : MonGSet G A), Fintype.card X.carrier ≤ n →
      ∃ s : Multiset ((K : Subgroup G) × (K →* A)),
        Skel.mk X = (s.map fun p => Skel.mk (induced p.1 p.2)).sum := by
  intro n
  induction n with
  | zero =>
    intro X hle
    refine ⟨0, ?_⟩
    rw [Multiset.map_zero, Multiset.sum_zero]
    exact Quotient.sound (isIso_of_isEmpty (Nat.le_zero.mp hle) rfl)
  | succ n ih =>
    intro X hle
    by_cases hX : Fintype.card X.carrier = 0
    · refine ⟨0, ?_⟩
      rw [Multiset.map_zero, Multiset.sum_zero]
      exact Quotient.sound (isIso_of_isEmpty hX rfl)
    · -- pick any point and peel its orbit
      obtain ⟨x₀⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hX)
      set OX := X.ofInvariant (orbit G x₀) (FinGSet.orbit_invariant x₀) with hOX
      set CX := X.ofInvariant (orbit G x₀)ᶜ
        (compl_invariant X _ (FinGSet.orbit_invariant x₀)) with hCX
      have hdX : IsIso X (OX.disjUnion CX) := isIso_sum_compl X _ _
      have hcard_split : Fintype.card X.carrier =
          Fintype.card OX.carrier + Fintype.card CX.carrier := by
        obtain ⟨e, -⟩ := hdX
        rw [Fintype.card_congr e]
        exact Fintype.card_sum
      have hcard_orb : 0 < Fintype.card OX.carrier :=
        Fintype.card_pos_iff.mpr ⟨⟨x₀, mem_orbit_self x₀⟩⟩
      obtain ⟨s, hs⟩ := ih CX (by omega)
      refine ⟨⟨stabilizer G x₀, pointChar X x₀⟩ ::ₘ s, ?_⟩
      rw [Multiset.map_cons, Multiset.sum_cons, ← hs]
      have h1 : Skel.mk X = Skel.mk OX + Skel.mk CX := Quotient.sound hdX
      have h2 : Skel.mk OX =
          Skel.mk (induced (stabilizer G x₀) (pointChar X x₀)) :=
        Quotient.sound (isIso_orbit_induced X x₀)
      rw [h1, h2]

/-- **The decomposition theorem**: every iso class of monomial `G`-sets is a
finite sum of induced classes `[K, λ]` (Müller Satz 2.1.1, spanning). -/
theorem exists_decomposition (a : Skel G A) :
    ∃ s : Multiset ((K : Subgroup G) × (K →* A)),
      a = (s.map fun p => Skel.mk (induced p.1 p.2)).sum := by
  obtain ⟨X⟩ := a
  exact exists_decomposition_aux (Fintype.card X.carrier) X le_rfl

end Skel

end MonGSet

namespace DRing

open MonGSet

variable {G : Type u} [Group G] [Fintype G]

/-- **The `[K, λ]` span `D(G)`**: every element of the D-ring is a
difference of sums of basis elements. -/
theorem exists_basisElt_decomposition (x : DRing G) :
    ∃ s t : Multiset ((K : Subgroup G) × (K →* ℂˣ)),
      x = (s.map fun p => basisElt p.1 p.2).sum -
        (t.map fun p => basisElt p.1 p.2).sum := by
  obtain ⟨p⟩ := x
  obtain ⟨s, hs⟩ := Skel.exists_decomposition p.1
  obtain ⟨t, ht⟩ := Skel.exists_decomposition p.2
  refine ⟨s, t, ?_⟩
  have hx : (Quot.mk _ p : DRing G) = GrothendieckRing.of p.1 - GrothendieckRing.of p.2 :=
    GrothendieckRing.mk_eq_of_sub_of p.1 p.2
  rw [hx, hs, ht, ← GrothendieckRing.ofHom_apply, ← GrothendieckRing.ofHom_apply,
    map_multiset_sum GrothendieckRing.ofHom, map_multiset_sum GrothendieckRing.ofHom,
    Multiset.map_map, Multiset.map_map]
  rfl

end DRing

end LeanDring
