/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.Decomposition

/-!
# Classification of the basis elements: `[K, λ] ≅ [K′, λ′] ↔ conjugate`

Müller, Satz 2.1.1 (i): two induced monomial `G`-sets are isomorphic iff
their defining pairs are conjugate in `G`
(`MonGSet.isIso_induced_iff_conjPair`), and correspondingly in the D-ring
`DRing.basisElt_eq_iff` — so the `[K,λ]`, up to conjugacy of pairs, are
pairwise distinct generators of `D(G)`. Together with the decomposition
theorem (`Decomposition.lean`) this pins the basis combinatorics that all
rank/fibre-bag arguments (cyclic-index-2, metacyclic, extraspecial strata)
compute with.

Key computations:
* `mem_stabilizer_coset` — `Stab_{G/K}(bK) = bKb⁻¹` (membership form);
* `weight_induced_coset` — the character of an arbitrary coset `bK` of
  `[K, λ]` is `k ↦ λ(b⁻¹kb)` (the section drops out by commutativity);
* conjugate ⇒ iso via the gauge-matched orbit isomorphism;
* iso ⇒ conjugate by transporting the identity coset through the
  isomorphism and cancelling the gauge at fixed points.

`IsConjPair` is reflexive and symmetric (`refl`/`symm` provided) — the
conjugacy *classes* of pairs index the basis.
-/

namespace LeanDring

open MulAction

universe u v

variable {G : Type u} [Group G] {A : Type v} [CommGroup A]

namespace MonGSet

/-! ## Stabilizers and characters of arbitrary cosets -/

/-- Membership form of `Stab_{G/K}(bK) = bKb⁻¹`. -/
theorem mem_stabilizer_coset {K : Subgroup G} {g b : G} :
    g ∈ stabilizer G ((b : G) : G ⧸ K) ↔ b⁻¹ * g * b ∈ K := by
  rw [mem_stabilizer_iff]
  change ((g * b : G) : G ⧸ K) = ((b : G) : G ⧸ K) ↔ _
  rw [QuotientGroup.eq]
  constructor
  · intro h
    rw [show (g * b)⁻¹ * b = (b⁻¹ * g * b)⁻¹ by group] at h
    exact inv_mem_iff.mp h
  · intro h
    rw [show (g * b)⁻¹ * b = (b⁻¹ * g * b)⁻¹ by group]
    exact inv_mem h

variable [Fintype G]

/-- The character of an arbitrary coset `bK` in `[K, λ]` is `k ↦ λ(b⁻¹kb)`:
the choice of section drops out by commutativity of the fiber. -/
theorem weight_induced_coset (K : Subgroup G) (l : K →* A) {k b : G}
    (hk : b⁻¹ * k * b ∈ K) :
    (induced K l).weight k ((b : G) : G ⧸ K) = l ⟨b⁻¹ * k * b, hk⟩ := by
  have hfix : k • ((b : G) : G ⧸ K) = ((b : G) : G ⧸ K) :=
    mem_stabilizer_iff.mp (mem_stabilizer_coset.mpr hk)
  have hd : ((b : G) : G ⧸ K).out⁻¹ * b ∈ K :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' ((b : G) : G ⧸ K))
  have harg : (⟨(k • ((b : G) : G ⧸ K)).out⁻¹ * k * ((b : G) : G ⧸ K).out,
      induced_mem K k _⟩ : K) =
      ⟨((b : G) : G ⧸ K).out⁻¹ * b, hd⟩ * ⟨b⁻¹ * k * b, hk⟩ *
        (⟨((b : G) : G ⧸ K).out⁻¹ * b, hd⟩)⁻¹ := by
    refine Subtype.ext ?_
    change (k • ((b : G) : G ⧸ K)).out⁻¹ * k * ((b : G) : G ⧸ K).out =
      (((b : G) : G ⧸ K).out⁻¹ * b) * (b⁻¹ * k * b) *
        (((b : G) : G ⧸ K).out⁻¹ * b)⁻¹
    rw [hfix]
    group
  change l _ = _
  rw [harg, map_mul, map_mul, map_inv,
    mul_comm (l ⟨((b : G) : G ⧸ K).out⁻¹ * b, hd⟩), mul_assoc,
    mul_inv_cancel, mul_one]

omit [Fintype G] in
/-- Every coset lies in the orbit of any fixed coset: `G/K` is transitive. -/
theorem mem_orbit_coset (K : Subgroup G) (b : G) (q : G ⧸ K) :
    q ∈ orbit G ((b : G) : G ⧸ K) := by
  refine QuotientGroup.induction_on q fun c => ?_
  refine mem_orbit_iff.mpr ⟨c * b⁻¹, ?_⟩
  change ((c * b⁻¹ * b : G) : G ⧸ K) = ((c : G) : G ⧸ K)
  rw [inv_mul_cancel_right]

/-! ## Transport lemmas along isomorphisms -/

omit [Fintype G] in
/-- Equivariant bijections preserve stabilizers. -/
theorem stabilizer_eq_of_equivariant {α β : Type u} [MulAction G α] [MulAction G β]
    (e : α ≃ β) (he : ∀ (g : G) (x : α), e (g • x) = g • e x) (x : α) :
    stabilizer G x = stabilizer G (e x) := by
  ext g
  rw [mem_stabilizer_iff, mem_stabilizer_iff]
  constructor
  · intro h
    rw [← he, h]
  · intro h
    apply e.injective
    rw [he, h]

omit [Fintype G] in
/-- At a fixed point, the gauge cancels: an isomorphism preserves weights of
stabilizing elements on the nose. -/
theorem weight_eq_of_iso_parts {X Y : MonGSet G A} {e : X.carrier ≃ Y.carrier}
    {φ : X.carrier → A}
    (hw : ∀ (g : G) (x : X.carrier), Y.weight g (e x) * φ x = φ (g • x) * X.weight g x)
    {k : G} {x : X.carrier} (hfix : k • x = x) :
    Y.weight k (e x) = X.weight k x := by
  have h := hw k x
  rw [hfix] at h
  exact mul_right_cancel (h.trans (mul_comm _ _))

/-! ## Conjugacy of pairs -/

/-- Conjugacy of character pairs: `(K, λ) ∼ (K′, λ′)` iff some `a : G`
conjugates `K` onto `K′` carrying `λ` to `λ′`. -/
def IsConjPair (K K' : Subgroup G) (l : K →* A) (l' : K' →* A) : Prop :=
  ∃ (a : G) (hmem : ∀ k : G, k ∈ K ↔ a * k * a⁻¹ ∈ K'),
    ∀ (k : G) (hk : k ∈ K), l' ⟨a * k * a⁻¹, (hmem k).mp hk⟩ = l ⟨k, hk⟩

omit [Fintype G] in
theorem IsConjPair.refl (K : Subgroup G) (l : K →* A) : IsConjPair K K l l := by
  refine ⟨1, fun k => by simp, fun k hk => ?_⟩
  exact congrArg l (Subtype.ext (by group))

omit [Fintype G] in
theorem IsConjPair.symm {K K' : Subgroup G} {l : K →* A} {l' : K' →* A}
    (h : IsConjPair K K' l l') : IsConjPair K' K l' l := by
  obtain ⟨a, hmem, hl⟩ := h
  have hcalc : ∀ k' : G, a * (a⁻¹ * k' * a) * a⁻¹ = k' := fun k' => by group
  have hmem' : ∀ k' : G, k' ∈ K' ↔ a⁻¹ * k' * (a⁻¹)⁻¹ ∈ K := by
    intro k'
    rw [inv_inv]
    constructor
    · intro hk'
      by_contra hno
      exact hno ((hmem _).mpr (by rwa [hcalc]))
    · intro hk
      have := (hmem _).mp hk
      rwa [hcalc] at this
  refine ⟨a⁻¹, hmem', fun k' hk' => ?_⟩
  have hk : a⁻¹ * k' * a ∈ K := by
    have := (hmem' k').mp hk'
    rwa [inv_inv] at this
  have := hl (a⁻¹ * k' * a) hk
  calc l ⟨a⁻¹ * k' * (a⁻¹)⁻¹, (hmem' k').mp hk'⟩
      = l ⟨a⁻¹ * k' * a, hk⟩ := congrArg l (Subtype.ext (by group))
    _ = l' ⟨a * (a⁻¹ * k' * a) * a⁻¹, (hmem _).mp hk⟩ := this.symm
    _ = l' ⟨k', hk'⟩ := congrArg l' (Subtype.ext (hcalc k'))

/-! ## The classification theorem -/

/-- Conjugate pairs give isomorphic induced monomial `G`-sets, via the
gauge-matched orbit isomorphism between the identity coset of `[K, λ]` and
the coset `a⁻¹K′` of `[K′, λ′]`. -/
theorem isIso_induced_of_conjPair {K K' : Subgroup G} {l : K →* A} {l' : K' →* A}
    (h : IsConjPair K K' l l') : IsIso (induced K l) (induced K' l') := by
  obtain ⟨a, hmem, hl⟩ := h
  -- match `⟦1⟧ ∈ [K,λ]` against `⟦a⁻¹⟧ ∈ [K′,λ′]`
  have hstab : stabilizer G (((1 : G) : G ⧸ K) : (induced K l).carrier) =
      stabilizer G (((a⁻¹ : G) : G ⧸ K') : (induced K' l').carrier) := by
    ext g
    rw [show ((1 : G) : G ⧸ K) = ((1 : G) : G ⧸ K) from rfl, mem_stabilizer_coset,
      mem_stabilizer_coset]
    simp only [inv_one, one_mul, mul_one, inv_inv]
    exact hmem g
  have hchar : ∀ k ∈ stabilizer G (((1 : G) : G ⧸ K) : (induced K l).carrier),
      (induced K l).weight k ((1 : G) : G ⧸ K) =
        (induced K' l').weight k ((a⁻¹ : G) : G ⧸ K') := by
    intro k hk
    have hkK : k ∈ K := by
      have := mem_stabilizer_coset.mp hk
      simpa using this
    have hk' : (a⁻¹)⁻¹ * k * a⁻¹ ∈ K' := by
      rw [inv_inv]
      exact (hmem k).mp hkK
    rw [weight_induced_one K l hkK, weight_induced_coset K' l' hk']
    calc l ⟨k, hkK⟩
        = l' ⟨a * k * a⁻¹, (hmem k).mp hkK⟩ := (hl k hkK).symm
      _ = l' ⟨(a⁻¹)⁻¹ * k * a⁻¹, hk'⟩ := congrArg l' (Subtype.ext (by group))
  refine ((isIso_ofInvariant_of_univ _ _ (mem_orbit_coset K 1)).symm.trans
    (isIso_orbit_matched hstab hchar)).trans
    (isIso_ofInvariant_of_univ _ _ (mem_orbit_coset K' a⁻¹))

/-- Isomorphic induced monomial `G`-sets have conjugate pairs: transport the
identity coset through the isomorphism and cancel the gauge. -/
theorem conjPair_of_isIso_induced {K K' : Subgroup G} {l : K →* A} {l' : K' →* A}
    (h : IsIso (induced K l) (induced K' l')) : IsConjPair K K' l l' := by
  obtain ⟨e, φ, he, hw⟩ := h
  set b : G := (e ((1 : G) : G ⧸ K)).out with hb
  have hq : ((b : G) : G ⧸ K') = e ((1 : G) : G ⧸ K) :=
    QuotientGroup.out_eq' _
  have hstab := stabilizer_eq_of_equivariant e he ((1 : G) : G ⧸ K)
  have hmem : ∀ k : G, k ∈ K ↔ b⁻¹ * k * (b⁻¹)⁻¹ ∈ K' := by
    intro k
    rw [inv_inv]
    constructor
    · intro hk
      have h1 : k ∈ stabilizer G (((1 : G) : G ⧸ K) : (induced K l).carrier) :=
        mem_stabilizer_coset.mpr (by simpa using hk)
      have h2 := hstab ▸ h1
      rw [← hq] at h2
      have := mem_stabilizer_coset.mp h2
      -- `b⁻¹ * k * b ∈ K'`, adjust bracketing
      convert this using 2
    · intro hk'
      have h2 : k ∈ stabilizer G (e (((1 : G) : G ⧸ K) : (induced K l).carrier)) := by
        rw [← hq]
        exact mem_stabilizer_coset.mpr hk'
      have h1 := hstab.symm ▸ h2
      have := mem_stabilizer_coset.mp h1
      simpa using this
  refine ⟨b⁻¹, hmem, fun k hk => ?_⟩
  have hfix : k • (((1 : G) : G ⧸ K) : (induced K l).carrier) = ((1 : G) : G ⧸ K) :=
    mem_stabilizer_iff.mp (mem_stabilizer_coset.mpr (by simpa using hk))
  have h1 : (induced K' l').weight k (e ((1 : G) : G ⧸ K)) =
      (induced K l).weight k ((1 : G) : G ⧸ K) :=
    weight_eq_of_iso_parts hw hfix
  rw [weight_induced_one K l hk, ← hq] at h1
  have hk' : b⁻¹ * k * b ∈ K' := by
    have := (hmem k).mp hk
    rwa [inv_inv] at this
  rw [weight_induced_coset K' l' hk'] at h1
  calc l' ⟨b⁻¹ * k * (b⁻¹)⁻¹, (hmem k).mp hk⟩
      = l' ⟨b⁻¹ * k * b, hk'⟩ := congrArg l' (Subtype.ext (by group))
    _ = l ⟨k, hk⟩ := h1

/-- **Classification of basis elements** (Müller, Satz 2.1.1 (i)):
`[K, λ] ≅ [K′, λ′]` iff `(K, λ)` and `(K′, λ′)` are conjugate in `G`. -/
theorem isIso_induced_iff_conjPair (K K' : Subgroup G) (l : K →* A) (l' : K' →* A) :
    IsIso (induced K l) (induced K' l') ↔ IsConjPair K K' l l' :=
  ⟨conjPair_of_isIso_induced, isIso_induced_of_conjPair⟩

end MonGSet

/-! ## The classification in the D-ring -/

namespace DRing

open MonGSet MonRing

variable {G : Type u} [Group G] [Fintype G]

omit [Fintype G] in
/-- Addition cancels in the monomial Burnside semiring over `ℂˣ` (species
separate, and `ℂ` cancels). -/
theorem monSkel_add_cancel {a b c : Skel G ℂˣ} (h : a + c = b + c) : a = b := by
  apply Skel.species_injective
  funext H m
  change speciesHom (Units.coeHom ℂ) H m a = speciesHom (Units.coeHom ℂ) H m b
  have hm := congrArg (speciesHom (Units.coeHom ℂ) H m) h
  rw [map_add, map_add] at hm
  exact add_right_cancel hm

/-- **Classification in `D(G)`**: two basis elements are equal iff their
pairs are conjugate. The `[K, λ]` up to conjugacy are pairwise distinct. -/
theorem basisElt_eq_iff (K K' : Subgroup G) (l : K →* ℂˣ) (l' : K' →* ℂˣ) :
    basisElt K l = basisElt K' l' ↔ IsConjPair K K' l l' := by
  constructor
  · intro h
    have h1 : Skel.mk (induced K l) = Skel.mk (induced K' l') :=
      GrothendieckRing.of_injective (fun _ _ _ => monSkel_add_cancel) h
    exact conjPair_of_isIso_induced (Quotient.exact h1)
  · intro h
    exact congrArg GrothendieckRing.of
      (Quotient.sound (isIso_induced_of_conjPair h))

end DRing

end LeanDring
