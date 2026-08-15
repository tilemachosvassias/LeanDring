/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.Classification

/-!
# The orbit census: uniqueness of the `[K, λ]`-decomposition

To every monomial `G`-set we attach its **census**: the multiset of
conjugacy classes of pairs `(Stab x, χ_x)` over the orbits. The census is
an isomorphism invariant (`census_congr`), additive over disjoint unions
(`census_disjUnion`), and the census of `[K, λ]` is the singleton class of
`(K, λ)` (`census_induced`). Consequently the decomposition of a monomial
`G`-set into induced pieces is **unique up to conjugacy**
(`Skel.decomposition_unique`) — the remaining half of Müller Satz 2.1.1:
the `[K, λ]` up to conjugacy are a *free* basis of the monomial Burnside
semiring, and their classes count the rank of `D(G)`.

`IsConjPair.trans` completes the equivalence (`charPairSetoid`), so the
classes form a genuine quotient type `CharPairClass G A`.
-/

namespace LeanDring

open MulAction

universe u v

variable {G : Type u} [Group G] {A : Type v} [CommGroup A]

namespace MonGSet

/-! ## Conjugacy of pairs is an equivalence -/

theorem IsConjPair.trans {K K' K'' : Subgroup G} {l : K →* A} {l' : K' →* A}
    {l'' : K'' →* A} (h1 : IsConjPair K K' l l') (h2 : IsConjPair K' K'' l' l'') :
    IsConjPair K K'' l l'' := by
  obtain ⟨a, hma, hla⟩ := h1
  obtain ⟨c, hmc, hlc⟩ := h2
  have hgrp : ∀ k : G, (c * a) * k * (c * a)⁻¹ = c * (a * k * a⁻¹) * c⁻¹ :=
    fun k => by group
  refine ⟨c * a, fun k => by rw [hgrp k, hma k, hmc], fun k hk => ?_⟩
  calc l'' ⟨(c * a) * k * (c * a)⁻¹, _⟩
      = l'' ⟨c * (a * k * a⁻¹) * c⁻¹, (hmc _).mp ((hma k).mp hk)⟩ :=
        congrArg l'' (Subtype.ext (hgrp k))
    _ = l' ⟨a * k * a⁻¹, (hma k).mp hk⟩ := hlc _ _
    _ = l ⟨k, hk⟩ := hla k hk

variable (G A) in
/-- A character pair `(K, λ)`. -/
abbrev CharPair := (K : Subgroup G) × (K →* A)

variable (G A) in
/-- Conjugacy of character pairs as a setoid. -/
instance charPairSetoid : Setoid (CharPair G A) where
  r p q := IsConjPair p.1 q.1 p.2 q.2
  iseqv := ⟨fun p => IsConjPair.refl p.1 p.2, IsConjPair.symm, IsConjPair.trans⟩

variable (G A) in
/-- Conjugacy classes of character pairs — the index set of the `[K, λ]`
basis of `D(G)`. -/
def CharPairClass := Quotient (charPairSetoid G A)

/-! ## The pair of a point, and its conjugacy behaviour -/

/-- The character pair attached to a point: its stabilizer and character. -/
noncomputable def pointPair (X : MonGSet G A) (x : X.carrier) : CharPair G A :=
  ⟨stabilizer G x, pointChar X x⟩

/-- Translating a point conjugates its pair. -/
theorem pointPair_smul (X : MonGSet G A) (g : G) (x : X.carrier) :
    pointPair X x ≈ pointPair X (g • x) := by
  refine ⟨g, fun k => ?_, fun k hk => ?_⟩
  · change k ∈ stabilizer G x ↔ g * k * g⁻¹ ∈ stabilizer G (g • x)
    rw [mem_stabilizer_iff, mem_stabilizer_iff]
    constructor
    · intro h
      rw [smul_smul, show g * k * g⁻¹ * g = g * k by group, mul_smul, h]
    · intro h
      rw [smul_smul, show g * k * g⁻¹ * g = g * k by group, mul_smul] at h
      exact MulAction.injective g h
  · -- the weight computation: `μ(gkg⁻¹, g•x) = μ(k, x)` by the cocycle rule
    change X.weight (g * k * g⁻¹) (g • x) = X.weight k x
    have hfix : k • x = x := mem_stabilizer_iff.mp hk
    have h1 : X.weight (g * k) x = X.weight g x * X.weight k x := by
      rw [X.weight_mul g k x, hfix]
    have h2 := X.weight_mul (g * k * g⁻¹) g x
    rw [show g * k * g⁻¹ * g = g * k by group] at h2
    -- h2 : weight (g*k) x = weight (gkg⁻¹) (g•x) * weight g x
    have h3 : X.weight k x * X.weight g x =
        X.weight (g * k * g⁻¹) (g • x) * X.weight g x :=
      (mul_comm _ _).trans (h1.symm.trans h2)
    exact mul_right_cancel h3.symm

/-- Points in the same orbit have conjugate pairs. -/
theorem pointPair_class_eq_of_mem_orbit (X : MonGSet G A) {x x' : X.carrier}
    (h : x' ∈ orbit G x) :
    (⟦pointPair X x'⟧ : CharPairClass G A) = ⟦pointPair X x⟧ := by
  obtain ⟨g, rfl⟩ := mem_orbit_iff.mp h
  exact Quotient.sound (pointPair_smul X g x).symm

/-- Isomorphisms preserve point pairs up to conjugacy (gauge cancels at
fixed points). -/
theorem pointPair_iso {X Y : MonGSet G A} {e : X.carrier ≃ Y.carrier}
    {φ : X.carrier → A} (he : ∀ (g : G) (x : X.carrier), e (g • x) = g • e x)
    (hw : ∀ (g : G) (x : X.carrier), Y.weight g (e x) * φ x = φ (g • x) * X.weight g x)
    (x : X.carrier) : pointPair Y (e x) ≈ pointPair X x := by
  have hstab := stabilizer_eq_of_equivariant e he x
  refine ⟨1, fun k => ?_, fun k hk => ?_⟩
  · change k ∈ stabilizer G (e x) ↔ 1 * k * 1⁻¹ ∈ stabilizer G x
    simp only [one_mul, inv_one, mul_one]
    rw [← hstab]
  · have hkex : k ∈ stabilizer G (e x) := hk
    have hkx : k ∈ stabilizer G x := hstab ▸ hkex
    have hfix : k • x = x := mem_stabilizer_iff.mp hkx
    have h1 : Y.weight k (e x) = X.weight k x := weight_eq_of_iso_parts hw hfix
    change X.weight (1 * k * 1⁻¹) x = Y.weight k (e x)
    rw [show (1 : G) * k * 1⁻¹ = k by group]
    exact h1.symm

/-- The pair of a point of a disjoint union (left component). -/
theorem pointPair_inl (X Y : MonGSet G A) (x : X.carrier) :
    pointPair (X.disjUnion Y) (Sum.inl x) ≈ pointPair X x := by
  refine ⟨1, fun k => ?_, fun k hk => ?_⟩
  · change k ∈ stabilizer G (Sum.inl x : (X.disjUnion Y).carrier) ↔
      1 * k * 1⁻¹ ∈ stabilizer G x
    simp only [one_mul, inv_one, mul_one]
    rw [mem_stabilizer_iff, mem_stabilizer_iff]
    exact ⟨fun h => Sum.inl.inj h, fun h => congrArg Sum.inl h⟩
  · change X.weight (1 * k * 1⁻¹) x =
      (X.disjUnion Y).weight k (Sum.inl x)
    rw [show (1 : G) * k * 1⁻¹ = k by group]
    rfl

/-- The pair of a point of a disjoint union (right component). -/
theorem pointPair_inr (X Y : MonGSet G A) (y : Y.carrier) :
    pointPair (X.disjUnion Y) (Sum.inr y) ≈ pointPair Y y := by
  refine ⟨1, fun k => ?_, fun k hk => ?_⟩
  · change k ∈ stabilizer G (Sum.inr y : (X.disjUnion Y).carrier) ↔
      1 * k * 1⁻¹ ∈ stabilizer G y
    simp only [one_mul, inv_one, mul_one]
    rw [mem_stabilizer_iff, mem_stabilizer_iff]
    exact ⟨fun h => Sum.inr.inj h, fun h => congrArg Sum.inr h⟩
  · change Y.weight (1 * k * 1⁻¹) y =
      (X.disjUnion Y).weight k (Sum.inr y)
    rw [show (1 : G) * k * 1⁻¹ = k by group]
    rfl

/-- The pair of any coset of `[K, λ]` is conjugate to `(K, λ)`. -/
theorem pointPair_induced [Fintype G] (K : Subgroup G) (l : K →* A) (q : (induced K l).carrier) :
    pointPair (induced K l) q ≈ (⟨K, l⟩ : CharPair G A) := by
  obtain ⟨b, rfl⟩ : ∃ b : G, ((b : G) : G ⧸ K) = q := ⟨q.out, QuotientGroup.out_eq' q⟩
  refine ⟨b⁻¹, fun k => ?_, fun k hk => ?_⟩
  · change k ∈ stabilizer G ((b : G) : G ⧸ K) ↔ b⁻¹ * k * (b⁻¹)⁻¹ ∈ K
    rw [inv_inv, mem_stabilizer_coset]
  · have hk' : b⁻¹ * k * b ∈ K := by
      have h2 : k ∈ stabilizer G ((b : G) : G ⧸ K) := hk
      rwa [mem_stabilizer_coset] at h2
    have h1 : pointChar (induced K l) ((b : G) : G ⧸ K) ⟨k, hk⟩ =
        l ⟨b⁻¹ * k * b, hk'⟩ := by
      change (induced K l).weight k ((b : G) : G ⧸ K) = _
      exact weight_induced_coset K l hk'
    change l ⟨b⁻¹ * k * (b⁻¹)⁻¹, _⟩ =
      pointChar (induced K l) ((b : G) : G ⧸ K) ⟨k, hk⟩
    rw [h1]
    exact congrArg l (Subtype.ext (by group))

/-! ## The census -/

/-- Canonical (noncomputable) `Fintype` on orbit spaces of monomial
`G`-sets. -/
noncomputable instance (X : MonGSet G A) :
    Fintype (Quotient (orbitRel G X.carrier)) :=
  Fintype.ofFinite _

/-- **The census** of a monomial `G`-set: the multiset of conjugacy classes
of `(Stab x, χ_x)` over its orbits. -/
noncomputable def census (X : MonGSet G A) : Multiset (CharPairClass G A) :=
  Finset.univ.val.map fun ω : Quotient (orbitRel G X.carrier) =>
    (⟦pointPair X ω.out⟧ : CharPairClass G A)

/-- The census is an isomorphism invariant. -/
theorem census_congr {X Y : MonGSet G A} (h : IsIso X Y) : census X = census Y := by
  obtain ⟨e, φ, he, hw⟩ := h
  have horb : ∀ a b : X.carrier, orbitRel G X.carrier a b ↔
      orbitRel G Y.carrier (e a) (e b) := by
    intro a b
    rw [orbitRel_apply, orbitRel_apply, mem_orbit_iff, mem_orbit_iff]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, (he g b).symm⟩
    · rintro ⟨g, hg⟩
      exact ⟨g, e.injective ((he g b).trans hg)⟩
  set eQ : Quotient (orbitRel G X.carrier) ≃ Quotient (orbitRel G Y.carrier) :=
    Quotient.congr e horb with heQ
  have huniv : (Finset.univ.val : Multiset (Quotient (orbitRel G Y.carrier))) =
      Finset.univ.val.map eQ :=
    (Multiset.map_univ_val_equiv eQ).symm
  rw [census, census, huniv, Multiset.map_map]
  refine Multiset.map_congr rfl fun ω _ => ?_
  -- `(eQ ω).out` lies in the orbit of `e ω.out`
  have hmk : (⟦(eQ ω).out⟧ : Quotient (orbitRel G Y.carrier)) = ⟦e ω.out⟧ := by
    rw [Quotient.out_eq]
    conv_lhs => rw [← Quotient.out_eq ω]
    rfl
  have hclass : ((eQ ω).out : Y.carrier) ∈ orbit G (e ω.out) :=
    orbitRel_apply.mp (Quotient.exact hmk)
  change (⟦pointPair X ω.out⟧ : CharPairClass G A) = ⟦pointPair Y (eQ ω).out⟧
  rw [pointPair_class_eq_of_mem_orbit Y hclass]
  exact (Quotient.sound (pointPair_iso he hw ω.out)).symm

/-- The census of a disjoint union is the sum of the censuses. -/
theorem census_disjUnion (X Y : MonGSet G A) :
    census (X.disjUnion Y) = census X + census Y := by
  classical
  -- orbits of the sum split as orbits of the parts
  have horbl : ∀ a b : X.carrier, orbitRel G X.carrier a b ↔
      orbitRel G (X.disjUnion Y).carrier (Sum.inl a) (Sum.inl b) := by
    intro a b
    rw [orbitRel_apply, orbitRel_apply, mem_orbit_iff, mem_orbit_iff]
    exact ⟨fun ⟨g, hg⟩ => ⟨g, congrArg Sum.inl hg⟩,
      fun ⟨g, hg⟩ => ⟨g, Sum.inl.inj hg⟩⟩
  have horbr : ∀ a b : Y.carrier, orbitRel G Y.carrier a b ↔
      orbitRel G (X.disjUnion Y).carrier (Sum.inr a) (Sum.inr b) := by
    intro a b
    rw [orbitRel_apply, orbitRel_apply, mem_orbit_iff, mem_orbit_iff]
    exact ⟨fun ⟨g, hg⟩ => ⟨g, congrArg Sum.inr hg⟩,
      fun ⟨g, hg⟩ => ⟨g, Sum.inr.inj hg⟩⟩
  -- the orbit-space equivalence
  set qe : Quotient (orbitRel G X.carrier) ⊕ Quotient (orbitRel G Y.carrier) ≃
      Quotient (orbitRel G (X.disjUnion Y).carrier) :=
    { toFun := Sum.elim (Quotient.map Sum.inl fun a b h => (horbl a b).mp h)
        (Quotient.map Sum.inr fun a b h => (horbr a b).mp h)
      invFun := Quotient.lift
        (Sum.elim (fun x => Sum.inl (⟦x⟧ : Quotient (orbitRel G X.carrier)))
          (fun y => Sum.inr (⟦y⟧ : Quotient (orbitRel G Y.carrier)))) (by
        rintro (a | a) (b | b) h
        · exact congrArg Sum.inl (Quotient.sound ((horbl a b).mpr h))
        · obtain ⟨g, hg⟩ := mem_orbit_iff.mp (orbitRel_apply.mp h)
          exact (Sum.inr_ne_inl (show Sum.inr (g • b) = Sum.inl a from hg)).elim
        · obtain ⟨g, hg⟩ := mem_orbit_iff.mp (orbitRel_apply.mp h)
          exact (Sum.inl_ne_inr (show Sum.inl (g • b) = Sum.inr a from hg)).elim
        · exact congrArg Sum.inr (Quotient.sound ((horbr a b).mpr h)))
      left_inv := by
        rintro (ω | ω) <;> induction ω using Quotient.ind <;> rfl
      right_inv := by
        intro ω
        induction ω using Quotient.ind with
        | _ z => rcases z with x | y <;> rfl } with hqe
  have huniv : (Finset.univ.val :
      Multiset (Quotient (orbitRel G (X.disjUnion Y).carrier))) =
      Finset.univ.val.map qe :=
    (Multiset.map_univ_val_equiv qe).symm
  rw [census, huniv, Multiset.map_map]
  have hsplit : (Finset.univ.val : Multiset (Quotient (orbitRel G X.carrier) ⊕
      Quotient (orbitRel G Y.carrier))) =
      (Finset.univ.val.map Sum.inl) + (Finset.univ.val.map Sum.inr) := by
    rw [← Finset.univ_disjSum_univ, Finset.val_disjSum]
    rfl
  rw [hsplit, Multiset.map_add, Multiset.map_map, Multiset.map_map]
  congr 1
  · refine Multiset.map_congr rfl fun ω _ => ?_
    -- the representative of `qe (inl ω)` is in the orbit of `inl ω.out`
    have hmk : (⟦(qe (Sum.inl ω)).out⟧ :
        Quotient (orbitRel G (X.disjUnion Y).carrier)) = ⟦Sum.inl ω.out⟧ := by
      rw [Quotient.out_eq]
      conv_lhs => rw [← Quotient.out_eq ω]
      rfl
    have hclass : ((qe (Sum.inl ω)).out : (X.disjUnion Y).carrier) ∈
        orbit G (Sum.inl ω.out) := orbitRel_apply.mp (Quotient.exact hmk)
    change (⟦pointPair (X.disjUnion Y) (qe (Sum.inl ω)).out⟧ :
      CharPairClass G A) = ⟦pointPair X ω.out⟧
    rw [pointPair_class_eq_of_mem_orbit _ hclass]
    exact Quotient.sound (pointPair_inl X Y ω.out)
  · refine Multiset.map_congr rfl fun ω _ => ?_
    have hmk : (⟦(qe (Sum.inr ω)).out⟧ :
        Quotient (orbitRel G (X.disjUnion Y).carrier)) = ⟦Sum.inr ω.out⟧ := by
      rw [Quotient.out_eq]
      conv_lhs => rw [← Quotient.out_eq ω]
      rfl
    have hclass : ((qe (Sum.inr ω)).out : (X.disjUnion Y).carrier) ∈
        orbit G (Sum.inr ω.out) := orbitRel_apply.mp (Quotient.exact hmk)
    change (⟦pointPair (X.disjUnion Y) (qe (Sum.inr ω)).out⟧ :
      CharPairClass G A) = ⟦pointPair Y ω.out⟧
    rw [pointPair_class_eq_of_mem_orbit _ hclass]
    exact Quotient.sound (pointPair_inr X Y ω.out)

/-- The census of the empty monomial `G`-set is empty. -/
theorem census_empty : census (empty : MonGSet G A) = 0 := by
  have : IsEmpty (Quotient (orbitRel G (empty : MonGSet G A).carrier)) := by
    refine ⟨fun ω => ?_⟩
    induction ω using Quotient.ind with
    | _ z => exact z.elim
  rw [census, Finset.univ_eq_empty]
  rfl

/-- **The census of a basis element is its class**:
`census [K, λ] = {⟦(K, λ)⟧}`. -/
theorem census_induced [Fintype G] (K : Subgroup G) (l : K →* A) :
    census (induced K l) = {(⟦⟨K, l⟩⟧ : CharPairClass G A)} := by
  have huniq : ∀ ω : Quotient (orbitRel G (induced K l).carrier),
      ω = ⟦((1 : G) : G ⧸ K)⟧ := by
    intro ω
    induction ω using Quotient.ind with
    | _ q => exact Quotient.sound (orbitRel_apply.mpr (mem_orbit_coset K 1 q))
  haveI : Unique (Quotient (orbitRel G (induced K l).carrier)) :=
    { default := ⟦((1 : G) : G ⧸ K)⟧
      uniq := huniq }
  rw [census, Finset.univ_unique, Finset.singleton_val, Multiset.map_singleton]
  exact congrArg (· ::ₘ 0) (Quotient.sound (pointPair_induced K l _))

/-! ## Descent to iso classes and uniqueness of decomposition -/

namespace Skel

/-- The census descends to iso classes. -/
noncomputable def censusSkel : Skel G A → Multiset (CharPairClass G A) :=
  Quotient.lift census fun _ _ h => census_congr h

@[simp] theorem censusSkel_mk (X : MonGSet G A) :
    censusSkel (Skel.mk X) = census X := rfl

@[simp] theorem censusSkel_zero : censusSkel (0 : Skel G A) = 0 := census_empty

@[simp] theorem censusSkel_add (a b : Skel G A) :
    censusSkel (a + b) = censusSkel a + censusSkel b := by
  refine Quotient.ind₂ (fun X Y => ?_) a b
  exact census_disjUnion X Y

/-- The census of a sum of basis elements reads off the class multiset. -/
theorem censusSkel_sum_induced [Fintype G] (s : Multiset (CharPair G A)) :
    censusSkel ((s.map fun p => Skel.mk (induced p.1 p.2)).sum) =
      s.map (fun p => (⟦p⟧ : CharPairClass G A)) := by
  induction s using Multiset.induction with
  | empty =>
    rw [Multiset.map_zero, Multiset.map_zero, Multiset.sum_zero, censusSkel_zero]
    rfl
  | cons p s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, censusSkel_add, ih,
      Multiset.map_cons, censusSkel_mk, census_induced]
    rfl

/-- **Uniqueness of the decomposition** (the free half of Müller Satz
2.1.1): two decompositions of the same monomial `G`-set into induced basis
elements have the same multiset of conjugacy classes. Together with
`exists_decomposition` this makes the classes of `[K, λ]` a free basis of
the monomial Burnside semiring. -/
theorem decomposition_unique [Fintype G] (s t : Multiset (CharPair G A))
    (h : (s.map fun p => Skel.mk (induced p.1 p.2)).sum =
      (t.map fun p => Skel.mk (induced p.1 p.2)).sum) :
    s.map (fun p => (⟦p⟧ : CharPairClass G A)) =
      t.map (fun p => (⟦p⟧ : CharPairClass G A)) := by
  rw [← censusSkel_sum_induced, ← censusSkel_sum_induced, h]

end Skel

/-- Class-equal multisets are `Rel`-related (pairing off conjugates). -/
theorem rel_of_map_class_eq {s t : Multiset (CharPair G A)}
    (h : s.map (fun p => (⟦p⟧ : CharPairClass G A)) =
      t.map (fun p => (⟦p⟧ : CharPairClass G A))) :
    Multiset.Rel (· ≈ ·) s t := by
  classical
  induction s using Multiset.induction generalizing t with
  | empty =>
    rw [Multiset.map_zero] at h
    rw [Multiset.map_eq_zero.mp h.symm]
    exact Multiset.Rel.zero
  | cons p s ih =>
    rw [Multiset.map_cons] at h
    have hmem : (⟦p⟧ : CharPairClass G A) ∈ t.map (fun p => ⟦p⟧) := by
      rw [← h]
      exact Multiset.mem_cons_self _ _
    obtain ⟨q, hq, hcl⟩ := Multiset.mem_map.mp hmem
    have ht : t = q ::ₘ t.erase q := (Multiset.cons_erase hq).symm
    rw [ht, Multiset.map_cons, hcl] at h
    have h' := (Multiset.cons_inj_right _).mp h
    rw [ht]
    exact Multiset.Rel.cons (Setoid.symm (Quotient.exact hcl)) (ih h')

/-- Conjugate multisets have equal sums of induced classes. -/
theorem sum_induced_eq_of_rel [Fintype G] {s t : Multiset (CharPair G A)}
    (h : Multiset.Rel (· ≈ ·) s t) :
    (s.map fun p => Skel.mk (induced p.1 p.2)).sum =
      (t.map fun p => Skel.mk (induced p.1 p.2)).sum := by
  induction h with
  | zero => rfl
  | @cons a b s t hab _ ih =>
    have hab' : Skel.mk (induced a.1 a.2) = Skel.mk (induced b.1 b.2) :=
      Quotient.sound (isIso_induced_of_conjPair hab)
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons,
      ih, hab']

/-- **The free-basis theorem**: sums of induced basis elements agree *iff*
the class multisets agree — `Skel G A` contains the free commutative monoid
on `CharPairClass G A`, faithfully. -/
theorem sum_induced_eq_iff [Fintype G] (s t : Multiset (CharPair G A)) :
    (s.map fun p => Skel.mk (induced p.1 p.2)).sum =
      (t.map fun p => Skel.mk (induced p.1 p.2)).sum ↔
    s.map (fun p => (⟦p⟧ : CharPairClass G A)) =
      t.map (fun p => (⟦p⟧ : CharPairClass G A)) :=
  ⟨Skel.decomposition_unique s t, fun h => sum_induced_eq_of_rel (rel_of_map_class_eq h)⟩

end MonGSet

/-! ## Uniqueness in the D-ring -/

namespace DRing

open MonGSet

variable {G : Type u} [Group G] [Fintype G]

/-- **Uniqueness of the basis expansion in `D(G)`**: two sums of basis
elements that agree have the same multiset of conjugacy classes. With
`exists_basisElt_decomposition` (spanning) and `basisElt_eq_iff`
(distinctness), the classes `⟦(K, λ)⟧` are a free `ℕ`-basis of the monomial
semiring inside `D(G)`; their number is the rank of `D(G)`. -/
theorem basisElt_sum_unique (s t : Multiset (CharPair G ℂˣ))
    (h : (s.map fun p => basisElt p.1 p.2).sum = (t.map fun p => basisElt p.1 p.2).sum) :
    s.map (fun p => (⟦p⟧ : CharPairClass G ℂˣ)) =
      t.map (fun p => (⟦p⟧ : CharPairClass G ℂˣ)) := by
  refine Skel.decomposition_unique s t ?_
  refine GrothendieckRing.of_injective (fun _ _ _ => monSkel_add_cancel) ?_
  have hs : GrothendieckRing.of ((s.map fun p => Skel.mk (induced p.1 p.2)).sum) =
      (s.map fun p => basisElt p.1 p.2).sum := by
    rw [← GrothendieckRing.ofHom_apply, map_multiset_sum GrothendieckRing.ofHom,
      Multiset.map_map]
    rfl
  have ht : GrothendieckRing.of ((t.map fun p => Skel.mk (induced p.1 p.2)).sum) =
      (t.map fun p => basisElt p.1 p.2).sum := by
    rw [← GrothendieckRing.ofHom_apply, map_multiset_sum GrothendieckRing.ofHom,
      Multiset.map_map]
    rfl
  rw [hs, ht, h]

end DRing

end LeanDring
