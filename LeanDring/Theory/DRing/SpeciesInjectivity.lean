/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.Species
import LeanDring.Theory.DRing.MarkInjectivity
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# The species table is a complete invariant: injectivity of species

The D-ring analogue of `MarkInjectivity`: a monomial `G`-set over `ℂˣ` is
determined up to isomorphism by its species `(H, h) ↦ φ_{H,h}`
(`MonGSet.isIso_of_speciesSum_eq`), hence the total species map
`D(G) → ∏_{(H,h)} ℂ` is injective (`DRing.species_injective`) — Müller's
ghost-ring embedding, the statement that the *species table* determines the
class of an element of the monomial representation ring.

Proof: the minimal-orbit matching induction of `MarkInjectivity`, refined by
**Dedekind's linear independence of characters**: at a subgroup `H`, the
species values over all `h ∈ H` determine the multiset of characters
`fixedWeight : H →* ℂˣ` carried by the `H`-fixed points
(`count_eq_of_sum_eq`). The matched point of `Y` can therefore be
chosen with the *same* stabilizer **and the same character** as the
minimal-orbit point `x₀` of `X`; the two monomial orbits are then
isomorphic via the canonical orbit map with the gauge
`φ(g • x₀) = μ_Y(g, y) · μ_X(g, x₀)⁻¹` (well-defined precisely because the
characters agree on the common stabilizer). Peel and recurse.
-/

namespace LeanDring

open MulAction Finset

universe u v

variable {G : Type u} [Group G]

/-! ## Dedekind counting: equal power sums ⇒ equal character multiplicities -/

section CharCount

variable {M : Type*} [Group M]

/-- A `ℂˣ`-valued character as a `ℂ`-valued monoid homomorphism. -/
def unitsCharToC (l : M →* ℂˣ) : M →* ℂ := (Units.coeHom ℂ).comp l

theorem unitsCharToC_injective : Function.Injective (unitsCharToC (M := M)) := by
  intro a b hab
  ext m
  exact DFunLike.congr_fun hab m

/-- **Dedekind counting.** If two finite families of `ℂˣ`-characters of `M`
have equal value-sums at every `m : M`, then every character occurs in both
families with the same multiplicity. -/
theorem count_eq_of_sum_eq {F₁ F₂ : Type*} [Fintype F₁] [Fintype F₂]
    [DecidableEq (M →* ℂˣ)]
    (w₁ : F₁ → (M →* ℂˣ)) (w₂ : F₂ → (M →* ℂˣ))
    (h : ∀ m : M, ∑ x, ((w₁ x m : ℂˣ) : ℂ) = ∑ y, ((w₂ y m : ℂˣ) : ℂ))
    (l : M →* ℂˣ) :
    (univ.filter fun x => w₁ x = l).card = (univ.filter fun y => w₂ y = l).card := by
  classical
  set u₁ : F₁ → (M →* ℂ) := fun x => unitsCharToC (w₁ x) with hu₁
  set u₂ : F₂ → (M →* ℂ) := fun y => unitsCharToC (w₂ y) with hu₂
  set S : Finset (M →* ℂ) := univ.image u₁ ∪ univ.image u₂ with hS
  -- the two total sums agree as functions `M → ℂ`
  have hsum : ∑ x, ((u₁ x : M → ℂ)) = ∑ y, ((u₂ y : M → ℂ)) := by
    funext m
    simpa [Finset.sum_apply, hu₁, hu₂, unitsCharToC] using h m
  -- group each total sum by character
  have hkey₁ : ∑ j ∈ S, (univ.filter fun x => u₁ x = j).card • (j : M → ℂ) =
      ∑ x, ((u₁ x : M → ℂ)) := by
    rw [← Finset.sum_fiberwise_of_maps_to'
      (fun x _ => Finset.mem_union_left _ (mem_image_of_mem u₁ (mem_univ x)))
      (fun j : M →* ℂ => (j : M → ℂ))]
    exact Finset.sum_congr rfl fun j _ => (Finset.sum_const _).symm
  have hkey₂ : ∑ j ∈ S, (univ.filter fun y => u₂ y = j).card • (j : M → ℂ) =
      ∑ y, ((u₂ y : M → ℂ)) := by
    rw [← Finset.sum_fiberwise_of_maps_to'
      (fun y _ => Finset.mem_union_right _ (mem_image_of_mem u₂ (mem_univ y)))
      (fun j : M →* ℂ => (j : M → ℂ))]
    exact Finset.sum_congr rfl fun j _ => (Finset.sum_const _).symm
  -- linear independence of characters kills the difference coefficients
  have hzero : ∀ j ∈ S,
      (((univ.filter fun x => u₁ x = j).card : ℂ) -
        ((univ.filter fun y => u₂ y = j).card : ℂ)) = 0 := by
    refine linearIndependent_iff'.mp (linearIndependent_monoidHom M ℂ) S
      (fun j => ((univ.filter fun x => u₁ x = j).card : ℂ) -
        ((univ.filter fun y => u₂ y = j).card : ℂ)) ?_
    have : ∑ j ∈ S,
        ((((univ.filter fun x => u₁ x = j).card : ℂ) -
          ((univ.filter fun y => u₂ y = j).card : ℂ)) • (j : M → ℂ)) =
        (∑ j ∈ S, (univ.filter fun x => u₁ x = j).card • (j : M → ℂ)) -
        (∑ j ∈ S, (univ.filter fun y => u₂ y = j).card • (j : M → ℂ)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [sub_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    rw [this, hkey₁, hkey₂, hsum, sub_self]
  -- transfer back through the injective coercion
  have hfilter₁ : (univ.filter fun x => w₁ x = l) =
      (univ.filter fun x => u₁ x = unitsCharToC l) := by
    refine Finset.filter_congr fun x _ => ?_
    exact ⟨fun hx => by rw [hu₁]; exact congrArg unitsCharToC hx,
      fun hx => unitsCharToC_injective hx⟩
  have hfilter₂ : (univ.filter fun y => w₂ y = l) =
      (univ.filter fun y => u₂ y = unitsCharToC l) := by
    refine Finset.filter_congr fun y _ => ?_
    exact ⟨fun hy => by rw [hu₂]; exact congrArg unitsCharToC hy,
      fun hy => unitsCharToC_injective hy⟩
  rw [hfilter₁, hfilter₂]
  by_cases hmem : unitsCharToC l ∈ S
  · have hcast : ((univ.filter fun x => u₁ x = unitsCharToC l).card : ℂ) =
        ((univ.filter fun y => u₂ y = unitsCharToC l).card : ℂ) :=
      sub_eq_zero.mp (hzero _ hmem)
    exact_mod_cast hcast
  · -- the character occurs in neither family
    have h1 : (univ.filter fun x => u₁ x = unitsCharToC l) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun x _ hx => ?_
      exact hmem (Finset.mem_union_left _ (hx ▸ mem_image_of_mem u₁ (mem_univ x)))
    have h2 : (univ.filter fun y => u₂ y = unitsCharToC l) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun y _ hy => ?_
      exact hmem (Finset.mem_union_right _ (hy ▸ mem_image_of_mem u₂ (mem_univ y)))
    rw [h1, h2]
    rfl

end CharCount

namespace MonGSet

variable {A : Type v} [CommGroup A]

/-! ## Invariant subsets of monomial `G`-sets -/

/-- A `G`-invariant subset of a monomial `G`-set, with restricted weights. -/
noncomputable def ofInvariant (X : MonGSet G A) (S : Set X.carrier)
    (hS : ∀ (g : G) (x : X.carrier), x ∈ S → g • x ∈ S) : MonGSet G A where
  carrier := S
  fintype := Fintype.ofFinite _
  action :=
    { smul := fun g z => ⟨g • z.1, hS g z.1 z.2⟩
      one_smul := fun z => Subtype.ext (one_smul G z.1)
      mul_smul := fun g h z => Subtype.ext (mul_smul g h z.1) }
  weight := fun g z => X.weight g z.1
  weight_mul := fun g h z => X.weight_mul g h z.1

/-- Complements of invariant subsets are invariant. -/
theorem compl_invariant (X : MonGSet G A) (S : Set X.carrier)
    (hS : ∀ (g : G) (x : X.carrier), x ∈ S → g • x ∈ S) :
    ∀ (g : G) (x : X.carrier), x ∈ Sᶜ → g • x ∈ Sᶜ := by
  intro g x hx hmem
  exact hx (by simpa using hS g⁻¹ (g • x) hmem)

/-- A monomial `G`-set splits along any invariant subset. -/
theorem isIso_sum_compl (X : MonGSet G A) (S : Set X.carrier)
    (hS : ∀ (g : G) (x : X.carrier), x ∈ S → g • x ∈ S) :
    IsIso X ((X.ofInvariant S hS).disjUnion
      (X.ofInvariant Sᶜ (compl_invariant X S hS))) := by
  classical
  refine IsIso.symm (isIso_of_weight_eq
    ⟨Sum.elim Subtype.val Subtype.val,
      fun x => if h : x ∈ S then .inl ⟨x, h⟩ else .inr ⟨x, h⟩, ?_, ?_⟩
    (by rintro g (z | z) <;> rfl)
    (by rintro g (z | z) <;> rfl))
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · simp [hx]
    · simp [(Set.mem_compl_iff S x).mp hx]
  · intro x
    by_cases hx : x ∈ S <;> simp [hx]

/-! ## The gauge orbit isomorphism for matched pairs -/

section GaugeOrbit

variable {X Y : MonGSet G A} {x : X.carrier} {y : Y.carrier}

/-- The gauge ratio `μ_Y(g, y) · μ_X(g, x)⁻¹` is independent of the chosen
representative `g` of an orbit point — precisely because the two weights
restrict to the *same* character on the common stabilizer. -/
theorem gauge_well_defined (hstab : stabilizer G x = stabilizer G y)
    (hchar : ∀ k ∈ stabilizer G x, X.weight k x = Y.weight k y)
    {g g' : G} (h : g • x = g' • x) :
    Y.weight g y * (X.weight g x)⁻¹ = Y.weight g' y * (X.weight g' x)⁻¹ := by
  have hk : g'⁻¹ * g ∈ stabilizer G x := by
    rw [mem_stabilizer_iff, mul_smul, h, inv_smul_smul]
  have hg : g = g' * (g'⁻¹ * g) := by group
  have hXsplit : X.weight g x = X.weight g' x * X.weight (g'⁻¹ * g) x := by
    conv_lhs => rw [hg]
    rw [X.weight_mul, mem_stabilizer_iff.mp hk]
  have hYsplit : Y.weight g y = Y.weight g' y * Y.weight (g'⁻¹ * g) y := by
    conv_lhs => rw [hg]
    rw [Y.weight_mul, mem_stabilizer_iff.mp (hstab ▸ hk)]
  rw [hXsplit, hYsplit, ← hchar _ hk]
  group

/-- **The matched-orbit isomorphism**: points with equal stabilizers *and*
equal characters on the stabilizer have isomorphic monomial orbits, via the
canonical orbit map with gauge `φ(g • x) = μ_Y(g, y) · μ_X(g, x)⁻¹`. -/
theorem isIso_orbit_matched (hstab : stabilizer G x = stabilizer G y)
    (hchar : ∀ k ∈ stabilizer G x, X.weight k x = Y.weight k y) :
    IsIso (X.ofInvariant (orbit G x) (FinGSet.orbit_invariant x))
      (Y.ofInvariant (orbit G y) (FinGSet.orbit_invariant y)) := by
  -- the underlying equivariant bijection (from the marks development)
  have key : ∀ z : orbit G x,
      FinGSet.orbitMapOfLe hstab.ge (FinGSet.orbitMapOfLe hstab.le z) = z := by
    intro z
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp z.2
    refine Subtype.ext ?_
    rw [FinGSet.orbitMapOfLe_spec hstab.ge _ g
      (FinGSet.orbitMapOfLe_spec hstab.le z g hg).symm, hg]
  have key' : ∀ w : orbit G y,
      FinGSet.orbitMapOfLe hstab.le (FinGSet.orbitMapOfLe hstab.ge w) = w := by
    intro w
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp w.2
    refine Subtype.ext ?_
    rw [FinGSet.orbitMapOfLe_spec hstab.le _ g
      (FinGSet.orbitMapOfLe_spec hstab.ge w g hg).symm, hg]
  -- the gauge
  set φ : orbit G x → A :=
    fun z => Y.weight (Classical.choose (mem_orbit_iff.mp z.2)) y *
      (X.weight (Classical.choose (mem_orbit_iff.mp z.2)) x)⁻¹ with hφ
  have φspec : ∀ (z : orbit G x) (g : G), g • x = z.1 →
      φ z = Y.weight g y * (X.weight g x)⁻¹ := fun z g hg =>
    gauge_well_defined hstab hchar
      ((Classical.choose_spec (mem_orbit_iff.mp z.2)).trans hg.symm)
  refine ⟨⟨FinGSet.orbitMapOfLe hstab.le, FinGSet.orbitMapOfLe hstab.ge, key, key'⟩,
    φ, fun g z => ?_, fun g' z => ?_⟩
  · -- equivariance
    obtain ⟨g₀, hg₀⟩ := mem_orbit_iff.mp z.2
    refine Subtype.ext ?_
    have h1 : (FinGSet.orbitMapOfLe hstab.le (g • z)).1 = (g * g₀) • y :=
      FinGSet.orbitMapOfLe_spec hstab.le (g • z) (g * g₀)
        (show (g * g₀) • x = g • z.1 by rw [mul_smul, hg₀])
    have h2 : (FinGSet.orbitMapOfLe hstab.le z).1 = g₀ • y :=
      FinGSet.orbitMapOfLe_spec hstab.le z g₀ hg₀
    exact h1.trans ((mul_smul g g₀ y).trans (congrArg (g • ·) h2.symm))
  · -- the weight-gauge relation
    obtain ⟨g₀, hg₀⟩ := mem_orbit_iff.mp z.2
    have h1 : (FinGSet.orbitMapOfLe hstab.le z).1 = g₀ • y :=
      FinGSet.orbitMapOfLe_spec hstab.le z g₀ hg₀
    have h2 : φ z = Y.weight g₀ y * (X.weight g₀ x)⁻¹ := φspec z g₀ hg₀
    have h3 : φ (g' • z) = Y.weight (g' * g₀) y * (X.weight (g' * g₀) x)⁻¹ :=
      φspec (g' • z) (g' * g₀) (show (g' * g₀) • x = g' • z.1 by rw [mul_smul, hg₀])
    change Y.weight g' (FinGSet.orbitMapOfLe hstab.le z).1 * φ z =
      φ (g' • z) * X.weight g' z.1
    rw [h1, h2, h3, show z.1 = g₀ • x from hg₀.symm,
      Y.weight_mul g' g₀ y, X.weight_mul g' g₀ x]
    group

end GaugeOrbit

/-! ## The matching step, refined by characters -/

/-- If all species agree and `x₀` has minimal orbit size among the points of
both `X` and `Y`, then `Y` has a point with the same stabilizer *and* the
same character on it. -/
theorem exists_matched_point_mon {X Y : MonGSet G ℂˣ}
    (h : ∀ (H : Subgroup G) (m : H),
      speciesSum (Units.coeHom ℂ) H m X = speciesSum (Units.coeHom ℂ) H m Y)
    (x₀ : X.carrier)
    (hminY : ∀ y : Y.carrier, Nat.card (orbit G x₀) ≤ Nat.card (orbit G y)) :
    ∃ y : Y.carrier, stabilizer G x₀ = stabilizer G y ∧
      ∀ k ∈ stabilizer G x₀, X.weight k x₀ = Y.weight k y := by
  classical
  have hx₀fix : x₀ ∈ fixedPoints (stabilizer G x₀) X.carrier :=
    fun m => mem_stabilizer_iff.mp m.2
  -- Dedekind counting at H := Stab x₀ produces a point of `Y` with the
  -- character of `x₀`
  have hcount := count_eq_of_sum_eq
    (X.fixedWeight (stabilizer G x₀)) (Y.fixedWeight (stabilizer G x₀))
    (fun m => h (stabilizer G x₀) m)
    (X.fixedWeight (stabilizer G x₀) ⟨x₀, hx₀fix⟩)
  have hpos : 0 < (univ.filter fun x =>
      X.fixedWeight (stabilizer G x₀) x =
        X.fixedWeight (stabilizer G x₀) ⟨x₀, hx₀fix⟩).card :=
    Finset.card_pos.mpr ⟨⟨x₀, hx₀fix⟩, by simp⟩
  rw [hcount] at hpos
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
  have hychar := (Finset.mem_filter.mp hy).2
  -- stabilizer containment and the minimality squeeze
  have hle : stabilizer G x₀ ≤ stabilizer G y.1 :=
    fun k hk => mem_stabilizer_iff.mpr (y.2 ⟨k, hk⟩)
  have hstab : stabilizer G x₀ = stabilizer G y.1 :=
    FinGSet.stabilizer_eq_of_le_of_card_le hle (hminY y.1)
  refine ⟨y.1, hstab, fun k hk => ?_⟩
  exact (DFunLike.congr_fun hychar ⟨k, hk⟩).symm

/-! ## Base facts -/

/-- The species at `(⊥, 1)` is the cardinality. -/
theorem speciesSum_bot_one (X : MonGSet G ℂˣ) :
    speciesSum (Units.coeHom ℂ) ⊥ 1 X = (Fintype.card X.carrier : ℂ) := by
  have huniv : fixedPoints (⊥ : Subgroup G) X.carrier = Set.univ := by
    ext z
    simp only [mem_fixedPoints, Set.mem_univ, iff_true]
    rintro ⟨k, hk⟩
    obtain rfl : k = 1 := hk
    exact one_smul G z
  have hone : ∀ x : fixedPoints (⊥ : Subgroup G) X.carrier,
      (Units.coeHom ℂ) ((X.fixedWeight ⊥ x) 1) = 1 := fun x => by
    rw [map_one, map_one]
  rw [speciesSum, Finset.sum_congr rfl fun x _ => hone x, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  congr 1
  rw [← Nat.card_eq_fintype_card, huniv, Nat.card_congr (Equiv.Set.univ _),
    Nat.card_eq_fintype_card]

/-- Empty monomial `G`-sets are isomorphic. -/
theorem isIso_of_isEmpty {X Y : MonGSet G A} (hX : Fintype.card X.carrier = 0)
    (hY : Fintype.card Y.carrier = 0) : IsIso X Y := by
  have : IsEmpty X.carrier := Fintype.card_eq_zero_iff.mp hX
  have : IsEmpty Y.carrier := Fintype.card_eq_zero_iff.mp hY
  exact ⟨Equiv.equivOfIsEmpty _ _, fun _ => 1, fun g z => isEmptyElim z,
    fun g z => isEmptyElim z⟩

/-! ## The main induction -/

/-- **Species determine monomial `G`-sets** (bounded-cardinality induction). -/
theorem isIso_of_speciesSum_eq_aux :
    ∀ (n : ℕ) (X Y : MonGSet G ℂˣ), Fintype.card X.carrier ≤ n →
      (∀ (H : Subgroup G) (m : H),
        speciesSum (Units.coeHom ℂ) H m X = speciesSum (Units.coeHom ℂ) H m Y) →
      IsIso X Y := by
  intro n
  induction n with
  | zero =>
    intro X Y hle h
    have hcards : (Fintype.card X.carrier : ℂ) = (Fintype.card Y.carrier : ℂ) := by
      rw [← speciesSum_bot_one, ← speciesSum_bot_one]
      exact h ⊥ 1
    have hcards' : Fintype.card X.carrier = Fintype.card Y.carrier :=
      Nat.cast_injective hcards
    exact isIso_of_isEmpty (Nat.le_zero.mp hle) (hcards' ▸ Nat.le_zero.mp hle)
  | succ n ih =>
    intro X Y hle h
    have hcards : Fintype.card X.carrier = Fintype.card Y.carrier := by
      refine Nat.cast_injective (R := ℂ) ?_
      rw [← speciesSum_bot_one, ← speciesSum_bot_one]
      exact h ⊥ 1
    by_cases hX : Fintype.card X.carrier = 0
    · exact isIso_of_isEmpty hX (hcards ▸ hX)
    -- both nonempty: pick a global minimal-orbit point
    have hneX : Nonempty X.carrier := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hX)
    have hneY : Nonempty Y.carrier := by
      rw [hcards] at hX
      exact Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hX)
    obtain ⟨p, -, hp⟩ := Finset.exists_min_image Finset.univ
      (Sum.elim (fun x : X.carrier => Nat.card (orbit G x))
        (fun y : Y.carrier => Nat.card (orbit G y)))
      Finset.univ_nonempty
    -- extract a matched pair with equal stabilizers and equal characters
    obtain ⟨x₀, y₀, hstab, hchar⟩ :
        ∃ (x₀ : X.carrier) (y₀ : Y.carrier),
          stabilizer G x₀ = stabilizer G y₀ ∧
            ∀ k ∈ stabilizer G x₀, X.weight k x₀ = Y.weight k y₀ := by
      rcases p with x₀ | y₀
      · obtain ⟨y₀, hy₀, hy₀c⟩ := exists_matched_point_mon h x₀
          (fun y => hp (.inr y) (Finset.mem_univ _))
        exact ⟨x₀, y₀, hy₀, hy₀c⟩
      · obtain ⟨x₀, hx₀, hx₀c⟩ := exists_matched_point_mon
          (fun H m => (h H m).symm) y₀ (fun x => hp (.inl x) (Finset.mem_univ _))
        exact ⟨x₀, y₀, hx₀.symm, fun k hk =>
          (hx₀c k (hx₀ ▸ hk)).symm⟩
    -- peel off the matched orbits
    set OX := X.ofInvariant (orbit G x₀) (FinGSet.orbit_invariant x₀) with hOX
    set OY := Y.ofInvariant (orbit G y₀) (FinGSet.orbit_invariant y₀) with hOY
    set CX := X.ofInvariant (orbit G x₀)ᶜ
      (compl_invariant X _ (FinGSet.orbit_invariant x₀)) with hCX
    set CY := Y.ofInvariant (orbit G y₀)ᶜ
      (compl_invariant Y _ (FinGSet.orbit_invariant y₀)) with hCY
    have hdX : IsIso X (OX.disjUnion CX) := isIso_sum_compl X _ _
    have hdY : IsIso Y (OY.disjUnion CY) := isIso_sum_compl Y _ _
    have hOrb : IsIso OX OY := isIso_orbit_matched hstab hchar
    -- species of the complements agree
    have hcompl : ∀ (H : Subgroup G) (m : H),
        speciesSum (Units.coeHom ℂ) H m CX = speciesSum (Units.coeHom ℂ) H m CY := by
      intro H m
      have e1 : speciesSum (Units.coeHom ℂ) H m X =
          speciesSum (Units.coeHom ℂ) H m OX + speciesSum (Units.coeHom ℂ) H m CX := by
        rw [speciesSum_congr _ H m hdX, speciesSum_disjUnion]
      have e2 : speciesSum (Units.coeHom ℂ) H m Y =
          speciesSum (Units.coeHom ℂ) H m OY + speciesSum (Units.coeHom ℂ) H m CY := by
        rw [speciesSum_congr _ H m hdY, speciesSum_disjUnion]
      have e3 : speciesSum (Units.coeHom ℂ) H m OX =
          speciesSum (Units.coeHom ℂ) H m OY := speciesSum_congr _ H m hOrb
      have := h H m
      rw [e1, e2, e3] at this
      exact add_left_cancel this
    -- cardinality drops
    have hcard_split : Fintype.card X.carrier =
        Fintype.card OX.carrier + Fintype.card CX.carrier := by
      obtain ⟨e, -⟩ := hdX
      rw [Fintype.card_congr e]
      exact Fintype.card_sum
    have hcard_orb : 0 < Fintype.card OX.carrier :=
      Fintype.card_pos_iff.mpr ⟨⟨x₀, mem_orbit_self x₀⟩⟩
    have hcard_le : Fintype.card CX.carrier ≤ n := by omega
    exact hdX.trans ((disjUnion_congr hOrb (ih CX CY hcard_le hcompl)).trans hdY.symm)

/-- **Species determine monomial `G`-sets**: if all species values agree,
the monomial `G`-sets are isomorphic. -/
theorem isIso_of_speciesSum_eq {X Y : MonGSet G ℂˣ}
    (h : ∀ (H : Subgroup G) (m : H),
      speciesSum (Units.coeHom ℂ) H m X = speciesSum (Units.coeHom ℂ) H m Y) :
    IsIso X Y :=
  isIso_of_speciesSum_eq_aux (Fintype.card X.carrier) X Y le_rfl h

/-- Species separate iso classes of monomial `G`-sets. -/
theorem Skel.species_injective :
    Function.Injective (fun a : Skel G ℂˣ => fun (H : Subgroup G) (m : H) =>
      MonRing.speciesHom (Units.coeHom ℂ) H m a) := by
  intro a b hab
  obtain ⟨X⟩ := a
  obtain ⟨Y⟩ := b
  exact Quotient.sound (isIso_of_speciesSum_eq fun H m =>
    congrFun (congrFun hab H) m)

end MonGSet

/-! ## The headline: the species table determines `D(G)`-elements -/

namespace DRing

open MonGSet

/-- **The species table is a complete invariant**: the total species map
`D(G) → ∏_{(H, h)} ℂ` is injective (Müller's ghost-ring embedding). -/
theorem species_injective :
    Function.Injective (fun x : DRing G => fun (H : Subgroup G) (m : H) =>
      species H m x) := by
  intro a b hab
  obtain ⟨p⟩ := a
  obtain ⟨q⟩ := b
  refine Quotient.sound ⟨0, ?_⟩
  apply MonGSet.Skel.species_injective
  funext H m
  have hH := congrFun (congrFun hab H) m
  change (MonRing.speciesHom (Units.coeHom ℂ) H m p.1 : ℂ) -
      MonRing.speciesHom (Units.coeHom ℂ) H m p.2 =
    (MonRing.speciesHom (Units.coeHom ℂ) H m q.1 : ℂ) -
      MonRing.speciesHom (Units.coeHom ℂ) H m q.2 at hH
  change MonRing.speciesHom (Units.coeHom ℂ) H m (p.1 + q.2 + 0) =
    MonRing.speciesHom (Units.coeHom ℂ) H m (q.1 + p.2 + 0)
  simp only [map_add, add_zero]
  linear_combination hH

end DRing

end LeanDring
