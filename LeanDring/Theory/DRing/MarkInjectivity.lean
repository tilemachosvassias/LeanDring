/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.Marks

/-!
# Marks determine finite `G`-sets: injectivity of the mark homomorphism

The fundamental theorem of the Burnside ring: a finite `G`-set is determined
up to equivariant isomorphism by its marks `H ↦ |Fix_H(X)|`
(`isIso_of_fix_eq`), hence the mark homomorphism `B(G) → ∏_H ℤ` is injective
(`BurnsideRing.mark_injective`), `⊔` cancels on iso classes, and
`of : Skel G → B(G)` is injective.

The proof is a strong induction on `|X|` that avoids the table-of-marks
triangularity: pick a point `x₀` (of `X ⊔ Y`) whose orbit has **minimal**
cardinality — its stabilizer is then maximal among occurring stabilizers.
`fix (Stab x₀) Y > 0` produces `y` with `Stab y ⊇ Stab x₀`; the canonical
equivariant surjection `orbit x₀ ↠ orbit y` together with minimality forces
equal orbit sizes, hence bijectivity, hence `Stab y = Stab x₀`. The two
orbits are then isomorphic; peel them off and recurse on the complements.
-/

namespace LeanDring

open MulAction

universe u

variable {G : Type u} [Group G]

namespace FinGSet

/-! ## Invariant subsets as `G`-sets -/

/-- A `G`-invariant subset of a finite `G`-set, as a `G`-set. -/
noncomputable def ofInvariant (X : FinGSet G) (S : Set X)
    (hS : ∀ (g : G) (x : X), x ∈ S → g • x ∈ S) : FinGSet G where
  carrier := S
  fintype := Fintype.ofFinite _
  action :=
    { smul := fun g z => ⟨g • z.1, hS g z.1 z.2⟩
      one_smul := fun z => Subtype.ext (one_smul G z.1)
      mul_smul := fun g h z => Subtype.ext (mul_smul g h z.1) }

@[simp] theorem ofInvariant_smul_coe (X : FinGSet G) (S : Set X)
    (hS : ∀ (g : G) (x : X), x ∈ S → g • x ∈ S) (g : G) (z : X.ofInvariant S hS) :
    (g • z).1 = g • z.1 := rfl

/-- Complements of invariant subsets are invariant. -/
theorem compl_invariant (X : FinGSet G) (S : Set X)
    (hS : ∀ (g : G) (x : X), x ∈ S → g • x ∈ S) :
    ∀ (g : G) (x : X), x ∈ Sᶜ → g • x ∈ Sᶜ := by
  intro g x hx hmem
  exact hx (by simpa using hS g⁻¹ (g • x) hmem)

/-- A finite `G`-set splits along any invariant subset. -/
theorem isIso_sum_compl (X : FinGSet G) (S : Set X)
    (hS : ∀ (g : G) (x : X), x ∈ S → g • x ∈ S) :
    IsIso X ((X.ofInvariant S hS).disjUnion
      (X.ofInvariant Sᶜ (compl_invariant X S hS))) := by
  classical
  refine IsIso.symm ⟨⟨Sum.elim Subtype.val Subtype.val,
    fun x => if h : x ∈ S then .inl ⟨x, h⟩ else .inr ⟨x, h⟩, ?_, ?_⟩, ?_⟩
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · simp [hx]
    · simp [(Set.mem_compl_iff S x).mp hx]
  · intro x
    by_cases hx : x ∈ S <;> simp [hx]
  · rintro g (z | z) <;> rfl

/-- Orbits are invariant (any `G`-action). -/
theorem orbit_invariant {α : Type u} [MulAction G α] (x : α) :
    ∀ (g : G) (z : α), z ∈ orbit G x → g • z ∈ orbit G x := by
  intro g z hz
  obtain ⟨g₀, rfl⟩ := mem_orbit_iff.mp hz
  rw [← mul_smul]
  exact mem_orbit x (g * g₀)

/-! ## The canonical map between orbits with nested stabilizers

Stated for bare `MulAction` types so that both plain and monomial `G`-sets
can use it. -/

section OrbitMap

variable {α β : Type u} [MulAction G α] [MulAction G β] {x : α} {y : β}

/-- If `Stab x ≤ Stab y` then `g • x = g' • x` implies `g • y = g' • y`. -/
theorem smul_eq_smul_of_stabilizer_le (hle : stabilizer G x ≤ stabilizer G y)
    {g g' : G} (h : g • x = g' • x) : g • y = g' • y := by
  have hmem : g'⁻¹ * g ∈ stabilizer G x := by
    rw [mem_stabilizer_iff, mul_smul, h, inv_smul_smul]
  have := mem_stabilizer_iff.mp (hle hmem)
  rwa [mul_smul, inv_smul_eq_iff] at this

/-- The canonical map `orbit x → orbit y` for `Stab x ≤ Stab y`:
`g • x ↦ g • y`. -/
noncomputable def orbitMapOfLe (_hle : stabilizer G x ≤ stabilizer G y)
    (z : orbit G x) : orbit G y :=
  ⟨Classical.choose (mem_orbit_iff.mp z.2) • y, mem_orbit y _⟩

theorem orbitMapOfLe_spec (hle : stabilizer G x ≤ stabilizer G y)
    (z : orbit G x) (g : G) (hg : g • x = z.1) :
    (orbitMapOfLe hle z).1 = g • y :=
  smul_eq_smul_of_stabilizer_le hle
    ((Classical.choose_spec (mem_orbit_iff.mp z.2)).trans hg.symm)

theorem orbitMapOfLe_surjective (hle : stabilizer G x ≤ stabilizer G y) :
    Function.Surjective (orbitMapOfLe hle) := by
  intro w
  obtain ⟨g, hg⟩ := mem_orbit_iff.mp w.2
  exact ⟨⟨g • x, mem_orbit x g⟩, Subtype.ext ((orbitMapOfLe_spec hle _ g rfl).trans hg)⟩

/-- If moreover `|orbit x| ≤ |orbit y|`, the stabilizers are equal. This is
the maximality step: the canonical surjection is then a bijection. -/
theorem stabilizer_eq_of_le_of_card_le [Finite α] (hle : stabilizer G x ≤ stabilizer G y)
    (hcard : Nat.card (orbit G x) ≤ Nat.card (orbit G y)) :
    stabilizer G x = stabilizer G y := by
  have hsurj := orbitMapOfLe_surjective hle
  have hbij : Function.Bijective (orbitMapOfLe hle) :=
    (Nat.bijective_iff_surjective_and_card _).mpr
      ⟨hsurj, le_antisymm hcard (Nat.card_le_card_of_surjective _ hsurj)⟩
  refine le_antisymm hle fun k hk => ?_
  have h1 : (orbitMapOfLe hle ⟨k • x, mem_orbit x k⟩).1 = k • y :=
    orbitMapOfLe_spec hle _ k rfl
  have h2 : (orbitMapOfLe hle ⟨x, mem_orbit_self x⟩).1 = (1 : G) • y :=
    orbitMapOfLe_spec hle _ 1 (one_smul G x)
  have heq : orbitMapOfLe hle ⟨k • x, mem_orbit x k⟩ =
      orbitMapOfLe hle ⟨x, mem_orbit_self x⟩ := by
    refine Subtype.ext ?_
    rw [h1, h2, one_smul, mem_stabilizer_iff.mp hk]
  have := hbij.injective heq
  rw [mem_stabilizer_iff]
  exact congrArg Subtype.val this

end OrbitMap

section OrbitIso

variable {X Y : FinGSet G} {x : X} {y : Y}

/-- Orbits of points with equal stabilizers are isomorphic `G`-sets. -/
theorem isIso_orbit_of_stabilizer_eq (h : stabilizer G x = stabilizer G y) :
    IsIso (X.ofInvariant (orbit G x) (orbit_invariant x))
      (Y.ofInvariant (orbit G y) (orbit_invariant y)) := by
  have key : ∀ z : orbit G x, orbitMapOfLe h.ge (orbitMapOfLe h.le z) = z := by
    intro z
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp z.2
    refine Subtype.ext ?_
    rw [orbitMapOfLe_spec h.ge _ g (orbitMapOfLe_spec h.le z g hg.symm.symm).symm, hg]
  have key' : ∀ w : orbit G y, orbitMapOfLe h.le (orbitMapOfLe h.ge w) = w := by
    intro w
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp w.2
    refine Subtype.ext ?_
    rw [orbitMapOfLe_spec h.le _ g (orbitMapOfLe_spec h.ge w g hg.symm.symm).symm, hg]
  refine ⟨⟨orbitMapOfLe h.le, orbitMapOfLe h.ge, key, key'⟩, fun g z => ?_⟩
  -- equivariance: `g • x`-translates map to `g • y`-translates
  obtain ⟨g₀, hg₀⟩ := mem_orbit_iff.mp z.2
  refine Subtype.ext ?_
  have h1 : (orbitMapOfLe h.le (g • z)).1 = (g * g₀) • y :=
    orbitMapOfLe_spec h.le (g • z) (g * g₀)
      (show (g * g₀) • x = g • z.1 by rw [mul_smul, hg₀])
  have h2 : (orbitMapOfLe h.le z).1 = g₀ • y := orbitMapOfLe_spec h.le z g₀ hg₀
  exact h1.trans ((mul_smul g g₀ y).trans (congrArg (g • ·) h2.symm))

end OrbitIso

/-! ## The matching step -/

/-- If all marks agree and `x₀ : X` has minimal orbit size among the points
of both `X` and `Y`, then `Y` has a point with the *same* stabilizer. -/
theorem exists_matched_point {X Y : FinGSet G}
    (h : ∀ H : Subgroup G, fix H X = fix H Y) (x₀ : X)
    (hminY : ∀ y : Y, Nat.card (orbit G x₀) ≤ Nat.card (orbit G y)) :
    ∃ y : Y, stabilizer G x₀ = stabilizer G y := by
  set H := stabilizer G x₀ with hH
  -- `x₀` is an `H`-fixed point, so `fix H X > 0`, so `fix H Y > 0`
  have hne : (fixedPoints H X.carrier).Nonempty :=
    ⟨x₀, fun m => mem_stabilizer_iff.mp m.2⟩
  have hpos : 0 < fix H X := by
    have : Nonempty (fixedPoints H X.carrier) := hne.to_subtype
    exact Nat.card_pos
  have hposY : 0 < fix H Y := h H ▸ hpos
  have : Nonempty (fixedPoints H Y.carrier) :=
    (Nat.card_ne_zero.mp (Nat.pos_iff_ne_zero.mp hposY)).1
  obtain ⟨y, hy⟩ := this
  have hle : H ≤ stabilizer G y := fun k hk => mem_stabilizer_iff.mpr (hy ⟨k, hk⟩)
  exact ⟨y, stabilizer_eq_of_le_of_card_le hle (hminY y)⟩

/-! ## The main induction -/

theorem isIso_of_isEmpty {X Y : FinGSet G} (hX : Fintype.card X = 0)
    (hY : Fintype.card Y = 0) : IsIso X Y := by
  have : IsEmpty X.carrier := Fintype.card_eq_zero_iff.mp hX
  have : IsEmpty Y.carrier := Fintype.card_eq_zero_iff.mp hY
  exact ⟨Equiv.equivOfIsEmpty _ _, fun g x => isEmptyElim x⟩

/-- **Marks determine finite `G`-sets** (bounded-cardinality induction). -/
theorem isIso_of_fix_eq_aux :
    ∀ (n : ℕ) (X Y : FinGSet G), Fintype.card X ≤ n →
      (∀ H : Subgroup G, fix H X = fix H Y) → IsIso X Y := by
  intro n
  induction n with
  | zero =>
    intro X Y hle h
    refine isIso_of_isEmpty (Nat.le_zero.mp hle) ?_
    have := h ⊥
    rw [fix_bot, fix_bot] at this
    omega
  | succ n ih =>
    intro X Y hle h
    have hcards : Fintype.card X = Fintype.card Y := by
      have := h ⊥
      rwa [fix_bot, fix_bot] at this
    by_cases hX : Fintype.card X = 0
    · exact isIso_of_isEmpty hX (hcards ▸ hX)
    -- both nonempty: pick a global minimal-orbit point
    have hneX : Nonempty X.carrier := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hX)
    have hneY : Nonempty Y.carrier := by
      rw [hcards] at hX
      exact Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hX)
    obtain ⟨p, -, hp⟩ := Finset.exists_min_image Finset.univ
      (Sum.elim (fun x : X => Nat.card (orbit G x)) (fun y : Y => Nat.card (orbit G y)))
      Finset.univ_nonempty
    -- extract a matched pair (x₀, y₀) with equal stabilizers
    obtain ⟨x₀, y₀, hstab⟩ :
        ∃ (x₀ : X) (y₀ : Y), stabilizer G x₀ = stabilizer G y₀ := by
      rcases p with x₀ | y₀
      · obtain ⟨y₀, hy₀⟩ := exists_matched_point h x₀
          (fun y => hp (.inr y) (Finset.mem_univ _))
        exact ⟨x₀, y₀, hy₀⟩
      · obtain ⟨x₀, hx₀⟩ := exists_matched_point (fun H => (h H).symm) y₀
          (fun x => hp (.inl x) (Finset.mem_univ _))
        exact ⟨x₀, y₀, hx₀.symm⟩
    -- peel off the matched orbits
    set OX := X.ofInvariant (orbit G x₀) (orbit_invariant x₀) with hOX
    set OY := Y.ofInvariant (orbit G y₀) (orbit_invariant y₀) with hOY
    set CX := X.ofInvariant (orbit G x₀)ᶜ
      (fun g x hx hmem => hx (by simpa using orbit_invariant x₀ g⁻¹ _ hmem)) with hCX
    set CY := Y.ofInvariant (orbit G y₀)ᶜ
      (fun g y hy hmem => hy (by simpa using orbit_invariant y₀ g⁻¹ _ hmem)) with hCY
    have hdX : IsIso X (OX.disjUnion CX) := isIso_sum_compl X _ _
    have hdY : IsIso Y (OY.disjUnion CY) := isIso_sum_compl Y _ _
    have hOrb : IsIso OX OY := isIso_orbit_of_stabilizer_eq hstab
    -- marks of the complements agree
    have hcompl_marks : ∀ H : Subgroup G, fix H CX = fix H CY := by
      intro H
      have e1 : fix H X = fix H OX + fix H CX := by
        rw [fix_congr H hdX, fix_disjUnion]
      have e2 : fix H Y = fix H OY + fix H CY := by
        rw [fix_congr H hdY, fix_disjUnion]
      have e3 : fix H OX = fix H OY := fix_congr H hOrb
      have := h H
      omega
    -- cardinality drops: the orbit of `x₀` is nonempty
    have hcard_orb : 0 < Fintype.card OX :=
      Fintype.card_pos_iff.mpr ⟨⟨x₀, mem_orbit_self x₀⟩⟩
    have hcard_le : Fintype.card CX ≤ n := by
      have e1 : fix ⊥ X = fix ⊥ OX + fix ⊥ CX := by
        rw [fix_congr ⊥ hdX, fix_disjUnion]
      rw [fix_bot, fix_bot, fix_bot] at e1
      omega
    exact hdX.trans ((disjUnion_congr hOrb (ih CX CY hcard_le hcompl_marks)).trans hdY.symm)

/-- **Marks determine finite `G`-sets**: if `|Fix_H X| = |Fix_H Y|` for every
subgroup `H ≤ G`, then `X ≅ Y` equivariantly. -/
theorem isIso_of_fix_eq {X Y : FinGSet G}
    (h : ∀ H : Subgroup G, fix H X = fix H Y) : IsIso X Y :=
  isIso_of_fix_eq_aux (Fintype.card X) X Y le_rfl h

/-! ## Corollaries: the sorried statements, now proven -/

namespace Skel

/-- **Burnside/Dress**: a finite `G`-set is determined up to iso by its
marks — injectivity of the table of marks. -/
theorem mark_injective :
    Function.Injective (fun a : Skel G => fun H : Subgroup G => mark H a) := by
  intro a b h
  obtain ⟨X⟩ := a
  obtain ⟨Y⟩ := b
  exact Quotient.sound (isIso_of_fix_eq fun H => congrFun h H)

/-- Cancellativity of `⊔` on iso classes. -/
theorem add_cancel_of_marks {a b c : Skel G} (h : a + c = b + c) : a = b := by
  apply mark_injective
  funext H
  change mark H a = mark H b
  have hm := congrArg (mark H) h
  simp only [mark_add] at hm
  omega

end Skel

end FinGSet

namespace BurnsideRing

open FinGSet

/-- `[X] = [Y]` in `B(G)` iff `X ≅ Y` — `of : Skel G → B(G)` is injective. -/
theorem of_injective : Function.Injective (of : Skel G → BurnsideRing G) :=
  GrothendieckRing.of_injective fun _ _ _ h => Skel.add_cancel_of_marks h

/-- **The mark homomorphism is injective**: `B(G) ↪ ∏_H ℤ` — the fundamental
theorem of the Burnside ring. -/
theorem mark_injective :
    Function.Injective (fun x : BurnsideRing G => fun H : Subgroup G => mark H x) := by
  intro a b
  obtain ⟨p⟩ := a
  obtain ⟨q⟩ := b
  intro h
  refine Quotient.sound ⟨0, ?_⟩
  apply Skel.mark_injective
  funext H
  have hH := congrFun h H
  change (Skel.mark H p.1 : ℤ) - Skel.mark H p.2 =
    (Skel.mark H q.1 : ℤ) - Skel.mark H q.2 at hH
  change Skel.mark H (p.1 + q.2 + 0) = Skel.mark H (q.1 + p.2 + 0)
  simp only [Skel.mark_add, Skel.mark_zero]
  omega

end BurnsideRing

end LeanDring
