/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Even.OrderTransfer

/-!
# `MullerTrivialBound`, proven: Burnside triangularity at the trivial pair

**EVEN-ORDER LAYER.** Inside the root module's build closure and audit:
no `sorry`, three standard axioms. The results here are
verified *implications*; their hypotheses are named `Prop`s (see §7.6 of
the paper).

This file proves `MullerTrivialBound` (`mullerTrivialBound`), the second
of the two halves `LeanDring/Even/OrderTransfer.lean` states as hypotheses, so that
`mullerOrder (D(G)) = |G|` and `OrderTransfer` are conditional on
`MullerIsolation` alone.

The route:

1. `regularGSet G` — the regular `G`-set; its marks are `|G|` at `⊥` and
   `0` at every nontrivial subgroup (`fix_regularGSet_of_ne_bot`);
2. `dvd_card_sub_card_of_fix_eq` — **the triangularity lemma**: if two
   finite `G`-sets have equal marks at every *nontrivial* subgroup then
   `|G|` divides the difference of their cardinalities.  Proof: a peel
   induction on `|X| + |Y|`.  Either some point (of `X` or `Y`) has a
   nontrivial stabilizer — then a globally minimal such orbit is matched
   across the two sides by `FinGSet.stabilizer_eq_of_le_of_card_le` and
   peeled off, leaving the difference unchanged — or all stabilizers are
   trivial, and peeling one free orbit changes the difference by exactly
   `|G|`.  (This is Burnside triangularity without a basis: the corpus
   has no `[G/H]`-basis of `B(G)`, only `MarkInjectivity`, whose
   minimal-orbit induction is reused here.)
3. `dvd_mark_bot_of_mark_eq_zero` — the same statement in `B(G)`: an
   element whose marks vanish at every nontrivial subgroup has `⊥`-mark
   divisible by `|G|`;
4. `species_ne_complexify_trivialPoint` — the trivial species
   `φ_{⊥,1} = mark_⊥ ∘ forget` is separated from every `φ_{H,1}`,
   `H ≠ ⊥`, by the class of the regular `G`-set;
5. `mullerTrivialBound` — **[PROVEN]** and its corollaries
   `mullerOrder_dring_eq_card_of_isolation`,
   `orderTransfer_of_mullerIsolation`.
-/

set_option linter.unusedFintypeInType false

namespace LeanDring

namespace Even

open MulAction FinGSet MonRing DRing

universe u

/-! ## The regular `G`-set -/

section Regular

variable (G : Type u) [Group G] [Fintype G]

/-- The regular `G`-set `G/1`: `G` acting on itself by left
multiplication.  Its marks are `|G|` at `⊥` and `0` everywhere else. -/
abbrev regularGSet : FinGSet G := ⟨G⟩

variable {G}

@[simp] theorem card_regularGSet : Fintype.card (regularGSet G) = Fintype.card G := rfl

/-- The regular `G`-set has no nontrivial fixed points. -/
theorem fix_regularGSet_of_ne_bot {H : Subgroup G} (hH : H ≠ ⊥) :
    fix H (regularGSet G) = 0 := by
  obtain ⟨h, hh, hne⟩ : ∃ h : G, h ∈ H ∧ h ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hH (le_bot_iff.mp fun x hx => Subgroup.mem_bot.mpr (hcon x hx))
  have hempty : IsEmpty (fixedPoints H (regularGSet G).carrier) := by
    refine ⟨fun z => hne ?_⟩
    have hz : h * z.1 = z.1 := z.2 ⟨h, hh⟩
    have hz' : h * z.1 = (1 : G) * z.1 := by rw [one_mul]; exact hz
    exact mul_right_cancel hz'
  exact Nat.card_eq_zero.mpr (Or.inl hempty)

@[simp] theorem fix_bot_regularGSet :
    fix (⊥ : Subgroup G) (regularGSet G) = Fintype.card G := fix_bot _

end Regular

/-! ## Stabilizers and orbits inside invariant subsets -/

section Peel

variable {G : Type u} [Group G]

variable [Fintype G]

/-- A free orbit has exactly `|G|` elements. -/
theorem card_orbit_of_stabilizer_eq_bot {X : FinGSet G} (x : X)
    (hx : stabilizer G x = ⊥) :
    Fintype.card (X.ofInvariant (orbit G x) (FinGSet.orbit_invariant x)) =
      Fintype.card G := by
  have h1 : Nat.card (orbit G x) = Nat.card (G ⧸ stabilizer G x) :=
    Nat.card_congr (orbitEquivQuotientStabilizer G x)
  rw [hx] at h1
  have h2 : Nat.card (G ⧸ (⊥ : Subgroup G)) = Nat.card G :=
    Nat.card_congr (QuotientGroup.quotientBot).toEquiv
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  change Nat.card (orbit G x) = Nat.card G
  rw [h1, h2]

omit [Fintype G] in
/-- A free orbit is fixed-point free at every nontrivial subgroup. -/
theorem fix_orbit_eq_zero_of_stabilizer_eq_bot {X : FinGSet G} (x : X)
    (hfree : ∀ z : X, stabilizer G z = ⊥) {H : Subgroup G} (hH : H ≠ ⊥) :
    fix H (X.ofInvariant (orbit G x) (FinGSet.orbit_invariant x)) = 0 := by
  have hempty :
      IsEmpty (fixedPoints H (X.ofInvariant (orbit G x)
        (FinGSet.orbit_invariant x)).carrier) := by
    refine ⟨fun z => hH (le_bot_iff.mp fun k hk => ?_)⟩
    have hz : k • z.1 = z.1 := z.2 ⟨k, hk⟩
    have hz2 : k • (z.1.1 : X) = z.1.1 := by
      have hc := congrArg Subtype.val hz
      rw [FinGSet.ofInvariant_smul_coe] at hc
      exact hc
    have hmem : k ∈ stabilizer G (z.1.1 : X) := mem_stabilizer_iff.mpr hz2
    rw [hfree z.1.1] at hmem
    exact hmem
  exact Nat.card_eq_zero.mpr (Or.inl hempty)

omit [Fintype G] in
/-- The matching step, restricted to points with nontrivial stabilizer:
the variant of `FinGSet.exists_matched_point` that only needs the marks
at *nontrivial* subgroups. -/
theorem exists_matched_point_ne_bot {X Y : FinGSet G}
    (h : ∀ H : Subgroup G, H ≠ ⊥ → fix H X = fix H Y) (x₀ : X)
    (hx₀ : stabilizer G x₀ ≠ ⊥)
    (hmin : ∀ y : Y, stabilizer G y ≠ ⊥ →
      Nat.card (orbit G x₀) ≤ Nat.card (orbit G y)) :
    ∃ y : Y, stabilizer G x₀ = stabilizer G y := by
  set H := stabilizer G x₀ with hH
  have hne : Nonempty (fixedPoints H X.carrier) :=
    ⟨⟨x₀, fun m => mem_stabilizer_iff.mp m.2⟩⟩
  have hpos : 0 < fix H X := Nat.card_pos
  have hposY : 0 < fix H Y := (h H hx₀) ▸ hpos
  have hneY : Nonempty (fixedPoints H Y.carrier) :=
    (Nat.card_ne_zero.mp (Nat.pos_iff_ne_zero.mp hposY)).1
  obtain ⟨y, hy⟩ := hneY
  have hle : H ≤ stabilizer G y := fun k hk => mem_stabilizer_iff.mpr (hy ⟨k, hk⟩)
  have hyne : stabilizer G y ≠ ⊥ := fun hb => hx₀ (le_bot_iff.mp (hb ▸ hle))
  exact ⟨y, FinGSet.stabilizer_eq_of_le_of_card_le hle (hmin y hyne)⟩

end Peel

/-! ## Burnside triangularity -/

section Triangularity

variable {G : Type u} [Group G] [Fintype G]

/-- The complement of an orbit, as a `G`-set. -/
private noncomputable def orbitCompl {X : FinGSet G} (x : X) : FinGSet G :=
  X.ofInvariant (orbit G x)ᶜ
    (fun g z hz hmem => hz (by simpa using FinGSet.orbit_invariant x g⁻¹ _ hmem))

omit [Fintype G] in
/-- Splitting a `G`-set along an orbit. -/
private theorem isIso_orbit_disjUnion {X : FinGSet G} (x : X) :
    FinGSet.IsIso X ((X.ofInvariant (orbit G x)
      (FinGSet.orbit_invariant x)).disjUnion (orbitCompl x)) :=
  FinGSet.isIso_sum_compl X _ _

omit [Fintype G] in
private theorem fix_split {X : FinGSet G} (x : X) (H : Subgroup G) :
    fix H X = fix H (X.ofInvariant (orbit G x) (FinGSet.orbit_invariant x)) +
      fix H (orbitCompl x) := by
  rw [fix_congr H (isIso_orbit_disjUnion x), fix_disjUnion]

omit [Fintype G] in
private theorem card_split {X : FinGSet G} (x : X) :
    Fintype.card X = Fintype.card (X.ofInvariant (orbit G x)
      (FinGSet.orbit_invariant x)) + Fintype.card (orbitCompl x) := by
  have := fix_split x ⊥
  rwa [fix_bot, fix_bot, fix_bot] at this

omit [Fintype G] in
private theorem card_orbit_pos {X : FinGSet G} (x : X) :
    0 < Fintype.card (X.ofInvariant (orbit G x) (FinGSet.orbit_invariant x)) :=
  Fintype.card_pos_iff.mpr ⟨⟨x, mem_orbit_self x⟩⟩

/-- **Burnside triangularity, `G`-set form** (bounded-cardinality
induction).  If two finite `G`-sets have the same marks at every
*nontrivial* subgroup, then `|G|` divides the difference of their
cardinalities. -/
theorem dvd_card_sub_card_aux :
    ∀ (n : ℕ) (X Y : FinGSet G), Fintype.card X + Fintype.card Y ≤ n →
      (∀ H : Subgroup G, H ≠ ⊥ → fix H X = fix H Y) →
        (Fintype.card G : ℤ) ∣ (Fintype.card X : ℤ) - (Fintype.card Y : ℤ) := by
  intro n
  induction n with
  | zero =>
    intro X Y hle _
    have hX : Fintype.card X = 0 := by omega
    have hY : Fintype.card Y = 0 := by omega
    have h0 : (Fintype.card X : ℤ) - (Fintype.card Y : ℤ) = 0 := by
      rw [hX, hY]; norm_num
    rw [h0]
    exact dvd_zero _
  | succ n ih =>
    intro X Y hle h
    classical
    by_cases hT : (Finset.univ.filter fun p : X.carrier ⊕ Y.carrier =>
        Sum.elim (fun x : X.carrier => stabilizer G x ≠ ⊥)
          (fun y : Y.carrier => stabilizer G y ≠ ⊥) p).Nonempty
    · -- some point has a nontrivial stabilizer: match and peel two orbits
      obtain ⟨p, hpT, hp⟩ := Finset.exists_min_image _
        (Sum.elim (fun x : X.carrier => Nat.card (orbit G x))
          (fun y : Y.carrier => Nat.card (orbit G y))) hT
      obtain ⟨x₀, y₀, hstab⟩ :
          ∃ (x₀ : X) (y₀ : Y), stabilizer G x₀ = stabilizer G y₀ := by
        rcases p with x₀ | y₀
        · have hx₀ : stabilizer G x₀ ≠ ⊥ := (Finset.mem_filter.mp hpT).2
          obtain ⟨y₀, hy₀⟩ := exists_matched_point_ne_bot h x₀ hx₀
            (fun y hy => hp (.inr y) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩))
          exact ⟨x₀, y₀, hy₀⟩
        · have hy₀ : stabilizer G y₀ ≠ ⊥ := (Finset.mem_filter.mp hpT).2
          obtain ⟨x₀, hx₀⟩ := exists_matched_point_ne_bot
            (fun H hH => (h H hH).symm) y₀ hy₀
            (fun x hx => hp (.inl x) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩))
          exact ⟨x₀, y₀, hx₀.symm⟩
      have hOrb : FinGSet.IsIso
          (X.ofInvariant (orbit G x₀) (FinGSet.orbit_invariant x₀))
          (Y.ofInvariant (orbit G y₀) (FinGSet.orbit_invariant y₀)) :=
        FinGSet.isIso_orbit_of_stabilizer_eq hstab
      have hmarks : ∀ H : Subgroup G, H ≠ ⊥ →
          fix H (orbitCompl x₀) = fix H (orbitCompl y₀) := by
        intro H hH
        have e1 := fix_split x₀ H
        have e2 := fix_split y₀ H
        have e3 := fix_congr H hOrb
        have e4 := h H hH
        omega
      have hcX := card_split x₀
      have hcY := card_split y₀
      have hcOrb : Fintype.card (X.ofInvariant (orbit G x₀)
          (FinGSet.orbit_invariant x₀)) =
          Fintype.card (Y.ofInvariant (orbit G y₀)
            (FinGSet.orbit_invariant y₀)) := by
        have := fix_congr (⊥ : Subgroup G) hOrb
        rwa [fix_bot, fix_bot] at this
      have hposX := card_orbit_pos x₀
      have hposY := card_orbit_pos y₀
      have hbound : Fintype.card (orbitCompl x₀) + Fintype.card (orbitCompl y₀) ≤ n := by
        omega
      have hrec := ih (orbitCompl x₀) (orbitCompl y₀) hbound hmarks
      have hdiff : (Fintype.card X : ℤ) - (Fintype.card Y : ℤ) =
          (Fintype.card (orbitCompl x₀) : ℤ) - (Fintype.card (orbitCompl y₀) : ℤ) := by
        have hcX' : (Fintype.card X : ℤ) =
            (Fintype.card (X.ofInvariant (orbit G x₀)
              (FinGSet.orbit_invariant x₀)) : ℤ) + (Fintype.card (orbitCompl x₀) : ℤ) := by
          exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hcX
        have hcY' : (Fintype.card Y : ℤ) =
            (Fintype.card (Y.ofInvariant (orbit G y₀)
              (FinGSet.orbit_invariant y₀)) : ℤ) + (Fintype.card (orbitCompl y₀) : ℤ) := by
          exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hcY
        have hcOrb' : (Fintype.card (X.ofInvariant (orbit G x₀)
            (FinGSet.orbit_invariant x₀)) : ℤ) =
            (Fintype.card (Y.ofInvariant (orbit G y₀)
              (FinGSet.orbit_invariant y₀)) : ℤ) := by
          exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hcOrb
        rw [hcX', hcY', hcOrb']
        ring
      rw [hdiff]
      exact hrec
    · -- every stabilizer is trivial: peel one free orbit
      have hfreeX : ∀ x : X.carrier, stabilizer G x = ⊥ := by
        intro x
        by_contra hx
        exact hT ⟨.inl x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
      have hfreeY : ∀ y : Y.carrier, stabilizer G y = ⊥ := by
        intro y
        by_contra hy
        exact hT ⟨.inr y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩⟩
      by_cases hXe : IsEmpty X.carrier
      · by_cases hYe : IsEmpty Y.carrier
        · have hX : Fintype.card X = 0 := Fintype.card_eq_zero_iff.mpr hXe
          have hY : Fintype.card Y = 0 := Fintype.card_eq_zero_iff.mpr hYe
          have h0 : (Fintype.card X : ℤ) - (Fintype.card Y : ℤ) = 0 := by
            rw [hX, hY]; norm_num
          rw [h0]
          exact dvd_zero _
        · -- peel a free orbit off `Y`
          obtain ⟨y₀⟩ := not_isEmpty_iff.mp hYe
          have hmarks : ∀ H : Subgroup G, H ≠ ⊥ → fix H X = fix H (orbitCompl y₀) := by
            intro H hH
            have e1 := fix_split y₀ H
            have e2 := fix_orbit_eq_zero_of_stabilizer_eq_bot y₀ hfreeY hH
            have e3 := h H hH
            omega
          have hcY := card_split y₀
          have hcOrb := card_orbit_of_stabilizer_eq_bot y₀ (hfreeY y₀)
          have hX : Fintype.card X = 0 := Fintype.card_eq_zero_iff.mpr hXe
          have hbound : Fintype.card X + Fintype.card (orbitCompl y₀) ≤ n := by
            have hG : 0 < Fintype.card G := Fintype.card_pos
            omega
          have hrec := ih X (orbitCompl y₀) hbound hmarks
          have hdiff : (Fintype.card Y : ℤ) =
              (Fintype.card G : ℤ) + (Fintype.card (orbitCompl y₀) : ℤ) := by
            rw [hcY, hcOrb]; push_cast; ring
          rw [hdiff]
          have : (Fintype.card X : ℤ) - ((Fintype.card G : ℤ) +
              (Fintype.card (orbitCompl y₀) : ℤ)) =
              ((Fintype.card X : ℤ) - (Fintype.card (orbitCompl y₀) : ℤ)) -
                (Fintype.card G : ℤ) := by ring
          rw [this]
          exact dvd_sub hrec dvd_rfl
      · -- peel a free orbit off `X`
        obtain ⟨x₀⟩ := not_isEmpty_iff.mp hXe
        have hmarks : ∀ H : Subgroup G, H ≠ ⊥ → fix H (orbitCompl x₀) = fix H Y := by
          intro H hH
          have e1 := fix_split x₀ H
          have e2 := fix_orbit_eq_zero_of_stabilizer_eq_bot x₀ hfreeX hH
          have e3 := h H hH
          omega
        have hcX := card_split x₀
        have hcOrb := card_orbit_of_stabilizer_eq_bot x₀ (hfreeX x₀)
        have hbound : Fintype.card (orbitCompl x₀) + Fintype.card Y ≤ n := by
          have hG : 0 < Fintype.card G := Fintype.card_pos
          omega
        have hrec := ih (orbitCompl x₀) Y hbound hmarks
        have hdiff : (Fintype.card X : ℤ) =
            (Fintype.card G : ℤ) + (Fintype.card (orbitCompl x₀) : ℤ) := by
          rw [hcX, hcOrb]; push_cast; ring
        rw [hdiff]
        have : (Fintype.card G : ℤ) + (Fintype.card (orbitCompl x₀) : ℤ) -
            (Fintype.card Y : ℤ) =
            ((Fintype.card (orbitCompl x₀) : ℤ) - (Fintype.card Y : ℤ)) +
              (Fintype.card G : ℤ) := by ring
        rw [this]
        exact dvd_add hrec dvd_rfl

/-- **Burnside triangularity, `G`-set form.** -/
theorem dvd_card_sub_card_of_fix_eq (X Y : FinGSet G)
    (h : ∀ H : Subgroup G, H ≠ ⊥ → fix H X = fix H Y) :
    (Fintype.card G : ℤ) ∣ (Fintype.card X : ℤ) - (Fintype.card Y : ℤ) :=
  dvd_card_sub_card_aux (Fintype.card X + Fintype.card Y) X Y le_rfl h

/-- **Burnside triangularity in `B(G)`**: an element whose marks vanish at
every nontrivial subgroup has `⊥`-mark divisible by `|G|`.  (Classically:
such an element is an integer multiple of `[G/1]`.) -/
theorem dvd_mark_bot_of_mark_eq_zero (b : BurnsideRing G)
    (h : ∀ H : Subgroup G, H ≠ ⊥ → BurnsideRing.mark H b = 0) :
    (Nat.card G : ℤ) ∣ BurnsideRing.mark (⊥ : Subgroup G) b := by
  induction b using Quotient.ind with
  | _ p =>
    obtain ⟨a, c⟩ := p
    induction a using Quotient.ind with
    | _ X =>
      induction c using Quotient.ind with
      | _ Y =>
        have hmarks : ∀ H : Subgroup G, H ≠ ⊥ → fix H X = fix H Y := by
          intro H hH
          have := h H hH
          change (Skel.mark H (Skel.mk X) : ℤ) - (Skel.mark H (Skel.mk Y) : ℤ) = 0 at this
          rw [Skel.mark_mk, Skel.mark_mk] at this
          omega
        have hd := dvd_card_sub_card_of_fix_eq X Y hmarks
        rw [Nat.card_eq_fintype_card]
        change (Fintype.card G : ℤ) ∣
          (Skel.mark ⊥ (Skel.mk X) : ℤ) - (Skel.mark ⊥ (Skel.mk Y) : ℤ)
        rw [Skel.mark_mk, Skel.mark_mk, fix_bot, fix_bot]
        exact hd

end Triangularity

/-! ## The trivial integer point and its isolation bound -/

section TrivialPoint

variable {G : Type u} [Group G] [Fintype G]

variable (G) in
/-- The trivial integer point of `D(G)`: the mark at `⊥` of the underlying
`G`-set, i.e. `mark_⊥ ∘ forget`.  Its complexification is the trivial
species `φ_{⊥,1}`. -/
noncomputable def trivialPoint : DRing G →+* ℤ :=
  (BurnsideRing.mark (⊥ : Subgroup G)).comp (MonRing.forget)

omit [Fintype G] in
theorem complexify_trivialPoint :
    complexify (DRing G) (trivialPoint G) = DRing.species (⊥ : Subgroup G) 1 := by
  refine RingHom.ext fun x => ?_
  have h := DFunLike.congr_fun (DRing.species_one_eq_mark_forget (⊥ : Subgroup G)) x
  simp only [RingHom.coe_comp, Function.comp_apply] at h
  simp only [complexify, trivialPoint, RingHom.coe_comp, Function.comp_apply]
  rw [h]

/-- **The trivial species is separated from every other trivial-fibre
species** by the class of the regular `G`-set: `φ_{H,1}` gives `0` there
for `H ≠ ⊥`, while `φ_{⊥,1}` gives `|G| ≠ 0`. -/
theorem species_ne_complexify_trivialPoint {H : Subgroup G} (hH : H ≠ ⊥) :
    DRing.species H 1 ≠ complexify (DRing G) (trivialPoint G) := by
  intro hcon
  set b : BurnsideRing G := GrothendieckRing.of (Skel.mk (regularGSet G)) with hb
  have h1 : DRing.species H 1 (MonRing.eta b) = 0 := by
    have := DFunLike.congr_fun (DRing.species_comp_eta H (1 : H)) b
    simp only [RingHom.coe_comp, Function.comp_apply] at this
    rw [this, hb, BurnsideRing.mark_of, Skel.mark_mk, fix_regularGSet_of_ne_bot hH]
    norm_num
  have h2 : complexify (DRing G) (trivialPoint G) (MonRing.eta b) =
      (Fintype.card G : ℂ) := by
    simp only [complexify, trivialPoint, RingHom.coe_comp, Function.comp_apply]
    rw [MonRing.forget_eta, hb, BurnsideRing.mark_of, Skel.mark_mk, fix_bot]
    norm_num
  rw [hcon, h2] at h1
  exact absurd h1 (by exact_mod_cast Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

end TrivialPoint

/-! ## `MullerTrivialBound`, proven -/

/-- **[PROVEN — Müller Satz 2.3.1 (Boltje Cor. 2.8), easy direction, at
the trivial pair]** The trivial integer point of `D(G)` admits only
isolated values divisible by `|G|`.

Proof: if `x` isolates `p₀ = mark_⊥ ∘ forget` with value `n`, then every
species `φ_{H,1}` with `H ≠ ⊥` kills `x`
(`species_ne_complexify_trivialPoint`), i.e. every nontrivial mark of
`forget x` vanishes; Burnside triangularity
(`dvd_mark_bot_of_mark_eq_zero`) then forces `|G| ∣ mark_⊥ (forget x) =
n`. -/
theorem dvd_of_isolates_trivialPoint {G : Type u} [Group G] [Fintype G]
    (x : DRing G) (n : ℕ) (hx : Isolates (trivialPoint G) x n) :
    Nat.card G ∣ n := by
  have hzero : ∀ H : Subgroup G, H ≠ ⊥ →
      BurnsideRing.mark H (MonRing.forget x) = 0 := by
    intro H hH
    have hkill : DRing.species H 1 x = 0 :=
      hx.2 (DRing.species H 1) (species_ne_complexify_trivialPoint hH)
    have hval := DFunLike.congr_fun (DRing.species_one_eq_mark_forget H) x
    simp only [RingHom.coe_comp, Function.comp_apply] at hval
    rw [hval] at hkill
    have hc : ((BurnsideRing.mark H (MonRing.forget x) : ℤ) : ℂ) = 0 := hkill
    exact_mod_cast hc
  have hdvd := dvd_mark_bot_of_mark_eq_zero (MonRing.forget x) hzero
  have hval : BurnsideRing.mark (⊥ : Subgroup G) (MonRing.forget x) = (n : ℤ) := hx.1
  rw [hval] at hdvd
  exact_mod_cast hdvd

/-- **[PROVEN]** `MullerTrivialBound`, witnessed by the trivial point. -/
theorem mullerTrivialBound : MullerTrivialBound.{u} :=
  fun G _ _ => ⟨trivialPoint G, dvd_of_isolates_trivialPoint⟩

/-- **Satz 2.3.4, half-assembled**: with `MullerTrivialBound` proven,
`mullerOrder (D(G)) = |G|` is conditional on `MullerIsolation` alone. -/
theorem mullerOrder_dring_eq_card_of_isolation (hiso : MullerIsolation.{u})
    (G : Type u) [Group G] [Fintype G] :
    mullerOrder (DRing G) = Nat.card G :=
  mullerOrder_dring_eq_card hiso mullerTrivialBound G

/-- **Order transfer** now rests on `MullerIsolation` alone. -/
theorem orderTransfer_of_mullerIsolation (hiso : MullerIsolation.{u}) :
    OrderTransfer.{u} :=
  orderTransfer_of_muller hiso mullerTrivialBound

end Even

end LeanDring
