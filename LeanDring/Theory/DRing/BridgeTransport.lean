/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.BridgeRecognition
import LeanDring.Theory.DRing.FreeBasis

/-!
# Transport along a species-table isomorphism

`SpeciesTableIso G G'`: a bijection of table rows (basis classes `[K,λ]`)
together with two-sided column correspondences respecting the `H`-blocks
(columns are `(H, h)`-labelled, as in the Speziestafel), such
that corresponding entries are **equal**.

Main transport theorems (sorry-free):

* `SpeciesTableIso.symm` — the notion is symmetric;
* `isMarkClass_iff_mem_range_eta` + `SpeciesTableIso.isMarkClass_rows` —
  the row bijection **preserves mark classes** `[K,1]` (recognition via
  species-constancy);
* `SpeciesTableIso.sub_bot` — the correspondence **fixes `⊥`** (the
  augmentation column is the unique zero-free column);
* `SpeciesTableIso.card_eq` — `|G| = |G'|`;
* `SpeciesTableIso.rows_bot` — `σ[⊥,1] = [⊥,1]`;
* `SpeciesTableIso.quotient_card_eq` / `subgroup_card_eq` — matched mark
  classes have equal `|G/K|`, hence equal `|K|`: **the table transports
  subgroup orders**.
-/

namespace LeanDring

open MulAction Finset

universe u

namespace DRing

open MonGSet MonRing

variable {G : Type u} [Group G] [Fintype G]

set_option linter.unusedFintypeInType false in
omit [Fintype G] in
/-- All cosets are `⊥`-fixed. -/
theorem card_fixedPoints_bot (K : Subgroup G) :
    Nat.card (fixedPoints (⊥ : Subgroup G) (G ⧸ K)) = Nat.card (G ⧸ K) := by
  refine Nat.card_congr (Equiv.subtypeUnivEquiv ?_)
  intro x k
  have hk : (k : G) = 1 := Subgroup.mem_bot.mp k.2
  change (k : G) • x = x
  rw [hk, one_smul]

/-- The augmentation entry on a general row: `φ_{⊥,1}[K,λ] = |G/K|`. -/
theorem species_bot_one_basisElt' (K : Subgroup G) (l : K →* ℂˣ) :
    species (⊥ : Subgroup G) 1 (basisElt K l) =
      (Nat.card (G ⧸ K) : ℂ) := by
  rw [species_one_basisElt, card_fixedPoints_bot]

/-- Augmentation entries never vanish. -/
theorem species_bot_one_basisElt_ne_zero (K : Subgroup G) (l : K →* ℂˣ) :
    species (⊥ : Subgroup G) 1 (basisElt K l) ≠ 0 := by
  rw [species_bot_one_basisElt']
  have hpos : 0 < Nat.card (G ⧸ K) := Nat.card_pos
  exact_mod_cast hpos.ne'

/-- A **mark class**: the class of a trivial-character pair `(K, 1)`. -/
def IsMarkClass (c : CharPairClass G ℂˣ) : Prop :=
  ∃ K : Subgroup G, c = (⟦⟨K, 1⟩⟧ : CharPairClass G ℂˣ)

/-- Mark classes are exactly the rows lying in the Burnside copy. -/
theorem isMarkClass_iff_mem_range_eta (c : CharPairClass G ℂˣ) :
    IsMarkClass c ↔
      classElt c ∈ Set.range (eta : BurnsideRing G →+* DRing G) := by
  constructor
  · rintro ⟨K, rfl⟩
    rw [classElt_mk, basisElt_one]
    exact ⟨_, rfl⟩
  · intro hmem
    rcases hout : c.out with ⟨K₀, l₀⟩
    have h1 : classElt c = basisElt K₀ l₀ := by
      change basisElt c.out.1 c.out.2 = basisElt K₀ l₀
      rw [hout]
    rw [h1] at hmem
    have h2 : l₀ = 1 := (basisElt_mem_range_eta_iff K₀ l₀).mp hmem
    refine ⟨K₀, ?_⟩
    conv_lhs => rw [← Quotient.out_eq c, hout, h2]

variable {G' : Type u} [Group G'] [Fintype G']

/-- **A species-table isomorphism**: a row bijection plus two-sided
`H`-block-respecting column correspondences with equal entries — the
formal counterpart of "Speziestafeln sind isomorph"
(columns carry their `(H, h)` labels). -/
structure SpeciesTableIso (G G' : Type u) [Group G] [Fintype G]
    [Group G'] [Fintype G'] where
  rows : CharPairClass G ℂˣ ≃ CharPairClass G' ℂˣ
  sub : Subgroup G → Subgroup G'
  el : ∀ {H : Subgroup G}, H → (sub H)
  sub' : Subgroup G' → Subgroup G
  el' : ∀ {H' : Subgroup G'}, H' → (sub' H')
  entry : ∀ (H : Subgroup G) (h : H) (c : CharPairClass G ℂˣ),
    species (sub H) (el h) (classElt (rows c)) = species H h (classElt c)
  entry' : ∀ (H' : Subgroup G') (h' : H') (c' : CharPairClass G' ℂˣ),
    species (sub' H') (el' h') (classElt (rows.symm c')) =
      species H' h' (classElt c')
  /-- The column maps send the identity element to the identity — the `h = 1`
  columns (the marks) correspond. -/
  el_one : ∀ H : Subgroup G, el (1 : H) = (1 : sub H)
  /-- The reverse column map sends the identity to the identity. -/
  el'_one : ∀ H' : Subgroup G', el' (1 : H') = (1 : sub' H')

namespace SpeciesTableIso

variable (T : SpeciesTableIso G G')

/-- Table isomorphism is symmetric. -/
def symm : SpeciesTableIso G' G where
  rows := T.rows.symm
  sub := T.sub'
  el := T.el'
  sub' := T.sub
  el' := T.el
  entry := T.entry'
  entry' := by
    intro H h c
    have h1 := T.entry H h c
    simpa using h1
  el_one := T.el'_one
  el'_one := T.el_one

/-- **The `h = 1` (marks) column of every row is transported.** Because the
column maps fix the identity (`el_one`), `T` sends the mark column
`H ↦ φ_{H,1}` of each row `c` to the mark column of its image `T c` (read on
the matched subgroups `sub H`). Since `φ_{H,1}[K,χ] = #(G/K)^H` is
independent of the character `χ`, this is exactly the marks of the row's
underlying subgroup — so a row's underlying subgroup class is table-visible,
even for non-mark rows. -/
theorem species_one_rows (c : CharPairClass G ℂˣ) (H : Subgroup G) :
    species (T.sub H) (1 : T.sub H) (classElt (T.rows c)) =
      species H (1 : H) (classElt c) := by
  have h := T.entry H 1 c
  rwa [T.el_one H] at h

/-- Species-constancy of a row transfers along the table isomorphism. -/
theorem species_const_rows {c : CharPairClass G ℂˣ}
    (hc : ∀ (H : Subgroup G) (h : H),
      species H h (classElt c) = species H 1 (classElt c)) :
    ∀ (H' : Subgroup G') (h' : H'),
      species H' h' (classElt (T.rows c)) =
        species H' 1 (classElt (T.rows c)) := by
  intro H' h'
  have h1 := T.entry' H' h' (T.rows c)
  have h2 := T.entry' H' 1 (T.rows c)
  rw [Equiv.symm_apply_apply] at h1 h2
  rw [← h1, ← h2, hc (T.sub' H') (T.el' h'), hc (T.sub' H') (T.el' 1)]

/-- **The row bijection preserves mark classes.** -/
theorem isMarkClass_rows {c : CharPairClass G ℂˣ} (hc : IsMarkClass c) :
    IsMarkClass (T.rows c) := by
  rw [isMarkClass_iff_mem_range_eta] at hc ⊢
  rw [mem_range_eta_iff_species_const] at hc ⊢
  exact fun H' h' => T.species_const_rows hc H' h'

/-- **The correspondence fixes `⊥`**: the augmentation column is the
unique zero-free column. -/
theorem sub_bot : T.sub ⊥ = ⊥ := by
  by_contra hne
  -- evaluate the `(sub ⊥, el 1)` column at the row `σ⁻¹[⊥', 1]`
  have h1 := T.entry ⊥ 1 (T.rows.symm (⟦⟨⊥, 1⟩⟧ : CharPairClass G' ℂˣ))
  rw [Equiv.apply_symm_apply, classElt_mk] at h1
  rw [species_basisElt_bot hne (T.el 1) (1 : (⊥ : Subgroup G') →* ℂˣ)] at h1
  exact species_bot_one_basisElt_ne_zero _ _ h1.symm

/-- Matched mark classes have equal coset-space cardinalities. -/
theorem quotient_card_eq {K : Subgroup G} {K' : Subgroup G'}
    (hKK' : T.rows (⟦⟨K, 1⟩⟧ : CharPairClass G ℂˣ) =
      (⟦⟨K', 1⟩⟧ : CharPairClass G' ℂˣ)) :
    Nat.card (G ⧸ K) = Nat.card (G' ⧸ K') := by
  have h1 := T.entry ⊥ 1 (⟦⟨K, 1⟩⟧ : CharPairClass G ℂˣ)
  rw [hKK', classElt_mk, classElt_mk] at h1
  rw [species_bot_one_basisElt'] at h1
  -- the left column is `(⊥', 1)` after `sub_bot`
  have h2 : ∀ (H₀ : Subgroup G') (e : H₀), H₀ = ⊥ →
      species H₀ e (basisElt K' (1 : K' →* ℂˣ)) =
        species (⊥ : Subgroup G') 1 (basisElt K' (1 : K' →* ℂˣ)) := by
    intro H₀ e hH₀
    subst hH₀
    have he : e = 1 := Subtype.ext (by
      have := e.2
      rw [Subgroup.mem_bot] at this
      simpa using this)
    rw [he]
  rw [h2 _ _ T.sub_bot, species_bot_one_basisElt'] at h1
  exact_mod_cast h1.symm

/-- `|G| = |G'|` and `σ[⊥,1] = [⊥,1]`. -/
theorem card_eq_and_rows_bot :
    Nat.card G = Nat.card G' ∧
      T.rows (⟦⟨(⊥ : Subgroup G), 1⟩⟧ : CharPairClass G ℂˣ) =
        (⟦⟨(⊥ : Subgroup G'), 1⟩⟧ : CharPairClass G' ℂˣ) := by
  -- the image of `[⊥,1]` is some mark class `[K',1]`
  obtain ⟨K', hK'⟩ := T.isMarkClass_rows ⟨⊥, rfl⟩
  obtain ⟨K, hK⟩ := T.symm.isMarkClass_rows (⟨⊥, rfl⟩ :
    IsMarkClass (⟦⟨(⊥ : Subgroup G'), 1⟩⟧ : CharPairClass G' ℂˣ))
  -- cardinalities through the two readings
  have h1 := T.quotient_card_eq hK'
  have h2 := T.symm.quotient_card_eq hK
  -- `|G ⧸ ⊥| = |G|`
  have hbotG : Nat.card (G ⧸ (⊥ : Subgroup G)) = Nat.card G :=
    Nat.card_congr (QuotientGroup.quotientBot (G := G)).toEquiv
  have hbotG' : Nat.card (G' ⧸ (⊥ : Subgroup G')) = Nat.card G' :=
    Nat.card_congr (QuotientGroup.quotientBot (G := G')).toEquiv
  rw [hbotG] at h1
  rw [hbotG'] at h2
  -- `|G| = |G'/K'| ≤ |G'|` and symmetrically
  have hle1 : Nat.card G ≤ Nat.card G' := by
    rw [h1]
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup K'
    have hpos : 0 < Nat.card K' := Nat.card_pos
    calc Nat.card (G' ⧸ K') ≤ Nat.card (G' ⧸ K') * Nat.card K' :=
          Nat.le_mul_of_pos_right _ hpos
      _ = Nat.card G' := hmul.symm
  have hle2 : Nat.card G' ≤ Nat.card G := by
    rw [h2]
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    have hpos : 0 < Nat.card K := Nat.card_pos
    calc Nat.card (G ⧸ K) ≤ Nat.card (G ⧸ K) * Nat.card K :=
          Nat.le_mul_of_pos_right _ hpos
      _ = Nat.card G := hmul.symm
  have hcard : Nat.card G = Nat.card G' := le_antisymm hle1 hle2
  refine ⟨hcard, ?_⟩
  -- `|G'/K'| = |G'|` forces `K' = ⊥`
  have hK'card : Nat.card K' = 1 := by
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup K'
    rw [← h1, hcard] at hmul
    have hpos : 0 < Nat.card G' := Nat.card_pos
    have h3 : Nat.card G' * Nat.card K' = Nat.card G' * 1 := by
      rw [mul_one]
      exact hmul.symm
    exact Nat.eq_of_mul_eq_mul_left hpos h3
  have hK'bot : K' = ⊥ := Subgroup.eq_bot_of_card_eq K' hK'card
  rw [hK', hK'bot]

include T in
/-- `|G| = |G'|`. -/
theorem card_eq : Nat.card G = Nat.card G' := (card_eq_and_rows_bot T).1

/-- **The table transports subgroup orders**: matched mark classes have
`|K| = |K'|`. -/
theorem subgroup_card_eq {K : Subgroup G} {K' : Subgroup G'}
    (hKK' : T.rows (⟦⟨K, 1⟩⟧ : CharPairClass G ℂˣ) =
      (⟦⟨K', 1⟩⟧ : CharPairClass G' ℂˣ)) :
    Nat.card K = Nat.card K' := by
  have h1 := T.quotient_card_eq hKK'
  have hmulG := Subgroup.card_eq_card_quotient_mul_card_subgroup K
  have hmulG' := Subgroup.card_eq_card_quotient_mul_card_subgroup K'
  have hcard := card_eq T
  have hpos : 0 < Nat.card (G ⧸ K) := Nat.card_pos
  rw [hcard, hmulG'] at hmulG
  rw [← h1] at hmulG
  exact Nat.eq_of_mul_eq_mul_left hpos hmulG.symm

end SpeciesTableIso

end DRing

end LeanDring
