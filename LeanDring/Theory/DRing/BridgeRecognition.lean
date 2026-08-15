/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.Induced
import LeanDring.Theory.DRing.BridgeEntries
import Mathlib.Analysis.Complex.Basic

/-!
# Row recognition: `[K,1]`-rows are the species-constant rows

The second layer of the species→marks bridge. Main results (sorry-free):

* `species_one_basisElt` — **the `h = 1` columns are marks on every
  row**: `φ_{H,1}[K,λ] = #(G/K)^H`, independent of `λ`;
* `species_basisElt_bot` — **the `[⊥,λ]`-row zero pattern**: for
  `H ≠ ⊥`, `φ_{H,h}[⊥,λ] = 0` — so the augmentation column `(⊥,1)` is
  the unique column with no zero entry;
* `sum_units_eq_card` — rigidity: unit-modulus numbers summing to the
  count are all `1`;
* `basisElt_mem_range_eta_iff` — **row recognition**: `[K,λ] ∈ η(B(G))`
  iff `λ = 1`. Combined with `mem_range_eta_iff_species_const`, a row is
  a `[K,1]`-row exactly when its table entries are `h`-independent — an
  intrinsic property of the table, preserved by any entry-matching
  correspondence.
-/

namespace LeanDring

open MulAction Finset

universe u

variable {G : Type u} [Group G] [Fintype G]

namespace DRing

open MonGSet

/-- **The `h = 1` columns are marks on every row**:
`φ_{H,1}[K,λ] = #(G/K)^H`, independent of `λ`. -/
theorem species_one_basisElt (H K : Subgroup G) (l : K →* ℂˣ) :
    species H 1 (basisElt K l) =
      (Nat.card (fixedPoints H (G ⧸ K)) : ℂ) := by
  classical
  rw [species_basisElt]
  have hval : ∀ q : fixedPoints H
      (induced K l : MonGSet G ℂˣ).carrier,
      ((l ⟨q.1.out⁻¹ * ((1 : H) : G) * q.1.out,
        sectionConj_mem K H 1 q.1 (q.2 1)⟩ : ℂˣ) : ℂ) = 1 := by
    intro q
    have harg : (⟨q.1.out⁻¹ * ((1 : H) : G) * q.1.out,
        sectionConj_mem K H 1 q.1 (q.2 1)⟩ : K) = 1 := by
      refine Subtype.ext ?_
      change q.1.out⁻¹ * ((1 : H) : G) * q.1.out = 1
      have hcoe : ((1 : H) : G) = 1 := rfl
      rw [hcoe]
      group
    rw [harg, map_one]
    rfl
  rw [Finset.sum_congr rfl fun q _ => hval q, Finset.sum_const,
    nsmul_eq_mul, mul_one, Finset.card_univ, ← Nat.card_eq_fintype_card]
  rfl

/-- **The `[⊥,λ]`-row zero pattern**: for `H ≠ ⊥` every entry vanishes.
Hence the augmentation column `(⊥,1)` is recognizable from the table as
the unique column without zeros. -/
theorem species_basisElt_bot {H : Subgroup G} (hH : H ≠ ⊥) (h : H)
    (l : (⊥ : Subgroup G) →* ℂˣ) :
    species H h (basisElt ⊥ l) = 0 := by
  classical
  rw [species_basisElt]
  -- the fixed-point set is empty: the `G`-action on `G/⊥` is free
  haveI : IsEmpty (fixedPoints H
      (induced (⊥ : Subgroup G) l : MonGSet G ℂˣ).carrier) := by
    constructor
    rintro ⟨q, hq⟩
    obtain ⟨k, hkH, hk1⟩ : ∃ k : G, k ∈ H ∧ k ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hH (Subgroup.ext fun x =>
        ⟨fun hx => Subgroup.mem_bot.mpr (hcon x hx),
         fun hx => (Subgroup.mem_bot.mp hx) ▸ H.one_mem⟩)
    have hfix := hq ⟨k, hkH⟩
    obtain ⟨g⟩ := q
    have h2 : ((k * g : G) : G ⧸ (⊥ : Subgroup G)) =
        ((g : G) : G ⧸ (⊥ : Subgroup G)) := hfix
    have h3 := (QuotientGroup.eq).mp h2
    rw [Subgroup.mem_bot] at h3
    apply hk1
    have h4 : (k * g)⁻¹ * g = 1 := h3
    have h5 : k * g = g := by
      have := congrArg (fun z => (k * g) * z) h4
      simpa [mul_assoc] using this.symm
    exact mul_right_cancel (h5.trans (one_mul g).symm)
  rw [Finset.univ_eq_empty, Finset.sum_empty]

end DRing

/-- **Rigidity**: unit-modulus complex numbers summing to their count are
all equal to `1`. -/
theorem sum_units_eq_card {ι : Type*} [Fintype ι] (z : ι → ℂ)
    (hz : ∀ i, ‖z i‖ = 1)
    (hsum : ∑ i, z i = (Fintype.card ι : ℂ)) (i : ι) : z i = 1 := by
  classical
  -- real parts: each `≤ 1`, summing to the count forces each `= 1`
  have hre_le : ∀ j, (z j).re ≤ 1 := by
    intro j
    calc (z j).re ≤ ‖z j‖ := Complex.re_le_norm _
      _ = 1 := hz j
  have hre_sum : ∑ j, (z j).re = (Fintype.card ι : ℝ) := by
    have h1 := congrArg Complex.re hsum
    rw [Complex.re_sum] at h1
    simpa using h1
  have hre : ∀ j, (z j).re = 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨j₀, hj₀⟩ := hcon
    have hlt : (z j₀).re < 1 := lt_of_le_of_ne (hre_le j₀) hj₀
    have hstrict : ∑ j, (z j).re < ∑ _j : ι, (1 : ℝ) := by
      refine Finset.sum_lt_sum (fun j _ => hre_le j)
        ⟨j₀, Finset.mem_univ _, hlt⟩
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ] at hstrict
    rw [hre_sum] at hstrict
    exact lt_irrefl _ hstrict
  -- unit modulus with real part `1` forces `z = 1`
  have h1 : ‖z i‖ ^ 2 = 1 := by rw [hz i]; norm_num
  have h2 : (z i).re * (z i).re + (z i).im * (z i).im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq]
    exact h1
  have h3 : (z i).im = 0 := by
    have h4 := hre i
    nlinarith [sq_nonneg (z i).im]
  refine Complex.ext ?_ ?_
  · rw [hre i]
    rfl
  · rw [h3]
    rfl

namespace DRing

open MonGSet MonRing

/-- **Row recognition**: `[K,λ]` lies in the Burnside copy `η(B(G))` iff
`λ = 1`. Since membership in `η(B)` is species-constancy — an intrinsic
property of the row's table entries — the `[K,1]`-rows are recognizable
from the table alone. -/
theorem basisElt_mem_range_eta_iff (K : Subgroup G) (l : K →* ℂˣ) :
    basisElt K l ∈ Set.range (eta : BurnsideRing G →+* DRing G) ↔
      l = 1 := by
  classical
  constructor
  · intro hmem
    have hconst := (mem_range_eta_iff_species_const _).mp hmem
    refine MonoidHom.ext fun h => ?_
    haveI : Fintype K := Fintype.ofFinite _
    -- the `(K,h)` entry equals the `(K,1)` entry, which is the count
    have hentry := hconst K h
    rw [species_basisElt, species_one_basisElt] at hentry
    -- rigidity: every summand is `1`
    have hnorm : ∀ q : fixedPoints K
        (induced K l : MonGSet G ℂˣ).carrier,
        ‖((l ⟨q.1.out⁻¹ * (h : G) * q.1.out,
          sectionConj_mem K K h q.1 (q.2 h)⟩ : ℂˣ) : ℂ)‖ = 1 := by
      intro q
      set x : K := ⟨q.1.out⁻¹ * (h : G) * q.1.out,
        sectionConj_mem K K h q.1 (q.2 h)⟩ with hx
      have hpow : ((l x : ℂˣ) : ℂ) ^ Fintype.card K = 1 := by
        have h1 : x ^ Fintype.card K = 1 := pow_card_eq_one
        calc ((l x : ℂˣ) : ℂ) ^ Fintype.card K
            = (((l x) ^ Fintype.card K : ℂˣ) : ℂ) := by
              rw [Units.val_pow_eq_pow_val]
          _ = ((l (x ^ Fintype.card K) : ℂˣ) : ℂ) := by rw [map_pow]
          _ = 1 := by rw [h1, map_one]; rfl
      exact Complex.norm_eq_one_of_pow_eq_one hpow Fintype.card_ne_zero
    have hcount : (Nat.card (fixedPoints K (G ⧸ K)) : ℂ) =
        (Fintype.card (fixedPoints K
          (induced K l : MonGSet G ℂˣ).carrier) : ℂ) := by
      rw [← Nat.card_eq_fintype_card]
      rfl
    rw [hcount] at hentry
    have hall := fun q => sum_units_eq_card _ hnorm hentry q
    -- evaluate at the identity coset
    have hq₀mem : (((1 : G) : G ⧸ K)) ∈ fixedPoints K
        ((induced K l : MonGSet G ℂˣ).carrier) := by
      intro k
      change (((k : G) * (1 : G) : G) : G ⧸ K) = (((1 : G)) : G ⧸ K)
      refine (QuotientGroup.eq).mpr ?_
      have hk : ((k : G) * 1)⁻¹ * 1 = (k : G)⁻¹ := by group
      rw [hk]
      exact K.inv_mem k.2
    have h1 := hall ⟨(((1 : G)) : G ⧸ K), hq₀mem⟩
    -- the representative of the identity coset lies in `K`
    have hout : (((1 : G)) : G ⧸ K).out ∈ K := by
      have h2 : (((((1 : G)) : G ⧸ K).out : G) : G ⧸ K) =
          (((1 : G)) : G ⧸ K) := QuotientGroup.out_eq' _
      have h3 := (QuotientGroup.eq).mp h2
      have h4 : ((((1 : G)) : G ⧸ K).out)⁻¹ ∈ K := by
        simpa using h3
      simpa using K.inv_mem h4
    -- conjugation by a member of `K` fixes the character value
    have hsplit : (⟨(((1 : G)) : G ⧸ K).out⁻¹ * (h : G) *
        (((1 : G)) : G ⧸ K).out,
        sectionConj_mem K K h _ (hq₀mem h)⟩ : K) =
        (⟨(((1 : G)) : G ⧸ K).out, hout⟩ : K)⁻¹ * h *
          ⟨(((1 : G)) : G ⧸ K).out, hout⟩ := rfl
    rw [hsplit, map_mul, map_mul, map_inv] at h1
    have hval : ((l h : ℂˣ) : ℂ) = 1 := by
      have hcomm : (l ⟨(((1 : G)) : G ⧸ K).out, hout⟩)⁻¹ * l h *
          l ⟨(((1 : G)) : G ⧸ K).out, hout⟩ = l h := by
        calc (l ⟨(((1 : G)) : G ⧸ K).out, hout⟩)⁻¹ * l h *
            l ⟨(((1 : G)) : G ⧸ K).out, hout⟩
            = l h * ((l ⟨(((1 : G)) : G ⧸ K).out, hout⟩)⁻¹ *
                l ⟨(((1 : G)) : G ⧸ K).out, hout⟩) := by
              rw [mul_comm ((l ⟨(((1 : G)) : G ⧸ K).out, hout⟩)⁻¹) (l h),
                mul_assoc]
          _ = l h := by rw [inv_mul_cancel, mul_one]
      rw [← hcomm]
      exact h1
    have : l h = 1 := Units.ext hval
    rw [this]
    rfl
  · rintro rfl
    rw [basisElt_one]
    exact ⟨_, rfl⟩

end DRing

end LeanDring
