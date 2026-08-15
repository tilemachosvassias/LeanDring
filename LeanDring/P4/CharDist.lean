/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P4.Hentry
import LeanDring.P4.ExpA
import LeanDring.Theory.DRing.GabCount
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.GroupTheory.SpecificGroups.Cyclic
/-!
# The distinguished character of `subA d` exists

`exists_charDist`: for `d ≠ 0`, there is a character `χ : subA p d →* ℂˣ` with
`χ(sElt) = ζ_{p²}` and `χ(bElt 1) = ζ_p⁻¹` — the character at which the `G₂`
entry formula is evaluated.  Since `subA d = ⟨sElt⟩ · ⟨bElt⟩` (an internal direct
product with `⟨sElt⟩ ≅ C_{p²}`, `⟨bElt⟩ ≅ C_p`), the evaluation map
`χ ↦ (χ(sElt), χ(bElt 1))` is an injective homomorphism from the (order-`p³`)
character group into `{ζ : ζ^{p²}=1} × {ξ : ξ^p=1}` (also order `p³`), hence a
bijection; the target pair `(ζ_{p²}, ζ_p⁻¹)` is therefore attained.
-/


namespace LeanDring.P4

open Model

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

/-- The `s`-coordinate is a homomorphism `subA d →* Multiplicative (ZMod p)`. -/
def uHom {d : ZMod p} : (subA p d) →* Multiplicative (ZMod p) where
  toFun x := Multiplicative.ofAdd ((x : Model p d).u)
  map_one' := rfl
  map_mul' x y := by
    change Multiplicative.ofAdd (((x * y : subA p d) : Model p d).u) = _
    rw [Subgroup.coe_mul, congrArg Model.u (mul_def (x : Model p d) (y : Model p d))]
    rfl

/-- The `b`-coordinate is a homomorphism `subA d →* Multiplicative (ZMod p)`
(the `redp α = 0` condition kills the multiplication's `v`-twist). -/
def vHom {d : ZMod p} : (subA p d) →* Multiplicative (ZMod p) where
  toFun x := Multiplicative.ofAdd ((x : Model p d).v)
  map_one' := rfl
  map_mul' x y := by
    change Multiplicative.ofAdd (((x * y : subA p d) : Model p d).v) = _
    rw [Subgroup.coe_mul, congrArg Model.v (mul_def (x : Model p d) (y : Model p d)),
      mem_subA_iff.mp y.2, zero_mul, add_zero]
    rfl

/-- `sElt` has order `p²`. -/
theorem orderOf_sElt {d : ZMod p} (hp5 : 5 ≤ p) (hd : d ≠ 0) :
    orderOf (sElt p d) = p ^ 2 := by
  apply orderOf_eq_prime_pow
  · rw [pow_one, sElt_pow_p hp5]
    intro h
    have hα : liftp p d = (0 : ZMod (p ^ 2)) :=
      congrArg (fun z : subA p d => (z : Model p d).α) h
    exact hd (liftp_eq_zero_iff.mp hα)
  · exact sElt_pow_psq hp5

/-- `bElt 1` has order `p`. -/
theorem orderOf_bElt {d : ZMod p} (hp5 : 5 ≤ p) : orderOf (bElt p d 1) = p := by
  apply orderOf_eq_prime (p := p)
  · apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change (⟨0, 0, 1⟩ : Model p d) ^ p = 1
    rw [pow_p hp5 (⟨0, 0, 1⟩ : Model p d)]
    change (⟨liftp p (redp p 0 + d * 0), 0, 0⟩ : Model p d) = 1
    rw [map_zero, mul_zero, add_zero, liftp_zero]; rfl
  · intro h
    have hv : (1 : ZMod p) = 0 := congrArg (fun z : subA p d => (z : Model p d).v) h
    exact one_ne_zero hv

/-- `⟨sElt⟩` and `⟨bElt 1⟩` intersect trivially: `bElt 1 ∉ ⟨sElt⟩` because it has
nonzero `v`-coordinate while all powers of `sElt` have `v = 0`. -/
theorem sElt_bElt_disjoint {d : ZMod p} (hp5 : 5 ≤ p) :
    Disjoint (Subgroup.zpowers (sElt p d)) (Subgroup.zpowers (bElt p d 1)) := by
  rw [disjoint_iff]
  by_contra hne
  have hcardK : Nat.card (Subgroup.zpowers (bElt p d 1)) = p := by
    rw [Nat.card_zpowers, orderOf_bElt hp5]
  have hdvd : Nat.card (Subgroup.zpowers (sElt p d) ⊓ Subgroup.zpowers (bElt p d 1) :
      Subgroup (subA p d)) ∣ p := by
    have h := Subgroup.card_dvd_of_le (inf_le_right :
      Subgroup.zpowers (sElt p d) ⊓ Subgroup.zpowers (bElt p d 1) ≤ _)
    rwa [hcardK] at h
  have hpos : 1 < Nat.card (Subgroup.zpowers (sElt p d) ⊓ Subgroup.zpowers (bElt p d 1) :
      Subgroup (subA p d)) := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  have heq : Subgroup.zpowers (sElt p d) ⊓ Subgroup.zpowers (bElt p d 1) =
      Subgroup.zpowers (bElt p d 1) := by
    apply Subgroup.eq_of_le_of_card_ge inf_le_right
    rw [hcardK]
    rcases (Nat.Prime.eq_one_or_self_of_dvd Fact.out _ hdvd) with h | h
    · omega
    · exact le_of_eq h.symm
  have hmem : bElt p d 1 ∈ Subgroup.zpowers (sElt p d) := by
    have : bElt p d 1 ∈ Subgroup.zpowers (sElt p d) ⊓ Subgroup.zpowers (bElt p d 1) := by
      rw [heq]; exact Subgroup.mem_zpowers _
    exact this.1
  obtain ⟨i, hi⟩ := hmem
  have hv1 : vHom (bElt p d 1) = 1 := by
    rw [← hi, map_zpow]
    have : vHom (sElt p d) = 1 := by
      change Multiplicative.ofAdd ((sElt p d : Model p d).v) = 1
      rw [sElt_coe]; rfl
    rw [this, one_zpow]
  have hv2 : vHom (bElt p d 1) = Multiplicative.ofAdd (1 : ZMod p) := rfl
  rw [hv2] at hv1
  exact one_ne_zero (Multiplicative.ofAdd.injective hv1)

/-- `⟨sElt⟩` and `⟨bElt 1⟩` are complementary in `subA d`: their orders multiply
to `p³ = |subA d|` and they are disjoint. -/
theorem sElt_bElt_isComplement {d : ZMod p} (hp5 : 5 ≤ p) (hd : d ≠ 0) :
    (Subgroup.zpowers (sElt p d)).IsComplement' (Subgroup.zpowers (bElt p d 1)) := by
  apply Subgroup.isComplement'_of_card_mul_and_disjoint
  · rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_sElt hp5 hd, orderOf_bElt hp5,
      show (Nat.card (subA p d)) = p ^ 3 from card_subA p d]
    ring
  · exact sElt_bElt_disjoint hp5

/-- Every pair of a `p²`-th root `ζ` and a `p`-th root `ξ` of unity is the pair of
values `(χ(sElt), χ(bElt 1))` of some character of `subA d`. -/
theorem exists_char_values {d : ZMod p} (hp5 : 5 ≤ p) (hd : d ≠ 0)
    (ζ ξ : ℂˣ) (hζ : ζ ^ (p ^ 2) = 1) (hξ : ξ ^ p = 1) :
    ∃ χ : (subA p d) →* ℂˣ, χ (sElt p d) = ζ ∧ χ (bElt p d 1) = ξ := by
  let ev : ((subA p d) →* ℂˣ) →* ℂˣ × ℂˣ :=
    { toFun := fun χ => (χ (sElt p d), χ (bElt p d 1))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hev_inj : Function.Injective ev := by
    rw [injective_iff_map_eq_one]
    intro χ hχ
    rw [MonoidHom.ext_iff]
    intro x
    have h1 : χ (sElt p d) = 1 := (Prod.ext_iff.mp hχ).1
    have h2 : χ (bElt p d 1) = 1 := (Prod.ext_iff.mp hχ).2
    have hker1 : Subgroup.zpowers (sElt p d) ≤ χ.ker := by
      intro y hy; obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [MonoidHom.mem_ker, map_zpow, h1, one_zpow]
    have hker2 : Subgroup.zpowers (bElt p d 1) ≤ χ.ker := by
      intro y hy; obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [MonoidHom.mem_ker, map_zpow, h2, one_zpow]
    have hsup : Subgroup.zpowers (sElt p d) ⊔ Subgroup.zpowers (bElt p d 1) ≤ χ.ker :=
      sup_le hker1 hker2
    have htop : Subgroup.zpowers (sElt p d) ⊔ Subgroup.zpowers (bElt p d 1) = ⊤ :=
      (sElt_bElt_isComplement hp5 hd).sup_eq_top
    rw [htop] at hsup
    have hx : χ x = 1 := MonoidHom.mem_ker.mp (hsup (Subgroup.mem_top x))
    exact hx
  have hcard_dom : Nat.card ((subA p d) →* ℂˣ) = p ^ 3 := by
    have h : Nat.card ((subA p d) →* ℂˣ) = Nat.card (subA p d) := by
      haveI : Finite (subA p d) := Subtype.finite
      haveI : NeZero ((Monoid.exponent (subA p d) : ℂ)) :=
        ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩
      haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent (subA p d)) :=
        IsSepClosed.hasEnoughRootsOfUnity ℂ _
      exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (subA p d) ℂ
    rw [h, card_subA p d]
  let R : Subgroup (ℂˣ × ℂˣ) := (rootsOfUnity (p ^ 2) ℂ).prod (rootsOfUnity p ℂ)
  have hR_equiv : R ≃ (rootsOfUnity (p ^ 2) ℂ) × (rootsOfUnity p ℂ) :=
    Equiv.Set.prod (rootsOfUnity (p ^ 2) ℂ : Set ℂˣ) (rootsOfUnity p ℂ : Set ℂˣ)
  haveI : Finite R := Finite.of_equiv _ hR_equiv.symm
  have hcard_R : Nat.card R = p ^ 3 := by
    haveI : NeZero (p ^ 2) := ⟨by positivity⟩
    haveI : NeZero p := ⟨by positivity⟩
    have h1 : Nat.card (rootsOfUnity (p ^ 2) ℂ) = p ^ 2 := Complex.card_rootsOfUnity (p ^ 2)
    have h2 : Nat.card (rootsOfUnity p ℂ) = p := Complex.card_rootsOfUnity p
    rw [Nat.card_congr hR_equiv, Nat.card_prod, h1, h2]
    ring
  have h_range : ev.range = R := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨χ, rfl⟩
      rw [Subgroup.mem_prod]
      constructor
      · change (χ (sElt p d)) ^ (p ^ 2) = 1
        rw [← map_pow, sElt_pow_psq hp5, map_one]
      · change (χ (bElt p d 1)) ^ p = 1
        rw [← map_pow]
        have hbp : (bElt p d 1) ^ p = 1 := by
          have h1 := pow_orderOf_eq_one (bElt p d 1)
          rw [orderOf_bElt hp5] at h1
          exact h1
        rw [hbp, map_one]
    · rw [hcard_R, ← hcard_dom]
      exact le_of_eq (Nat.card_congr (Equiv.ofInjective ev hev_inj))
  have h_mem_R : (ζ, ξ) ∈ R := by
    rw [Subgroup.mem_prod]
    exact ⟨hζ, hξ⟩
  have h_mem_range : (ζ, ξ) ∈ ev.range := by
    rw [h_range]
    exact h_mem_R
  rcases h_mem_range with ⟨χ, hχ⟩
  use χ
  exact Prod.ext_iff.mp hχ

/-- `zElt z = sElt^{p·(d⁻¹z)}`: the centre is the `p`-th power layer of `⟨sElt⟩`.
Since `sElt^p = zElt d` and `zElt` is additive, `zElt(z) = zElt((d⁻¹z)·d) =
(zElt d)^{(d⁻¹z)} = (sElt^p)^{(d⁻¹z)}`. -/
theorem zElt_eq_sElt_pow {d : ZMod p} (hp5 : 5 ≤ p) (hd : d ≠ 0) (z : ZMod p) :
    zElt p d z = (sElt p d) ^ (p * (d⁻¹ * z).val) := by
  have hnsmul : ∀ (n : ℕ) (w : ZMod p), zElt p d (n • w) = (zElt p d w) ^ n := by
    intro n w
    induction n with
    | zero => simp only [zero_smul, pow_zero]; exact Subtype.ext (by
        change (⟨liftp p 0, 0, 0⟩ : Model p d) = 1; rw [liftp_zero, one_def])
    | succ k ih => rw [succ_nsmul, zElt_add, ih, pow_succ]
  have hz : z = (d⁻¹ * z).val • d := by
    rw [nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id, mul_right_comm, inv_mul_cancel₀ hd,
      one_mul]
  conv_lhs => rw [hz]
  rw [hnsmul, ← sElt_pow_p hp5, ← pow_mul]

open scoped Complex in
/-- **The distinguished character exists.**  For `d ≠ 0`, there is a
character `χ` of `subA d` with `χ(sElt) = ζ_{p²}`, `zChar χ = stdAddChar.mulShift d⁻¹`,
and `bChar χ = stdAddChar.mulShift (-1)` — the exact hypotheses of
`A_block_entry_eq_z_impossible` / `g2_entry_form`.  Instantiates
`exists_char_values` at `(ζ_{p²}, ζ_p⁻¹)`; the `zChar`/`bChar` values are
determined by `χ(sElt)`/`χ(bElt 1)` (via `zElt_eq_sElt_pow` and `bElt` additivity),
checked at the generator `1` through `addChar_ext_of_apply_one`. -/
theorem exists_charDist {d : ZMod p} (hp5 : 5 ≤ p) (hd : d ≠ 0) :
    ∃ χ : (subA p d) →* ℂˣ,
      ((χ (sElt p d) : ℂˣ) : ℂ) = zetaP2 p ∧
      zChar χ = (ZMod.stdAddChar : AddChar (ZMod p) ℂ).mulShift d⁻¹ ∧
      bChar χ = (ZMod.stdAddChar : AddChar (ZMod p) ℂ).mulShift (-1) := by
  have hp : p.Prime := Fact.out
  have hzne : zetaP2 p ≠ 0 := by rw [zetaP2]; exact Complex.exp_ne_zero _
  have hζprim : IsPrimitiveRoot (zetaP2 p) (p ^ 2) := by
    rw [zetaP2]; exact Complex.isPrimitiveRoot_exp (p ^ 2) (pow_ne_zero 2 hp.ne_zero)
  set ζ : ℂˣ := Units.mk0 (zetaP2 p) hzne with hζdef
  have hζval : (ζ : ℂ) = zetaP2 p := rfl
  have hζpsq : ζ ^ (p ^ 2) = 1 := by
    apply Units.ext; push_cast [hζval]; exact hζprim.pow_eq_one
  set ξ : ℂˣ := (ζ ^ p)⁻¹ with hξdef
  have hξp : ξ ^ p = 1 := by
    rw [hξdef, inv_pow, ← pow_mul, show p * p = p ^ 2 by ring, hζpsq, inv_one]
  obtain ⟨χ, hs, hb⟩ := exists_char_values hp5 hd ζ ξ hζpsq hξp
  refine ⟨χ, ?_, ?_, ?_⟩
  · rw [hs, hζval]
  · -- zChar χ = mulShift d⁻¹, checked at 1
    apply addChar_ext_of_apply_one
    change ((χ (zElt p d 1) : ℂˣ) : ℂ) =
      (ZMod.stdAddChar : AddChar (ZMod p) ℂ).mulShift d⁻¹ 1
    rw [zElt_eq_sElt_pow hp5 hd 1, mul_one, map_pow, hs, AddChar.mulShift_apply, mul_one,
      stdAddChar_eq_zeta_pow, Units.val_pow_eq_pow_val, hζval,
      show p * (d⁻¹ : ZMod p).val = (d⁻¹ : ZMod p).val * p from mul_comm _ _, zetaP2_pow_eq]
  · -- bChar χ = mulShift (-1), checked at 1
    apply addChar_ext_of_apply_one
    change ((χ (bElt p d 1) : ℂˣ) : ℂ) =
      (ZMod.stdAddChar : AddChar (ZMod p) ℂ).mulShift (-1) 1
    have hzp : zetaP2 p ^ p = zeta8 p ^ 8 := by simpa using zetaP2_pow_eq (p := p) 1
    have hz8p : zeta8 p ^ (8 * p) = 1 :=
      (Complex.isPrimitiveRoot_exp (8 * p) (by positivity)).pow_eq_one
    have hvneg : ((-1 : ZMod p) * 1).val = p - 1 := by
      rw [mul_one, show (-1 : ZMod p) = ((p - 1 : ℕ) : ZMod p) by
        rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one, zero_sub],
        ZMod.val_natCast_of_lt (by omega)]
    have hmul : zeta8 p ^ (8 * (p - 1)) * zeta8 p ^ 8 = 1 := by
      rw [← pow_add, show 8 * (p - 1) + 8 = 8 * p by omega, hz8p]
    rw [hb, AddChar.mulShift_apply, stdAddChar_eq_zeta_pow, hvneg, hξdef,
      Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, hζval, hzp]
    exact inv_eq_of_mul_eq_one_left hmul

end LeanDring.P4
