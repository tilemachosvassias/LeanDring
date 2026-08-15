/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P4.SocleCount
import LeanDring.P4.SweepCounts
import LeanDring.P4.LastModels

/-!
# Column 2 by socle decomposition: ids 3, 8, 9, (vii) and (xii)/(xiii)

`Gid3 p` (SmallGroup `(p⁴, 3)`, class 2, exponent `p²`) has order-`p²`
subgroup count `2p² + p + 1`. Assembling via the socle decomposition
(`card_p2_subgroups_socle`):

  `N_{p²}(Gid3) = #{cyclic order-p²} + N_{p²}(Ω)`,

where the socle `Ω = {x | redp p x.α = 0}` is the (abelian, exponent-`p`,
order-`p³`) `p`-torsion subgroup. The cyclic count is `p²` (from
`|Ω₁| = p³`, `|Ω₂| = p⁴` and the cyclic double-counting), and the abelian
exponent-`p` engine gives `N_{p²}(Ω) = p² + p + 1`, so the total is
`p² + (p² + p + 1) = 2p² + p + 1`.

The sections below run the same assembly for `Gid8` (`2p² + p + 1`),
`G9` (`2p² + p + 1`), `CH7` (`p² + p + 1`) and `Model p d`
(`p² + p + 1`) — the last two with a *nonabelian* (Heisenberg) socle.
-/

namespace LeanDring.P4

open Finset

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

/-- The **socle** of `Gid3 p`: the `p`-torsion subgroup `{x | redp p x.α = 0}`. -/
def socleGid3 : Subgroup (Gid3 p) where
  carrier := {x | redp p x.α = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    change redp p (a.α + b.α) = 0
    rw [map_add, ha, hb, add_zero]
  one_mem' := by
    change redp p (0 : ZMod (p ^ 2)) = 0
    rw [map_zero]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    change redp p (-a.α) = 0
    rw [map_neg, ha, neg_zero]

omit [Fact (Odd p)] in
theorem mem_socleGid3 {x : Gid3 p} : x ∈ (socleGid3 : Subgroup (Gid3 p)) ↔ redp p x.α = 0 :=
  Iff.rfl

omit [Fact (Odd p)] in
/-- Two socle elements commute: the only asymmetric coordinate (`y`) carries the
factor `redp p α`, which vanishes on the socle. -/
theorem socle_mul_comm {x y : Gid3 p} (hx : redp p x.α = 0) (hy : redp p y.α = 0) :
    x * y = y * x := by
  rw [Gid3.mul_def, Gid3.mul_def, hx, hy]
  refine Gid3.ext ?_ ?_ ?_
  · change x.α + y.α = y.α + x.α; ring
  · change x.y + y.y + x.u * 0 = y.y + x.y + y.u * 0; ring
  · change x.u + y.u = y.u + x.u; ring

omit [Fact (Odd p)] in
/-- The socle is abelian. -/
theorem socleGid3_mul_comm (x y : (socleGid3 : Subgroup (Gid3 p))) : x * y = y * x :=
  Subtype.ext (socle_mul_comm (mem_socleGid3.mp x.2) (mem_socleGid3.mp y.2))

/-- The socle has exponent `p`. -/
theorem socleGid3_exp (x : (socleGid3 : Subgroup (Gid3 p))) : x ^ p = 1 := by
  have h : (x : Gid3 p) ^ p = 1 :=
    (Gid3.pow_p_eq_one_iff (x : Gid3 p)).mpr (mem_socleGid3.mp x.2)
  exact Subtype.ext (by simpa [SubmonoidClass.coe_pow] using h)

variable (p) in
/-- `|Ω| = p³`: the socle is exactly the `p`-torsion, whose count is `p³`. -/
theorem card_socleGid3 : Nat.card (socleGid3 : Subgroup (Gid3 p)) = p ^ 3 := by
  rw [← Gid3.card_omega p]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x =>
    mem_socleGid3.trans (Gid3.pow_p_eq_one_iff x).symm)

variable (p) in
/-- **Table row (x)/(xi) member id 3, second column**: `2p² + p + 1`
subgroups of order `p²`. -/
theorem card_order_p2_subgroups_gid3 :
    Nat.card {H : Subgroup (Gid3 p) // Nat.card H = p ^ 2} = 2 * p ^ 2 + p + 1 := by
  classical
  have hp : p.Prime := Fact.out
  -- Step 1: `#{cyclic order-p²} = p²` via the cyclic double-counting.
  have hΩ1 : (univ.filter fun x : Gid3 p => x ^ p = 1).card = p ^ 3 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Gid3.card_omega p
  have hΩ2 : (univ.filter fun x : Gid3 p => x ^ p ^ 2 = 1).card = p ^ 4 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact card_omega2_gid3
  have hcount : (univ.filter fun x : Gid3 p => orderOf x = p ^ 2).card = p ^ 4 - p ^ 3 := by
    rw [card_orderOf_sq_sub, hΩ1, hΩ2]
  have hcyc := card_orderOf_eq_prime_sq (G := Gid3 p) (p := p)
  rw [hcount] at hcyc
  have harith : p ^ 4 - p ^ 3 = p ^ 2 * (p ^ 2 - p) := by
    rw [Nat.mul_sub]; ring_nf
  rw [harith] at hcyc
  have hpos : 0 < p ^ 2 - p := by
    have h1 := hp.one_lt
    have h2 : p < p ^ 2 := by nlinarith
    omega
  have hN : Nat.card {H : Subgroup (Gid3 p) // Nat.card H = p ^ 2 ∧ IsCyclic H} = p ^ 2 :=
    (Nat.eq_of_mul_eq_mul_right hpos hcyc).symm
  -- Step 2: the socle count `N_{p²}(Ω) = p² + p + 1` (abelian, exp `p`, order `p³`).
  have hΩexp : ∀ x ∈ (socleGid3 : Subgroup (Gid3 p)), x ^ p = 1 := fun x hx =>
    (Gid3.pow_p_eq_one_iff x).mpr (mem_socleGid3.mp hx)
  have hΩtors : ∀ x : Gid3 p, x ^ p = 1 → x ∈ (socleGid3 : Subgroup (Gid3 p)) := fun x hx =>
    mem_socleGid3.mpr ((Gid3.pow_p_eq_one_iff x).mp hx)
  haveI : Fintype (socleGid3 : Subgroup (Gid3 p)) := Fintype.ofFinite _
  have hNΩ : Nat.card {K : Subgroup (socleGid3 : Subgroup (Gid3 p)) // Nat.card K = p ^ 2} =
      p ^ 2 + p + 1 :=
    card_p2_subgroups_abelian_exp_p socleGid3_mul_comm socleGid3_exp (card_socleGid3 p)
  -- Step 3: combine.
  rw [card_p2_subgroups_socle (socleGid3 : Subgroup (Gid3 p)) hΩexp hΩtors, hN, hNΩ]
  ring

/-- The **socle** of `Gid8 p`: the `p`-torsion subgroup `{g | g.w = 0}`. -/
def socleGid8 : Subgroup (Gid8 p) where
  carrier := {g | g.w = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    change a.w + b.w = 0
    rw [ha, hb, add_zero]
  one_mem' := by
    change (1 : Gid8 p).w = 0
    rw [Gid8.one_def]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    change -a.w = 0
    rw [ha, neg_zero]

theorem mem_socleGid8 {g : Gid8 p} : g ∈ (socleGid8 : Subgroup (Gid8 p)) ↔ g.w = 0 :=
  Iff.rfl

omit [Fact (Odd p)] in
/-- Two socle elements commute: with `w = 0` the twisting action `actMC` acts
trivially and the carry cocycle `cvec` vanishes, leaving abelian vector
addition. -/
theorem socle_mul_comm_gid8 {x y : Gid8 p} (hx : x.w = 0) (hy : y.w = 0) :
    x * y = y * x := by
  rw [Gid8.mul_def, Gid8.mul_def, hx, hy]
  refine Gid8.ext ?_ ?_
  · change x.vec + actMC p 0 y.vec + Gid8.cvec p 0 0 = y.vec + actMC p 0 x.vec + Gid8.cvec p 0 0
    rw [actMC_zero, actMC_zero, Gid8.cvec_zero]
    abel
  · change (0 : ZMod p) + 0 = 0 + 0
    ring

/-- The socle is abelian. -/
theorem socleGid8_mul_comm (x y : (socleGid8 : Subgroup (Gid8 p))) : x * y = y * x :=
  Subtype.ext (socle_mul_comm_gid8 (mem_socleGid8.mp x.2) (mem_socleGid8.mp y.2))

/-- The socle has exponent `p`. -/
theorem socleGid8_exp (hp5 : 5 ≤ p) (x : (socleGid8 : Subgroup (Gid8 p))) : x ^ p = 1 := by
  have h : (x : Gid8 p) ^ p = 1 :=
    (Gid8.pow_p_eq_one_iff hp5 (x : Gid8 p)).mpr (mem_socleGid8.mp x.2)
  exact Subtype.ext (by simpa [SubmonoidClass.coe_pow] using h)

variable (p) in
/-- `|Ω| = p³`: the socle is exactly the `p`-torsion, whose count is `p³`. -/
theorem card_socleGid8 (hp5 : 5 ≤ p) : Nat.card (socleGid8 : Subgroup (Gid8 p)) = p ^ 3 := by
  rw [← Gid8.card_omega p hp5]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x =>
    mem_socleGid8.trans (Gid8.pow_p_eq_one_iff hp5 x).symm)

variable (p) in
/-- **Table row (x)/(xi) member id 8, second column**: `2p² + p + 1`
subgroups of order `p²` (`p ≥ 5`). -/
theorem card_order_p2_subgroups_gid8 (hp5 : 5 ≤ p) :
    Nat.card {H : Subgroup (Gid8 p) // Nat.card H = p ^ 2} = 2 * p ^ 2 + p + 1 := by
  classical
  have hp : p.Prime := Fact.out
  -- Step 1: `#{cyclic order-p²} = p²` via the cyclic double-counting.
  have hΩ1 : (univ.filter fun x : Gid8 p => x ^ p = 1).card = p ^ 3 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Gid8.card_omega p hp5
  have hΩ2 : (univ.filter fun x : Gid8 p => x ^ p ^ 2 = 1).card = p ^ 4 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact card_omega2_gid8 hp5
  have hcount : (univ.filter fun x : Gid8 p => orderOf x = p ^ 2).card = p ^ 4 - p ^ 3 := by
    rw [card_orderOf_sq_sub, hΩ1, hΩ2]
  have hcyc := card_orderOf_eq_prime_sq (G := Gid8 p) (p := p)
  rw [hcount] at hcyc
  have harith : p ^ 4 - p ^ 3 = p ^ 2 * (p ^ 2 - p) := by
    rw [Nat.mul_sub]; ring_nf
  rw [harith] at hcyc
  have hpos : 0 < p ^ 2 - p := by
    have h1 := hp.one_lt
    have h2 : p < p ^ 2 := by nlinarith
    omega
  have hN : Nat.card {H : Subgroup (Gid8 p) // Nat.card H = p ^ 2 ∧ IsCyclic H} = p ^ 2 :=
    (Nat.eq_of_mul_eq_mul_right hpos hcyc).symm
  -- Step 2: the socle count `N_{p²}(Ω) = p² + p + 1` (abelian, exp `p`, order `p³`).
  have hΩexp : ∀ x ∈ (socleGid8 : Subgroup (Gid8 p)), x ^ p = 1 := fun x hx =>
    (Gid8.pow_p_eq_one_iff hp5 x).mpr (mem_socleGid8.mp hx)
  have hΩtors : ∀ x : Gid8 p, x ^ p = 1 → x ∈ (socleGid8 : Subgroup (Gid8 p)) := fun x hx =>
    mem_socleGid8.mpr ((Gid8.pow_p_eq_one_iff hp5 x).mp hx)
  haveI : Fintype (socleGid8 : Subgroup (Gid8 p)) := Fintype.ofFinite _
  have hNΩ : Nat.card {K : Subgroup (socleGid8 : Subgroup (Gid8 p)) // Nat.card K = p ^ 2} =
      p ^ 2 + p + 1 :=
    card_p2_subgroups_abelian_exp_p socleGid8_mul_comm (socleGid8_exp hp5) (card_socleGid8 p hp5)
  -- Step 3: combine.
  rw [card_p2_subgroups_socle (socleGid8 : Subgroup (Gid8 p)) hΩexp hΩtors, hN, hNΩ]
  ring

/-! ## Column 2 for group id 9: `N_{p²}(G9) = 2p² + p + 1`

`G9 p = Mod3 p × C_p` (SmallGroup `(p⁴, 13)`). The socle is the `p`-torsion
subgroup `Ω = {x | redp p x.1.α = 0}`: the `Mod3`-coordinate is `p`-divisible
while the central `C_p` factor is unconstrained. Same socle assembly as `Gid3`.
-/

/-- `x^p = 1` in `G9` iff its `Mod3`-coordinate is `p`-torsion: the central
`C_p` factor always satisfies `c^p = 1`, so only the `Mod3` factor constrains. -/
theorem pow_p_eq_one_iff_g9 (x : G9 p) : x ^ p = 1 ↔ redp p x.1.α = 0 := by
  constructor
  · intro h
    have h1 : x.1 ^ p = 1 := congrArg Prod.fst h
    exact (Mod3.pow_p_eq_one_iff x.1).mp h1
  · intro h
    have h1 : x.1 ^ p = 1 := (Mod3.pow_p_eq_one_iff x.1).mpr h
    exact Prod.ext h1 (multZMod_pow_p x.2)

/-- The **socle** of `G9 p`: the `p`-torsion subgroup `{x | redp p x.1.α = 0}`. -/
def socleG9 : Subgroup (G9 p) where
  carrier := {x | redp p x.1.α = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    change redp p (a.1.α + b.1.α + liftp p (a.1.u * redp p b.1.α)) = 0
    simp only [map_add, redp_liftp, ha, hb, add_zero]
  one_mem' := by
    change redp p (0 : ZMod (p ^ 2)) = 0
    rw [map_zero]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    change redp p (-a.1.α + liftp p (a.1.u * redp p a.1.α)) = 0
    simp only [map_add, map_neg, ha, neg_zero, redp_liftp, add_zero]

omit [Fact (Odd p)] in
theorem mem_socleG9 {x : G9 p} : x ∈ (socleG9 : Subgroup (G9 p)) ↔ redp p x.1.α = 0 :=
  Iff.rfl

omit [Fact (Odd p)] in
/-- Two socle elements commute: in the `Mod3` factor the only asymmetric
coordinate carries `redp p α`, which vanishes on the socle; the `C_p` factor is
central. -/
theorem socleG9_coe_mul_comm {x y : G9 p} (hx : redp p x.1.α = 0) (hy : redp p y.1.α = 0) :
    x * y = y * x := by
  refine Prod.ext ?_ ?_
  · change x.1 * y.1 = y.1 * x.1
    rw [Mod3.mul_def, Mod3.mul_def, hx, hy]
    refine Mod3.ext ?_ ?_
    · change x.1.α + y.1.α + liftp p (x.1.u * 0) = y.1.α + x.1.α + liftp p (y.1.u * 0)
      simp only [mul_zero, liftp_zero, add_zero]; ring
    · change x.1.u + y.1.u = y.1.u + x.1.u; ring
  · change x.2 * y.2 = y.2 * x.2
    exact mul_comm _ _

omit [Fact (Odd p)] in
/-- The socle is abelian. -/
theorem socleG9_mul_comm (x y : (socleG9 : Subgroup (G9 p))) : x * y = y * x :=
  Subtype.ext (socleG9_coe_mul_comm (mem_socleG9.mp x.2) (mem_socleG9.mp y.2))

/-- The socle has exponent `p`. -/
theorem socleG9_exp (x : (socleG9 : Subgroup (G9 p))) : x ^ p = 1 := by
  have h : (x : G9 p) ^ p = 1 :=
    (pow_p_eq_one_iff_g9 (x : G9 p)).mpr (mem_socleG9.mp x.2)
  exact Subtype.ext (by simpa [SubmonoidClass.coe_pow] using h)

variable (p) in
/-- `|Ω| = p³`: the socle is exactly the `p`-torsion, whose count is `p³`. -/
theorem card_socleG9 : Nat.card (socleG9 : Subgroup (G9 p)) = p ^ 3 := by
  rw [← card_omega_g9 p]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x =>
    mem_socleG9.trans (pow_p_eq_one_iff_g9 x).symm)

variable (p) in
/-- **Table row (ix), second column**: `M(p³) × C_p` has exactly `2p² + p + 1`
subgroups of order `p²`. -/
theorem card_order_p2_subgroups_g9 :
    Nat.card {H : Subgroup (G9 p) // Nat.card H = p ^ 2} = 2 * p ^ 2 + p + 1 := by
  classical
  have hp : p.Prime := Fact.out
  -- Step 1: `#{cyclic order-p²} = p²` via the cyclic double-counting.
  have hΩ1 : (univ.filter fun x : G9 p => x ^ p = 1).card = p ^ 3 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact card_omega_g9 p
  have hΩ2 : (univ.filter fun x : G9 p => x ^ p ^ 2 = 1).card = p ^ 4 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact card_omega2_g9
  have hcount : (univ.filter fun x : G9 p => orderOf x = p ^ 2).card = p ^ 4 - p ^ 3 := by
    rw [card_orderOf_sq_sub, hΩ1, hΩ2]
  have hcyc := card_orderOf_eq_prime_sq (G := G9 p) (p := p)
  rw [hcount] at hcyc
  have harith : p ^ 4 - p ^ 3 = p ^ 2 * (p ^ 2 - p) := by
    rw [Nat.mul_sub]; ring_nf
  rw [harith] at hcyc
  have hpos : 0 < p ^ 2 - p := by
    have h1 := hp.one_lt
    have h2 : p < p ^ 2 := by nlinarith
    omega
  have hN : Nat.card {H : Subgroup (G9 p) // Nat.card H = p ^ 2 ∧ IsCyclic H} = p ^ 2 :=
    (Nat.eq_of_mul_eq_mul_right hpos hcyc).symm
  -- Step 2: the socle count `N_{p²}(Ω) = p² + p + 1` (abelian, exp `p`, order `p³`).
  have hΩexp : ∀ x ∈ (socleG9 : Subgroup (G9 p)), x ^ p = 1 := fun x hx =>
    (pow_p_eq_one_iff_g9 x).mpr (mem_socleG9.mp hx)
  have hΩtors : ∀ x : G9 p, x ^ p = 1 → x ∈ (socleG9 : Subgroup (G9 p)) := fun x hx =>
    mem_socleG9.mpr ((pow_p_eq_one_iff_g9 x).mp hx)
  haveI : Fintype (socleG9 : Subgroup (G9 p)) := Fintype.ofFinite _
  have hNΩ : Nat.card {K : Subgroup (socleG9 : Subgroup (G9 p)) // Nat.card K = p ^ 2} =
      p ^ 2 + p + 1 :=
    card_p2_subgroups_abelian_exp_p socleG9_mul_comm socleG9_exp (card_socleG9 p)
  -- Step 3: combine.
  rw [card_p2_subgroups_socle (socleG9 : Subgroup (G9 p)) hΩexp hΩtors, hN, hNΩ]
  ring

/-! ## Column 2 for group id 7 (vii): `N_{p²}(CH7) = p² + p + 1`

`CH7 p = C_{p²} ∘ Heis(p)` (SmallGroup `(p⁴, 14)`). The socle is the `p`-torsion
subgroup `Ω = {a | redp p a.z = 0}`. Unlike `Gid3`/`Gid8`/`G9`, this socle is
**nonabelian** (it is the Heisenberg group `Heis(p)`), so the socle count is
`N_{p²}(Ω) = p + 1` (extraspecial) rather than `p² + p + 1`. The cyclic count is
still `p²`, giving the total `p² + (p + 1) = p² + p + 1`.
-/

/-- The **socle** of `CH7 p`: the `p`-torsion subgroup `{a | redp p a.z = 0}`. -/
def socleCH7 : Subgroup (CH7 p) where
  carrier := {a | redp p a.z = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    change redp p (a.z + b.z + liftp p (a.x * b.y)) = 0
    simp only [map_add, redp_liftp, ha, hb, add_zero]
  one_mem' := by
    change redp p (0 : ZMod (p ^ 2)) = 0
    rw [map_zero]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    change redp p (-a.z + liftp p (a.x * a.y)) = 0
    simp only [map_add, map_neg, ha, neg_zero, redp_liftp, add_zero]

omit [Fact (Odd p)] in
theorem mem_socleCH7 {a : CH7 p} : a ∈ (socleCH7 : Subgroup (CH7 p)) ↔ redp p a.z = 0 :=
  Iff.rfl

/-- The socle has exponent `p`. -/
theorem socleCH7_exp (x : (socleCH7 : Subgroup (CH7 p))) : x ^ p = 1 := by
  have h : (x : CH7 p) ^ p = 1 :=
    (CH7.pow_p_eq_one_iff (x : CH7 p)).mpr (mem_socleCH7.mp x.2)
  exact Subtype.ext (by simpa [SubmonoidClass.coe_pow] using h)

omit [Fact (Odd p)] in
/-- The socle is **nonabelian**: it is the Heisenberg group, and the two order-`p`
generators `⟨1,0,0⟩` and `⟨0,1,0⟩` (both in `Ω`) fail to commute — their products
differ in the central `z`-coordinate by `liftp p 1 ≠ 0`. -/
theorem socleCH7_nonabelian :
    ∃ a b : (socleCH7 : Subgroup (CH7 p)), a * b ≠ b * a := by
  have hmemA : (⟨1, 0, 0⟩ : CH7 p) ∈ (socleCH7 : Subgroup (CH7 p)) := by
    rw [mem_socleCH7]; change redp p (0 : ZMod (p ^ 2)) = 0; rw [map_zero]
  have hmemB : (⟨0, 1, 0⟩ : CH7 p) ∈ (socleCH7 : Subgroup (CH7 p)) := by
    rw [mem_socleCH7]; change redp p (0 : ZMod (p ^ 2)) = 0; rw [map_zero]
  refine ⟨⟨⟨1, 0, 0⟩, hmemA⟩, ⟨⟨0, 1, 0⟩, hmemB⟩, ?_⟩
  intro h
  have hc : (⟨1, 0, 0⟩ : CH7 p) * ⟨0, 1, 0⟩ = (⟨0, 1, 0⟩ : CH7 p) * ⟨1, 0, 0⟩ :=
    congrArg Subtype.val h
  rw [CH7.mul_def, CH7.mul_def] at hc
  have hz := congrArg CH7.z hc
  simp only [zero_add, mul_one, mul_zero, liftp_zero] at hz
  -- hz : liftp p 1 = 0
  exact one_ne_zero (Model.liftp_eq_zero_iff.mp hz)

variable (p) in
/-- `|Ω| = p³`: the socle is exactly the `p`-torsion, whose count is `p³`. -/
theorem card_socleCH7 : Nat.card (socleCH7 : Subgroup (CH7 p)) = p ^ 3 := by
  rw [← CH7.card_omega p]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x =>
    mem_socleCH7.trans (CH7.pow_p_eq_one_iff x).symm)

variable (p) in
/-- **Table row (vii), second column**: `C_{p²} ∘ Heis(p)` has exactly
`p² + p + 1` subgroups of order `p²`. The socle is the nonabelian Heisenberg
group, so its `N_{p²}` is `p + 1` (not `p² + p + 1`). -/
theorem card_order_p2_subgroups_ch7 :
    Nat.card {H : Subgroup (CH7 p) // Nat.card H = p ^ 2} = p ^ 2 + p + 1 := by
  classical
  have hp : p.Prime := Fact.out
  -- Step 1: `#{cyclic order-p²} = p²` via the cyclic double-counting.
  have hΩ1 : (univ.filter fun x : CH7 p => x ^ p = 1).card = p ^ 3 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact CH7.card_omega p
  have hΩ2 : (univ.filter fun x : CH7 p => x ^ p ^ 2 = 1).card = p ^ 4 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact card_omega2_ch7
  have hcount : (univ.filter fun x : CH7 p => orderOf x = p ^ 2).card = p ^ 4 - p ^ 3 := by
    rw [card_orderOf_sq_sub, hΩ1, hΩ2]
  have hcyc := card_orderOf_eq_prime_sq (G := CH7 p) (p := p)
  rw [hcount] at hcyc
  have harith : p ^ 4 - p ^ 3 = p ^ 2 * (p ^ 2 - p) := by
    rw [Nat.mul_sub]; ring_nf
  rw [harith] at hcyc
  have hpos : 0 < p ^ 2 - p := by
    have h1 := hp.one_lt
    have h2 : p < p ^ 2 := by nlinarith
    omega
  have hN : Nat.card {H : Subgroup (CH7 p) // Nat.card H = p ^ 2 ∧ IsCyclic H} = p ^ 2 :=
    (Nat.eq_of_mul_eq_mul_right hpos hcyc).symm
  -- Step 2: the socle count `N_{p²}(Ω) = p + 1` (NONABELIAN, exp `p`, order `p³`).
  have hΩexp : ∀ x ∈ (socleCH7 : Subgroup (CH7 p)), x ^ p = 1 := fun x hx =>
    (CH7.pow_p_eq_one_iff x).mpr (mem_socleCH7.mp hx)
  have hΩtors : ∀ x : CH7 p, x ^ p = 1 → x ∈ (socleCH7 : Subgroup (CH7 p)) := fun x hx =>
    mem_socleCH7.mpr ((CH7.pow_p_eq_one_iff x).mp hx)
  haveI : Fintype (socleCH7 : Subgroup (CH7 p)) := Fintype.ofFinite _
  have hNΩ : Nat.card {K : Subgroup (socleCH7 : Subgroup (CH7 p)) // Nat.card K = p ^ 2} =
      p + 1 :=
    card_p2_subgroups_nonabelian_exp_p socleCH7_exp (card_socleCH7 p) socleCH7_nonabelian
  -- Step 3: combine.
  rw [card_p2_subgroups_socle (socleCH7 : Subgroup (CH7 p)) hΩexp hΩtors, hN, hNΩ]
  ring

/-! ## Column 2 for the critical pair (xii)/(xiii): `N_{p²}(Model p d) = p² + p + 1`

`Model p d` (the concrete order-`p⁴` model, `d ≠ 0`) is a
maximal-class group whose socle is the `p`-torsion subgroup
`Ω = {x | redp p x.α + d·x.u = 0}`. As for `CH7`, this socle is **nonabelian**
(Heisenberg): the commutator lands in the central `α`-coordinate as `liftp(-d)`,
nonzero exactly when `d ≠ 0`. Hence `N_{p²}(Ω) = p + 1` (extraspecial), and with
the cyclic count `p²` the total is `p² + (p + 1) = p² + p + 1`. -/

variable {d : ZMod p}

/-- The **socle** of `Model p d`: the `p`-torsion subgroup
`{x | redp p x.α + d·x.u = 0}` (closed under the group operations because both
`redp α` and `u` are additive across the model's multiplication). -/
def socleModel : Subgroup (Model p d) where
  carrier := {x | redp p x.α + d * x.u = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    change redp p (a.α + b.α + liftp p (tauP p d (redp p b.α) a.u a.v) +
        Model.dc d * carryF p a.u b.u) + d * (a.u + b.u) = 0
    simp only [map_add, redp_liftp, map_mul, redp_carryF, mul_zero, add_zero]
    linear_combination ha + hb
  one_mem' := by
    change redp p (0 : ZMod (p ^ 2)) + d * 0 = 0
    rw [map_zero, mul_zero, add_zero]
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    change redp p (-x.α - liftp p (tauP p d (redp p x.α) (-x.u)
        (redp p x.α * x.u - x.v)) - Model.dc d * carryF p (-x.u) x.u) +
        d * (-x.u) = 0
    simp only [map_sub, map_neg, redp_liftp, map_mul, redp_carryF, mul_zero,
      sub_zero]
    linear_combination -hx

theorem mem_socleModel {x : Model p d} :
    x ∈ (socleModel : Subgroup (Model p d)) ↔ redp p x.α + d * x.u = 0 :=
  Iff.rfl

/-- The socle has exponent `p`. -/
theorem socleModel_exp (hp5 : 5 ≤ p) (x : (socleModel : Subgroup (Model p d))) :
    x ^ p = 1 := by
  have h : (x : Model p d) ^ p = 1 :=
    (Model.pow_p_eq_one_iff hp5 (x : Model p d)).mpr (mem_socleModel.mp x.2)
  exact Subtype.ext (by simpa [SubmonoidClass.coe_pow] using h)

/-- The socle is **nonabelian** (`d ≠ 0`): the order-`p` generators `⟨0,0,1⟩` and
`⟨dc(-d),1,0⟩` both lie in `Ω`, but their products differ in the central
`α`-coordinate by `liftp p (-d) ≠ 0`. -/
theorem socleModel_nonabelian (hd : d ≠ 0) :
    ∃ a b : (socleModel : Subgroup (Model p d)), a * b ≠ b * a := by
  have hmemA : (⟨0, 0, 1⟩ : Model p d) ∈ (socleModel : Subgroup (Model p d)) := by
    rw [mem_socleModel]; change redp p (0 : ZMod (p ^ 2)) + d * 0 = 0
    rw [map_zero, mul_zero, add_zero]
  have hmemB : (⟨Model.dc (-d), 1, 0⟩ : Model p d) ∈
      (socleModel : Subgroup (Model p d)) := by
    rw [mem_socleModel]; change redp p (Model.dc (-d)) + d * 1 = 0
    rw [Model.redp_dc]; ring
  refine ⟨⟨⟨0, 0, 1⟩, hmemA⟩, ⟨⟨Model.dc (-d), 1, 0⟩, hmemB⟩, ?_⟩
  intro h
  have hc : (⟨0, 0, 1⟩ : Model p d) * ⟨Model.dc (-d), 1, 0⟩ =
      (⟨Model.dc (-d), 1, 0⟩ : Model p d) * ⟨0, 0, 1⟩ := congrArg Subtype.val h
  -- the two products agree in every coordinate, in particular the central `α`
  have hL : ((⟨0, 0, 1⟩ : Model p d) * ⟨Model.dc (-d), 1, 0⟩).α =
      Model.dc (-d) + liftp p (-d) := by
    rw [Model.mul_def]
    change (0 : ZMod (p ^ 2)) + Model.dc (-d) +
        liftp p (tauP p d (redp p (Model.dc (-d))) 0 1) +
        Model.dc d * carryF p 0 1 = Model.dc (-d) + liftp p (-d)
    rw [Model.redp_dc, carryF_zero']
    have htau : tauP p d (-d) 0 1 = -d := by unfold tauP; ring
    rw [htau]; ring
  have hR : ((⟨Model.dc (-d), 1, 0⟩ : Model p d) * ⟨0, 0, 1⟩).α = Model.dc (-d) := by
    rw [Model.mul_def]
    change Model.dc (-d) + (0 : ZMod (p ^ 2)) +
        liftp p (tauP p d (redp p (0 : ZMod (p ^ 2))) 1 0) +
        Model.dc d * carryF p 1 0 = Model.dc (-d)
    rw [map_zero, Model.tauP_zero_left, liftp_zero, carryF_zero, mul_zero,
      add_zero, add_zero, add_zero]
  have hαeq : Model.dc (-d) + liftp p (-d) = Model.dc (-d) := by
    have h2 := congrArg Model.α hc
    rw [hL, hR] at h2; exact h2
  have hz : liftp p (-d) = 0 :=
    add_left_cancel (a := Model.dc (-d)) (by rw [hαeq, add_zero])
  exact hd (neg_eq_zero.mp (Model.liftp_eq_zero_iff.mp hz))

variable (p) in
/-- `|Ω| = p³`: the socle is exactly the `p`-torsion, whose count is `p³`. -/
theorem card_socleModel (hp5 : 5 ≤ p) :
    Nat.card (socleModel : Subgroup (Model p d)) = p ^ 3 := by
  rw [← Model.card_omega1 (d := d) hp5]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x =>
    mem_socleModel.trans (Model.pow_p_eq_one_iff hp5 x).symm)

variable (p) in
/-- **Table row (xii)/(xiii), second column**: the critical-pair model `Model p d`
(`d ≠ 0`, `p ≥ 5`) has exactly `p² + p + 1` subgroups of order `p²`. The socle is
the nonabelian Heisenberg group, so its `N_{p²}` is `p + 1` (not `p² + p + 1`). -/
theorem card_order_p2_subgroups_model (hp5 : 5 ≤ p) (hd : d ≠ 0) :
    Nat.card {H : Subgroup (Model p d) // Nat.card H = p ^ 2} = p ^ 2 + p + 1 := by
  classical
  have hp : p.Prime := Fact.out
  -- Step 1: `#{cyclic order-p²} = p²` via the cyclic double-counting.
  have hΩ1 : (univ.filter fun x : Model p d => x ^ p = 1).card = p ^ 3 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Model.card_omega1 hp5
  have hΩ2 : (univ.filter fun x : Model p d => x ^ p ^ 2 = 1).card = p ^ 4 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact card_omega2_model hp5
  have hcount : (univ.filter fun x : Model p d => orderOf x = p ^ 2).card =
      p ^ 4 - p ^ 3 := by
    rw [card_orderOf_sq_sub, hΩ1, hΩ2]
  have hcyc := card_orderOf_eq_prime_sq (G := Model p d) (p := p)
  rw [hcount] at hcyc
  have harith : p ^ 4 - p ^ 3 = p ^ 2 * (p ^ 2 - p) := by
    rw [Nat.mul_sub]; ring_nf
  rw [harith] at hcyc
  have hpos : 0 < p ^ 2 - p := by
    have h1 := hp.one_lt
    have h2 : p < p ^ 2 := by nlinarith
    omega
  have hN : Nat.card {H : Subgroup (Model p d) // Nat.card H = p ^ 2 ∧ IsCyclic H} =
      p ^ 2 := (Nat.eq_of_mul_eq_mul_right hpos hcyc).symm
  -- Step 2: the socle count `N_{p²}(Ω) = p + 1` (NONABELIAN, exp `p`, order `p³`).
  have hΩexp : ∀ x ∈ (socleModel : Subgroup (Model p d)), x ^ p = 1 := fun x hx =>
    (Model.pow_p_eq_one_iff hp5 x).mpr (mem_socleModel.mp hx)
  have hΩtors : ∀ x : Model p d, x ^ p = 1 → x ∈ (socleModel : Subgroup (Model p d)) :=
    fun x hx => mem_socleModel.mpr ((Model.pow_p_eq_one_iff hp5 x).mp hx)
  haveI : Fintype (socleModel : Subgroup (Model p d)) := Fintype.ofFinite _
  have hNΩ : Nat.card {K : Subgroup (socleModel : Subgroup (Model p d)) //
      Nat.card K = p ^ 2} = p + 1 :=
    card_p2_subgroups_nonabelian_exp_p (socleModel_exp hp5) (card_socleModel p hp5)
      (socleModel_nonabelian hd)
  -- Step 3: combine.
  rw [card_p2_subgroups_socle (socleModel : Subgroup (Model p d)) hΩexp hΩtors, hN, hNΩ]
  ring

end LeanDring.P4
