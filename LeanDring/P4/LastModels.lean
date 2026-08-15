/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P4.ModelPow
import LeanDring.P4.ExpModels
import LeanDring.P4.ModularModels
import Mathlib.Algebra.BigOperators.Pi

/-!
# The last two models: groups (x)/(xi) = SmallGroups `(p⁴, 3)` and `(p⁴, 8)`

The pair `{(x), (xi)}` of the [GJG10] table is `{id 3, id 8}` (they share
all three subgroup-count columns `[p²+p+1, 2p²+p+1, p+1]`, and are
separated only by finer invariants — the class-count patch of the audit):

* **`Gid3`** (id 3, class 2): `(C_{p²} × C_p) ⋊ C_p` — Heisenberg-type
  with `a` of order `p²` and central commutator `c` generating a
  *separate* `C_p`: `[b, a] = c`, `Z = ⟨aᵖ, c⟩ ≅ C_p × C_p`;
* **`Gid8`** (id 8, class 3, maximal class): `(C_{p²} ⋊ C_p) ⋊ C_p` —
  the outer generator acts on `⟨a, b⟩ ≅ C_{p²} × C_p` by the mixed-level
  unipotent `a ↦ ab`, `b ↦ b aᵖ`; `Z = ⟨aᵖ⟩ ≅ C_p`.

Main results (sorry-free): group instances, `card = p⁴`, power laws,
`xᵖ = 1 ⟺ α ≡ 0 (mod p)` in both, `Ω₁ = p³`, and the shared
**first-column table row `p² + p + 1`** — completing all ten nonabelian
order-`p⁴` first-column rows from presentations.
-/

namespace LeanDring

namespace P4

open Finset Model

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

/-! ## Group id 3: `(C_{p²} × C_p) ⋊ C_p`, central commutator -/

variable (p) in
/-- **Group id 3** (one of the pair `(x)/(xi)`): normal forms
`a^α c^y b^u` with `[b, a] = c` central, `a` of order `p²`. -/
@[ext]
structure Gid3 where
  α : ZMod (p ^ 2)
  y : ZMod p
  u : ZMod p

namespace Gid3

instance : Mul (Gid3 p) :=
  ⟨fun x w => ⟨x.α + w.α, x.y + w.y + x.u * redp p w.α, x.u + w.u⟩⟩

instance : One (Gid3 p) := ⟨⟨0, 0, 0⟩⟩

instance : Inv (Gid3 p) :=
  ⟨fun x => ⟨-x.α, -x.y + x.u * redp p x.α, -x.u⟩⟩

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem mul_def (x w : Gid3 p) :
    x * w = ⟨x.α + w.α, x.y + w.y + x.u * redp p w.α, x.u + w.u⟩ := rfl

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem one_def : (1 : Gid3 p) = ⟨0, 0, 0⟩ := rfl

instance : Group (Gid3 p) :=
  Group.ofLeftAxioms
    (fun x w z => by
      simp only [mul_def]
      ext
      · change x.α + w.α + z.α = x.α + (w.α + z.α)
        ring
      · change x.y + w.y + x.u * redp p w.α + z.y +
            (x.u + w.u) * redp p z.α =
          x.y + (w.y + z.y + w.u * redp p z.α) +
            x.u * redp p (w.α + z.α)
        rw [map_add]
        ring
      · change x.u + w.u + z.u = x.u + (w.u + z.u)
        ring)
    (fun x => by
      simp only [mul_def, one_def]
      ext
      · change (0 : ZMod (p ^ 2)) + x.α = x.α
        ring
      · change (0 : ZMod p) + x.y + 0 * redp p x.α = x.y
        ring
      · change (0 : ZMod p) + x.u = x.u
        ring)
    (fun x => by
      change (⟨-x.α, -x.y + x.u * redp p x.α, -x.u⟩ : Gid3 p) * x = 1
      simp only [mul_def, one_def]
      ext
      · change -x.α + x.α = 0
        ring
      · change -x.y + x.u * redp p x.α + x.y + -x.u * redp p x.α = 0
        ring
      · change -x.u + x.u = 0
        ring)

variable (p) in
def toProd : Gid3 p ≃ ZMod (p ^ 2) × ZMod p × ZMod p where
  toFun x := (x.α, x.y, x.u)
  invFun w := ⟨w.1, w.2.1, w.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : Fintype (Gid3 p) :=
  Fintype.ofEquiv _ (toProd p).symm

variable (p) in
omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem card_gid3 : Nat.card (Gid3 p) = p ^ 4 := by
  rw [Nat.card_congr (toProd p), Nat.card_prod, Nat.card_prod,
    Nat.card_zmod, Nat.card_zmod]
  ring

/-- Powers in `Gid3`: `xⁿ = ⟨nα, ny + T(n)·u·(α mod p), nu⟩`. -/
theorem pow_formula (x : Gid3 p) (n : ℕ) :
    x ^ n = ⟨(n : ZMod (p ^ 2)) * x.α,
      (n : ZMod p) * x.y + tri p ((n : ZMod p)) * (x.u * redp p x.α),
      (n : ZMod p) * x.u⟩ := by
  induction n with
  | zero =>
    change (1 : Gid3 p) = _
    rw [one_def]
    have htri : tri p ((0 : ℕ) : ZMod p) = 0 := by
      unfold tri
      push_cast
      ring
    ext
    · change (0 : ZMod (p ^ 2)) = ((0 : ℕ) : ZMod (p ^ 2)) * x.α
      push_cast
      ring
    · change (0 : ZMod p) = ((0 : ℕ) : ZMod p) * x.y +
        tri p ((0 : ℕ) : ZMod p) * (x.u * redp p x.α)
      rw [htri]
      push_cast
      ring
    · change (0 : ZMod p) = ((0 : ℕ) : ZMod p) * x.u
      push_cast
      ring
  | succ n ih =>
    rw [pow_succ, ih, mul_def]
    have htri : tri p ((n + 1 : ℕ) : ZMod p) =
        tri p ((n : ZMod p)) + (n : ZMod p) := by
      push_cast
      rw [tri_add]
      have h1 : tri p (1 : ZMod p) = 0 := by
        unfold tri
        ring
      rw [h1]
      ring
    ext
    · change (n : ZMod (p ^ 2)) * x.α + x.α = ((n + 1 : ℕ) : ZMod (p ^ 2)) * x.α
      push_cast
      ring
    · change (n : ZMod p) * x.y + tri p ((n : ZMod p)) * (x.u * redp p x.α) +
          x.y + ((n : ZMod p) * x.u) * redp p x.α =
        ((n + 1 : ℕ) : ZMod p) * x.y +
          tri p ((n + 1 : ℕ) : ZMod p) * (x.u * redp p x.α)
      rw [htri]
      push_cast
      ring
    · change (n : ZMod p) * x.u + x.u = ((n + 1 : ℕ) : ZMod p) * x.u
      push_cast
      ring

/-- Torsion criterion in `Gid3`: `xᵖ = 1 ⟺ α ≡ 0 (mod p)`. -/
theorem pow_p_eq_one_iff (x : Gid3 p) :
    x ^ p = 1 ↔ redp p x.α = 0 := by
  have hp0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have htri : tri p (0 : ZMod p) = 0 := by
    unfold tri
    ring
  have hpow : x ^ p = ⟨liftp p (redp p x.α), 0, 0⟩ := by
    rw [pow_formula]
    ext
    · change ((p : ℕ) : ZMod (p ^ 2)) * x.α = liftp p (redp p x.α)
      exact p_mul_eq_liftp_redp x.α
    · change ((p : ℕ) : ZMod p) * x.y +
          tri p ((p : ℕ) : ZMod p) * (x.u * redp p x.α) = 0
      rw [hp0, htri]
      ring
    · change ((p : ℕ) : ZMod p) * x.u = 0
      rw [hp0, zero_mul]
  rw [hpow, one_def]
  constructor
  · intro h
    exact liftp_eq_zero_iff.mp (congrArg Gid3.α h)
  · intro h
    rw [h, liftp_zero]

variable (p) in
/-- `|Ω₁(Gid3)| = p³`. -/
theorem card_omega : Nat.card {x : Gid3 p // x ^ p = 1} = p ^ 3 := by
  have hp : p.Prime := Fact.out
  let f : ZMod p × ZMod p × ZMod p → {x : Gid3 p // x ^ p = 1} := fun w =>
    ⟨⟨liftp p w.1, w.2.1, w.2.2⟩, by
      rw [pow_p_eq_one_iff]
      exact redp_liftp w.1⟩
  let g : {x : Gid3 p // x ^ p = 1} → ZMod p × ZMod p × ZMod p := fun x =>
    (((x.1.α.val / p : ℕ) : ZMod p), x.1.y, x.1.u)
  have hbij : Function.Bijective f := by
    rw [Function.bijective_iff_has_inverse]
    refine ⟨g, fun w => ?_, fun x => ?_⟩
    · change ((((liftp p w.1).val / p : ℕ) : ZMod p), w.2.1, w.2.2) = w
      rw [liftp_val, Nat.mul_div_cancel_left _
        (Nat.pos_of_ne_zero hp.ne_zero), ZMod.natCast_val, ZMod.cast_id]
    · obtain ⟨x, hx⟩ := x
      have hred : redp p x.α = 0 := (pow_p_eq_one_iff x).mp hx
      refine Subtype.ext ?_
      change (⟨liftp p (((x.α.val / p : ℕ) : ZMod p)), x.y, x.u⟩ : Gid3 p) = x
      ext
      · exact liftp_of_redp_zero hred
      · rfl
      · rfl
  rw [← Nat.card_eq_of_bijective f hbij, Nat.card_prod, Nat.card_prod,
    Nat.card_zmod]
  ring

variable (p) in
/-- **Table row (x)/(xi) member id 3, first column**: `p² + p + 1`
subgroups of order `p`. -/
theorem card_order_p_subgroups_gid3 :
    Nat.card {H : Subgroup (Gid3 p) // Nat.card H = p} = p ^ 2 + p + 1 := by
  have h := card_order_p_subgroups_of_omega (Gid3 p) 3 (card_omega p)
  rw [h, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  ring

end Gid3

/-! ## Group id 8: the non-split `(C_p)³ ⋊ C_{p²}`, maximal class

GAP's pc presentation of SmallGroup `(p⁴, 8)`: `g₁` of order `p²` with
`g₁ᵖ = g₄` central, acting on `V = ⟨g₂,g₃,g₄⟩ ≅ (C_p)³` by the regular
unipotent (`g₂ ↦ g₂g₃`, `g₃ ↦ g₃g₄`). This is `MaxClass` twisted by the
carry 2-cocycle of `C_{p²} → C_p` landing in the center `⟨g₄⟩`. -/

variable (p) in
/-- The carry bit of addition in `ZMod p`: `0` or `1`. -/
def cbitN (x y : ZMod p) : ℕ := (x.val + y.val - (x + y).val) / p

omit [Fact (Odd p)] in
theorem cbit_spec (x y : ZMod p) :
    (x + y).val + p * cbitN p x y = x.val + y.val ∧ cbitN p x y ≤ 1 := by
  have hp : p.Prime := Fact.out
  have hppos : 0 < p := Nat.pos_of_ne_zero hp.ne_zero
  obtain ⟨hle, h0 | hpd⟩ := carry_val x y
  · have hc : cbitN p x y = 0 := by
      unfold cbitN
      rw [h0]
      exact Nat.zero_div p
    rw [hc]
    omega
  · have hc : cbitN p x y = 1 := by
      unfold cbitN
      rw [hpd]
      exact Nat.div_self hppos
    rw [hc]
    omega

omit [Fact (Odd p)] in
/-- The carry-bit 2-cocycle identity. -/
theorem cbit_cocycle (x y z : ZMod p) :
    cbitN p x y + cbitN p (x + y) z = cbitN p y z + cbitN p x (y + z) := by
  have hp : p.Prime := Fact.out
  have hppos : 0 < p := Nat.pos_of_ne_zero hp.ne_zero
  obtain ⟨s1, -⟩ := cbit_spec (p := p) x y
  obtain ⟨s2, -⟩ := cbit_spec (p := p) (x + y) z
  obtain ⟨s3, -⟩ := cbit_spec (p := p) y z
  obtain ⟨s4, -⟩ := cbit_spec (p := p) x (y + z)
  have hassoc : (x + y + z).val = (x + (y + z)).val := by
    rw [add_assoc]
  have hmul : p * (cbitN p x y + cbitN p (x + y) z) =
      p * (cbitN p y z + cbitN p x (y + z)) := by
    rw [Nat.mul_add, Nat.mul_add]
    omega
  exact Nat.eq_of_mul_eq_mul_left hppos hmul

omit [Fact (Odd p)] in
/-- The full-period carry-bit sum: `∑_{j<p} cbit(jw, w) = w.val`. -/
theorem sum_cbit (w : ZMod p) :
    (∑ j ∈ range p, cbitN p ((j : ZMod p) * w) w) = w.val := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hppos : 0 < p := Nat.pos_of_ne_zero hp.ne_zero
  have haux : ∀ n : ℕ,
      p * (∑ j ∈ range n, cbitN p ((j : ZMod p) * w) w) +
        (((n : ZMod p)) * w).val = n * w.val := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hstep : ((n : ZMod p) * w) + w = (((n + 1 : ℕ) : ZMod p)) * w := by
        push_cast
        ring
      obtain ⟨hs, -⟩ := cbit_spec (p := p) ((n : ZMod p) * w) w
      rw [hstep] at hs
      rw [Finset.sum_range_succ, Nat.mul_add, Nat.succ_mul]
      omega
  have hp0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have hzero : (((p : ZMod p)) * w).val = 0 := by
    rw [hp0, zero_mul, ZMod.val_zero]
  have h := haux p
  rw [hzero, Nat.add_zero] at h
  refine Nat.eq_of_mul_eq_mul_left hppos ?_
  exact h

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
/-- `actMC` fixes the central direction `(0,0,c)`. -/
theorem actMC_central (k c : ZMod p) :
    actMC p k ((0 : ZMod p), (0 : ZMod p), c) = (0, 0, c) := by
  unfold actMC
  ext
  · rfl
  · change (0 : ZMod p) + k * 0 = 0
    ring
  · change c + k * 0 + tri p k * 0 = c
    ring

variable (p) in
/-- **Group id 8** (the other member of the pair `(x)/(xi)`): the
non-split extension of `C_{p²}` by `(C_p)³`, regular unipotent action,
`sᵖ` = the central generator (SmallGroup `(p⁴, 8)`). -/
@[ext]
structure Gid8 where
  vec : ZMod p × ZMod p × ZMod p
  w : ZMod p

namespace Gid8

variable (p) in
/-- The central carry vector `(0, 0, cbit)`. -/
def cvec (x y : ZMod p) : ZMod p × ZMod p × ZMod p :=
  (0, 0, ((cbitN p x y : ℕ) : ZMod p))

noncomputable instance : Mul (Gid8 p) :=
  ⟨fun g h => ⟨g.vec + actMC p g.w h.vec + cvec p g.w h.w, g.w + h.w⟩⟩

instance : One (Gid8 p) := ⟨⟨0, 0⟩⟩

noncomputable instance : Inv (Gid8 p) :=
  ⟨fun g => ⟨-(actMC p (-g.w) g.vec) - cvec p (-g.w) g.w, -g.w⟩⟩

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem mul_def (g h : Gid8 p) :
    g * h = ⟨g.vec + actMC p g.w h.vec + cvec p g.w h.w, g.w + h.w⟩ := rfl

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem one_def : (1 : Gid8 p) = ⟨0, 0⟩ := rfl

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem cvec_zero (x : ZMod p) : cvec p 0 x = 0 := by
  unfold cvec cbitN
  have h : ((0 : ZMod p)).val + x.val - ((0 : ZMod p) + x).val = 0 := by
    rw [ZMod.val_zero, zero_add, zero_add]
    omega
  rw [h, Nat.zero_div]
  ext
  · rfl
  · rfl
  · exact Nat.cast_zero

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem actMC_cvec (k x y : ZMod p) :
    actMC p k (cvec p x y) = cvec p x y :=
  actMC_central k _

omit [Fact (Odd p)] in
theorem cvec_cocycle (x y z : ZMod p) :
    cvec p x y + cvec p (x + y) z = cvec p y z + cvec p x (y + z) := by
  unfold cvec
  have h := cbit_cocycle (p := p) x y z
  have hcast : ((cbitN p x y : ℕ) : ZMod p) + ((cbitN p (x + y) z : ℕ) : ZMod p) =
      ((cbitN p y z : ℕ) : ZMod p) + ((cbitN p x (y + z) : ℕ) : ZMod p) := by
    exact_mod_cast congrArg (fun m : ℕ => ((m : ℕ) : ZMod p)) h
  ext
  · change (0 : ZMod p) + 0 = 0 + 0
    ring
  · change (0 : ZMod p) + 0 = 0 + 0
    ring
  · exact hcast

noncomputable instance : Group (Gid8 p) :=
  Group.ofLeftAxioms
    (fun g h k => by
      simp only [mul_def]
      refine Gid8.ext ?_ (by change g.w + h.w + k.w = g.w + (h.w + k.w); ring)
      change g.vec + actMC p g.w h.vec + cvec p g.w h.w +
          actMC p (g.w + h.w) k.vec + cvec p (g.w + h.w) k.w =
        g.vec + actMC p g.w (h.vec + actMC p h.w k.vec + cvec p h.w k.w) +
          cvec p g.w (h.w + k.w)
      rw [actMC_add, actMC_addv, actMC_addv, actMC_cvec]
      have hc := cvec_cocycle (p := p) g.w h.w k.w
      -- rearrange: both sides are the same six summands
      have hgoal : g.vec + actMC p g.w h.vec + cvec p g.w h.w +
          actMC p g.w (actMC p h.w k.vec) + cvec p (g.w + h.w) k.w =
        g.vec + (actMC p g.w h.vec + actMC p g.w (actMC p h.w k.vec) +
          cvec p h.w k.w) + cvec p g.w (h.w + k.w) := by
        have h1 : cvec p g.w h.w + cvec p (g.w + h.w) k.w =
            cvec p h.w k.w + cvec p g.w (h.w + k.w) := hc
        calc g.vec + actMC p g.w h.vec + cvec p g.w h.w +
              actMC p g.w (actMC p h.w k.vec) + cvec p (g.w + h.w) k.w
            = g.vec + actMC p g.w h.vec + actMC p g.w (actMC p h.w k.vec) +
              (cvec p g.w h.w + cvec p (g.w + h.w) k.w) := by abel
          _ = g.vec + actMC p g.w h.vec + actMC p g.w (actMC p h.w k.vec) +
              (cvec p h.w k.w + cvec p g.w (h.w + k.w)) := by rw [h1]
          _ = g.vec + (actMC p g.w h.vec + actMC p g.w (actMC p h.w k.vec) +
              cvec p h.w k.w) + cvec p g.w (h.w + k.w) := by abel
      exact hgoal)
    (fun g => by
      simp only [mul_def, one_def]
      refine Gid8.ext ?_ (by change (0 : ZMod p) + g.w = g.w; ring)
      change (0 : ZMod p × ZMod p × ZMod p) + actMC p 0 g.vec +
          cvec p 0 g.w = g.vec
      rw [actMC_zero, cvec_zero, zero_add, add_zero])
    (fun g => by
      change (⟨-(actMC p (-g.w) g.vec) - cvec p (-g.w) g.w, -g.w⟩ : Gid8 p) *
        g = 1
      simp only [mul_def, one_def]
      refine Gid8.ext ?_ (by change -g.w + g.w = 0; ring)
      change -(actMC p (-g.w) g.vec) - cvec p (-g.w) g.w +
          actMC p (-g.w) g.vec + cvec p (-g.w) g.w = 0
      abel)

variable (p) in
def toProd : Gid8 p ≃ (ZMod p × ZMod p × ZMod p) × ZMod p where
  toFun g := (g.vec, g.w)
  invFun w := ⟨w.1, w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : Fintype (Gid8 p) :=
  Fintype.ofEquiv _ (toProd p).symm

variable (p) in
omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem card_gid8 : Nat.card (Gid8 p) = p ^ 4 := by
  rw [Nat.card_congr (toProd p), Nat.card_prod, Nat.card_prod,
    Nat.card_prod, Nat.card_zmod]
  ring

/-- Powers: `(a, w)ⁿ = (∑_{j<n} σ^{jw}(a) + (∑_{j<n} cbit(jw,w))·e, nw)`. -/
theorem pow_formula (g : Gid8 p) (n : ℕ) :
    g ^ n = ⟨(∑ j ∈ range n, actMC p ((j : ZMod p) * g.w) g.vec) +
        ((0 : ZMod p), (0 : ZMod p),
          (((∑ j ∈ range n, cbitN p ((j : ZMod p) * g.w) g.w : ℕ)) : ZMod p)),
      (n : ZMod p) * g.w⟩ := by
  induction n with
  | zero =>
    change (1 : Gid8 p) = _
    rw [one_def, range_zero, Finset.sum_empty, Finset.sum_empty]
    refine Gid8.ext ?_ ?_
    · change (0 : ZMod p × ZMod p × ZMod p) = 0 + (0, 0, ((0 : ℕ) : ZMod p))
      rw [zero_add]
      ext
      · rfl
      · rfl
      · exact Nat.cast_zero.symm
    · change (0 : ZMod p) = ((0 : ℕ) : ZMod p) * g.w
      push_cast
      ring
  | succ n ih =>
    rw [pow_succ, ih, mul_def]
    have hstepc : ((n : ZMod p) * g.w) + g.w =
        (((n + 1 : ℕ) : ZMod p)) * g.w := by
      push_cast
      ring
    refine Gid8.ext ?_ ?_
    · change (∑ j ∈ range n, actMC p ((j : ZMod p) * g.w) g.vec) +
          ((0 : ZMod p), (0 : ZMod p),
            (((∑ j ∈ range n, cbitN p ((j : ZMod p) * g.w) g.w : ℕ)) : ZMod p)) +
          actMC p ((n : ZMod p) * g.w) g.vec +
          cvec p ((n : ZMod p) * g.w) g.w = _
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      change _ = (∑ j ∈ range n, actMC p ((j : ZMod p) * g.w) g.vec) +
          actMC p ((n : ZMod p) * g.w) g.vec +
          ((0 : ZMod p), (0 : ZMod p),
            ((((∑ j ∈ range n, cbitN p ((j : ZMod p) * g.w) g.w) +
              cbitN p ((n : ZMod p) * g.w) g.w : ℕ)) : ZMod p))
      have hsplit : (((((∑ j ∈ range n, cbitN p ((j : ZMod p) * g.w) g.w) +
          cbitN p ((n : ZMod p) * g.w) g.w : ℕ)) : ZMod p)) =
          (((∑ j ∈ range n, cbitN p ((j : ZMod p) * g.w) g.w : ℕ)) : ZMod p) +
            ((cbitN p ((n : ZMod p) * g.w) g.w : ℕ) : ZMod p) := by
        push_cast
        ring
      have hvec : ((0 : ZMod p), (0 : ZMod p),
          (((∑ j ∈ range n, cbitN p ((j : ZMod p) * g.w) g.w : ℕ)) : ZMod p) +
            ((cbitN p ((n : ZMod p) * g.w) g.w : ℕ) : ZMod p)) =
          ((0 : ZMod p), (0 : ZMod p),
            (((∑ j ∈ range n, cbitN p ((j : ZMod p) * g.w) g.w : ℕ)) : ZMod p)) +
            cvec p ((n : ZMod p) * g.w) g.w := by
        unfold cvec
        ext
        · change (0 : ZMod p) = 0 + 0
          ring
        · change (0 : ZMod p) = 0 + 0
          ring
        · rfl
      rw [hsplit, hvec]
      abel
    · change (n : ZMod p) * g.w + g.w = ((n + 1 : ℕ) : ZMod p) * g.w
      push_cast
      ring

/-- The `sᵖ` law: `(a, w)ᵖ = ((0,0,w), 0)` for `p ≥ 5` — the outer
generator has order `p²`, with `sᵖ` = the central generator. -/
theorem pow_p (hp5 : 5 ≤ p) (g : Gid8 p) :
    g ^ p = ⟨((0 : ZMod p), (0 : ZMod p), g.w), 0⟩ := by
  rw [pow_formula]
  have hp0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have hlin : (∑ j ∈ range p, ((j : ZMod p))) = 0 := sum_range_cast_zero
  have htri : (∑ j ∈ range p, tri p ((j : ZMod p))) = 0 := sum_tri_zero hp5
  have hconst : ∀ c : ZMod p, (∑ _j ∈ range p, c) = 0 := by
    intro c
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hp0, zero_mul]
  have hval : ((((∑ j ∈ range p, cbitN p ((j : ZMod p) * g.w) g.w : ℕ))) :
      ZMod p) = g.w := by
    rw [sum_cbit, ZMod.natCast_val, ZMod.cast_id]
  -- the actMC sum vanishes exactly as in `MaxClass.pow_p`
  have hsum : (∑ j ∈ range p, actMC p ((j : ZMod p) * g.w) g.vec) = 0 := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · rw [Prod.fst_sum]
      calc (∑ j ∈ range p, (actMC p ((j : ZMod p) * g.w) g.vec).1)
          = ∑ _j ∈ range p, g.vec.1 := Finset.sum_congr rfl fun j _ => rfl
        _ = 0 := hconst _
    · rw [Prod.snd_sum, Prod.fst_sum]
      calc (∑ j ∈ range p, (actMC p ((j : ZMod p) * g.w) g.vec).2.1)
          = ∑ j ∈ range p,
              (g.vec.2.1 + (j : ZMod p) * (g.w * g.vec.1)) :=
            Finset.sum_congr rfl fun j _ => by
              change g.vec.2.1 + ((j : ZMod p) * g.w) * g.vec.1 = _
              ring
        _ = (∑ _j ∈ range p, g.vec.2.1) +
              (∑ j ∈ range p, ((j : ZMod p))) * (g.w * g.vec.1) := by
            rw [Finset.sum_add_distrib, Finset.sum_mul]
        _ = 0 := by rw [hconst, hlin, zero_mul, add_zero]
    · rw [Prod.snd_sum, Prod.snd_sum]
      calc (∑ j ∈ range p, (actMC p ((j : ZMod p) * g.w) g.vec).2.2)
          = ∑ j ∈ range p,
              (g.vec.2.2 + ((j : ZMod p) * (g.w * g.vec.2.1) +
                (tri p ((j : ZMod p)) * (g.w ^ 2 * g.vec.1) +
                  (j : ZMod p) * (tri p g.w * g.vec.1)))) :=
            Finset.sum_congr rfl fun j _ => by
              change g.vec.2.2 + ((j : ZMod p) * g.w) * g.vec.2.1 +
                tri p ((j : ZMod p) * g.w) * g.vec.1 = _
              rw [MaxClass.tri_mul]
              ring
        _ = (∑ _j ∈ range p, g.vec.2.2) +
              ((∑ j ∈ range p, ((j : ZMod p))) * (g.w * g.vec.2.1) +
                ((∑ j ∈ range p, tri p ((j : ZMod p))) *
                    (g.w ^ 2 * g.vec.1) +
                  (∑ j ∈ range p, ((j : ZMod p))) *
                    (tri p g.w * g.vec.1))) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
              Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul,
              Finset.sum_mul]
        _ = 0 := by
            rw [hconst, hlin, htri, zero_mul, zero_mul, zero_mul, add_zero,
              add_zero, add_zero]
  refine Gid8.ext ?_ ?_
  · change (∑ j ∈ range p, actMC p ((j : ZMod p) * g.w) g.vec) +
        ((0 : ZMod p), (0 : ZMod p), _) = ((0 : ZMod p), (0 : ZMod p), g.w)
    rw [hsum, hval, zero_add]
  · change ((p : ℕ) : ZMod p) * g.w = 0
    rw [hp0, zero_mul]

/-- Torsion criterion in `Gid8` (`p ≥ 5`): `gᵖ = 1 ⟺ w = 0` — the
`p`-torsion is exactly the normal `(C_p)³`. -/
theorem pow_p_eq_one_iff (hp5 : 5 ≤ p) (g : Gid8 p) :
    g ^ p = 1 ↔ g.w = 0 := by
  rw [pow_p hp5, one_def]
  constructor
  · intro h
    have hvec : ((0 : ZMod p), (0 : ZMod p), g.w) =
        (0 : ZMod p × ZMod p × ZMod p) := congrArg Gid8.vec h
    exact congrArg (fun v : ZMod p × ZMod p × ZMod p => v.2.2) hvec
  · intro h
    rw [h]
    rfl

variable (p) in
/-- `|Ω₁(Gid8)| = p³` (`p ≥ 5`). -/
theorem card_omega (hp5 : 5 ≤ p) :
    Nat.card {g : Gid8 p // g ^ p = 1} = p ^ 3 := by
  let f : (ZMod p × ZMod p × ZMod p) → {g : Gid8 p // g ^ p = 1} := fun v =>
    ⟨⟨v, 0⟩, by rw [pow_p_eq_one_iff hp5]⟩
  let g : {g : Gid8 p // g ^ p = 1} → ZMod p × ZMod p × ZMod p := fun x =>
    x.1.vec
  have hbij : Function.Bijective f := by
    rw [Function.bijective_iff_has_inverse]
    refine ⟨g, fun v => rfl, fun x => ?_⟩
    · obtain ⟨x, hx⟩ := x
      have hw : x.w = 0 := (pow_p_eq_one_iff hp5 x).mp hx
      refine Subtype.ext ?_
      refine Gid8.ext rfl ?_
      exact hw.symm
  rw [← Nat.card_eq_of_bijective f hbij, Nat.card_prod, Nat.card_prod,
    Nat.card_zmod]
  ring

variable (p) in
/-- **Table row (x)/(xi) member id 8, first column**: `p² + p + 1`
subgroups of order `p` (`p ≥ 5`). -/
theorem card_order_p_subgroups_gid8 (hp5 : 5 ≤ p) :
    Nat.card {H : Subgroup (Gid8 p) // Nat.card H = p} = p ^ 2 + p + 1 := by
  have h := card_order_p_subgroups_of_omega (Gid8 p) 3 (card_omega p hp5)
  rw [h, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  ring

end Gid8

end P4

end LeanDring
