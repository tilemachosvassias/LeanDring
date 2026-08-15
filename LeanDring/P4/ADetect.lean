/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P4.ABlock
import LeanDring.Theory.DRing.GabCount

/-!
# A-detection: the maximal abelian subgroup is the unique `p³`-character class

`eq_subA_of_charHom_card`: an order-`p³` subgroup `K` of `Model p d` with `p³`
linear characters equals the maximal abelian subgroup `A = subA p d`.  Proof:
`p³ = |K→*ℂˣ| = |Abelianization K|`, so `|commutator K| = 1` (Lagrange), hence
`K` is abelian, and `eq_subA_of_abelian_maximal` gives `K = A`.  This makes `A`
table-detectable (the unique subgroup class with a `p³`-character fiber), pinning
the block correspondence to `A` in the twin-separation reduction `hentry`.
-/

namespace LeanDring.P4
open Model
open Abelianization
open Function

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

open scoped Classical in
theorem eq_subA_of_charHom_card {d : ZMod p} (K : Subgroup (Model p d))
    (hcard : Nat.card K = p ^ 3) (hchar : Nat.card (K →* ℂˣ) = p ^ 3) :
    K = subA p d := by
  haveI : Finite K := Subtype.finite
  have h_ab_card : Nat.card (Abelianization K) = p ^ 3 := by
    have h1 := LeanDring.DRing.card_charHom_eq_card_abelianization (G := K)
    rw [← h1]
    exact hchar
  have h_lagrange : Nat.card K = Nat.card (Abelianization K) * Nat.card (commutator K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator K)
  rw [hcard, h_ab_card] at h_lagrange
  have hp_pos : 0 < p ^ 3 := pow_pos (Fact.out : p.Prime).pos 3
  have h_comm_card : Nat.card (commutator K) = 1 := by
    have h_eq : p ^ 3 * Nat.card (commutator K) = p ^ 3 * 1 := by
      rw [mul_one, ← h_lagrange]
    exact Nat.eq_of_mul_eq_mul_left hp_pos h_eq
  have h_comm_bot : commutator K = ⊥ := by
    exact Subgroup.card_eq_one.mp h_comm_card
  have h_ab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := by
    intro x hx y hy
    let x' : K := ⟨x, hx⟩
    let y' : K := ⟨y, hy⟩
    have h_mem : x' * y' * x'⁻¹ * y'⁻¹ ∈ commutator K := by
      apply Subgroup.subset_closure
      exact ⟨x', Subgroup.mem_top x', y', Subgroup.mem_top y', rfl⟩
    rw [h_comm_bot, Subgroup.mem_bot] at h_mem
    have h_eq2 : x' * y' * x'⁻¹ = y' := mul_inv_eq_one.mp h_mem
    have h_eq3 : x' * y' = y' * x' := by
      calc x' * y' = x' * y' * (x'⁻¹ * x') := by rw [inv_mul_cancel, mul_one]
                 _ = x' * y' * x'⁻¹ * x' := by rw [← mul_assoc]
                 _ = y' * x' := by rw [h_eq2]
    exact congrArg Subtype.val h_eq3
  exact eq_subA_of_abelian_maximal K hcard h_ab

end LeanDring.P4
