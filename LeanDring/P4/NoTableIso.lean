/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.BridgeCounts
import LeanDring.P4.ColTwo
import LeanDring.P4.ColTwoExp
import LeanDring.P4.ABlock
import LeanDring.P4.Endgame
import LeanDring.P4.TwinSeparation

/-!
# Non-isomorphic species tables among the order-`p⁴` groups

The payoff of the bridge: combining `SpeciesTableIso.card_subgroups_eq`
with the proven subgroup-count rows yields, for every prime `p ≥ 5`,
**machine-checked species-table separations**:

* `isEmpty_tableIso_m6_m8` — groups (vi) and (viii) (tied in column 1,
  separated by column 2: `p+1` vs `p²+p+1` subgroups of order `p²`);
* `isEmpty_tableIso_g14_maxClass` — groups (xiv) and (xv) (tied in
  column 1, separated by column 2: `p³+2p²+p+1` vs `2p²+p+1`);
* `isEmpty_tableIso_model_m6` — a column-1 example: (xii)/(xiii) vs (vi)
  (`p²+p+1` vs `p+1` subgroups of order `p`).

The subgroup counts they use are proven here rather than quoted, so no appeal
to [GJG10] or [Hue09] remains in the chain.
-/

namespace LeanDring

namespace P4

open DRing

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

/-- **Groups (vi) and (viii) have non-isomorphic species tables**:
they are tied in column 1 but separated by their `p²`-subgroup counts. -/
theorem isEmpty_tableIso_m6_m8 :
    IsEmpty (SpeciesTableIso (M6 p) (M8 p)) := by
  constructor
  intro T
  have h := T.card_subgroups_eq (p ^ 2)
  rw [M6.card_order_p2_subgroups_m6, M8.card_order_p2_subgroups_m8] at h
  have hp := (Fact.out : p.Prime).one_lt
  have hpos : 0 < p ^ 2 := pow_pos (Fact.out : p.Prime).pos 2
  omega

/-- **Groups (xiv) and (xv) have non-isomorphic species tables**:
they are tied in column 1 but separated by their `p²`-subgroup counts. -/
theorem isEmpty_tableIso_g14_maxClass (hp5 : 5 ≤ p) :
    IsEmpty (SpeciesTableIso (G14 p) (MaxClass p)) := by
  constructor
  intro T
  have h := T.card_subgroups_eq (p ^ 2)
  rw [card_order_p2_subgroups_g14, card_order_p2_subgroups_maxClass p hp5]
    at h
  have hpos : 0 < p ^ 3 := pow_pos (Fact.out : p.Prime).pos 3
  omega

/-- A column-1 separation: the (xii)/(xiii) model vs group (vi). -/
theorem isEmpty_tableIso_model_m6 (hp5 : 5 ≤ p) (d : ZMod p) :
    IsEmpty (SpeciesTableIso (Model p d) (M6 p)) := by
  constructor
  intro T
  have h := T.card_subgroups_eq p
  rw [Model.card_order_p_subgroups hp5, M6.card_order_p_subgroups_m6]
    at h
  have hpos : 0 < p ^ 2 := pow_pos (Fact.out : p.Prime).pos 2
  omega

/-! ## The last twin: (xii) vs (xiii)

The two models `Model p d₁` (`d₁` a QR) and `Model p d₂` (`d₂` a QNR) are the
one order-`p⁴` pair that **every counting invariant misses** — identical
subgroup counts, subgroup-class counts, and tables of marks. They are
separated only at the level of species *values*, by the sign of a quadratic
Gauss sum ([BEW98] Thm 1.5.2, proved in `LeanDring.Theory.Gauss.GaussSignTheorem`).

The two theorems below state that separation in conditional form, each
hypothesis naming the step of the reduction from a species-table isomorphism
down to an arithmetic identity, and each conclusion discharged by the proven
arithmetic core (`value_equation_impossible`, `twin_entry_equality_impossible`).
They are stated as separate interfaces because they isolate different amounts of
work; the unconditional separation, with both hypotheses discharged, is
`isEmpty_tableIso_model_model` in `LeanDring.P4.TwinFinal`. -/

open Complex in
/-- **The twin separation, reduced to its arithmetic core.** A species-table
isomorphism between the two `(xii)/(xiii)` models yields, through the A-block
Gauss-sum analysis, a solution of the value equation; since
`value_equation_impossible` refutes that, the tables cannot be isomorphic. The
hypothesis `hreduce` is the whole analytic reduction. -/
theorem isEmpty_tableIso_model_model_of_value_equation (d₁ d₂ : ZMod p)
    (hreduce : SpeciesTableIso (Model p d₁) (Model p d₂) →
      ∃ (m β : ℕ) (d' : ℤ),
        Complex.exp (2 * Real.pi * I / ((8 * p : ℕ) : ℂ)) ^
            ((p : ℤ) - (1 + 2 * (β : ℤ)) ^ 2 + 8 * (m : ℤ)) =
          (-1 : ℂ) ^ ((p ^ 2 + 7) / 8) * (if p % 4 = 1 then (1 : ℂ) else I) *
            Complex.exp (2 * Real.pi * I / ((8 * p : ℕ) : ℂ)) ^
              (-(d' * ((p : ℤ) + 1) ^ 3))) :
    IsEmpty (SpeciesTableIso (Model p d₁) (Model p d₂)) := by
  constructor
  intro T
  obtain ⟨m, β, d', heq⟩ := hreduce T
  have hp2 : p ≠ 2 := by
    have hodd : Odd p := Fact.out
    rintro rfl
    exact (by decide : ¬ Odd 2) hodd
  exact value_equation_impossible p Fact.out hp2 m β d' heq

open Complex in
/-- **The twin separation, reduced to the block/column matching only.**  A
sharper interface than the value-equation form: the hypothesis now asks only for
the *entry equality* a species-table isomorphism produces through the A-block
Gauss-sum evaluation — the `G₁` entry (`χ(ca) = ζ_{p²}^{1+mp}`)
equalling the `G₂` distinguished entry `z` (`χ(ca^d) = ζ_{p²}`),
in the exact `ζ`/`√p`/`ζ_{p²}` shape of `g1_entry_form` /
`g2_entry_form`.  Everything from that equality onward — cancelling
`√p·ζ_{p²}`, folding `ζ_{p²}^{1+mp}/ζ_{p²} = ζ₈ₚ^{8m}`, and refuting the
resulting value equation — is discharged by `twin_entry_equality_impossible`, so
`hentry` carries only the structural extraction of the entry equality from a
table iso (matching the distinguished A-block rows and columns across `T`),
needing no further number theory. -/
theorem isEmpty_tableIso_model_model_of_entry_reduction (d₁ d₂ : ZMod p)
    (hentry : SpeciesTableIso (Model p d₁) (Model p d₂) →
      ∃ (m β : ℕ) (d' : ℤ),
        zetaP2 p ^ (1 + m * p) *
            ((Real.sqrt p : ℂ) * zeta8 p ^ ((p : ℤ) - (1 + 2 * (β : ℤ)) ^ 2))
          = zetaP2 p * ((-1 : ℂ) ^ ((p ^ 2 + 7) / 8) *
              ((if p % 4 = 1 then (1 : ℂ) else I) *
                ((Real.sqrt p : ℂ) * zeta8 p ^ (-(d' * ((p : ℤ) + 1) ^ 3)))))) :
    IsEmpty (SpeciesTableIso (Model p d₁) (Model p d₂)) := by
  constructor
  intro T
  obtain ⟨m, β, d', heq⟩ := hentry T
  exact twin_entry_equality_impossible m β d' heq

end P4

end LeanDring
