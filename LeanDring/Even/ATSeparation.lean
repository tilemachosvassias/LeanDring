/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Even.BCSeparation

/-!
# Theorem AT, endgame: the binomial hole separates `A_n` from a Fitting-free twin

**EVEN-ORDER LAYER.** Inside the root module's build closure and audit:
no `sorry`, three standard axioms. The results here are
verified *implications*; their hypotheses are named `Prop`s (see §7.6 of
the paper).

This file types the *endgame* of Theorem AT — the spectrum / hole /
squeeze chain.

The mathematics.  Write `I(G)` for the set of `ind*` values of `G`.

* **the spectrum inclusion**: `I(A_n) ⊆ ⋃_s C(n,s)·(V_s ∪ ½V_s)`, with
  `V_s` a finite set depending only on the support `s`;
* **the hole**: consequently `I(A_n) ∩ (4C(n,4), 6C(n,5)) = ∅` for `n`
  large — the *hole*.  Both endpoints are attained values of `I(A_n)`
  (`4C(n,4) ∈ C(n,4)V_4`, `6C(n,5) ∈ C(n,5)V_5`), so **only strict
  inequalities may be used** at the delicate `s = 5` boundary.
* **the squeeze**: the relation `ℓ*·f₁·ι₁ = C(n,3)` forces the Lie-witness
  value of a putative twin `T` to be `C(n,3)·ρ` with
  `n − 3 < ρ < (3/10)(n−3)(n−4)`, i.e. *strictly inside* the hole.

What makes this an exact ℕ-statement rather than an approximation is a pair of
binomial identities, proven below, which say that the two hole endpoints are
*exactly* `C(n,3)` times the two `ρ`-bounds:

```
C(n,3)·(n−3)         = 4·C(n,4)          (`choose_three_mul_sub`)
C(n,3)·(n−3)·(n−4)   = 20·C(n,5)         (`choose_three_mul_sub_sub`)
```

so the hole is `(C(n,3)·(n−3), (3/10)·C(n,3)·(n−3)(n−4))` on the nose, and the
squeeze `n−3 < ρ`, `10ρ < 3(n−3)(n−4)` transports through multiplication by
`C(n,3) > 0` without any rounding.  Everything is ℕ; the only division in the
informal statement (`3/10`) is cleared by the factor `10`.

## What is PROVEN here (no axioms beyond the Lean standard three)

* the two binomial identities above, from `Nat.choose_succ_right_eq`;
* `holeLo_lt_holeHi` — the hole is non-empty (`4C(n,4) < 6C(n,5)`) exactly for
  `n ≥ 8`, derived from the identities rather than estimated;
* `choose_three_lt_choose_four`, `holeLo_pos`, and the ordering chain
  `C(n,3) < C(n,4) < 3C(n,4) < 4C(n,4)`;
* `squeeze` — **the arithmetic core**: from `n−3 < ρ` and
  `10ρ < 3(n−3)(n−4)`, conclude `4C(n,4) < C(n,3)·ρ < 6C(n,5)`;
* `atSeparation` — **[PROVEN from the three named inputs]**
  `IsEmpty (DRing A ≃+* DRing T)`.

`IsIndexValue` and `IsIndexValue.transfer` are reused verbatim from
`LeanDring/Even/BCSeparation.lean`; the transport is
`conductorMultiplicity_eq_of_ringEquiv` and nothing else.

## What remains a named hypothesis (the "known theorems" package)

* `hcard: Nat.card A = Nat.card T` — the twin has the order of `A_n`
  (forced by `D`-ring isomorphism at the order-transfer level);
* `hA: SpectrumHole A n` — the spectrum inclusion, the hole it implies,
  and the lower bound `min V_s > s⁶`.  This is the `S_n`-combinatorial
  input, and is not formalized;
* `hT: TwinWitness T n ρ` — the Lie witness (`Z(Syl_p)` for `L₃`, ratio
  `q+1`; `U_{P₂}` for `L₅`, ratio `q²+1`) together with the bounds on `q`
  that give the two inequalities on `ρ`.

**Upgrade**: `LeanDring/Even/BoltjeAssembly.lean` restates both inputs in pure
group theory (`SpectrumHoleIndStar`, `TwinWitnessIndStar`, in terms of
`IsIndStarValue`) and proves `atSeparation_of_boltje` from them, given the
single named `Prop` `BoltjeIntegrality` (`LeanDring/Even/ConductorAtSpecies.lean` §12).

**Range honesty.**  `SpectrumHole` is *false* at `n = 10`
(`I(A₁₀) ∩ (840,1512) = {945, 1350}`) and the hole is only
established for `n` above an explicit threshold (`n₀ = 10⁶+5` under the
Artin bound; `n ≥ 178089` hypothesis-free), the range `9 ≤ n ≤ 10¹¹` being
covered instead by the exact scan.  The Lean statement therefore
takes `SpectrumHole` as a hypothesis *at the given `n`* and does not claim it;
the numeric hypothesis `10 ≤ n` below is only what the arithmetic needs.
-/

set_option linter.unusedFintypeInType false

namespace LeanDring

namespace Even

universe u

/-! ## The hole, and the two binomial identities that pin its endpoints -/

/-- The left endpoint of the hole, `4C(n,4)`.  It is an *attained*
value of `I(A_n)` (`4 ∈ V_4`), so the hole is open here. -/
def holeLo (n : ℕ) : ℕ := 4 * n.choose 4

/-- The right endpoint of the hole, `6C(n,5)`.  It too is an
attained value (`6 = min V_5`), so the hole is open here as well. -/
def holeHi (n : ℕ) : ℕ := 6 * n.choose 5

/-- **[PROVEN] First binomial identity**: `C(n,3)·(n−3) = 4·C(n,4)`.
This is `Nat.choose_succ_right_eq` at `k = 3`; it says the left hole endpoint
is exactly `C(n,3)` times the lower `ρ`-bound. -/
theorem choose_three_mul_sub (n : ℕ) : n.choose 3 * (n - 3) = holeLo n := by
  have h : n.choose 4 * 4 = n.choose 3 * (n - 3) := Nat.choose_succ_right_eq n 3
  simp only [holeLo]
  omega

/-- **[PROVEN] Second binomial identity**: `C(n,3)·(n−3)·(n−4) = 20·C(n,5)`.
Two applications of `Nat.choose_succ_right_eq`.  It says
`6C(n,5) = (3/10)·C(n,3)·(n−3)(n−4)`, i.e. the right hole endpoint is exactly
`C(n,3)` times the upper `ρ`-bound. -/
theorem choose_three_mul_sub_sub (n : ℕ) :
    n.choose 3 * ((n - 3) * (n - 4)) = 20 * n.choose 5 := by
  have h5 : n.choose 5 * 5 = n.choose 4 * (n - 4) := Nat.choose_succ_right_eq n 4
  have : n.choose 3 * ((n - 3) * (n - 4)) = (n.choose 3 * (n - 3)) * (n - 4) := by
    ring
  rw [this, choose_three_mul_sub]
  simp only [holeLo]
  have : 4 * n.choose 4 * (n - 4) = 4 * (n.choose 4 * (n - 4)) := by ring
  rw [this, ← h5]
  ring

/-- `C(n,3) > 0` for `n ≥ 3`. -/
theorem choose_three_pos {n : ℕ} (hn : 3 ≤ n) : 0 < n.choose 3 :=
  Nat.choose_pos hn

/-- `C(n,4) > 0` for `n ≥ 4`, hence `0 < holeLo n`. -/
theorem holeLo_pos {n : ℕ} (hn : 4 ≤ n) : 0 < holeLo n := by
  have := Nat.choose_pos (n := n) (k := 4) hn
  simp only [holeLo]
  omega

/-- **[PROVEN] The hole is non-empty**: `4C(n,4) < 6C(n,5)` for `n ≥ 8`.
Proven *exactly*, from the two identities: multiplying by `10`,
`10·4C(n,4) = 10·C(n,3)(n−3)` and `10·6C(n,5) = 3·C(n,3)(n−3)(n−4)`, so the
claim is `10 < 3(n−4)`, i.e. `n ≥ 8` (the informal `4 < 6(n−4)/5 ⟺ n > 22/3`). -/
theorem holeLo_lt_holeHi {n : ℕ} (hn : 8 ≤ n) : holeLo n < holeHi n := by
  have hc : 0 < n.choose 3 := choose_three_pos (by omega)
  have hpos : 0 < n - 3 := by omega
  have key : 10 * holeLo n < 10 * holeHi n := by
    have e1 : 10 * holeLo n = 10 * (n.choose 3 * (n - 3)) := by
      rw [choose_three_mul_sub]
    have e2 : 10 * holeHi n = 3 * (n.choose 3 * ((n - 3) * (n - 4))) := by
      rw [choose_three_mul_sub_sub]; simp only [holeHi]; ring
    rw [e1, e2]
    have hstep : 10 * (n - 3) < 3 * ((n - 3) * (n - 4)) := by
      have : 3 * ((n - 3) * (n - 4)) = (n - 3) * (3 * (n - 4)) := by ring
      rw [this]
      have h12 : 12 ≤ 3 * (n - 4) := by omega
      calc 10 * (n - 3) < 12 * (n - 3) := by omega
        _ = (n - 3) * 12 := by ring
        _ ≤ (n - 3) * (3 * (n - 4)) := Nat.mul_le_mul_left _ h12
    calc 10 * (n.choose 3 * (n - 3)) = n.choose 3 * (10 * (n - 3)) := by ring
      _ < n.choose 3 * (3 * ((n - 3) * (n - 4))) := by
          exact Nat.mul_lt_mul_of_pos_left hstep hc
      _ = 3 * (n.choose 3 * ((n - 3) * (n - 4))) := by ring
  omega

/-- **[PROVEN] `C(n,3) < C(n,4)` for `n ≥ 8`** — the first link of the
monotonicity chain, again read off the identity `4C(n,4) = C(n,3)(n−3)`. -/
theorem choose_three_lt_choose_four {n : ℕ} (hn : 8 ≤ n) :
    n.choose 3 < n.choose 4 := by
  have hc : 0 < n.choose 3 := choose_three_pos (by omega)
  have hid := choose_three_mul_sub n
  simp only [holeLo] at hid
  have h5 : 5 * n.choose 3 ≤ n.choose 3 * (n - 3) := by
    have : (5 : ℕ) ≤ n - 3 := by omega
    calc 5 * n.choose 3 = n.choose 3 * 5 := by ring
      _ ≤ n.choose 3 * (n - 3) := Nat.mul_le_mul_left _ this
  omega

/-- **[PROVEN] The monotonicity chain `C(n,3) < C(n,4) < 3C(n,4) < 4C(n,4)`**
(`n ≥ 8`).  `4C(n,4) = holeLo n` is the left hole endpoint; the chain records
that the three `s = 4` values of the spectrum inclusion (`C(n,4)V_4`,
`V_4 = {1,3,4}`)
all lie at or below it, and the `s = 3` value `C(n,3)` strictly below. -/
theorem choose_chain {n : ℕ} (hn : 8 ≤ n) :
    n.choose 3 < n.choose 4 ∧ n.choose 4 < 3 * n.choose 4 ∧
      3 * n.choose 4 < holeLo n := by
  have h4 : 0 < n.choose 4 := Nat.choose_pos (by omega)
  refine ⟨choose_three_lt_choose_four hn, by omega, ?_⟩
  simp only [holeLo]; omega

/-! ## The squeeze -/

/-- **[PROVEN] THE SQUEEZE, in abstract integer form.**

Let `ρ` satisfy the two Lie-witness bounds

* `n − 3 < ρ` (the witness ratio exceeds the lower hole endpoint's
  `ρ`-value), and
* `10ρ < 3(n−3)(n−4)` (the integer form of `ρ < (3/10)(n−3)(n−4)`).

Then `C(n,3)·ρ` lies **strictly inside** the hole.  Strictness on both
sides is essential: both endpoints are attained values of `I(A_n)`, so a
non-strict squeeze would prove nothing. -/
theorem squeeze {n ρ : ℕ} (hn : 5 ≤ n) (hlo : n - 3 < ρ)
    (hhi : 10 * ρ < 3 * ((n - 3) * (n - 4))) :
    holeLo n < n.choose 3 * ρ ∧ n.choose 3 * ρ < holeHi n := by
  have hc : 0 < n.choose 3 := choose_three_pos (by omega)
  constructor
  · rw [← choose_three_mul_sub]
    exact Nat.mul_lt_mul_of_pos_left hlo hc
  · have key : 10 * (n.choose 3 * ρ) < 10 * holeHi n := by
      have e2 : 10 * holeHi n = 3 * (n.choose 3 * ((n - 3) * (n - 4))) := by
        rw [choose_three_mul_sub_sub]; simp only [holeHi]; ring
      rw [e2]
      calc 10 * (n.choose 3 * ρ) = n.choose 3 * (10 * ρ) := by ring
        _ < n.choose 3 * (3 * ((n - 3) * (n - 4))) :=
            Nat.mul_lt_mul_of_pos_left hhi hc
        _ = 3 * (n.choose 3 * ((n - 3) * (n - 4))) := by ring
    omega

/-! ## The hypothesis package (the "known theorems") -/

open DRing

/-- **[OPEN formally — the spectrum inclusion
`I(A_n) ⊆ ⋃_s C(n,s)(V_s ∪ ½V_s)`, the hole it implies, and the lower
bound `min V_s > s⁶` (which is CFSG-free)]**

Every index value of `A = A_n` avoids the open interval `(4C(n,4), 6C(n,5))`.

Established for `n` above an explicit threshold (`n₀ = 10⁶+5` under the
Artin bound; `n ≥ 178089` unconditionally), with `9 ≤ n ≤ 10¹¹` covered
instead by the
exact scan.  It is **false at `n = 10`**
(`I(A₁₀) ∩ (840,1512) = {945,1350}`), which is why it is a hypothesis *at a
given `n`* and not a theorem schema. -/
def SpectrumHole (A : Type u) [Group A] [Fintype A] (n : ℕ) : Prop :=
  ∀ x : ℕ, IsIndexValue A x → x ≤ holeLo n ∨ holeHi n ≤ x

/-- **[OPEN formally — the Lie witnesses and the squeeze]**

The putative Fitting-free twin `T` carries an abelian-witness index value
`C(n,3)·ρ` whose ratio `ρ` is squeezed strictly between the two hole
`ρ`-bounds.  Content: the relation `ℓ*·f₁·ι₁ = C(n,3)`, the abelian
witnesses `Z(Syl_p) ≤ L₃(q)` (ratio `q+1`) and `U_{P₂} ≤ L₅(q)` (ratio
`q²+1`), transported by `ind*_T(A) = ℓ*·f_A·[S: N_S(A)]`, and the bounds
on `q` which give the two inequalities.  Verified in exact integer
arithmetic for `n ≥ 10¹¹` (all live `f`) and by the contiguous
`10 ≤ n ≤ 10¹¹` scan below that. -/
def TwinWitness (T : Type u) [Group T] [Fintype T] (n ρ : ℕ) : Prop :=
  IsIndexValue T (n.choose 3 * ρ) ∧ n - 3 < ρ ∧ 10 * ρ < 3 * ((n - 3) * (n - 4))

/-! ## Theorem AT, endgame -/

/-- **Theorem AT endgame [PROVEN from the three named inputs]**.

Let `n ≥ 10`, let `A` play the role of `A_n` and `T` that of a putative
Fitting-free twin.  If

* `A` and `T` have the same order (order transfer),
* `A`'s index-value spectrum has the hole (`SpectrumHole`), and
* `T` has the squeezed Lie-witness value (`TwinWitness`),

then `D(A) ≇ D(T)`.

Proof: transport the witness `C(n,3)·ρ` from `T` to `A` along `Φ.symm` using
`IsIndexValue.transfer` (i.e. `conductorMultiplicity_eq_of_ringEquiv`); the
`squeeze` puts it strictly inside `(4C(n,4), 6C(n,5))`; `SpectrumHole` says
nothing lives there.  All arithmetic above the hypothesis line is proven
outright. -/
theorem atSeparation {A T : Type u} [Group A] [Group T] [Fintype A] [Fintype T]
    {n ρ : ℕ} (hn : 10 ≤ n)
    (hcard : Nat.card A = Nat.card T)
    (hA : SpectrumHole A n) (hT : TwinWitness T n ρ) :
    IsEmpty (DRing A ≃+* DRing T) := by
  refine ⟨fun Φ => ?_⟩
  obtain ⟨hval, hlo, hhi⟩ := hT
  have hvA : IsIndexValue A (n.choose 3 * ρ) :=
    hval.transfer (Φ.symm) hcard.symm
  obtain ⟨h1, h2⟩ := squeeze (n := n) (ρ := ρ) (by omega) hlo hhi
  rcases hA _ hvA with h | h <;> omega

/-- **Theorem AT endgame, isomorphism form**: no D-ring isomorphism exists. -/
theorem not_nonempty_dringEquiv_of_atSeparation
    {A T : Type u} [Group A] [Group T] [Fintype A] [Fintype T]
    {n ρ : ℕ} (hn : 10 ≤ n)
    (hcard : Nat.card A = Nat.card T)
    (hA : SpectrumHole A n) (hT : TwinWitness T n ρ) :
    ¬ Nonempty (DRing A ≃+* DRing T) := fun ⟨Φ⟩ =>
  (atSeparation hn hcard hA hT).elim Φ

end Even

end LeanDring

/-! ## Axiom audit

As in `LeanDring/Even/BCSeparation.lean`, the per-file audit lives here alongside the
results it covers.  Every line below must report the
three standard axioms `[propext, Classical.choice, Quot.sound]` (or fewer) and
nothing else — in particular no `sorry`. -/

#print axioms LeanDring.Even.choose_three_mul_sub
#print axioms LeanDring.Even.choose_three_mul_sub_sub
#print axioms LeanDring.Even.choose_three_pos
#print axioms LeanDring.Even.holeLo_pos
#print axioms LeanDring.Even.holeLo_lt_holeHi
#print axioms LeanDring.Even.choose_three_lt_choose_four
#print axioms LeanDring.Even.choose_chain
#print axioms LeanDring.Even.squeeze
#print axioms LeanDring.Even.atSeparation
#print axioms LeanDring.Even.not_nonempty_dringEquiv_of_atSeparation
