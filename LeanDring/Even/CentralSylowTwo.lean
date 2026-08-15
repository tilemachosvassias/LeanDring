/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.NoncommCoprod
import LeanDring.Even.Functorial
import LeanDring.Even.OrderTransfer

/-!
# Theorem MC1: the class `C₂ × H`, `H` of odd order

**EVEN-ORDER LAYER.** Inside the root module's build closure and audit:
no `sorry`, three standard axioms. The results here are verified
*implications*; their hypotheses are named `Prop`s.

This file formalizes what can be formalized of the central-Sylow-two
reformulation without the coprime tensor factorization of `D`, which the
corpus does not have.

The split is clean:

* the **group theory** is proven outright here — a finite group whose Sylow
  `2`-subgroup is central of order `2` is a direct product `K × P` with `K`
 of odd order (`directProduct_of_central_sylow_two`). The engine is
  Mathlib's Burnside transfer theorem `ker_transferSylow_isComplement'`;
  centrality supplies its hypothesis `N(P) ≤ C(P)` for free;
* the **ring theory** is typed, not proven: `CoprimeTensorFactorization`
  (Müller Satz 2.8.3), `TwoFactorCancellation` (Satz 2.8.5, whose proof
  runs through Satz 2.2.7 and the abstract cancellation Satz 2.8.4) and
  `BurnsideCoprimeMultiplicative` (Dress) are named `Prop`s, exactly as
  the simple-group lane types its classification input;
* the **odd-order step** is neither typed nor reproved: it is the
  kernel-checked `burnsideEquivOfOddOrder` of
  `LeanDring/Theory/OddOrder/OddOrder.lean`.

So `mc1` below is a verified implication whose only unverified inputs are
three published theorems, and `dtoB_of_central_sylow_two` upgrades it to
the group-theoretic class statement using the proven structure theorem —
i.e. the reduction from the class to the product form is *not* assumed.

No `sorry`, no custom axiom.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

namespace LeanDring

namespace Even

universe u

open Subgroup MonoidHom

/-! ## The structure theorem: central Sylow `2` of order `2` -/

section Structure

variable {G : Type u} [Group G] [Finite G]

/-- If a Sylow subgroup is central then Burnside's hypothesis
`N_G(P) ≤ C_G(P)` holds trivially: the centralizer of a central subgroup
is everything. -/
theorem normalizer_le_centralizer_of_le_center {p : ℕ} (P : Sylow p G)
    (hP : (P : Subgroup G) ≤ center G) :
    normalizer (P : Subgroup G) ≤ centralizer (P : Set G) := by
  intro g _
  rw [mem_centralizer_iff]
  intro h hh
  exact (Subgroup.mem_center_iff.mp (hP hh) g).symm

/-- **[PROVEN]** A finite group with central Sylow `2`-subgroup is the
direct product of an odd-order normal subgroup and that Sylow subgroup.

This is the group-theoretic content of the paper's Cor. 6.4 — the groups
with central Sylow `2`-subgroup of order `2` are exactly the `C₂ × H`
with `H` odd — proved here in the form that does not fix `|P| = 2`:
Burnside's transfer theorem gives a normal `2`-complement `K`, and
centrality of `P` turns the complement into a direct factor. -/
theorem directProduct_of_central_sylow_two (P : Sylow 2 G)
    (hP : (P : Subgroup G) ≤ center G) :
    ∃ K : Subgroup G, K.Normal ∧ ¬ (2 ∣ Nat.card K) ∧
      Nonempty (G ≃* (K × (P : Subgroup G))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Sylow 2 G) := inferInstance
  haveI : (P : Subgroup G).FiniteIndex := inferInstance
  have hNC : normalizer (P : Subgroup G) ≤ centralizer (P : Set G) :=
    normalizer_le_centralizer_of_le_center P hP
  set K : Subgroup G := (transferSylow P hNC).ker with hK
  have hcompl : IsComplement' K (P : Subgroup G) :=
    ker_transferSylow_isComplement' P hNC
  have hodd : ¬ (2 ∣ Nat.card K) := not_dvd_card_ker_transferSylow P hNC
  -- `P` is central, so the two inclusions commute elementwise and their
  -- coproduct `K × P →* G` is a homomorphism; the complement property says
  -- exactly that it is bijective.
  have hcomm : ∀ (a : K) (b : (P : Subgroup G)),
      Commute (K.subtype a) ((P : Subgroup G).subtype b) := by
    intro a b
    exact Subgroup.mem_center_iff.mp (hP b.2) (a : G)
  refine ⟨K, inferInstance, hodd, ⟨?_⟩⟩
  refine (MulEquiv.ofBijective
    (MonoidHom.noncommCoprod K.subtype (P : Subgroup G).subtype hcomm) ?_).symm
  exact hcompl

end Structure

/-! ## The three typed ring-theoretic inputs -/

/-- **[OPEN formally; Müller Satz 2.8.3 *and* Satz 2.8.5, in the repaired
form of the paper's Prop. 6.2 + Rem. 6.3]**

Read the statement, not the name: this is *not* only the tensor
factorization `D(P × H) ≅ D(P) ⊗ D(H)` (2.8.3). It is the **descent** —
a `D`-isomorphism of two coprime products yields isomorphisms of the
factors — and the descent is exactly the cancellation step, 2.8.5. So
this single `Prop` carries the mathematical heart of Theorem MC1; `mc1`
below obtains `D(H) ≅ D(H')` from it outright and then only applies the
kernel-checked odd-order theorem and reassembles. Do not read `mc1` as a
formalization of the cancellation argument: that argument is assumed here.

Two further cautions. (1) 2.8.5 is used in the *repaired* form: the
paper's Rem. 6.3 shows Müller's printed hypothesis (b), "`R ⊗ Bᵢ`
semisimple", cannot be met for the local ring `R` the application needs,
and replaces it by what Satz 2.2.7 actually supplies. The citation is to
the repaired statement. (2) Of the paper's Prop. 6.2 the idempotent core
*is* formalized, in `LeanDring/Even/Cancellation.lean`; what is assumed here is the
descent step (the `ℤ`-basis of `A₂` containing `1` forcing `1 ⊗ B₁ ↦
1 ⊗ B₂`).

Typing the tensor product itself would require the coprime decomposition
of monomial `G`-sets, which the corpus does not have. -/
def CoprimeTensorFactorization : Prop :=
  ∀ (P H P' H' : Type u) [Group P] [Group H] [Group P'] [Group H']
    [Fintype P] [Fintype H] [Fintype P'] [Fintype H'],
    IsPGroup 2 P → IsPGroup 2 P' → Odd (Nat.card H) → Odd (Nat.card H') →
      Nonempty (DRing (P × H) ≃+* DRing (P' × H')) →
        Nonempty (DRing P ≃+* DRing P') ∧ Nonempty (DRing H ≃+* DRing H')

/-- **[OPEN formally; Dress]** The Burnside ring is multiplicative on
coprime direct factors, in the form the assembly consumes: isomorphic
factors give isomorphic products. -/
def BurnsideCoprimeMultiplicative : Prop :=
  ∀ (P H P' H' : Type u) [Group P] [Group H] [Group P'] [Group H']
    [Fintype P] [Fintype H] [Fintype P'] [Fintype H'],
    Nonempty (P ≃* P') → Nonempty (BurnsideRing H ≃+* BurnsideRing H') →
      Nonempty (BurnsideRing (P × H) ≃+* BurnsideRing (P' × H'))

/-- A `2`-group of order `2` is determined: any two are isomorphic. This is
the only place where `|P| = 2` (rather than `P` elementary abelian) is
used, and it is elementary. -/
theorem mulEquiv_of_card_two {P P' : Type u} [Group P] [Group P']
    (hP : Nat.card P = 2) (hP' : Nat.card P' = 2) : Nonempty (P ≃* P') := by
  haveI : Finite P := Nat.finite_of_card_ne_zero (by omega)
  haveI : Finite P' := Nat.finite_of_card_ne_zero (by omega)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨mulEquivOfPrimeCardEq hP hP'⟩

/-! ## Theorem MC1 -/

/-- **Theorem MC1 [PROVEN from the typed inputs]**. For `H`,
`H'` of odd order, `D(C₂ × H) ≅ D(C₂ × H')` implies
`B(C₂ × H) ≅ B(C₂ × H')`.

The proof is the four-step chain: factor (`CoprimeTensorFactorization`),
cancel the `2`-part (same `Prop`), apply the odd-order theorem (the
kernel-checked `burnsideEquivOfOddOrder`), reassemble
(`BurnsideCoprimeMultiplicative`). -/
theorem mc1 (hfac : CoprimeTensorFactorization.{u})
    (hmul : BurnsideCoprimeMultiplicative.{u})
    (P P' H H' : Type u) [Group P] [Group P'] [Group H] [Group H']
    [Fintype P] [Fintype P'] [Fintype H] [Fintype H']
    (hP : Nat.card P = 2) (hP' : Nat.card P' = 2)
    (hH : Odd (Nat.card H)) (hH' : Odd (Nat.card H'))
    (hD : Nonempty (DRing (P × H) ≃+* DRing (P' × H'))) :
    Nonempty (BurnsideRing (P × H) ≃+* BurnsideRing (P' × H')) := by
  have hp : IsPGroup 2 P := IsPGroup.of_card (n := 1) (by simpa using hP)
  have hp' : IsPGroup 2 P' := IsPGroup.of_card (n := 1) (by simpa using hP')
  obtain ⟨-, hodd⟩ := hfac P H P' H' hp hp' hH hH' hD
  obtain ⟨Ψ⟩ := hodd
  refine hmul P H P' H' (mulEquiv_of_card_two hP hP') ⟨OddOrder.burnsideEquivOfOddOrder Ψ ?_ ?_⟩
  · simpa [Nat.card_eq_fintype_card] using hH
  · simpa [Nat.card_eq_fintype_card] using hH'

/-- **Corollary [PROVEN from the same inputs]**: the class statement. For
groups with central Sylow `2`-subgroup of order `2`, `D` determines `B`.
The reduction from the class to the product form is the proven
`directProduct_of_central_sylow_two`, not an assumption. -/
theorem dtoB_of_central_sylow_two (hfac : CoprimeTensorFactorization.{u})
    (hmul : BurnsideCoprimeMultiplicative.{u})
    (G G' : Type u) [Group G] [Group G'] [Fintype G] [Fintype G']
    (P : Sylow 2 G) (P' : Sylow 2 G')
    (hcard : Nat.card (P : Subgroup G) = 2)
    (hcard' : Nat.card (P' : Subgroup G') = 2)
    (hcen : (P : Subgroup G) ≤ center G) (hcen' : (P' : Subgroup G') ≤ center G')
    (hD : Nonempty (DRing G ≃+* DRing G')) :
    Nonempty (BurnsideRing G ≃+* BurnsideRing G') := by
  obtain ⟨K, -, hKodd, ⟨eG⟩⟩ := directProduct_of_central_sylow_two P hcen
  obtain ⟨K', -, hK'odd, ⟨eG'⟩⟩ := directProduct_of_central_sylow_two P' hcen'
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype K' := Fintype.ofFinite K'
  haveI : Fintype (P : Subgroup G) := Fintype.ofFinite _
  haveI : Fintype (P' : Subgroup G') := Fintype.ofFinite _
  have hodd : Odd (Nat.card K) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hKodd)
  have hodd' : Odd (Nat.card K') := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hK'odd)
  -- transport the hypothesis along the two structure isomorphisms
  obtain ⟨Φ⟩ := hD
  have hD' : Nonempty (DRing (K × (P : Subgroup G)) ≃+* DRing (K' × (P' : Subgroup G'))) :=
    ⟨((MonRing.congr eG).symm.trans Φ).trans (MonRing.congr eG')⟩
  -- and run MC1 with the factors in the order `(2-part, odd part)`
  have := mc1 hfac hmul (P : Subgroup G) (P' : Subgroup G') K K'
    hcard hcard' hodd hodd' (by
      obtain ⟨Ψ⟩ := hD'
      exact ⟨(MonRing.congr (MulEquiv.prodComm)).trans
        (Ψ.trans (MonRing.congr (MulEquiv.prodComm)))⟩)
  obtain ⟨Θ⟩ := this
  exact ⟨((burnsideRingCongr eG).trans
    ((burnsideRingCongr (MulEquiv.prodComm)).trans
      (Θ.trans (burnsideRingCongr (MulEquiv.prodComm))))).trans
        (burnsideRingCongr eG').symm⟩

end Even

end LeanDring

/-! ## Axiom audit -/

#print axioms LeanDring.Even.directProduct_of_central_sylow_two
#print axioms LeanDring.Even.mulEquiv_of_card_two
#print axioms LeanDring.Even.mc1
#print axioms LeanDring.Even.dtoB_of_central_sylow_two
