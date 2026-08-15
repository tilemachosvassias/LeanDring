/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Even.CriterionT

/-!
# The gauge group Γ(L) and the duality of gauges

**EVEN-ORDER LAYER.** No `sorry`, three standard axioms.

Criterion T (`LeanDring.Even.swap_preserves_iff`) decides single
transpositions. The object the gauge program (Theorem G1/G2, An5″)
actually studies is the **group of all lattice-preserving coordinate
permutations**. This file makes it a formal object and proves the
theory-level facts that hold in full generality:

* `latticePermGroup L` — **Γ(L)**, the gauge group, as a `Subgroup` of
 `Equiv.Perm ι`. Inverse-closure is a theorem, not an axiom: a
 permutation has finite order, so `σL ⊆ L` already forces
 `σ⁻¹L ⊆ L` (`comp_perm_symm_mem`).
* `mem_latticePermGroup_iff_dual` — **Theorem P, the duality of
 gauges**: `σ ∈ Γ(L)` iff the transposed-inverse action `r ↦ r ∘ σ`
 preserves the rational dual `L^∨`. This is the full generalization of
 Criterion T from transpositions to arbitrary permutations; it needs no
 index hypothesis (the dual membership lemma `L^∨∨ = L` does all the
 work). Criterion T is recovered as the rank-1 slice
 (`swap_mem_latticePermGroup_iff`).
* `pointPush` / `fixedPointSet` / `intPointEquiv_mem_fixedPointSet` —
 the **recognition frame**: for a ring endomorphism `T: D →+* D` the
 pushforward acts on integer points; for `D = D(G)` with `T = ψ²` and
 `G` a 2-group the fixed points are exactly the mark species (a
 decoration `h` with `h² ∼ h` is trivial in a 2-group), i.e. the
 B-slice on points. The transport lemma says the induced point
 bijection of a ring isomorphism carries fixed set to fixed set
 *provided the isomorphism intertwines the endomorphisms* — and that
 hypothesis is verbatim the ψ²-recognition wall
 (`LeanDring.Even.twoGroupDtoB_of_psiTwoRecognition`).

## Where the open problem now sits, formally

By `AL0`/`L1` every ring isomorphism induces a point bijection
preserving the ghost lattices; composing with any `σ ∈ Γ(L)` gives
another. The An5″/TIR question — and through FIX-ψ² the whole 2-group
`D ⇒ B` problem — is whether the `Γ`-orbit of the B-slice consists of
B-slice-equivalent coordinate sets. Theorem G1 (hand) computes the
bottom of `Γ` for cyclic/generalized-quaternion groups; the Q8
counterexample to An5′ shows `Γ` can genuinely move fibres, which is why
the target is orbit-equivalence, not pointwise fixity.
-/

namespace LeanDring

namespace Even

section GaugeGroup

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- Reindexing a pairing along a permutation: `⟨r, x ∘ σ⟩ = ⟨r ∘ σ⁻¹, x⟩`.
The transpose of the permutation action on columns is the inverse
permutation acting on rows. -/
theorem zpair_comp_perm [Fintype ι] (r : ι → ℚ) (x : ι → ℤ)
    (σ : Equiv.Perm ι) :
    zpair r (x ∘ σ) = zpair (r ∘ σ.symm) x := by
  simp only [zpair, Function.comp_apply]
  exact Fintype.sum_equiv σ _ _ fun i => by simp

omit [Fintype ι] in
/-- Powers of a lattice-preserving permutation preserve the lattice. -/
theorem comp_perm_pow_mem {L : AddSubgroup (ι → ℤ)} {σ : Equiv.Perm ι}
    (hσ : ∀ x ∈ L, x ∘ σ ∈ L) (n : ℕ) :
    ∀ x ∈ L, x ∘ ⇑(σ ^ n) ∈ L := by
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih =>
    intro x hx
    have h1 : x ∘ ⇑(σ ^ (n + 1)) = (x ∘ ⇑(σ ^ n)) ∘ σ := by
      funext j
      simp [pow_succ]
    rw [h1]
    exact hσ _ (ih x hx)

omit [Fintype ι] in
/-- **Inverse closure is automatic**: a permutation has finite order, so
preserving the lattice forwards already forces preserving it backwards.
This is what makes the gauge set a *group*. -/
theorem comp_perm_symm_mem [Finite ι] {L : AddSubgroup (ι → ℤ)} {σ : Equiv.Perm ι}
    (hσ : ∀ x ∈ L, x ∘ σ ∈ L) : ∀ x ∈ L, x ∘ ⇑σ.symm ∈ L := by
  intro x hx
  have hk : orderOf σ ≠ 0 := (orderOf_pos σ).ne'
  have h1 : σ * σ ^ (orderOf σ - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk),
      pow_orderOf_eq_one]
  have hinv : σ.symm = σ ^ (orderOf σ - 1) :=
    inv_eq_of_mul_eq_one_right h1
  rw [show x ∘ ⇑σ.symm = x ∘ ⇑(σ ^ (orderOf σ - 1)) by rw [hinv]]
  exact comp_perm_pow_mem hσ _ x hx

/-- **The gauge group `Γ(L)`**: all coordinate permutations preserving
the lattice, as a subgroup of `Equiv.Perm ι`.  For the ghost lattice of
`D(G)` this is the group whose bottom the central-gauge dichotomy
(Theorem G1) computes by hand. -/
def latticePermGroup (L : AddSubgroup (ι → ℤ)) : Subgroup (Equiv.Perm ι) where
  carrier := {σ | ∀ x ∈ L, x ∘ σ ∈ L}
  one_mem' := by intro x hx; simpa using hx
  mul_mem' := by
    intro σ τ hσ hτ x hx
    have h1 : x ∘ ⇑(σ * τ) = (x ∘ σ) ∘ τ := by
      funext j
      simp
    rw [h1]
    exact hτ _ (hσ x hx)
  inv_mem' := fun hσ => comp_perm_symm_mem hσ

theorem mem_latticePermGroup {L : AddSubgroup (ι → ℤ)} {σ : Equiv.Perm ι} :
    σ ∈ latticePermGroup L ↔ ∀ x ∈ L, x ∘ σ ∈ L := Iff.rfl

/-- **Theorem P — the duality of gauges**: a coordinate permutation
preserves the lattice iff its inverse, acting on rows, preserves the
rational dual.  This subsumes Criterion T (transpositions are the
self-inverse case) and holds for arbitrary sublattices — the dual
membership lemma `L^∨∨ = L` carries the whole proof. -/
theorem mem_latticePermGroup_iff_dual (L : AddSubgroup (ι → ℤ))
    (σ : Equiv.Perm ι) :
    σ ∈ latticePermGroup L ↔ ∀ r ∈ dualLat L, r ∘ ⇑σ.symm ∈ dualLat L := by
  constructor
  · intro hσ r hr x hx
    rw [← zpair_comp_perm]
    exact hr _ (hσ x hx)
  · intro hdual x hx
    apply mem_of_dual_pairing
    intro r hr
    rw [zpair_comp_perm]
    exact hdual r hr x hx

/-- Criterion T is the rank-1 slice of the gauge group: membership of a
transposition is decided by the linkage–dual-linkage divisibility. -/
theorem swap_mem_latticePermGroup_iff [DecidableEq ι]
    (L : AddSubgroup (ι → ℤ)) (p q : ι) :
    Equiv.swap p q ∈ latticePermGroup L ↔
      ∀ x ∈ L, ∀ r ∈ dualLat L,
        ((x p - x q : ℤ) : ℚ) * (r p - r q) ∈ (Int.castRingHom ℚ).range :=
  swap_preserves_iff L p q

end GaugeGroup

section Recognition

variable {D : Type*} [CommRing D] {D' : Type*} [CommRing D']

/-- Pushforward of integer points along a ring endomorphism:
`T⁎ φ = φ ∘ T`.  For `D = D(G)`, `T = ψ²` acts on species by
`(H, h) ↦ (H, h²)`. -/
def pointPush (T : D →+* D) : IntPoint D → IntPoint D := fun φ => φ.comp T

/-- The fixed points of a pushforward.  For `D = D(G)` with `T = ψ²` and
`G` a 2-group these are exactly the mark species — a fused decoration
with `h² ∼ h` has odd order, hence is trivial in a 2-group — i.e. the
**B-slice on integer points** (the point-level face of FIX-ψ²). -/
def fixedPointSet (T : D →+* D) : Set (IntPoint D) :=
  {φ | pointPush T φ = φ}

/-- **The recognition frame**: if a ring isomorphism intertwines the two
endomorphisms, the induced point bijection carries fixed set to fixed
set.  The hypothesis `hcomm` is verbatim the ψ²-recognition wall: for
2-groups it is exactly what `twoGroupDtoB_of_psiTwoRecognition` needs
and exactly what an abstract isomorphism does not automatically provide.
The open 2-group problem, in this vocabulary: must the point bijection
of an arbitrary isomorphism carry `fixedPointSet ψ²` to a `Γ`-gauge
image of `fixedPointSet ψ²`? -/
theorem intPointEquiv_mem_fixedPointSet (Φ : D ≃+* D') (T : D →+* D)
    (T' : D' →+* D') (hcomm : ∀ x, Φ (T x) = T' (Φ x))
    {φ : IntPoint D'} (hφ : φ ∈ fixedPointSet T') :
    intPointEquiv Φ φ ∈ fixedPointSet T := by
  simp only [fixedPointSet, Set.mem_setOf_eq] at hφ ⊢
  ext x
  change φ (Φ (T x)) = φ (Φ x)
  rw [hcomm]
  exact DFunLike.congr_fun hφ (Φ x)

end Recognition

end Even

end LeanDring
