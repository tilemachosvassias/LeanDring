/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Algebra.BigOperators.Pi
import LeanDring.Even.Linkage

/-!
# Criterion T: transposition gauges exist exactly at linkage ≥ dual linkage

**EVEN-ORDER LAYER.** No `sorry`, three standard axioms.

Native-Lean formalization of **Criterion T**
(hand-proven + audited):
a coordinate transposition preserves the ghost lattice iff the linkage of
the pair dominates its dual linkage.

The formalization **generalizes the hand theorem**. The hand version is
stated for `D_F`-lattices of 2-power index with `ℓ, ℓ∨` read as 2-adic
valuations; the proof below needs *no index hypothesis at all* — not
2-power, not finite, not even full rank. For an arbitrary additive
subgroup `L ⊆ ℤ^ι` (`ι` finite):

* `swap_preserves_iff` — **Criterion T, divisibility form**: the
 transposition `τ_{pq}` maps `L` into itself iff
 `(x p − x q) · (r p − r q) ∈ ℤ` for every `x ∈ L` and every `r` in the
 rational dual of `L`. Specialized to 2-power index, the two sides are
 `2^ℓ ℤ` and `2^{−ℓ∨} ℤ`-type data and the condition reads `ℓ ≥ ℓ∨` —
 the hand statement.

The load-bearing ingredient is the **dual membership lemma**
`mem_iff_dual_pairing` (`v ∈ L ↔ ⟨r, v⟩ ∈ ℤ ∀ r ∈ L^∨`, i.e. `L^∨∨ = L`),
which we obtain from `ℚ/ℤ` separating points of any abelian group
(Mathlib's `CharacterModule`, injectivity of the rational circle) plus a
basis lift of characters to rational row vectors — no Smith normal form
needed.

Specialization to the D-ring layer (`LeanDring.Even.Linkage`):

* `ghost_swap_preserves_iff` — Criterion T for the ghost lattice of a
 ring `D`, phrased in the linkage vocabulary (`linkSubgroup`);
* `ghostSwapGauge` — **Criterion T ⟹ gauge**: when the divisibility
 condition holds for a pair `(φ, ψ)` of integer points, transposing
 those two coordinates is a *ring automorphism* of the ghost lattice
 (via `ghostRangeAutoOfPreserving`). This is the abstract mechanism
 behind the central gauges of Theorem G1: the `(1,1) ↔ (z,1)` swap of a
 cyclic/generalized-quaternion 2-group is exactly such a pair.
-/

namespace LeanDring

namespace Even

section AbstractLattice

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The integral pairing `⟨r, x⟩ = ∑ i, r i · x i` between a rational row
vector and an integer vector. -/
def zpair (r : ι → ℚ) (x : ι → ℤ) : ℚ := ∑ i, r i * (x i : ℚ)

omit [DecidableEq ι] in
theorem zpair_sub_right (r : ι → ℚ) (x y : ι → ℤ) :
    zpair r (x - y) = zpair r x - zpair r y := by
  simp only [zpair, Pi.sub_apply, Int.cast_sub, mul_sub,
    Finset.sum_sub_distrib]

omit [DecidableEq ι] in
theorem zpair_zsmul_right (r : ι → ℚ) (c : ℤ) (x : ι → ℤ) :
    zpair r (c • x) = (c : ℚ) * zpair r x := by
  simp only [zpair, Pi.smul_apply, smul_eq_mul, Int.cast_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem zpair_single (r : ι → ℚ) (p : ι) (c : ℤ) :
    zpair r (Pi.single p c) = r p * (c : ℚ) := by
  rw [zpair, Finset.sum_eq_single p]
  · rw [Pi.single_eq_same]
  · intro i _ hip
    rw [Pi.single_eq_of_ne hip, Int.cast_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ p) h

/-- The **rational dual** of an integer lattice: row vectors pairing `L`
into `ℤ`.  For the D-ring ghost lattice these are the rows whose
2-valuations are the dual linkage `ℓ∨` of the hand notes. -/
def dualLat (L : AddSubgroup (ι → ℤ)) : Set (ι → ℚ) :=
  {r | ∀ x ∈ L, zpair r x ∈ (Int.castRingHom ℚ).range}

/-- A rational is integral iff it dies in the rational circle `ℚ/ℤ`. -/
theorem intRange_iff_coe_zero (q : ℚ) :
    q ∈ (Int.castRingHom ℚ).range ↔ ((q : AddCircle (1 : ℚ)) = 0) := by
  rw [AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, by simp⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa using hn⟩

omit [DecidableEq ι] in
/-- **The dual membership lemma** (`L^∨∨ = L`, hard direction): an integer
vector pairing integrally with every dual vector lies in `L`.  Proof: a
character of `ℤ^ι/L` separating `v` from `L` (Mathlib `CharacterModule`,
`ℚ/ℤ` an injective cogenerator) lifts along the standard basis to a
rational row vector in the dual, contradicting integrality at `v`. -/
theorem mem_of_dual_pairing {L : AddSubgroup (ι → ℤ)} {v : ι → ℤ}
    (h : ∀ r ∈ dualLat L, zpair r v ∈ (Int.castRingHom ℚ).range) :
    v ∈ L := by
  classical
  by_contra hv
  have hne : QuotientAddGroup.mk' L v ≠ 0 := by
    rw [Ne, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    exact hv
  obtain ⟨c, hc⟩ :=
    CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne
  set f : (ι → ℤ) →+ AddCircle (1 : ℚ) :=
    (c : ((ι → ℤ) ⧸ L) →+ AddCircle (1 : ℚ)).comp
      (QuotientAddGroup.mk' L) with hfdef
  have hfL : ∀ x ∈ L, f x = 0 := by
    intro x hx
    have hx0 : QuotientAddGroup.mk' L x = 0 := by
      rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      exact hx
    rw [hfdef, AddMonoidHom.comp_apply, hx0, map_zero]
  have hfv : f v ≠ 0 := hc
  -- lift the character to a rational row vector along the standard basis
  have hsurj : ∀ i : ι, ∃ q : ℚ, (q : AddCircle (1 : ℚ)) = f (Pi.single i 1) :=
    fun i => QuotientAddGroup.mk_surjective _
  choose r hr using hsurj
  set π : ℚ →+ AddCircle (1 : ℚ) :=
    QuotientAddGroup.mk' (AddSubgroup.zmultiples 1) with hπdef
  have hπ : ∀ q : ℚ, π q = (q : AddCircle (1 : ℚ)) := fun q =>
    QuotientAddGroup.mk'_apply _ q
  -- the lift computes `f` everywhere
  have key : ∀ x : ι → ℤ, π (zpair r x) = f x := by
    intro x
    have hxdec : f x = ∑ i, f (Pi.single i (x i)) := by
      conv_lhs => rw [← Finset.univ_sum_single x]
      exact map_sum f _ _
    rw [hxdec]
    simp only [zpair]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (Pi.single i (x i) : ι → ℤ) = x i • Pi.single i (1 : ℤ) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [h1, map_zsmul, ← hr i, ← hπ (r i), ← map_zsmul]
    congr 1
    rw [zsmul_eq_mul, mul_comm]
  have hrdual : r ∈ dualLat L := by
    intro x hx
    rw [intRange_iff_coe_zero, ← hπ, key]
    exact hfL x hx
  have hint := h r hrdual
  rw [intRange_iff_coe_zero, ← hπ, key] at hint
  exact hfv hint

omit [DecidableEq ι] in
/-- **Dual membership, both directions**: `v ∈ L ↔ ⟨r, v⟩ ∈ ℤ` for all
`r ∈ L^∨`.  This is `L^∨∨ = L` for arbitrary sublattices of `ℤ^ι`. -/
theorem mem_iff_dual_pairing (L : AddSubgroup (ι → ℤ)) (v : ι → ℤ) :
    v ∈ L ↔ ∀ r ∈ dualLat L, zpair r v ∈ (Int.castRingHom ℚ).range :=
  ⟨fun hv _ hr => hr v hv, mem_of_dual_pairing⟩

omit [Fintype ι] in
/-- Transposing two coordinates subtracts the linkage direction:
`x ∘ τ_{pq} = x − (x p − x q)(e_p − e_q)`. -/
theorem comp_swap_eq_sub (x : ι → ℤ) (p q : ι) :
    x ∘ Equiv.swap p q =
      x - (x p - x q) • (Pi.single p (1 : ℤ) - Pi.single q 1) := by
  by_cases hpq : p = q
  · subst hpq
    simp [Equiv.swap_self]
  funext i
  simp only [Function.comp_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rcases eq_or_ne i p with rfl | hip
  · rw [Equiv.swap_apply_left, Pi.single_eq_same, Pi.single_eq_of_ne hpq]
    ring
  rcases eq_or_ne i q with rfl | hiq
  · rw [Equiv.swap_apply_right, Pi.single_eq_of_ne (Ne.symm hpq),
      Pi.single_eq_same]
    ring
  · rw [Equiv.swap_apply_of_ne_of_ne hip hiq, Pi.single_eq_of_ne hip,
      Pi.single_eq_of_ne hiq]
    ring

/-- Pairing against a transposed vector: the correction term is the
linkage–dual-linkage product. -/
theorem zpair_comp_swap (r : ι → ℚ) (x : ι → ℤ) (p q : ι) :
    zpair r (x ∘ Equiv.swap p q) =
      zpair r x - ((x p - x q : ℤ) : ℚ) * (r p - r q) := by
  rw [comp_swap_eq_sub, zpair_sub_right, zpair_zsmul_right, zpair_sub_right,
    zpair_single, zpair_single]
  push_cast
  ring

/-- **Criterion T, divisibility form, arbitrary sublattice**: the
transposition `τ_{pq}` maps `L` into itself iff every linkage value
`x p − x q` (`x ∈ L`) multiplies every dual difference `r p − r q`
(`r ∈ L^∨`) into `ℤ`.  With 2-power index this is exactly the hand
criterion `ℓ(p,q) ≥ ℓ∨(p,q)`; no index hypothesis is needed. -/
theorem swap_preserves_iff (L : AddSubgroup (ι → ℤ)) (p q : ι) :
    (∀ x ∈ L, x ∘ Equiv.swap p q ∈ L) ↔
      ∀ x ∈ L, ∀ r ∈ dualLat L,
        ((x p - x q : ℤ) : ℚ) * (r p - r q) ∈ (Int.castRingHom ℚ).range := by
  constructor
  · intro hτ x hx r hr
    have hmem : x - x ∘ Equiv.swap p q ∈ L := sub_mem hx (hτ x hx)
    have h1 := hr _ hmem
    rw [zpair_sub_right, zpair_comp_swap] at h1
    simpa using h1
  · intro h x hx
    apply mem_of_dual_pairing
    intro r hr
    rw [zpair_comp_swap]
    exact sub_mem (hr x hx) (h x hx r hr)

end AbstractLattice

section Ghost

variable {D : Type*} [CommRing D]

/-- The ghost lattice of `D` as an additive subgroup of `ℤ^{IntPoint D}`. -/
def ghostLattice (D : Type*) [CommRing D] : AddSubgroup (IntPoint D → ℤ) :=
  Subring.toAddSubgroup (ghost D).range

theorem mem_ghostLattice {x : IntPoint D → ℤ} :
    x ∈ ghostLattice D ↔ ∃ a : D, ghost D a = x := by
  simp [ghostLattice]

variable [Fintype (IntPoint D)] [DecidableEq (IntPoint D)]

/-- **Criterion T on the ghost lattice**, in linkage vocabulary: the
transposition of two integer points `φ, ψ` preserves the ghost lattice
iff every linkage value of the pair multiplies every dual difference into
`ℤ` — the hand criterion `ℓ(φ,ψ) ≥ ℓ∨(φ,ψ)` in divisibility form. -/
theorem ghost_swap_preserves_iff (φ ψ : IntPoint D) :
    (∀ x ∈ ghostLattice D, x ∘ Equiv.swap φ ψ ∈ ghostLattice D) ↔
      ∀ n ∈ linkSubgroup φ ψ, ∀ r ∈ dualLat (ghostLattice D),
        (n : ℚ) * (r φ - r ψ) ∈ (Int.castRingHom ℚ).range := by
  rw [swap_preserves_iff]
  constructor
  · intro h n hn r hr
    obtain ⟨a, rfl⟩ := mem_linkSubgroup.mp hn
    have := h (ghost D a) (mem_ghostLattice.mpr ⟨a, rfl⟩) r hr
    simpa using this
  · intro h x hx r hr
    obtain ⟨a, rfl⟩ := mem_ghostLattice.mp hx
    have hn : φ a - ψ a ∈ linkSubgroup φ ψ := mem_linkSubgroup.mpr ⟨a, rfl⟩
    simpa using h _ hn r hr

/-- **Criterion T ⟹ gauge**: when the linkage–dual-linkage divisibility
holds for the pair `(φ, ψ)`, transposing those two coordinates is a ring
automorphism of the ghost lattice.  This is the abstract mechanism behind
the Theorem-G1 central gauges. -/
noncomputable def ghostSwapGauge (φ ψ : IntPoint D)
    (h : ∀ n ∈ linkSubgroup φ ψ, ∀ r ∈ dualLat (ghostLattice D),
      (n : ℚ) * (r φ - r ψ) ∈ (Int.castRingHom ℚ).range) :
    (ghost D).range ≃+* (ghost D).range :=
  ghostRangeAutoOfPreserving (Equiv.swap φ ψ) (by
    have hswap := (ghost_swap_preserves_iff φ ψ).mpr h
    have hτ : ∀ x ∈ (ghost D).range,
        x ∘ Equiv.swap φ ψ ∈ (ghost D).range := fun x hx =>
      mem_ghostLattice.mp (hswap x (mem_ghostLattice.mpr
        (RingHom.mem_range.mp hx))) |>.elim fun a ha =>
          RingHom.mem_range.mpr ⟨a, ha⟩
    have hcoe : ∀ x : IntPoint D → ℤ,
        (reindex (Equiv.swap φ ψ) : _ →+* _) x = x ∘ Equiv.swap φ ψ := by
      intro x
      funext γ
      simp [Equiv.symm_swap]
    apply le_antisymm
    · intro y hy
      rw [Subring.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [hcoe]
      exact hτ x hx
    · intro y hy
      rw [Subring.mem_map]
      refine ⟨y ∘ Equiv.swap φ ψ, hτ y hy, ?_⟩
      rw [hcoe]
      funext γ
      simp [Function.comp_apply, Equiv.swap_apply_self])

end Ghost

end Even

end LeanDring
