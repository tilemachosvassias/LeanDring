/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Even.Profiles

/-!
# The full transport package: arity sums and dual linkage are canonical
# under arbitrary lattice identifications

**EVEN-ORDER LAYER.** No `sorry`, three standard axioms.

The extraspecial anchoring analysis (An1–An5) shows a fibre-separating profile
must contain more than pairwise linkage: the twin blind spot (An2) and
the T2 shuffle (An3) are exact. The repair data are the **arity tower**
`ℓ(S)` and the **dual linkage** `ℓ∨` (Criterion-T data, the witness
webs). This file proves that *all* of it transports under arbitrary
lattice identifications, completing the `htrans` half of the profile
contract for every invariant the class programme will build:

* `IdentifiesLattices.symm` — identifications invert.
* `sumLinkSubgroup_of_identifies` — arity-`|S|` linkage is a lattice
 invariant, preserved by every identification.
* `comp_mem_dualLat_of_identifies` — identifications transport the
 rational dual (cross-ring Theorem P).
* `dualDiffSubgroup` / `dualDiffSubgroup_of_identifies` — the **dual
 linkage subgroup** `{r_φ − r_ψ: r ∈ L^∨} ⊆ ℚ` (whose negative
 2-valuation is the hand programme's `ℓ∨`) is preserved by every
 identification.

Consequently the candidate extraspecial profile
`I(φ) = (ℓ-row, ℓ∨-row, arity data)` is transported *for free*; the
only remaining debt of the class programme is the separation statement
`hlevel` (An5″), which is class-specific valuation combinatorics.
-/

namespace LeanDring

namespace Even

universe u v

/-- Lattice identifications invert. -/
theorem IdentifiesLattices.symm {D : Type*} [CommRing D]
    {D' : Type*} [CommRing D'] {e : IntPoint D' ≃ IntPoint D}
    (he : IdentifiesLattices e) : IdentifiesLattices e.symm := by
  intro v'
  have hcomp : (v' ∘ ⇑e.symm) ∘ ⇑e = v' := by
    funext p
    simp
  have h := he (v' ∘ ⇑e.symm)
  rw [hcomp] at h
  exact h.symm

/-- Arity sums are lattice data: membership in the arity-`|S|` linkage
subgroup is computed by the ghost lattice alone. -/
theorem mem_sumLinkSubgroup_iff_lattice {D : Type*} [CommRing D]
    {s : Finset (IntPoint D)} {n : ℤ} :
    n ∈ sumLinkSubgroup s ↔
      ∃ v ∈ (ghost D).range, ∑ φ ∈ s, v φ = n := by
  simp only [sumLinkSubgroup, AddMonoidHom.mem_range, sumHom_apply]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨ghost D x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨v, ⟨x, rfl⟩, h⟩
    exact ⟨x, h⟩

/-- **Arity transport**: every lattice identification preserves the
whole arity tower of linkage subgroups. -/
theorem sumLinkSubgroup_of_identifies {D : Type*} [CommRing D]
    {D' : Type*} [CommRing D'] {e : IntPoint D' ≃ IntPoint D}
    (he : IdentifiesLattices e) (s : Finset (IntPoint D')) :
    sumLinkSubgroup (s.map e.toEmbedding) = sumLinkSubgroup s := by
  ext n
  rw [mem_sumLinkSubgroup_iff_lattice, mem_sumLinkSubgroup_iff_lattice]
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨v ∘ ⇑e, ?_, ?_⟩
    · exact mem_ghostLattice_iff_mem_range.mp
        ((he v).mpr (mem_ghostLattice_iff_mem_range.mpr hv))
    · rw [← h, Finset.sum_map]
      rfl
  · rintro ⟨w, hw, h⟩
    have hcomp : (w ∘ ⇑e.symm) ∘ ⇑e = w := by
      funext p
      simp
    refine ⟨w ∘ ⇑e.symm, ?_, ?_⟩
    · refine mem_ghostLattice_iff_mem_range.mp ((he _).mp ?_)
      rw [hcomp]
      exact mem_ghostLattice_iff_mem_range.mpr hw
    · rw [← h, Finset.sum_map]
      refine Finset.sum_congr rfl fun φ' _ => ?_
      simp

section Dual

variable {D : Type u} [CommRing D] {D' : Type v} [CommRing D']
variable [Fintype (IntPoint D)] [Fintype (IntPoint D')]

theorem zpair_add_left {ι : Type*} [Fintype ι] (r s : ι → ℚ) (x : ι → ℤ) :
    zpair (r + s) x = zpair r x + zpair s x := by
  simp only [zpair, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem zpair_neg_left {ι : Type*} [Fintype ι] (r : ι → ℚ) (x : ι → ℤ) :
    zpair (-r) x = -zpair r x := by
  simp only [zpair, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

/-- **Cross-ring Theorem P**: a lattice identification transports the
rational dual — composition with `e` maps the dual of the `D`-side ghost
lattice into the dual of the `D'`-side one. -/
theorem comp_mem_dualLat_of_identifies {e : IntPoint D' ≃ IntPoint D}
    (he : IdentifiesLattices e) {r : IntPoint D → ℚ}
    (hr : r ∈ dualLat (ghostLattice D)) :
    r ∘ ⇑e ∈ dualLat (ghostLattice D') := by
  intro w hw
  have hreindex : zpair (r ∘ ⇑e) w = zpair r (w ∘ ⇑e.symm) := by
    simp only [zpair, Function.comp_apply]
    exact Fintype.sum_equiv e _ _ fun φ' => by simp
  rw [hreindex]
  exact hr _ ((he.symm w).mpr hw)

/-- The **dual linkage subgroup** of a pair of points:
`{r_φ − r_ψ: r ∈ L^∨} ⊆ ℚ`.  Its negative 2-valuation is the hand
programme's dual linkage `ℓ∨(φ,ψ)` — the Criterion-T datum. -/
def dualDiffSubgroup (D : Type u) [CommRing D] [Fintype (IntPoint D)]
    (φ ψ : IntPoint D) : AddSubgroup ℚ where
  carrier := {q | ∃ r ∈ dualLat (ghostLattice D), r φ - r ψ = q}
  zero_mem' := ⟨0, fun x _ => by
      have h0 : zpair (0 : IntPoint D → ℚ) x = 0 := by simp [zpair]
      rw [h0]
      exact zero_mem _,
    by simp⟩
  add_mem' := by
    rintro q₁ q₂ ⟨r₁, hr₁, rfl⟩ ⟨r₂, hr₂, rfl⟩
    refine ⟨r₁ + r₂, fun x hx => ?_, by simp only [Pi.add_apply]; ring⟩
    rw [zpair_add_left]
    exact add_mem (hr₁ x hx) (hr₂ x hx)
  neg_mem' := by
    rintro q ⟨r, hr, rfl⟩
    refine ⟨-r, fun x hx => ?_, by simp only [Pi.neg_apply]; ring⟩
    rw [zpair_neg_left]
    exact neg_mem (hr x hx)

/-- **Dual linkage is canonical under arbitrary lattice
identifications** — the ℓ∨ half of the profile transports for free. -/
theorem dualDiffSubgroup_of_identifies {e : IntPoint D' ≃ IntPoint D}
    (he : IdentifiesLattices e) (φ' ψ' : IntPoint D') :
    dualDiffSubgroup D (e φ') (e ψ') = dualDiffSubgroup D' φ' ψ' := by
  ext q
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r ∘ ⇑e, comp_mem_dualLat_of_identifies he hr, rfl⟩
  · rintro ⟨r', hr', rfl⟩
    refine ⟨r' ∘ ⇑e.symm, comp_mem_dualLat_of_identifies he.symm hr', ?_⟩
    simp

end Dual

end Even

end LeanDring

namespace LeanDring.Even  -- reopened for the unit bound

/-- **The unit bound (Proposition O)**: the unit of `D` has all-ones
ghost vector, so `|S|` always lies in the arity-`|S|` linkage subgroup —
`ℓ(S) ≤ v₂(|S|)` for every finite set of points of every ring.  All
odd-size sets carry no arity information; the fibre beacons
(`ℓ(F) = log₂ |F|`, An4) are extremal against this bound. -/
theorem card_mem_sumLinkSubgroup {D : Type*} [CommRing D]
    (s : Finset (IntPoint D)) :
    ((s.card : ℤ)) ∈ sumLinkSubgroup s :=
  ⟨1, by simp⟩

end LeanDring.Even
