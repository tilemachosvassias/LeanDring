/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Even.Arity

/-!
# Evaluation subgroups of arbitrary arity, and the class-constancy of
# Burnside generators

**EVEN-ORDER LAYER.** No `sorry`, three standard axioms.

Two formal pieces backing the hand results of `NOTES.md` §2d–§2f:

* `ghostEvalSubgroup` / `dualEvalSubgroup` — the **primal and dual
  evaluation subgroups of arbitrary arity**: for a tuple `s` of integer
  points, the subgroup of `ℤ^{ι'}` (resp. `ℚ^{ι'}`) of values
  `(r_{s i})_i` over the ghost (resp. dual) lattice.  These subsume the
  pairwise `linkSubgroup`/`dualDiffSubgroup` and are exactly the
  **F2′ triple lattices** at `ι' = Fin 3` — the objects whose coupled
  vectors `(−2,−2,1)` detect T2/line incidence, and whose Hermite
  normal forms are certified in the hand notes, not here.  Both are
  preserved by every lattice identification (`…_of_identifies`) — the
  transport half of any profile built from them is free, at every arity.

* `ghost_eta_constantOnClasses` / `ghost_eta_comp_eq` — **the TCR
  mechanism, abstractly**: the ghost vector of a Burnside element
  `η b` is constant on shadow classes (two points with equal shadow
  agree on `η(B)` — `burnsideShadow_eq_iff`), hence invariant under
  precomposition with any class-preserving point map.  This is the
  formal core of the disjoint-support pairing of Theorems TCR/TCR-0:
  the fibre-constant witnesses `[M,1]` are Burnside generators, so
  within-fibre compensations act trivially on them, and only crossing
  terms survive — those are then killed by
  `not_mem_latticePermGroup_of_witness` (`Transport.lean`) with the
  class-specific arithmetic supplying the non-integral value.
-/

namespace LeanDring

namespace Even

open MonRing

universe u v

section Eval

variable {D : Type*} [CommRing D] {D' : Type*} [CommRing D']
variable {ι' : Type*}

/-- The **primal evaluation subgroup** of a tuple of points: values of
ghost-lattice vectors along `s`. -/
def ghostEvalSubgroup (D : Type*) [CommRing D] (s : ι' → IntPoint D) :
    AddSubgroup (ι' → ℤ) where
  carrier := {q | ∃ v ∈ (ghost D).range, (fun i => v (s i)) = q}
  zero_mem' := ⟨0, zero_mem _, by funext i; rfl⟩
  add_mem' := by
    rintro a b ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨v + w, add_mem hv hw, by funext i; simp⟩
  neg_mem' := by
    rintro a ⟨v, hv, rfl⟩
    exact ⟨-v, neg_mem hv, by funext i; simp⟩

/-- Primal evaluation subgroups are preserved by every lattice
identification. -/
theorem ghostEvalSubgroup_of_identifies {e : IntPoint D' ≃ IntPoint D}
    (he : IdentifiesLattices e) (s : ι' → IntPoint D') :
    ghostEvalSubgroup D (⇑e ∘ s) = ghostEvalSubgroup D' s := by
  ext q
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v ∘ ⇑e, ?_, rfl⟩
    exact mem_ghostLattice_iff_mem_range.mp
      ((he v).mpr (mem_ghostLattice_iff_mem_range.mpr hv))
  · rintro ⟨w, hw, rfl⟩
    have hcomp : (w ∘ ⇑e.symm) ∘ ⇑e = w := by
      funext p
      simp
    refine ⟨w ∘ ⇑e.symm, ?_, ?_⟩
    · refine mem_ghostLattice_iff_mem_range.mp ((he _).mp ?_)
      rw [hcomp]
      exact mem_ghostLattice_iff_mem_range.mpr hw
    · funext i
      simp

/-- The **dual evaluation subgroup** of a tuple of points: values of
rational-dual vectors along `s`.  At `ι' = Fin 3` these are the F2′
triple lattices of `NOTES.md` §2d. -/
def dualEvalSubgroup (D : Type u) [CommRing D] [Fintype (IntPoint D)]
    (s : ι' → IntPoint D) : AddSubgroup (ι' → ℚ) where
  carrier := {q | ∃ r ∈ dualLat (ghostLattice D), (fun i => r (s i)) = q}
  zero_mem' := ⟨0, fun x _ => by
      have h0 : zpair (0 : IntPoint D → ℚ) x = 0 := by simp [zpair]
      rw [h0]
      exact zero_mem _,
    by funext i; rfl⟩
  add_mem' := by
    rintro a b ⟨r₁, hr₁, rfl⟩ ⟨r₂, hr₂, rfl⟩
    refine ⟨r₁ + r₂, fun x hx => ?_, by funext i; simp⟩
    rw [zpair_add_left]
    exact add_mem (hr₁ x hx) (hr₂ x hx)
  neg_mem' := by
    rintro a ⟨r, hr, rfl⟩
    refine ⟨-r, fun x hx => ?_, by funext i; simp⟩
    rw [zpair_neg_left]
    exact neg_mem (hr x hx)

/-- **Dual evaluation subgroups of every arity are preserved by every
lattice identification** — the transport half of the F2′ triple
profile, formal. -/
theorem dualEvalSubgroup_of_identifies {D : Type u} [CommRing D]
    {D' : Type v} [CommRing D']
    [Fintype (IntPoint D)] [Fintype (IntPoint D')]
    {e : IntPoint D' ≃ IntPoint D} (he : IdentifiesLattices e)
    (s : ι' → IntPoint D') :
    dualEvalSubgroup D (⇑e ∘ s) = dualEvalSubgroup D' s := by
  ext q
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r ∘ ⇑e, comp_mem_dualLat_of_identifies he hr, rfl⟩
  · rintro ⟨r', hr', rfl⟩
    refine ⟨r' ∘ ⇑e.symm, comp_mem_dualLat_of_identifies he.symm hr', ?_⟩
    funext i
    simp

end Eval

section ClassConstant

variable {G : Type u} [Group G]

/-- **Burnside generators are class-constant**: the ghost vector of
`η b` takes equal values at points with equal Burnside shadow. -/
theorem ghost_eta_constantOnClasses (b : BurnsideRing G)
    {φ ψ : IntPoint (DRing G)}
    (h : burnsideShadow φ = burnsideShadow ψ) :
    ghost (DRing G) (eta b) φ = ghost (DRing G) (eta b) ψ :=
  burnsideShadow_eq_iff.mp h b

/-- **The TCR compensation mechanism, abstractly**: precomposition with
any class-preserving point map fixes every Burnside-generator ghost
vector.  Within-fibre (and fibre-true) compensations therefore act
trivially on the fibre-constant witnesses of Theorems TCR/TCR-0, and
only crossing terms survive in the pairing — to be killed by
`not_mem_latticePermGroup_of_witness` with class-specific
arithmetic. -/
theorem ghost_eta_comp_eq (b : BurnsideRing G)
    {σ : IntPoint (DRing G) → IntPoint (DRing G)}
    (hσ : ∀ φ, burnsideShadow (σ φ) = burnsideShadow φ) :
    ghost (DRing G) (eta b) ∘ σ = ghost (DRing G) (eta b) := by
  funext φ
  exact ghost_eta_constantOnClasses b (hσ φ)

end ClassConstant

end Even

end LeanDring
