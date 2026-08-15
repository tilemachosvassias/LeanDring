/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Even.Transport
import LeanDring.Theory.DRing.DtoB

/-!
# The assembly: point-level slice recognition implies `B(G) ≅ B(H)`

**EVEN-ORDER LAYER.** No `sorry`, three standard axioms.

This file closes the gap between the point/lattice layer
(`Linkage`/`CriterionT`/`GaugeGroup`/`Transport`) and the Burnside-ring
target: it proves that the An5″/TIR orbit question is **sufficient** for
`D ⇒ B`, not merely upstream of it.

* `fixedSubring T` — the `T`-symmetric slice of the ghost lattice as a
  `Subring` (the intersection of `(ghost D).range` with the equalizer of
  precomposition-by-`T⁎` and the identity).  `ghost_comp_pointPush`
  shows `T` descends to the ghost range with exactly this fixed subring;
  for `D = D(G)`, `T = ψ²`, `G` a 2-group, FIX-ψ² + mark injectivity
  identify it with `B(G)` (see `MarksOntoSlice` below).

* `fixedSubringEquivOfIdentifies` — **the abstract assembly**: a lattice
  identification whose transport respects the symmetry condition
  restricts to a ring isomorphism of the fixed subrings.

* `identifiesLattices_trans` — composing a lattice identification with a
  gauge `σ ∈ Γ` yields another; so the recognition hypothesis below only
  needs to hold *after some gauge* — the orbit form.

* `burnsideNonempty_of_sliceRecognition` — **the payoff**: given the
  per-ring identifications `B ≅ fixedSubring ψ²` (the `MarksOntoSlice`
  hypotheses) and a `D`-ring isomorphism whose induced point bijection
  respects the ψ²-symmetric slice, `B(G) ≅ B(H)`.  Together with
  `identifiesLattices_trans` this makes the `Γ`-orbit question of
  `Transport.lean` provably sufficient for the 2-group `D ⇒ B` target.

## The `MarksOntoSlice` hypotheses

`Nonempty (BurnsideRing G ≃+* fixedSubring ψ²)` is *not* an unknown: it
is the gluing of two banked ring-level facts — FIX-ψ²
(`DRing.range_eta_eq_fix_psi_two`, proven in `LeanDring/Theory/DRing/Adams.lean`)
and injectivity of marks on `B(G)` (`LeanDring/Theory/DRing/MarkInjectivity.lean`),
plus the corestriction of integer-valued mark species to `ℤ`-points.
For `D(G)` of a finite 2-group it is discharged in
`LeanDring/Even/MarksSlice.lean` (`marksOntoSlice_of_isPGroup`), where the
mark species are produced as genuine `IntPoint`s; it is kept as a
hypothesis here so the assembly stays abstract and sorry-free.
-/

namespace LeanDring

namespace Even

section FixedSubring

variable {D : Type*} [CommRing D]

/-- `T` descends to the ghost range: the ghost vector of `T x` is the
pushforward-reindexing of the ghost vector of `x`. -/
theorem ghost_comp_pointPush (T : D →+* D) (x : D) :
    ghost D x ∘ pointPush T = ghost D (T x) := by
  funext φ
  rfl

/-- Precomposition with a map of index sets, as a ring homomorphism of
integer coordinate spaces. -/
def precompHom {α β : Type*} (g : β → α) : (α → ℤ) →+* (β → ℤ) :=
  RingHom.pi fun b => Pi.evalRingHom (fun _ => ℤ) (g b)

@[simp] theorem precompHom_apply {α β : Type*} (g : β → α) (v : α → ℤ) :
    precompHom g v = v ∘ g := rfl

/-- The **fixed subring of the ghost lattice**: ghost vectors symmetric
under the `T`-pushforward.  For `D = D(G)`, `T = ψ²`, `G` a 2-group this
is the coordinate-level home of `B(G)` (FIX-ψ² + mark injectivity). -/
def fixedSubring (T : D →+* D) : Subring (IntPoint D → ℤ) :=
  (ghost D).range ⊓ RingHom.eqLocus (precompHom (pointPush T)) (RingHom.id _)

theorem mem_fixedSubring {T : D →+* D} {v : IntPoint D → ℤ} :
    v ∈ fixedSubring T ↔ v ∈ (ghost D).range ∧ v ∘ pointPush T = v :=
  Subring.mem_inf

/-- Elements fixed by `T` land in the fixed subring. -/
theorem ghost_mem_fixedSubring {T : D →+* D} {x : D} (hx : T x = x) :
    ghost D x ∈ fixedSubring T :=
  mem_fixedSubring.mpr
    ⟨⟨x, rfl⟩, by rw [ghost_comp_pointPush, hx]⟩

end FixedSubring

section Assembly

variable {D : Type*} [CommRing D] {D' : Type*} [CommRing D']

/-- Bridge between the additive and ring-theoretic ghost lattices. -/
theorem mem_ghostLattice_iff_mem_range {v : IntPoint D → ℤ} :
    v ∈ ghostLattice D ↔ v ∈ (ghost D).range := by
  simp [ghostLattice]

/-- Composing a lattice identification with a gauge yields a lattice
identification: the recognition hypotheses below therefore only ever
need to hold after some `σ ∈ Γ` — the orbit form. -/
theorem identifiesLattices_trans [Fintype (IntPoint D)]
    {e : IntPoint D' ≃ IntPoint D} (he : IdentifiesLattices e)
    {σ : Equiv.Perm (IntPoint D)}
    (hσ : σ ∈ latticePermGroup (ghostLattice D)) :
    IdentifiesLattices (e.trans σ) := by
  intro v
  have h1 : v ∘ ⇑(e.trans σ) = (v ∘ ⇑σ) ∘ ⇑e := by
    funext p
    simp
  rw [h1]
  constructor
  · intro h
    have h2 := (he _).mp h
    have h3 := mem_latticePermGroup.mp (inv_mem hσ) _ h2
    have h4 : (v ∘ ⇑σ) ∘ ⇑(σ⁻¹ : Equiv.Perm (IntPoint D)) = v := by
      funext p
      simp
    rwa [h4] at h3
  · intro h
    exact (he _).mpr (mem_latticePermGroup.mp hσ v h)

/-- **The abstract assembly**: a lattice identification that respects the
symmetry condition restricts to a ring isomorphism of the fixed
subrings.  The hypothesis `hslice` is the point-level recognition — for
`D(G)`-rings it says the species matching sends ψ²-symmetric lattice
vectors to ψ²-symmetric lattice vectors and conversely. -/
def fixedSubringEquivOfIdentifies (e : IntPoint D' ≃ IntPoint D)
    (he : IdentifiesLattices e) (T : D →+* D) (T' : D' →+* D')
    (hslice : ∀ v : IntPoint D → ℤ, v ∈ (ghost D).range →
      (v ∘ pointPush T = v ↔ (v ∘ ⇑e) ∘ pointPush T' = v ∘ ⇑e)) :
    fixedSubring T ≃+* fixedSubring T' where
  toFun v := ⟨v.1 ∘ ⇑e, by
    obtain ⟨hv1, hv2⟩ := mem_fixedSubring.mp v.2
    refine mem_fixedSubring.mpr ⟨?_, (hslice v.1 hv1).mp hv2⟩
    exact mem_ghostLattice_iff_mem_range.mp
      ((he v.1).mpr (mem_ghostLattice_iff_mem_range.mpr hv1))⟩
  invFun w := ⟨w.1 ∘ ⇑e.symm, by
    obtain ⟨hw1, hw2⟩ := mem_fixedSubring.mp w.2
    have hcomp : (w.1 ∘ ⇑e.symm) ∘ ⇑e = w.1 := by
      funext p
      simp
    have hmem : w.1 ∘ ⇑e.symm ∈ (ghost D).range := by
      refine mem_ghostLattice_iff_mem_range.mp ((he _).mp ?_)
      rw [hcomp]
      exact mem_ghostLattice_iff_mem_range.mpr hw1
    refine mem_fixedSubring.mpr ⟨hmem, (hslice _ hmem).mpr ?_⟩
    rw [hcomp]
    exact hw2⟩
  left_inv v := by
    ext p
    simp
  right_inv w := by
    ext p
    simp
  map_add' v w := by
    ext p
    simp [Subring.coe_add]
  map_mul' v w := by
    ext p
    simp [Subring.coe_mul]

end Assembly

section DRingPayoff

open MonRing

universe u v

/-- The per-ring identification of `B(G)` with the ψ²-fixed slice of the
ghost lattice — FIX-ψ² + mark injectivity, glued (see the module
docstring). -/
def MarksOntoSlice (G : Type u) [Group G] : Prop :=
  Nonempty (BurnsideRing G ≃+*
    fixedSubring (MonRing.psi 2 : DRing G →+* DRing G))

/-- **The payoff — point-level slice recognition implies `D ⇒ B`**: given
the per-ring marks-onto-slice identifications, any `D`-ring isomorphism
whose induced point bijection respects the ψ²-symmetric slice yields
`B(G) ≅ B(H)`.  By `identifiesLattices_trans`, the slice hypothesis may
be arranged after any gauge `σ ∈ Γ` — so the `Γ`-orbit question (An5″ /
TIR) is *sufficient* for the 2-group `D ⇒ B` target, formally. -/
theorem burnsideNonempty_of_sliceRecognition {G : Type u} {H : Type v}
    [Group G] [Group H]
    (hBG : MarksOntoSlice G) (hBH : MarksOntoSlice H)
    (Φ : DRing G ≃+* DRing H)
    (hslice : ∀ v : IntPoint (DRing G) → ℤ, v ∈ (ghost (DRing G)).range →
      (v ∘ pointPush (MonRing.psi 2) = v ↔
        (v ∘ ⇑(intPointEquiv Φ)) ∘ pointPush (MonRing.psi 2) =
          v ∘ ⇑(intPointEquiv Φ))) :
    Nonempty (BurnsideRing G ≃+* BurnsideRing H) := by
  obtain ⟨eG⟩ := hBG
  obtain ⟨eH⟩ := hBH
  exact ⟨(eG.trans (fixedSubringEquivOfIdentifies (intPointEquiv Φ)
    (identifiesLattices_intPointEquiv Φ) _ _ hslice)).trans eH.symm⟩

end DRingPayoff

end Even

end LeanDring
