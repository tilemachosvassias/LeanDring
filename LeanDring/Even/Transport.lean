/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Even.GaugeGroup

/-!
# Transport: ring isomorphisms as lattice identifications, the gauge
# torsor, and the exclusion principle

**EVEN-ORDER LAYER.** No `sorry`, three standard axioms.

Three theory pieces that complete the formal frame around the gauge
group `Γ(L)` (`LeanDring.Even.latticePermGroup`):

* **The exclusion principle** (`not_mem_latticePermGroup_of_witness`,
 `not_mem_latticePermGroup_of_dual_witness`): a permutation is thrown
 out of `Γ(L)` by a single witness pair — one lattice vector and one
 dual row whose transported pairing is non-integral. Every hand
 exclusion argument of the anchoring program (W1/W2, R3–R8) is an instance of this
 one statement; the "witness webs" FW1/FW2 are the dual rows `r`.

* **N2, formal** (`comp_intPointEquiv_mem_ghostLattice_iff`,
 `identifiesLattices_intPointEquiv`): the point bijection induced by
 any ring isomorphism *identifies the ghost lattices* — the formal
 version of necessary condition N2 in the counterexample anatomy
 : "any `D`-iso is a
 coordinate pullback along an integral species bijection".

* **The gauge torsor** (`identifies_symm_trans_mem`): any two lattice
 identifications differ by an element of `Γ`. This makes the
 program's ubiquitous "up to gauge" precise: the species matching
 induced by a ring isomorphism is canonical exactly up to
 `latticePermGroup (ghostLattice D)` — in particular the matchings of
 `Φ` and `Φ ∘ α` (`α` a ring automorphism) differ by a gauge, which is
 why every recognition statement must be stated `Γ`-orbit-wise.

* **The slice** (`sliceFix`, `ghost_mem_sliceFix`): where `B` lives in
 the coordinate picture — the `T`-symmetric ghost vectors. For
 `D = D(G)`, `T = ψ²`: elements fixed by `ψ²` have `T`-symmetric ghost
 vectors (the free half of the `D_F`-level FIX-ψ²; the converse *is*
 FIX-ψ², proven at the D-ring level in `LeanDring/Theory/DRing/Adams.lean`, not
 abstractly available).

Together with Theorem P this reduces the still-open content of
`TwoGroupDtoB` to a single formal question about
`Γ(ghostLattice (DRing G))`-orbits of `sliceFix ψ²` — the An5″/TIR
frontier of the hand notes.
-/

namespace LeanDring

namespace Even

section Exclusion

variable {ι : Type*} [Fintype ι]

/-- **The exclusion principle, witness form**: one lattice vector and one
dual row with non-integral transported pairing expel a permutation from
the gauge group.  Every W1/W2/R3–R8 hand argument instantiates this. -/
theorem not_mem_latticePermGroup_of_witness {L : AddSubgroup (ι → ℤ)}
    {σ : Equiv.Perm ι} (r : ι → ℚ) (x : ι → ℤ)
    (hr : r ∈ dualLat L) (hx : x ∈ L)
    (hviol : zpair r (x ∘ σ) ∉ (Int.castRingHom ℚ).range) :
    σ ∉ latticePermGroup L :=
  fun hσ => hviol (hr _ (mem_latticePermGroup.mp hσ x hx))

/-- **The exclusion principle, dual form**: a dual row whose transport
leaves the dual expels the permutation (contrapositive of Theorem P).
The FW1/FW2 witness webs enter as the row `r`. -/
theorem not_mem_latticePermGroup_of_dual_witness {L : AddSubgroup (ι → ℤ)}
    {σ : Equiv.Perm ι} (r : ι → ℚ) (hr : r ∈ dualLat L)
    (hviol : r ∘ ⇑σ.symm ∉ dualLat L) :
    σ ∉ latticePermGroup L :=
  fun hσ => hviol ((mem_latticePermGroup_iff_dual L σ).mp hσ r hr)

end Exclusion

section TransportChain

variable {D : Type*} [CommRing D] {D' : Type*} [CommRing D']

/-- The ghost vector of `x`, reindexed along the induced point bijection,
is the ghost vector of `Φ x`: the square of ghost maps and point
bijections commutes on the nose. -/
theorem ghost_comp_intPointEquiv (Φ : D ≃+* D') (x : D) :
    ghost D x ∘ ⇑(intPointEquiv Φ) = ghost D' (Φ x) := by
  funext φ'
  rfl

theorem comp_intPointEquiv_mem_ghostLattice (Φ : D ≃+* D')
    {v : IntPoint D → ℤ} (hv : v ∈ ghostLattice D) :
    v ∘ ⇑(intPointEquiv Φ) ∈ ghostLattice D' := by
  obtain ⟨a, rfl⟩ := mem_ghostLattice.mp hv
  exact mem_ghostLattice.mpr ⟨Φ a, (ghost_comp_intPointEquiv Φ a).symm⟩

theorem intPointEquiv_symm (Φ : D ≃+* D') :
    (intPointEquiv Φ).symm = intPointEquiv Φ.symm :=
  Equiv.ext fun _ => rfl

/-- **N2, formal**: the point bijection induced by a ring isomorphism
identifies the ghost lattices — membership is preserved in both
directions.  This is the formal "ring iso = integral species bijection"
of the counterexample anatomy. -/
theorem comp_intPointEquiv_mem_ghostLattice_iff (Φ : D ≃+* D')
    (v : IntPoint D → ℤ) :
    v ∘ ⇑(intPointEquiv Φ) ∈ ghostLattice D' ↔ v ∈ ghostLattice D := by
  constructor
  · intro h
    have h2 := comp_intPointEquiv_mem_ghostLattice Φ.symm h
    rw [← intPointEquiv_symm] at h2
    have h3 : (v ∘ ⇑(intPointEquiv Φ)) ∘ ⇑(intPointEquiv Φ).symm = v := by
      funext p
      simp
    rwa [h3] at h2
  · exact comp_intPointEquiv_mem_ghostLattice Φ

/-- A coordinate bijection of integer points **identifying the ghost
lattices** — the abstract notion of an integral species matching. -/
def IdentifiesLattices (e : IntPoint D' ≃ IntPoint D) : Prop :=
  ∀ v : IntPoint D → ℤ, v ∘ ⇑e ∈ ghostLattice D' ↔ v ∈ ghostLattice D

/-- Every ring isomorphism provides a lattice identification. -/
theorem identifiesLattices_intPointEquiv (Φ : D ≃+* D') :
    IdentifiesLattices (intPointEquiv Φ) := fun v =>
  comp_intPointEquiv_mem_ghostLattice_iff Φ v

/-- **The gauge torsor**: any two lattice identifications differ by an
element of the gauge group.  "Up to gauge" is now a theorem: the species
matching of a ring isomorphism is canonical exactly up to
`Γ(ghostLattice D)`, so recognition statements (which species set is the
B-slice) can only ever be posed `Γ`-orbit-wise. -/
theorem identifies_symm_trans_mem [Fintype (IntPoint D)]
    {e e' : IntPoint D' ≃ IntPoint D}
    (he : IdentifiesLattices e) (he' : IdentifiesLattices e') :
    e.symm.trans e' ∈ latticePermGroup (ghostLattice D) := by
  refine mem_latticePermGroup.mpr fun v hv => ?_
  have hw : v ∘ ⇑e' ∈ ghostLattice D' := (he' v).mpr hv
  have h3 : ((v ∘ ⇑e') ∘ ⇑e.symm) ∘ ⇑e = v ∘ ⇑e' := by
    funext p
    simp
  have h4 : (v ∘ ⇑e') ∘ ⇑e.symm ∈ ghostLattice D :=
    (he _).mp (by rw [h3]; exact hw)
  have h5 : v ∘ ⇑(e.symm.trans e') = (v ∘ ⇑e') ∘ ⇑e.symm := by
    funext p
    simp
  rwa [h5]

end TransportChain

section Slice

variable {D : Type*} [CommRing D]

/-- The **`T`-symmetric slice** of the ghost coordinate space: vectors
constant along the pushforward.  For `D = D(G)`, `T = ψ²` this is where
the Burnside subring's ghost image lives. -/
def sliceFix (T : D →+* D) : Set (IntPoint D → ℤ) :=
  {v | v ∘ pointPush T = v}

/-- Elements fixed by `T` have `T`-symmetric ghost vectors — the free
half of the `D_F`-level FIX-ψ².  (The converse, that every symmetric
lattice vector comes from a fixed element, is FIX-ψ² itself: proven for
`D(G)` in `LeanDring/Theory/DRing/Adams.lean`, not abstractly true.) -/
theorem ghost_mem_sliceFix {T : D →+* D} {x : D} (hx : T x = x) :
    ghost D x ∈ sliceFix T := by
  change ghost D x ∘ pointPush T = ghost D x
  funext φ
  change φ (T x) = φ x
  rw [hx]

end Slice

end Even

end LeanDring
