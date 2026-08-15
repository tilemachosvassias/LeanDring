/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P4.SweepComplete

/-!
# The conditional order-`p⁴` capstone

`P4SweepComplete` proves all `105 = C(15,2)` pairwise separations
`IsEmpty (SpeciesTableIso Xᵢ Xⱼ)` of the fifteen order-`p⁴` models.  This file
turns that into a *conditional* classification statement:

> **Assuming** every group of order `p⁴` is `MulEquiv` to one of the fifteen
> models (`P4Classification`, a `[FOLKLORE-CHECK]`-grade hypothesis — Burnside's
> classification of groups of order `p⁴`, cf. [GJG10], arXiv:1611.00461), the
> species table separates **all** groups of order `p⁴`: two such groups with a
> species-table isomorphism are already `MulEquiv`.

`P4Classification` is **not** proven here; it is stated cleanly and marked as an
assumed input.  The capstone `p4_species_classifies` is *conditional* on it.

The mathematically substantive part of this file is the **transport of a
`SpeciesTableIso` along group isomorphisms** (`SpeciesTableIso.ofMulEquiv`,
`SpeciesTableIso.trans`, `SpeciesTableIso.congr`): a genuine functoriality
statement — isomorphic groups have isomorphic species tables — proved from
scratch via the pushforward of monomial `G`-sets along a `MulEquiv`.
-/

namespace LeanDring

open MulAction Finset

universe u

namespace DRing

open MonGSet MonRing

variable {G : Type u} [Group G] [Fintype G] {G' : Type u} [Group G'] [Fintype G']

/-! ## The character carried across `e` -/

/-- The character `λ : K →* ℂˣ` transported to `K.map e`, via the isomorphism
`(K.map e) ≃* K`. -/
noncomputable def charMap (e : G ≃* G') (K : Subgroup G) (l : K →* ℂˣ) :
    K.map (e : G →* G') →* ℂˣ :=
  l.comp (e.subgroupMap K).symm.toMonoidHom

omit [Fintype G] [Fintype G'] in
theorem charMap_apply (e : G ≃* G') (K : Subgroup G) (l : K →* ℂˣ)
    (y' : G') (hy' : y' ∈ K.map (e : G →* G')) :
    charMap e K l ⟨y', hy'⟩ = l ⟨e.symm y', by
      have := (Subgroup.mem_map_equiv (f := e)).1 hy'; simpa using this⟩ := by
  simp only [charMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.subgroupMap_symm_apply]

omit [Fintype G] in
/-- `ℂˣ` is abelian, so a character `λ : K →* ℂˣ` is invariant under conjugation
inside `K`. -/
private theorem l_conj {K : Subgroup G} (l : K →* ℂˣ) (a k : K) :
    l (k⁻¹ * a * k) = l a := by
  rw [map_mul, map_mul, map_inv, mul_assoc, mul_comm (l a) (l k), ← mul_assoc,
    inv_mul_cancel, one_mul]

/-! ## Species are natural under a group isomorphism -/

/-- **Naturality of species.**  A group isomorphism `e : G ≃* G'` carries the
basis element `[K, λ]` to `[K.map e, charMap e K λ]` compatibly with species:
`φ_{H.map e, e h}[K.map e, charMap] = φ_{H,h}[K, λ]`.

Proved directly from Müller's species formula (`species_basisElt`) and the coset
bijection `β : G ⧸ K ≃ G' ⧸ (K.map e)` through `e`, using that `ℂˣ` is abelian
(so `λ` is conjugation-invariant on `K`). -/
theorem species_natural (e : G ≃* G') (K : Subgroup G) (l : K →* ℂˣ)
    (H : Subgroup G) (h : H) :
    species (H.map (e : G →* G')) (e.subgroupMap H h)
        (basisElt (K.map (e : G →* G')) (charMap e K l))
      = species H h (basisElt K l) := by
  have hrel : ∀ a b : G, (QuotientGroup.leftRel K) a b ↔
      (QuotientGroup.leftRel (K.map (e : G →* G'))) (e a) (e b) := by
    intro a b
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, ← map_inv, ← map_mul]
    exact (Subgroup.mem_map_iff_mem e.injective).symm
  let β : (G ⧸ K) ≃ (G' ⧸ K.map (e : G →* G')) := Quotient.congr e.toEquiv hrel
  have hβmk : ∀ a : G, β ⟦a⟧ = ⟦e a⟧ := fun a => rfl
  have he : ∀ (g' : G') (q : G ⧸ K), β ((e.symm g' : G) • q) = g' • β q := by
    intro g' q
    induction q using QuotientGroup.induction_on with
    | _ a =>
      simp only [Quotient.smul_mk, hβmk, smul_eq_mul, map_mul, MulEquiv.apply_symm_apply]
  -- the coset bijection restricts to the `H`-fixed points
  have hfix_fwd : ∀ (q : fixedPoints H (induced K l).carrier)
      (s : H.map (e : G →* G')), (s : G') • β q.1 = β q.1 := by
    intro q s
    obtain ⟨t, ht, hEt⟩ := Subgroup.mem_map.1 s.2
    have hEt' : (e (t : G) : G') = (s : G') := hEt
    rw [← hEt', ← he, MulEquiv.symm_apply_apply]
    exact congrArg β (q.2 ⟨t, ht⟩)
  have hfix_bwd : ∀ (q' : fixedPoints (H.map (e : G →* G')) (induced (K.map (e : G →* G'))
      (charMap e K l)).carrier) (t : H), (t : G) • β.symm q'.1 = β.symm q'.1 := by
    intro q' t
    apply β.injective
    rw [Equiv.apply_symm_apply, ← MulEquiv.symm_apply_apply e (t : G), he,
      Equiv.apply_symm_apply]
    have hmem : (e (t : G)) ∈ H.map (e : G →* G') := Subgroup.mem_map.2 ⟨t, t.2, rfl⟩
    exact q'.2 ⟨e (t : G), hmem⟩
  let Efp : fixedPoints H (induced K l).carrier
      ≃ fixedPoints (H.map (e : G →* G')) (induced (K.map (e : G →* G'))
        (charMap e K l)).carrier :=
    { toFun := fun q => ⟨β q.1, fun s => by
        change (s : G') • β q.1 = β q.1; exact hfix_fwd q s⟩
      invFun := fun q' => ⟨β.symm q'.1, fun t => by
        change (t : G) • β.symm q'.1 = β.symm q'.1; exact hfix_bwd q' t⟩
      left_inv := fun q => Subtype.ext (β.symm_apply_apply q.1)
      right_inv := fun q' => Subtype.ext (β.apply_symm_apply q'.1) }
  rw [species_basisElt, species_basisElt]
  refine (Fintype.sum_equiv Efp _ _ ?_).symm
  intro q
  refine congrArg (fun u : ℂˣ => (u : ℂ)) ?_
  -- both summands are `λ` of a conjugate of `h`; the reps differ by `k ∈ K`
  have hb : (⟦e.symm ((β q.1).out)⟧ : G ⧸ K) = q.1 := by
    apply β.injective
    rw [hβmk, MulEquiv.apply_symm_apply, Quotient.out_eq]
  have hk : (q.1.out)⁻¹ * e.symm ((β q.1).out) ∈ K :=
    QuotientGroup.eq.mp ((Quotient.out_eq q.1).trans hb.symm)
  have hscp : (q.1.out)⁻¹ * (h : G) * q.1.out ∈ K := sectionConj_mem K H h q.1 (q.2 h)
  rw [charMap_apply, ← l_conj l ⟨(q.1.out)⁻¹ * (h : G) * q.1.out, hscp⟩
      ⟨(q.1.out)⁻¹ * e.symm ((β q.1).out), hk⟩]
  refine congrArg l (Subtype.ext ?_)
  change ((q.1.out)⁻¹ * e.symm ((β q.1).out))⁻¹ * ((q.1.out)⁻¹ * (h : G) * q.1.out)
        * ((q.1.out)⁻¹ * e.symm ((β q.1).out))
      = e.symm ((β q.1).out⁻¹ * (↑(e.subgroupMap H h) : G') * (β q.1).out)
  simp only [map_mul, map_inv, MulEquiv.coe_subgroupMap_apply, MulEquiv.symm_apply_apply]
  group

/-! ## Transport of a `SpeciesTableIso` along group isomorphisms -/

/-- Pushforward of a character pair `(K, λ)` along `e`: `(K.map e, charMap e K λ)`. -/
noncomputable def pairMap (e : G ≃* G') : CharPair G ℂˣ → CharPair G' ℂˣ :=
  fun p => ⟨p.1.map (e : G →* G'), charMap e p.1 p.2⟩

omit [Fintype G] [Fintype G'] in
@[simp] theorem pairMap_fst (e : G ≃* G') (p : CharPair G ℂˣ) :
    (pairMap e p).1 = p.1.map (e : G →* G') := rfl

omit [Fintype G] [Fintype G'] in
/-- Conjugacy of character pairs is preserved by pushforward. -/
theorem pairMap_conj (e : G ≃* G') {p q : CharPair G ℂˣ} (h : p ≈ q) :
    pairMap e p ≈ pairMap e q := by
  obtain ⟨K, l⟩ := p; obtain ⟨K₂, l₂⟩ := q
  obtain ⟨a, hmem, hchar⟩ := h
  refine ⟨e a, fun y => ?_, fun y hy => ?_⟩
  · change y ∈ K.map (e : G →* G') ↔ (e a) * y * (e a)⁻¹ ∈ K₂.map (e : G →* G')
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
      exact Subgroup.mem_map.2 ⟨a * x * a⁻¹, (hmem x).1 hx, by simp [map_mul, map_inv]⟩
    · intro hy
      have h2 : e.symm ((e a) * y * (e a)⁻¹) ∈ K₂ := (Subgroup.mem_map_equiv (f := e)).1 hy
      have h3 : a * e.symm y * a⁻¹ ∈ K₂ := by
        have hrw : e.symm ((e a) * y * (e a)⁻¹) = a * e.symm y * a⁻¹ := by
          simp [map_mul, map_inv]
        rwa [hrw] at h2
      exact Subgroup.mem_map.2 ⟨e.symm y, (hmem _).2 h3, by simp⟩
  · change charMap e K₂ l₂ ⟨(e a) * y * (e a)⁻¹, _⟩ = charMap e K l ⟨y, hy⟩
    rw [charMap_apply, charMap_apply]
    refine Eq.trans (congrArg l₂ (Subtype.ext ?_))
      (hchar (e.symm y) ((Subgroup.mem_map_equiv (f := e)).1 hy))
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]

omit [Fintype G] [Fintype G'] in
/-- The composite subgroup map is the identity: `(K.map e).map e.symm = K`. -/
theorem map_map_symm (e : G ≃* G') (K : Subgroup G) :
    (K.map (e : G →* G')).map (e.symm : G' →* G) = K := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id K using 2
  exact MonoidHom.ext fun x => e.symm_apply_apply x

omit [Fintype G] [Fintype G'] in
/-- The round trip `pairMap e.symm ∘ pairMap e` returns to the original class. -/
theorem pairMap_symm_pairMap (e : G ≃* G') (p : CharPair G ℂˣ) :
    pairMap e.symm (pairMap e p) ≈ p := by
  obtain ⟨K, l⟩ := p
  refine ⟨1, fun k => ?_, fun k hk => ?_⟩
  · simp only [pairMap_fst, map_map_symm, one_mul, inv_one, mul_one]
  · change l ⟨1 * k * 1⁻¹, _⟩
      = charMap e.symm (K.map (e : G →* G')) (charMap e K l) ⟨k, hk⟩
    rw [charMap_apply, charMap_apply]
    refine congrArg l (Subtype.ext ?_)
    simp [MulEquiv.symm_symm]

/-- The bijection of table rows (basis classes) induced by `e`. -/
noncomputable def rowsEquiv (e : G ≃* G') : CharPairClass G ℂˣ ≃ CharPairClass G' ℂˣ where
  toFun := Quotient.map (pairMap e) (fun _ _ h => pairMap_conj e h)
  invFun := Quotient.map (pairMap e.symm) (fun _ _ h => pairMap_conj e.symm h)
  left_inv := by
    refine Quotient.ind fun p => ?_
    exact Quotient.sound (pairMap_symm_pairMap e p)
  right_inv := by
    refine Quotient.ind fun p => ?_
    have h := pairMap_symm_pairMap e.symm p
    rw [MulEquiv.symm_symm] at h
    exact Quotient.sound h

/-- **A group isomorphism `e : G ≃* G'` induces a species-table isomorphism.**
The row bijection is `rowsEquiv e`; the two-sided column correspondences are the
subgroup images under `e`/`e⁻¹`; the equal-entry conditions are `species_natural`. -/
noncomputable def SpeciesTableIso.ofMulEquiv (e : G ≃* G') : SpeciesTableIso G G' where
  rows := rowsEquiv e
  sub H := H.map (e : G →* G')
  el {H} h := e.subgroupMap H h
  sub' H' := H'.map (e.symm : G' →* G)
  el' {H'} h' := e.symm.subgroupMap H' h'
  entry H h c := by
    induction c using Quotient.ind with
    | _ p =>
      obtain ⟨K, l⟩ := p
      rw [show rowsEquiv e ⟦(⟨K, l⟩ : CharPair G ℂˣ)⟧
            = ⟦(⟨K.map (e : G →* G'), charMap e K l⟩ : CharPair G' ℂˣ)⟧ from rfl,
        classElt_mk, classElt_mk]
      exact species_natural e K l H h
  entry' H' h' c' := by
    induction c' using Quotient.ind with
    | _ p =>
      obtain ⟨K', l'⟩ := p
      rw [show (rowsEquiv e).symm ⟦(⟨K', l'⟩ : CharPair G' ℂˣ)⟧
            = ⟦(⟨K'.map (e.symm : G' →* G), charMap e.symm K' l'⟩
                : CharPair G ℂˣ)⟧ from rfl,
        classElt_mk, classElt_mk]
      exact species_natural e.symm K' l' H' h'
  el_one H := map_one (e.subgroupMap H)
  el'_one H' := map_one (e.symm.subgroupMap H')

variable {G'' : Type u} [Group G''] [Fintype G'']

/-- Composition of species-table isomorphisms. -/
def SpeciesTableIso.trans (S : SpeciesTableIso G G') (T : SpeciesTableIso G' G'') :
    SpeciesTableIso G G'' where
  rows := S.rows.trans T.rows
  sub H := T.sub (S.sub H)
  el {H} h := T.el (S.el h)
  sub' H'' := S.sub' (T.sub' H'')
  el' {H''} h'' := S.el' (T.el' h'')
  entry H h c := by
    simp only [Equiv.trans_apply]
    rw [T.entry, S.entry]
  entry' H'' h'' c'' := by
    simp only [Equiv.symm_trans_apply]
    rw [S.entry', T.entry']
  el_one H := by
    rw [S.el_one]; exact T.el_one _
  el'_one H'' := by
    rw [T.el'_one]; exact S.el'_one _

/-- **Transport of a species-table isomorphism along group isomorphisms.**  If
`G ≃* G₁`, `G' ≃* G₁'` and `G`, `G'` are species-table isomorphic, then so are
`G₁`, `G₁'`. -/
noncomputable def SpeciesTableIso.congr {G₁ G₁' : Type u} [Group G₁] [Fintype G₁]
    [Group G₁'] [Fintype G₁'] (eG : G ≃* G₁) (eH : G' ≃* G₁')
    (T : SpeciesTableIso G G') : SpeciesTableIso G₁ G₁' :=
  ((SpeciesTableIso.ofMulEquiv eG).symm.trans T).trans (SpeciesTableIso.ofMulEquiv eH)

end DRing

namespace P4

open DRing

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

/-- Species-table distinctness is symmetric (transport a would-be iso by `.symm`). -/
theorem isEmpty_symm {A B : Type u} [Group A] [Fintype A] [Group B] [Fintype B]
    (h : IsEmpty (SpeciesTableIso A B)) : IsEmpty (SpeciesTableIso B A) :=
  ⟨fun t => h.false t.symm⟩

/-- **Assumed classification of groups of order `p⁴`** (Burnside; cf. [GJG10],
arXiv:1611.00461).  Every group of order `p⁴` is `MulEquiv` to one of the fifteen
listed models.  This is a `[FOLKLORE-CHECK]`-grade input: it is **not proven
here**, and the capstone `p4_species_classifies` is *conditional* on it. -/
def P4Classification (p : ℕ) [Fact p.Prime] [Fact (Odd p)] (d : ZMod p) : Prop :=
  ∀ (X : Type) [Group X] [Fintype X], Nat.card X = p ^ 4 →
    (Nonempty (X ≃* A4 p) ∨
      Nonempty (X ≃* A31 p) ∨
      Nonempty (X ≃* A22 p) ∨
      Nonempty (X ≃* A211 p) ∨
      Nonempty (X ≃* A1111 p) ∨
      Nonempty (X ≃* M6 p) ∨
      Nonempty (X ≃* M8 p) ∨
      Nonempty (X ≃* G9 p) ∨
      Nonempty (X ≃* CH7 p) ∨
      Nonempty (X ≃* Gid3 p) ∨
      Nonempty (X ≃* G14 p) ∨
      Nonempty (X ≃* Gid8 p) ∨
      Nonempty (X ≃* MaxClass p) ∨
      Nonempty (X ≃* Model p 1) ∨
      Nonempty (X ≃* Model p d))

set_option maxHeartbeats 2000000 in
-- the 105-way conjunction of separations makes this a very large term
/-- **Conditional order-`p⁴` capstone.**  Assuming the classification
`P4Classification p d` (and the sweep hypotheses `5 ≤ p`, `d ≠ 0`, `d` a
quadratic non-residue), the species table separates **all** groups of order
`p⁴`: two order-`p⁴` groups with a species-table isomorphism are `MulEquiv`. -/
theorem p4_species_classifies (hp5 : 5 ≤ p) {d : ZMod p} (hd : d ≠ 0)
    (hd_qnr : quadraticChar (ZMod p) d = -1) (hclass : P4Classification p d)
    {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H]
    (hG : Nat.card G = p ^ 4) (hH : Nat.card H = p ^ 4)
    (hiso : Nonempty (SpeciesTableIso G H)) : Nonempty (G ≃* H) := by
  obtain ⟨T⟩ := hiso
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
      h30, h31, h32, h33, h34, h35, h36, h37, h38, h39,
      h40, h41, h42, h43, h44, h45, h46, h47, h48, h49,
      h50, h51, h52, h53, h54, h55, h56, h57, h58, h59,
      h60, h61, h62, h63, h64, h65, h66, h67, h68, h69,
      h70, h71, h72, h73, h74, h75, h76, h77, h78, h79,
      h80, h81, h82, h83, h84, h85, h86, h87, h88, h89,
      h90, h91, h92, h93, h94, h95, h96, h97, h98, h99,
      h100, h101, h102, h103, h104⟩ :=
    p4_pairwise_species_distinct hp5 hd hd_qnr
  rcases hclass G hG with hg|hg|hg|hg|hg|hg|hg|hg|hg|hg|hg|hg|hg|hg|hg
  · rcases hclass H hH with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh <;>
      first
      | exact ⟨hg.some.trans hh.some.symm⟩
      | (have stiso := SpeciesTableIso.congr hg.some hh.some T
         first
         | exact (h0.false stiso).elim
         | exact (h1.false stiso).elim
         | exact (h2.false stiso).elim
         | exact (h3.false stiso).elim
         | exact (h4.false stiso).elim
         | exact (h5.false stiso).elim
         | exact (h6.false stiso).elim
         | exact (h7.false stiso).elim
         | exact (h8.false stiso).elim
         | exact (h9.false stiso).elim
         | exact (h10.false stiso).elim
         | exact (h11.false stiso).elim
         | exact (h12.false stiso).elim
         | exact (h13.false stiso).elim)
  · rcases hclass H hH with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh <;>
      first
      | exact ⟨hg.some.trans hh.some.symm⟩
      | (have stiso := SpeciesTableIso.congr hg.some hh.some T
         first
         | exact ((isEmpty_symm h0).false stiso).elim
         | exact (h14.false stiso).elim
         | exact (h15.false stiso).elim
         | exact (h16.false stiso).elim
         | exact (h17.false stiso).elim
         | exact (h18.false stiso).elim
         | exact (h19.false stiso).elim
         | exact (h20.false stiso).elim
         | exact (h21.false stiso).elim
         | exact (h22.false stiso).elim
         | exact (h23.false stiso).elim
         | exact (h24.false stiso).elim
         | exact (h25.false stiso).elim
         | exact (h26.false stiso).elim)
  · rcases hclass H hH with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh <;>
      first
      | exact ⟨hg.some.trans hh.some.symm⟩
      | (have stiso := SpeciesTableIso.congr hg.some hh.some T
         first
         | exact ((isEmpty_symm h1).false stiso).elim
         | exact ((isEmpty_symm h14).false stiso).elim
         | exact (h27.false stiso).elim
         | exact (h28.false stiso).elim
         | exact (h29.false stiso).elim
         | exact (h30.false stiso).elim
         | exact (h31.false stiso).elim
         | exact (h32.false stiso).elim
         | exact (h33.false stiso).elim
         | exact (h34.false stiso).elim
         | exact (h35.false stiso).elim
         | exact (h36.false stiso).elim
         | exact (h37.false stiso).elim
         | exact (h38.false stiso).elim)
  · rcases hclass H hH with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh <;>
      first
      | exact ⟨hg.some.trans hh.some.symm⟩
      | (have stiso := SpeciesTableIso.congr hg.some hh.some T
         first
         | exact ((isEmpty_symm h2).false stiso).elim
         | exact ((isEmpty_symm h15).false stiso).elim
         | exact ((isEmpty_symm h27).false stiso).elim
         | exact (h39.false stiso).elim
         | exact (h40.false stiso).elim
         | exact (h41.false stiso).elim
         | exact (h42.false stiso).elim
         | exact (h43.false stiso).elim
         | exact (h44.false stiso).elim
         | exact (h45.false stiso).elim
         | exact (h46.false stiso).elim
         | exact (h47.false stiso).elim
         | exact (h48.false stiso).elim
         | exact (h49.false stiso).elim)
  · rcases hclass H hH with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh <;>
      first
      | exact ⟨hg.some.trans hh.some.symm⟩
      | (have stiso := SpeciesTableIso.congr hg.some hh.some T
         first
         | exact ((isEmpty_symm h3).false stiso).elim
         | exact ((isEmpty_symm h16).false stiso).elim
         | exact ((isEmpty_symm h28).false stiso).elim
         | exact ((isEmpty_symm h39).false stiso).elim
         | exact (h50.false stiso).elim
         | exact (h51.false stiso).elim
         | exact (h52.false stiso).elim
         | exact (h53.false stiso).elim
         | exact (h54.false stiso).elim
         | exact (h55.false stiso).elim
         | exact (h56.false stiso).elim
         | exact (h57.false stiso).elim
         | exact (h58.false stiso).elim
         | exact (h59.false stiso).elim)
  · rcases hclass H hH with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh <;>
      first
      | exact ⟨hg.some.trans hh.some.symm⟩
      | (have stiso := SpeciesTableIso.congr hg.some hh.some T
         first
         | exact ((isEmpty_symm h4).false stiso).elim
         | exact ((isEmpty_symm h17).false stiso).elim
         | exact ((isEmpty_symm h29).false stiso).elim
         | exact ((isEmpty_symm h40).false stiso).elim
         | exact ((isEmpty_symm h50).false stiso).elim
         | exact (h60.false stiso).elim
         | exact (h61.false stiso).elim
         | exact (h62.false stiso).elim
         | exact (h63.false stiso).elim
         | exact (h64.false stiso).elim
         | exact (h65.false stiso).elim
         | exact (h66.false stiso).elim
         | exact (h67.false stiso).elim
         | exact (h68.false stiso).elim)
  · rcases hclass H hH with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh <;>
      first
      | exact ⟨hg.some.trans hh.some.symm⟩
      | (have stiso := SpeciesTableIso.congr hg.some hh.some T
         first
         | exact ((isEmpty_symm h5).false stiso).elim
         | exact ((isEmpty_symm h18).false stiso).elim
         | exact ((isEmpty_symm h30).false stiso).elim
         | exact ((isEmpty_symm h41).false stiso).elim
         | exact ((isEmpty_symm h51).false stiso).elim
         | exact ((isEmpty_symm h60).false stiso).elim
         | exact (h69.false stiso).elim
         | exact (h70.false stiso).elim
         | exact (h71.false stiso).elim
         | exact (h72.false stiso).elim
         | exact (h73.false stiso).elim
         | exact (h74.false stiso).elim
         | exact (h75.false stiso).elim
         | exact (h76.false stiso).elim)
  · rcases hclass H hH with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh <;>
      first
      | exact ⟨hg.some.trans hh.some.symm⟩
      | (have stiso := SpeciesTableIso.congr hg.some hh.some T
         first
         | exact ((isEmpty_symm h6).false stiso).elim
         | exact ((isEmpty_symm h19).false stiso).elim
         | exact ((isEmpty_symm h31).false stiso).elim
         | exact ((isEmpty_symm h42).false stiso).elim
         | exact ((isEmpty_symm h52).false stiso).elim
         | exact ((isEmpty_symm h61).false stiso).elim
         | exact ((isEmpty_symm h69).false stiso).elim
         | exact (h77.false stiso).elim
         | exact (h78.false stiso).elim
         | exact (h79.false stiso).elim
         | exact (h80.false stiso).elim
         | exact (h81.false stiso).elim
         | exact (h82.false stiso).elim
         | exact (h83.false stiso).elim)
  · rcases hclass H hH with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh <;>
      first
      | exact ⟨hg.some.trans hh.some.symm⟩
      | (have stiso := SpeciesTableIso.congr hg.some hh.some T
         first
         | exact ((isEmpty_symm h7).false stiso).elim
         | exact ((isEmpty_symm h20).false stiso).elim
         | exact ((isEmpty_symm h32).false stiso).elim
         | exact ((isEmpty_symm h43).false stiso).elim
         | exact ((isEmpty_symm h53).false stiso).elim
         | exact ((isEmpty_symm h62).false stiso).elim
         | exact ((isEmpty_symm h70).false stiso).elim
         | exact ((isEmpty_symm h77).false stiso).elim
         | exact (h84.false stiso).elim
         | exact (h85.false stiso).elim
         | exact (h86.false stiso).elim
         | exact (h87.false stiso).elim
         | exact (h88.false stiso).elim
         | exact (h89.false stiso).elim)
  · rcases hclass H hH with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh <;>
      first
      | exact ⟨hg.some.trans hh.some.symm⟩
      | (have stiso := SpeciesTableIso.congr hg.some hh.some T
         first
         | exact ((isEmpty_symm h8).false stiso).elim
         | exact ((isEmpty_symm h21).false stiso).elim
         | exact ((isEmpty_symm h33).false stiso).elim
         | exact ((isEmpty_symm h44).false stiso).elim
         | exact ((isEmpty_symm h54).false stiso).elim
         | exact ((isEmpty_symm h63).false stiso).elim
         | exact ((isEmpty_symm h71).false stiso).elim
         | exact ((isEmpty_symm h78).false stiso).elim
         | exact ((isEmpty_symm h84).false stiso).elim
         | exact (h90.false stiso).elim
         | exact (h91.false stiso).elim
         | exact (h92.false stiso).elim
         | exact (h93.false stiso).elim
         | exact (h94.false stiso).elim)
  · rcases hclass H hH with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh <;>
      first
      | exact ⟨hg.some.trans hh.some.symm⟩
      | (have stiso := SpeciesTableIso.congr hg.some hh.some T
         first
         | exact ((isEmpty_symm h9).false stiso).elim
         | exact ((isEmpty_symm h22).false stiso).elim
         | exact ((isEmpty_symm h34).false stiso).elim
         | exact ((isEmpty_symm h45).false stiso).elim
         | exact ((isEmpty_symm h55).false stiso).elim
         | exact ((isEmpty_symm h64).false stiso).elim
         | exact ((isEmpty_symm h72).false stiso).elim
         | exact ((isEmpty_symm h79).false stiso).elim
         | exact ((isEmpty_symm h85).false stiso).elim
         | exact ((isEmpty_symm h90).false stiso).elim
         | exact (h95.false stiso).elim
         | exact (h96.false stiso).elim
         | exact (h97.false stiso).elim
         | exact (h98.false stiso).elim)
  · rcases hclass H hH with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh <;>
      first
      | exact ⟨hg.some.trans hh.some.symm⟩
      | (have stiso := SpeciesTableIso.congr hg.some hh.some T
         first
         | exact ((isEmpty_symm h10).false stiso).elim
         | exact ((isEmpty_symm h23).false stiso).elim
         | exact ((isEmpty_symm h35).false stiso).elim
         | exact ((isEmpty_symm h46).false stiso).elim
         | exact ((isEmpty_symm h56).false stiso).elim
         | exact ((isEmpty_symm h65).false stiso).elim
         | exact ((isEmpty_symm h73).false stiso).elim
         | exact ((isEmpty_symm h80).false stiso).elim
         | exact ((isEmpty_symm h86).false stiso).elim
         | exact ((isEmpty_symm h91).false stiso).elim
         | exact ((isEmpty_symm h95).false stiso).elim
         | exact (h99.false stiso).elim
         | exact (h100.false stiso).elim
         | exact (h101.false stiso).elim)
  · rcases hclass H hH with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh <;>
      first
      | exact ⟨hg.some.trans hh.some.symm⟩
      | (have stiso := SpeciesTableIso.congr hg.some hh.some T
         first
         | exact ((isEmpty_symm h11).false stiso).elim
         | exact ((isEmpty_symm h24).false stiso).elim
         | exact ((isEmpty_symm h36).false stiso).elim
         | exact ((isEmpty_symm h47).false stiso).elim
         | exact ((isEmpty_symm h57).false stiso).elim
         | exact ((isEmpty_symm h66).false stiso).elim
         | exact ((isEmpty_symm h74).false stiso).elim
         | exact ((isEmpty_symm h81).false stiso).elim
         | exact ((isEmpty_symm h87).false stiso).elim
         | exact ((isEmpty_symm h92).false stiso).elim
         | exact ((isEmpty_symm h96).false stiso).elim
         | exact ((isEmpty_symm h99).false stiso).elim
         | exact (h102.false stiso).elim
         | exact (h103.false stiso).elim)
  · rcases hclass H hH with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh <;>
      first
      | exact ⟨hg.some.trans hh.some.symm⟩
      | (have stiso := SpeciesTableIso.congr hg.some hh.some T
         first
         | exact ((isEmpty_symm h12).false stiso).elim
         | exact ((isEmpty_symm h25).false stiso).elim
         | exact ((isEmpty_symm h37).false stiso).elim
         | exact ((isEmpty_symm h48).false stiso).elim
         | exact ((isEmpty_symm h58).false stiso).elim
         | exact ((isEmpty_symm h67).false stiso).elim
         | exact ((isEmpty_symm h75).false stiso).elim
         | exact ((isEmpty_symm h82).false stiso).elim
         | exact ((isEmpty_symm h88).false stiso).elim
         | exact ((isEmpty_symm h93).false stiso).elim
         | exact ((isEmpty_symm h97).false stiso).elim
         | exact ((isEmpty_symm h100).false stiso).elim
         | exact ((isEmpty_symm h102).false stiso).elim
         | exact (h104.false stiso).elim)
  · rcases hclass H hH with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh <;>
      first
      | exact ⟨hg.some.trans hh.some.symm⟩
      | (have stiso := SpeciesTableIso.congr hg.some hh.some T
         first
         | exact ((isEmpty_symm h13).false stiso).elim
         | exact ((isEmpty_symm h26).false stiso).elim
         | exact ((isEmpty_symm h38).false stiso).elim
         | exact ((isEmpty_symm h49).false stiso).elim
         | exact ((isEmpty_symm h59).false stiso).elim
         | exact ((isEmpty_symm h68).false stiso).elim
         | exact ((isEmpty_symm h76).false stiso).elim
         | exact ((isEmpty_symm h83).false stiso).elim
         | exact ((isEmpty_symm h89).false stiso).elim
         | exact ((isEmpty_symm h94).false stiso).elim
         | exact ((isEmpty_symm h98).false stiso).elim
         | exact ((isEmpty_symm h101).false stiso).elim
         | exact ((isEmpty_symm h103).false stiso).elim
         | exact ((isEmpty_symm h104).false stiso).elim)

end P4

end LeanDring
