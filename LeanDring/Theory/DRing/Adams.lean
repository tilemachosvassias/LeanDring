/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.SpeciesInjectivity

/-!
# Adams (twist) operations and the ψ-recognition of `B(G)` inside `D(G)`

The `k`-th **Adams/twist operation** on monomial `G`-sets raises all weights
to the `k`-th power: `ψᵏ(X, μ) = (X, μᵏ)`. It is a ring endomorphism of
`B^A(G)` fixing the Burnside copy `η(B(G))` pointwise, and it interacts with
species by `φ_{H,h} ∘ ψᵏ = φ_{H,hᵏ}`.

Main results (all sorry-free, resting on species injectivity,
`DRing.species_injective`):

* `DRing.mem_range_eta_iff_species_const` — **the Burnside copy is exactly
  the species-h-independent part**: `x ∈ η(B(G))` iff every species value
  `φ_{H,h}(x)` is independent of `h`.
* `DRing.range_eta_eq_fix_psi` — **`η(B) = Fix(ψᴺ)`** whenever `gᴺ = 1` for
  all `g : G` (e.g. `N = exp G`): the Burnside copy is the fixed subring of
  the collapsing Adams operation.
* `DRing.range_eta_eq_fix_psi_two` — **the `ψ²` form for 2-groups**: if
  `g^(2^m) = 1` for all `g`, then `η(B) = Fix(ψ²)`, so for 2-groups
  recognizing the Burnside subring is exactly recognizing `ψ²`.

Consequently `D(G) ≅ D(H) ⇒ B(G) ≅ B(H)` reduces, for `2`-groups, to
transporting `ψ²` along the isomorphism. (The analogous reduction for odd
order runs through coprime Adams operations and their Galois-intrinsicness,
Müller's §2.5; it is not formalized here.)
-/

namespace LeanDring

open MulAction

universe u v

variable {G : Type u} [Group G] {A : Type v} [CommGroup A]

namespace MonGSet

/-! ## The twist on monomial `G`-sets -/

/-- The `k`-th Adams/twist operation: raise all weights to the `k`-th power. -/
def twist (k : ℕ) (X : MonGSet G A) : MonGSet G A where
  carrier := X.carrier
  fintype := X.fintype
  action := X.action
  weight g x := (X.weight g x) ^ k
  weight_mul g h x := by rw [X.weight_mul g h x, mul_pow]

theorem twist_congr (k : ℕ) {X Y : MonGSet G A} (h : IsIso X Y) :
    IsIso (X.twist k) (Y.twist k) := by
  obtain ⟨e, φ, he, hw⟩ := h
  refine ⟨e, fun x => (φ x) ^ k, he, fun g x => ?_⟩
  change (Y.weight g (e x)) ^ k * (φ x) ^ k = (φ (g • x)) ^ k * (X.weight g x) ^ k
  rw [← mul_pow, hw g x, mul_pow]
  rfl

/-- Twisting a fixed-point character raises it to the `k`-th power; species
transform by `φ_{H,h}(ψᵏ X) = φ_{H,hᵏ}(X)`. -/
theorem speciesSum_twist {R : Type*} [CommRing R] (χ : A →* R) (H : Subgroup G)
    (h : H) (k : ℕ) (X : MonGSet G A) :
    speciesSum χ H h (X.twist k) = speciesSum χ H (h ^ k) X := by
  refine Fintype.sum_equiv
    ((Equiv.refl (fixedPoints H X.carrier) :
      fixedPoints H (X.twist k).carrier ≃ fixedPoints H X.carrier)) _ _ fun x => ?_
  change χ ((X.weight (h : G) x.1) ^ k) = χ ((X.fixedWeight H x) (h ^ k))
  rw [(X.fixedWeight H x).map_pow h k]
  rfl

end MonGSet

/-! ## The Adams operations on `B^A(G)` -/

namespace MonRing

open MonGSet

/-- The `k`-th Adams operation on the fibered Burnside semiring. -/
def psiHom (k : ℕ) : MonGSet.Skel G A →+* MonGSet.Skel G A where
  toFun := Quotient.map (twist k) fun _ _ h => twist_congr k h
  map_zero' := Quotient.sound <| isIso_of_weight_eq (Equiv.refl _)
    (fun _ z => rfl) (fun _ z => z.elim)
  map_one' := Quotient.sound <| isIso_of_weight_eq (Equiv.refl _)
    (fun _ _ => rfl) (fun g z => (one_pow k).symm)
  map_add' a b := by
    refine Quotient.ind₂ (fun X Y => ?_) a b
    refine Quotient.sound <| isIso_of_weight_eq (Equiv.refl _) (fun _ _ => rfl) ?_
    rintro g (x | y) <;> rfl
  map_mul' a b := by
    refine Quotient.ind₂ (fun X Y => ?_) a b
    refine Quotient.sound <| isIso_of_weight_eq (Equiv.refl _) (fun _ _ => rfl) ?_
    intro g p
    exact (mul_pow _ _ k).symm

/-- The `k`-th **Adams operation** `ψᵏ : B^A(G) →+* B^A(G)`. -/
def psi (k : ℕ) : MonRing G A →+* MonRing G A :=
  GrothendieckRing.map (psiHom k)

/-- `ψᵏ` fixes the Burnside copy pointwise. -/
theorem psiHom_comp_ofFinHom (k : ℕ) :
    (psiHom (G := G) (A := A) k).comp Skel.ofFinHom = Skel.ofFinHom := by
  refine RingHom.ext fun a => ?_
  obtain ⟨X⟩ := a
  exact Quotient.sound <| isIso_of_weight_eq (Equiv.refl _)
    (fun _ _ => rfl) (fun g z => (one_pow k).symm)

@[simp] theorem psi_eta (k : ℕ) (b : BurnsideRing G) :
    psi k (eta (A := A) b) = eta b := by
  rw [psi, eta, GrothendieckRing.map_map, psiHom_comp_ofFinHom]

/-- `ψ¹` is the identity. -/
theorem psiHom_one : psiHom (G := G) (A := A) 1 = RingHom.id _ := by
  refine RingHom.ext fun a => ?_
  obtain ⟨X⟩ := a
  exact Quotient.sound <| isIso_of_weight_eq (Equiv.refl _)
    (fun _ _ => rfl) (fun g z => (pow_one _).symm)

@[simp] theorem psi_one (x : MonRing G A) : psi 1 x = x := by
  obtain ⟨p⟩ := x
  change GrothendieckRing.map (psiHom 1) (GrothendieckRing.mk p.1 p.2) = _
  rw [psiHom_one, GrothendieckRing.map_id]
  rfl

/-- Composition law `ψᵏ ∘ ψˡ = ψˡᵏ`. -/
theorem psiHom_comp (k l : ℕ) :
    (psiHom (G := G) (A := A) k).comp (psiHom l) = psiHom (l * k) := by
  refine RingHom.ext fun a => ?_
  obtain ⟨X⟩ := a
  refine Quotient.sound <| isIso_of_weight_eq (Equiv.refl _) (fun _ _ => rfl) ?_
  intro g z
  exact pow_mul (X.weight g z) l k

@[simp] theorem psi_psi (k l : ℕ) (x : MonRing G A) :
    psi k (psi l x) = psi (l * k) x := by
  rw [psi, psi, GrothendieckRing.map_map, psiHom_comp]
  rfl

end MonRing

/-! ## Species under Adams operations, and the ψ-recognition theorems -/

namespace DRing

open MonGSet MonRing

variable {G : Type u} [Group G]

/-- **The species–Adams relation** (hom level): `φ_{H,h} ∘ ψᵏ = φ_{H,hᵏ}`. -/
theorem species_comp_psi (H : Subgroup G) (h : H) (k : ℕ) :
    (species (G := G) H h).comp (psi k) = species H (h ^ k) := by
  refine GrothendieckRing.hom_ext fun a => ?_
  obtain ⟨X⟩ := a
  have h1 : psi k (GrothendieckRing.of (Skel.mk X)) =
      GrothendieckRing.of (Skel.mk (X.twist k)) :=
    GrothendieckRing.map_of (psiHom k) (Skel.mk X)
  have e1 : species H h (GrothendieckRing.of (Skel.mk (X.twist k))) =
      speciesSum (Units.coeHom ℂ) H h (X.twist k) :=
    GrothendieckRing.lift_of _ _
  have e2 : species H (h ^ k) (GrothendieckRing.of (Skel.mk X)) =
      speciesSum (Units.coeHom ℂ) H (h ^ k) X :=
    GrothendieckRing.lift_of _ _
  change species H h (psi k (GrothendieckRing.of (Skel.mk X))) =
    species H (h ^ k) (GrothendieckRing.of (Skel.mk X))
  rw [h1, e1, e2]
  exact speciesSum_twist _ H h k X

/-- **The species–Adams relation**: `φ_{H,h}(ψᵏ x) = φ_{H,hᵏ}(x)`. -/
theorem species_psi (H : Subgroup G) (h : H) (k : ℕ) (x : DRing G) :
    species H h (psi k x) = species H (h ^ k) x :=
  DFunLike.congr_fun (species_comp_psi H h k) x

/-- The species at `(H, 1)` computes the mark of the underlying `G`-set. -/
theorem speciesSum_one (H : Subgroup G) (X : MonGSet G ℂˣ) :
    speciesSum (Units.coeHom ℂ) H 1 X = (FinGSet.fix H X.toFinGSet : ℂ) := by
  have hcard : FinGSet.fix H X.toFinGSet =
      Fintype.card (fixedPoints H X.carrier) :=
    Nat.card_eq_fintype_card (α := fixedPoints H X.carrier)
  have hone : ∀ x : fixedPoints H X.carrier,
      (Units.coeHom ℂ) ((X.fixedWeight H x) 1) = 1 := fun x => by
    rw [map_one, map_one]
  rw [speciesSum, Finset.sum_congr rfl fun x _ => hone x, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, hcard]

/-- Hom-level: `φ_{H,1} = mark_H ∘ forget`. -/
theorem species_one_eq_mark_forget (H : Subgroup G) :
    (species (G := G) H 1) =
      (Int.castRingHom ℂ).comp ((BurnsideRing.mark H).comp MonRing.forget) := by
  refine GrothendieckRing.hom_ext fun a => ?_
  obtain ⟨X⟩ := a
  change species H 1 (GrothendieckRing.of (Skel.mk X)) = _
  rw [species, MonRing.species, GrothendieckRing.lift_of]
  have hforget : MonRing.forget (GrothendieckRing.of (Skel.mk X)) =
      GrothendieckRing.of (Skel.forgetHom (Skel.mk X)) :=
    GrothendieckRing.map_of _ _
  change (speciesSum (Units.coeHom ℂ) H 1 X : ℂ) =
    (Int.castRingHom ℂ) (BurnsideRing.mark H (MonRing.forget (GrothendieckRing.of (Skel.mk X))))
  rw [hforget, BurnsideRing.mark_of, speciesSum_one]
  rfl

/-- **The Burnside copy is the species-`h`-independent part of `D(G)`**:
`x ∈ η(B(G))` iff every species value is independent of the group element. -/
theorem mem_range_eta_iff_species_const (x : DRing G) :
    x ∈ Set.range (eta : BurnsideRing G →+* DRing G) ↔
      ∀ (H : Subgroup G) (h : H), species H h x = species H 1 x := by
  constructor
  · rintro ⟨b, rfl⟩ H h
    have h1 := DFunLike.congr_fun (species_comp_eta H h) b
    have h2 := DFunLike.congr_fun (species_comp_eta H 1) b
    simp only [RingHom.coe_comp, Function.comp_apply] at h1 h2
    rw [h1, h2]
  · intro hconst
    refine ⟨MonRing.forget x, ?_⟩
    -- `η (forget x)` has the same species table as `x`
    refine (species_injective (funext fun H => funext fun h => ?_)).symm
    change species H h x = species H h (eta (MonRing.forget x))
    have h1 := DFunLike.congr_fun (species_comp_eta H h) (MonRing.forget x)
    simp only [RingHom.coe_comp, Function.comp_apply] at h1
    rw [hconst H h, h1]
    have h2 := DFunLike.congr_fun (species_one_eq_mark_forget H) x
    simp only [RingHom.coe_comp, Function.comp_apply] at h2
    rw [h2]

/-- **`η(B) = Fix(ψᴺ)`** for any exponent `N` annihilating `G`: the Burnside
copy inside `D(G)` is the fixed subring of the collapsing Adams operation. -/
theorem range_eta_eq_fix_psi {N : ℕ} (hN : ∀ g : G, g ^ N = 1) :
    Set.range (eta : BurnsideRing G →+* DRing G) = {x | psi N x = x} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨b, rfl⟩
    exact psi_eta N b
  · intro x hx
    rw [mem_range_eta_iff_species_const]
    intro H h
    have hpow : h ^ N = (1 : H) := by
      ext
      push_cast
      exact hN h
    calc species H h x = species H h (psi N x) := by rw [hx]
      _ = species H (h ^ N) x := species_psi H h N x
      _ = species H 1 x := by rw [hpow]

/-- **`η(B) = Fix(ψ²)` for 2-groups**: if `g^(2^m) = 1` for all `g : G`, then
the Burnside copy inside `D(G)` is exactly the fixed subring of `ψ²`. Hence
for 2-groups, `D ⇒ B` is equivalent to transporting `ψ²` along ring
isomorphisms. -/
theorem range_eta_eq_fix_psi_two {m : ℕ} (h2 : ∀ g : G, g ^ (2 ^ m) = 1) :
    Set.range (eta : BurnsideRing G →+* DRing G) = {x | psi 2 x = x} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨b, rfl⟩
    exact psi_eta 2 b
  · intro x hx
    have hx' : psi 2 x = x := hx
    have hiter : ∀ i : ℕ, psi (2 ^ i) x = x := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        have h' := psi_psi 2 (2 ^ i) x
        rw [ih, hx'] at h'
        -- h' : x = psi (2 ^ i * 2) x
        rw [pow_succ]
        exact h'.symm
    rw [range_eta_eq_fix_psi h2]
    exact hiter m

end DRing

end LeanDring
