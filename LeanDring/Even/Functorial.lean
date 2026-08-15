/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Even.TIR

/-!
# D-ring functoriality and the sandwich theorem:
# rigidity ⟹ shadow recognition ⟹ `D ⇒ B`

**EVEN-ORDER LAYER.** No `sorry`, three standard axioms.

The mathematical result of this file is the **sandwich theorem**: the
open `ShadowRecognition` question sits strictly between the program's
two live conjectures,

 2-group D-rigidity ⟹ ShadowRecognition ⟹ 2-group `D ⇒ B`,

with both implications now formal. The proof of the left implication:
a group isomorphism `θ: G ≃* H` induces a ring isomorphism
`D(θ): D(G) ≅ D(H)` commuting with `η` and `forget` on the nose, so
its point bijection intertwines the Burnside shadows *exactly* — a
shadow-descending lattice identification exists whenever the groups are
abstractly isomorphic. (The identification exhibited need not be the
one induced by the given `Φ`; `ShadowRecognition` only asks for
existence, and by the gauge torsor all identifications are
`Γ`-translates of each other.)

En route, the missing functoriality is built once and for all:

* `MonGSet.comap` — pull back a monomial `G'`-set along `e: G →* G'`
  (same carrier, action and weights through `e`); `IsIso` transports
  verbatim (same equivalence, same gauge).
* `MonGSet.skelCongr` / `MonRing.congr` — the fibered Burnside semiring
  and the `A`-fibered Burnside ring are functorial in group
  isomorphisms; `D(θ):= MonRing.congr θ` at `A = ℂˣ`.
* `MonRing.congr_eta` / `MonRing.forget_congr` — the two commutation
  squares with the Burnside retraction pair: `D(θ) ∘ η = η ∘ B(θ)` and
  `forget ∘ D(θ) = B(θ) ∘ forget`.

Mathematical context for why this is the honest stopping point of a
direct attack: at odd order every isomorphism
is ψ²-equivariant (coprime Adams — Müller), so recognition holds with
`σ = id`; at `p = 2` the Q8 central gauge shows single identifications
genuinely fail to descend, so no pointwise mechanism can work; and an
*unconditional* proof of `ShadowRecognition` is equivalent to RAT-BR
(the transported Burnside subring `Φ⁻¹(η B(H)) ⊆ D(G)` must be
`Γ`-aligned with `η B(G)`), whose broad and canonically-pinned versions
are refuted — only the orbit form, this statement, remains open.
-/

namespace LeanDring

universe u v

/-! ## Monomial `G`-sets are functorial: pullback along a homomorphism -/

namespace MonGSet

variable {G : Type u} [Group G] {G' : Type u} [Group G']
variable {A : Type v} [CommGroup A]

/-- Pull back a monomial `G'`-set along `e: G →* G'`: same carrier,
action and weights through `e`. -/
def comap (e : G →* G') (X : MonGSet G' A) : MonGSet G A where
  carrier := X.carrier
  fintype := X.fintype
  action := MulAction.compHom X.carrier e
  weight := fun g x => X.weight (e g) x
  weight_mul := fun g h x => by
    have h1 := X.weight_mul (e g) (e h) x
    rw [← map_mul] at h1
    exact h1

/-- Pulling back preserves monomial isomorphism (same equivalence, same
gauge). -/
theorem IsIso.comap {e : G →* G'} {X Y : MonGSet G' A} (h : IsIso X Y) :
    IsIso (MonGSet.comap e X) (MonGSet.comap e Y) := by
  obtain ⟨f, φ, hf, hw⟩ := h
  exact ⟨f, φ, fun g x => hf (e g) x, fun g x => hw (e g) x⟩

/-- The pullback semiring homomorphism on fibered Burnside semirings. -/
def comapSkelHom (e : G →* G') : Skel G' A →+* Skel G A where
  toFun := Quotient.map (MonGSet.comap e) fun _ _ h => h.comap
  map_zero' := Quotient.sound <| isIso_of_weight_eq (Equiv.refl _)
    (fun _ x => x.elim) (fun _ x => x.elim)
  map_one' := Quotient.sound <| isIso_of_weight_eq (Equiv.refl _)
    (fun _ _ => rfl) (fun _ _ => rfl)
  map_add' a b := by
    refine Quotient.ind₂ (fun X Y => ?_) a b
    refine Quotient.sound <| isIso_of_weight_eq (Equiv.refl _) ?_ ?_
    · rintro g (x | y) <;> rfl
    · rintro g (x | y) <;> rfl
  map_mul' a b := by
    refine Quotient.ind₂ (fun X Y => ?_) a b
    exact Quotient.sound <| isIso_of_weight_eq (Equiv.refl _)
      (fun _ _ => rfl) (fun _ _ => rfl)

theorem comap_comap_isIso {G'' : Type u} [Group G''] (f : G →* G')
    (g' : G' →* G'') (X : MonGSet G'' A) :
    IsIso (MonGSet.comap f (MonGSet.comap g' X))
      (MonGSet.comap (g'.comp f) X) :=
  isIso_of_weight_eq (Equiv.refl _) (fun _ _ => rfl) (fun _ _ => rfl)

theorem comap_id_isIso (X : MonGSet G A) :
    IsIso (MonGSet.comap (MonoidHom.id G) X) X :=
  isIso_of_weight_eq (Equiv.refl _) (fun _ _ => rfl) (fun _ _ => rfl)

theorem comapSkelHom_comp_apply (e : G ≃* G') (a : Skel G A) :
    comapSkelHom e.toMonoidHom (comapSkelHom e.symm.toMonoidHom a) = a := by
  obtain ⟨X⟩ := a
  have hhom : (e.symm.toMonoidHom).comp e.toMonoidHom = MonoidHom.id G := by
    ext g
    simp
  calc (⟦MonGSet.comap e.toMonoidHom
        (MonGSet.comap e.symm.toMonoidHom X)⟧ : Skel G A)
      = ⟦MonGSet.comap ((e.symm.toMonoidHom).comp e.toMonoidHom) X⟧ :=
        Quotient.sound (comap_comap_isIso _ _ X)
    _ = ⟦MonGSet.comap (MonoidHom.id G) X⟧ := by rw [hhom]
    _ = ⟦X⟧ := Quotient.sound (comap_id_isIso X)

/-- Fibered Burnside semirings are functorial in group isomorphisms. -/
noncomputable def skelCongr (e : G ≃* G') : Skel G A ≃+* Skel G' A :=
  RingEquiv.ofRingHom (comapSkelHom e.symm.toMonoidHom)
    (comapSkelHom e.toMonoidHom)
    (RingHom.ext fun a => comapSkelHom_comp_apply e.symm a)
    (RingHom.ext fun a => comapSkelHom_comp_apply e a)

/-! ### The two commutation squares at the skeleton level -/

theorem comapSkelHom_ofFinHom (e : G →* G') (a : FinGSet.Skel G') :
    comapSkelHom (A := A) e (Skel.ofFinHom a) =
      Skel.ofFinHom (FinGSet.comapSkelHom e a) := by
  obtain ⟨X⟩ := a
  rfl

theorem forgetHom_comapSkelHom (e : G →* G') (a : Skel G' A) :
    Skel.forgetHom (comapSkelHom (A := A) e a) =
      FinGSet.comapSkelHom e (Skel.forgetHom a) := by
  obtain ⟨X⟩ := a
  rfl

end MonGSet

/-! ## D-ring functoriality and the retraction squares -/

namespace MonRing

open MonGSet

variable {G : Type u} [Group G] {G' : Type u} [Group G']
variable {A : Type v} [CommGroup A]

/-- **Fibered Burnside rings are functorial in group isomorphisms.**
At `A = ℂˣ` this is `D(θ): D(G) ≅ D(G')`. -/
noncomputable def congr (e : G ≃* G') : MonRing G A ≃+* MonRing G' A :=
  GrothendieckRing.congr (MonGSet.skelCongr e)

theorem congr_apply_eq_map (e : G ≃* G') (x : MonRing G A) :
    congr (A := A) e x =
      GrothendieckRing.map (comapSkelHom e.symm.toMonoidHom) x := rfl

theorem burnsideRingCongr_apply_eq_map (e : G ≃* G') (b : BurnsideRing G) :
    burnsideRingCongr e b =
      GrothendieckRing.map (FinGSet.comapSkelHom e.symm.toMonoidHom) b := rfl

/-- **The η-square**: `D(θ) ∘ η = η ∘ B(θ)`. -/
theorem congr_eta (e : G ≃* G') (b : BurnsideRing G) :
    congr (A := A) e (eta b) = eta (burnsideRingCongr e b) := by
  rw [congr_apply_eq_map, burnsideRingCongr_apply_eq_map, eta, eta,
    GrothendieckRing.map_map, GrothendieckRing.map_map]
  exact DFunLike.congr_fun (congrArg GrothendieckRing.map
    (RingHom.ext fun a => comapSkelHom_ofFinHom _ a)) b

/-- **The forget-square**: `forget ∘ D(θ) = B(θ) ∘ forget`. -/
theorem forget_congr (e : G ≃* G') (x : MonRing G A) :
    forget (congr (A := A) e x) = burnsideRingCongr e (forget x) := by
  rw [congr_apply_eq_map, burnsideRingCongr_apply_eq_map, forget, forget,
    GrothendieckRing.map_map, GrothendieckRing.map_map]
  exact DFunLike.congr_fun (congrArg GrothendieckRing.map
    (RingHom.ext fun a => forgetHom_comapSkelHom _ a)) x

end MonRing

/-! ## The sandwich theorem -/

namespace Even

open MonRing

/-- The point bijection of a group-induced D-ring isomorphism
intertwines the Burnside shadows **exactly** (not merely up to gauge):
both squares commute on the nose. -/
theorem burnsideShadow_intPointEquiv_congr {G : Type u} [Group G]
    {G' : Type u} [Group G'] (θ : G ≃* G')
    (φ' : IntPoint (DRing G')) :
    burnsideShadow (intPointEquiv
        (MonRing.congr θ : DRing G ≃+* DRing G') φ') =
      intPointEquiv (MonRing.congr θ : DRing G ≃+* DRing G')
        (burnsideShadow φ') := by
  ext x
  change φ' (MonRing.congr θ (eta (MonRing.forget x))) =
    φ' (eta (MonRing.forget (MonRing.congr θ x)))
  rw [MonRing.congr_eta, MonRing.forget_congr]

/-- **[OPEN] 2-group D-rigidity**, as a typed statement: isomorphic
D-rings of finite 2-groups come from isomorphic groups. All computed
evidence (every order ≤ 128, all candidate pairs) is consistent with
it; it is the program's strongest conjecture. -/
def TwoGroupRigidity : Prop :=
  ∀ (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H],
    IsPGroup 2 G → IsPGroup 2 H →
      Nonempty (DRing G ≃+* DRing H) → Nonempty (G ≃* H)

/-- **The sandwich theorem, left half**: 2-group D-rigidity implies
shadow recognition. Given `Φ: D(G) ≅ D(H)`, rigidity supplies a group
isomorphism `θ`; the identification induced by `D(θ)` intertwines the
shadows exactly, so a shadow-descending identification exists. -/
theorem shadowRecognition_of_rigidity (hrig : TwoGroupRigidity.{u}) :
    ShadowRecognition.{u} := by
  intro G H _ _ _ _ hG hH Φ
  obtain ⟨θ⟩ := hrig G H hG hH ⟨Φ⟩
  refine ⟨intPointEquiv (MonRing.congr θ : DRing G ≃+* DRing H),
    identifiesLattices_intPointEquiv _, ?_, ?_⟩
  · intro φ'
    rw [burnsideShadow_intPointEquiv_congr θ,
      burnsideShadow_intPointEquiv_congr θ, burnsideShadow_idempotent]
  · intro φ
    have h2 : (intPointEquiv (MonRing.congr θ : DRing G ≃+* DRing H)).symm
        (burnsideShadow φ) =
        burnsideShadow ((intPointEquiv
          (MonRing.congr θ : DRing G ≃+* DRing H)).symm φ) := by
      apply (intPointEquiv (MonRing.congr θ : DRing G ≃+* DRing H)).injective
      rw [Equiv.apply_symm_apply, ← burnsideShadow_intPointEquiv_congr θ,
        Equiv.apply_symm_apply]
    rw [h2, burnsideShadow_idempotent]

/-- **The sandwich, assembled**: rigidity ⟹ recognition ⟹ `D ⇒ B`.
The open recognition question is strictly intermediate between the
program's two conjectures. -/
theorem twoGroupDtoB_of_rigidity (hrig : TwoGroupRigidity.{u}) :
    TwoGroupDtoB.{u} :=
  twoGroupDtoB_of_shadowRecognition (shadowRecognition_of_rigidity hrig)

end Even

end LeanDring

namespace LeanDring.Even -- reopened: the relativized (per-pair) sandwich

open MonRing

/-- **The sandwich, per-pair form** (audit item 17b): a group isomorphism
alone yields a shadow-descending lattice identification between the two
D-rings. This is the body of `shadowRecognition_of_rigidity`, extracted
so that PER-STRATUM rigidity results (e.g. within-stratum extraspecial
D-rigidity, AC31–AC32) compose formally: they provide `G ≃* H` for the
pairs they cover, and this lemma turns that into the recognition datum
without any global quantification. -/
theorem exists_descending_identification_of_mulEquiv
    {G : Type u} [Group G] {H : Type u} [Group H]
    (h : Nonempty (G ≃* H)) :
    ∃ e : IntPoint (DRing H) ≃ IntPoint (DRing G),
      IdentifiesLattices e ∧
      (∀ φ' : IntPoint (DRing H),
        burnsideShadow (e (burnsideShadow φ')) = burnsideShadow (e φ')) ∧
      ∀ φ : IntPoint (DRing G),
        burnsideShadow (e.symm (burnsideShadow φ)) =
          burnsideShadow (e.symm φ) := by
  obtain ⟨θ⟩ := h
  refine ⟨intPointEquiv (MonRing.congr θ : DRing G ≃+* DRing H),
    identifiesLattices_intPointEquiv _, ?_, ?_⟩
  · intro φ'
    rw [burnsideShadow_intPointEquiv_congr θ,
      burnsideShadow_intPointEquiv_congr θ, burnsideShadow_idempotent]
  · intro φ
    have h2 : (intPointEquiv (MonRing.congr θ : DRing G ≃+* DRing H)).symm
        (burnsideShadow φ) =
        burnsideShadow ((intPointEquiv
          (MonRing.congr θ : DRing G ≃+* DRing H)).symm φ) := by
      apply (intPointEquiv (MonRing.congr θ : DRing G ≃+* DRing H)).injective
      rw [Equiv.apply_symm_apply, ← burnsideShadow_intPointEquiv_congr θ,
        Equiv.apply_symm_apply]
    rw [h2, burnsideShadow_idempotent]

/-- **Per-pair recognition from per-pair rigidity** — the relativized
composition target for AC32: for a single pair covered by a rigidity
result, every D-ring isomorphism admits a shadow-descending lattice
identification. -/
theorem shadowRecognition_pair_of_rigidity
    {G : Type u} [Group G] {H : Type u} [Group H]
    (hrig : Nonempty (DRing G ≃+* DRing H) → Nonempty (G ≃* H))
    (Φ : DRing G ≃+* DRing H) :
    ∃ e : IntPoint (DRing H) ≃ IntPoint (DRing G),
      IdentifiesLattices e ∧
      (∀ φ' : IntPoint (DRing H),
        burnsideShadow (e (burnsideShadow φ')) = burnsideShadow (e φ')) ∧
      ∀ φ : IntPoint (DRing G),
        burnsideShadow (e.symm (burnsideShadow φ)) =
          burnsideShadow (e.symm φ) :=
  exists_descending_identification_of_mulEquiv (hrig ⟨Φ⟩)

end LeanDring.Even
