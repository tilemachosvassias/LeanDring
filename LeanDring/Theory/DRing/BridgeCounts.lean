/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.BridgeTransport
import LeanDring.Theory.DRing.SpeciesConj

-- The `[Fintype _]` binders below are unused in several *statements* but are
-- load-bearing in their *proofs* (instance synthesis for cardinality and basis
-- constructions), so they cannot be `omit`ted.  The linter's suggested rewrite
-- to `[Finite _]` + `Fintype.ofFinite` is a genuine refactor, not a cleanup.
set_option linter.unusedFintypeInType false

/-!
# Diagonal matching: the table transports normalizer data

The last nontrivial step of the species→marks bridge. For a
`SpeciesTableIso T` matching mark classes `[K,1] ↦ [K',1]`:

* `mark_ne_zero_iff` — nonvanishing of a mark is subconjugacy;
* `map_conj_eq_of_subconj_card` — subconjugate + equal order ⇒ conjugate;
* `SpeciesTableIso.mark_self_transfer` — **the diagonal transfers**:
  `#(G'/K')^{K'} = #(G/K)^K`. The proof needs no poset induction:
  `T.sub K` is subconjugate to `K'` with the *same order* (squeezed
  between the transported orders of `K` and of the preimage of
  `[T.sub K, 1]`), hence conjugate to `K'`, and conjugation preserves
  marks (`species_conj`).

Combined with `card_fixedPoints_coset` this transports `|N(K)|`, hence
conjugacy-class sizes — the inputs for counting subgroups per order.
-/

namespace LeanDring

open MulAction Finset

universe u

namespace DRing

open MonGSet MonRing

variable {G : Type u} [Group G] [Fintype G]

/-- The mark entry at an arbitrary column element: on a trivial-character
row every summand is `1`, so `φ_{H,h}[K,1] = #(G/K)^H` for **every** `h`. -/
theorem species_basisElt_one_char (H K : Subgroup G) (h : H) :
    species H h (basisElt K (1 : K →* ℂˣ)) =
      (Nat.card (fixedPoints H (G ⧸ K)) : ℂ) := by
  classical
  rw [species_basisElt]
  have hval : ∀ q : fixedPoints H
      (induced K (1 : K →* ℂˣ) : MonGSet G ℂˣ).carrier,
      (((1 : K →* ℂˣ) ⟨q.1.out⁻¹ * (h : G) * q.1.out,
        sectionConj_mem K H h q.1 (q.2 h)⟩ : ℂˣ) : ℂ) = 1 := by
    intro q
    rw [MonoidHom.one_apply]
    rfl
  rw [Finset.sum_congr rfl fun q _ => hval q, Finset.sum_const,
    nsmul_eq_mul, mul_one, Finset.card_univ, ← Nat.card_eq_fintype_card]
  rfl

/-- **Marks detect subconjugacy**: `#(G/K)^H ≠ 0` iff some conjugate of
`H` lies in `K`. -/
theorem mark_ne_zero_iff (H K : Subgroup G) :
    Nat.card (fixedPoints H (G ⧸ K)) ≠ 0 ↔
      ∃ g : G, ∀ x ∈ H, g⁻¹ * x * g ∈ K := by
  constructor
  · intro hne
    have hnonempty : Nonempty (fixedPoints H (G ⧸ K)) := by
      rcases Nat.card_ne_zero.mp hne with ⟨h1, -⟩
      exact h1
    obtain ⟨q, hq⟩ := hnonempty
    refine ⟨q.out, fun x hx => ?_⟩
    have h1 := hq ⟨x⁻¹, H.inv_mem hx⟩
    have h2 : ((x⁻¹ * q.out : G) : G ⧸ K) = ((q.out : G) : G ⧸ K) := by
      have h3 : ((x⁻¹ * q.out : G) : G ⧸ K) = (x⁻¹ : G) • q := by
        conv_rhs => rw [← QuotientGroup.out_eq' q]
        rfl
      rw [h3]
      have h4 : ((q.out : G) : G ⧸ K) = q := QuotientGroup.out_eq' q
      rw [h4]
      exact h1
    have h5 := (QuotientGroup.eq).mp h2
    rwa [mul_inv_rev, inv_inv] at h5
  · rintro ⟨g, hg⟩
    have hmem : ((g : G) : G ⧸ K) ∈ fixedPoints H (G ⧸ K) := by
      intro x
      change (((x : G) * g : G) : G ⧸ K) = ((g : G) : G ⧸ K)
      refine (QuotientGroup.eq).mpr ?_
      have h1 : ((x : G) * g)⁻¹ * g = g⁻¹ * (x : G)⁻¹ * g := by group
      rw [h1]
      exact hg _ (H.inv_mem x.2)
    have hne2 : Nonempty (fixedPoints H (G ⧸ K)) := ⟨⟨_, hmem⟩⟩
    haveI : Finite (fixedPoints H (G ⧸ K)) := Subtype.finite
    exact Nat.card_ne_zero.mpr ⟨hne2, inferInstance⟩

/-- The identity coset is always `K`-fixed: `#(G/K)^K ≠ 0`. -/
theorem mark_self_ne_zero (K : Subgroup G) :
    Nat.card (fixedPoints K (G ⧸ K)) ≠ 0 := by
  rw [mark_ne_zero_iff]
  exact ⟨1, fun x hx => by simpa using hx⟩

/-- Subconjugate subgroups of equal order are conjugate. -/
theorem map_conj_eq_of_subconj_card {H K : Subgroup G} {g : G}
    (hsub : ∀ x ∈ H, g⁻¹ * x * g ∈ K)
    (hcard : Nat.card H = Nat.card K) :
    H.map (MulAut.conj g⁻¹).toMonoidHom = K := by
  have hle : H.map (MulAut.conj g⁻¹).toMonoidHom ≤ K := by
    rintro y ⟨x, hx, rfl⟩
    have h1 : (MulAut.conj g⁻¹).toMonoidHom x = g⁻¹ * x * g := by
      change g⁻¹ * x * g⁻¹⁻¹ = g⁻¹ * x * g
      rw [inv_inv]
    rw [h1]
    exact hsub x hx
  have hcards : Nat.card (H.map (MulAut.conj g⁻¹).toMonoidHom) =
      Nat.card K := by
    rw [← hcard]
    refine Nat.card_congr ?_
    exact (Subgroup.equivMapOfInjective H _
      (MulAut.conj g⁻¹).injective).symm.toEquiv
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcards.symm)

/-- Subconjugacy bounds orders. -/
theorem card_le_of_subconj {H K : Subgroup G} {g : G}
    (hsub : ∀ x ∈ H, g⁻¹ * x * g ∈ K) : Nat.card H ≤ Nat.card K := by
  have hle : H.map (MulAut.conj g⁻¹).toMonoidHom ≤ K := by
    rintro y ⟨x, hx, rfl⟩
    have h1 : (MulAut.conj g⁻¹).toMonoidHom x = g⁻¹ * x * g := by
      change g⁻¹ * x * g⁻¹⁻¹ = g⁻¹ * x * g
      rw [inv_inv]
    rw [h1]
    exact hsub x hx
  have hcards : Nat.card (H.map (MulAut.conj g⁻¹).toMonoidHom) =
      Nat.card H :=
    Nat.card_congr (Subgroup.equivMapOfInjective H _
      (MulAut.conj g⁻¹).injective).symm.toEquiv
  calc Nat.card H = Nat.card (H.map (MulAut.conj g⁻¹).toMonoidHom) :=
        hcards.symm
    _ ≤ Nat.card K := Subgroup.card_le_of_le hle

variable {G' : Type u} [Group G'] [Fintype G']

namespace SpeciesTableIso

variable (T : SpeciesTableIso G G')

/-- Entries of the transported columns on matched mark rows are the
`G`-marks. -/
theorem mark_row_entry {L : Subgroup G} {L' : Subgroup G'}
    (hLL' : T.rows (⟦⟨L, 1⟩⟧ : CharPairClass G ℂˣ) =
      (⟦⟨L', 1⟩⟧ : CharPairClass G' ℂˣ))
    (H : Subgroup G) (h : H) :
    species (T.sub H) (T.el h) (basisElt L' (1 : L' →* ℂˣ)) =
      (Nat.card (fixedPoints H (G ⧸ L)) : ℂ) := by
  have h1 := T.entry H h (⟦⟨L, 1⟩⟧ : CharPairClass G ℂˣ)
  rw [hLL', classElt_mk, classElt_mk,
    species_basisElt_one_char H L h] at h1
  exact h1

/-- Every `G'`-mark class is the image of a `G`-mark class. -/
theorem exists_rows_eq_markClass (L' : Subgroup G') :
    ∃ L : Subgroup G, T.rows (⟦⟨L, 1⟩⟧ : CharPairClass G ℂˣ) =
      (⟦⟨L', 1⟩⟧ : CharPairClass G' ℂˣ) := by
  obtain ⟨L, hL⟩ := T.symm.isMarkClass_rows
    (⟨L', rfl⟩ : IsMarkClass (⟦⟨L', 1⟩⟧ : CharPairClass G' ℂˣ))
  refine ⟨L, ?_⟩
  have h1 : T.rows (T.rows.symm (⟦⟨L', 1⟩⟧ : CharPairClass G' ℂˣ)) =
      (⟦⟨L', 1⟩⟧ : CharPairClass G' ℂˣ) := T.rows.apply_symm_apply _
  have h2 : T.symm.rows (⟦⟨L', 1⟩⟧ : CharPairClass G' ℂˣ) =
      (⟦⟨L, 1⟩⟧ : CharPairClass G ℂˣ) := hL
  have h3 : T.rows.symm (⟦⟨L', 1⟩⟧ : CharPairClass G' ℂˣ) =
      (⟦⟨L, 1⟩⟧ : CharPairClass G ℂˣ) := h2
  rw [← h3]
  exact h1

/-- **The diagonal transfers**: matched mark classes have equal diagonal
marks `#(G/K)^K = #(G'/K')^{K'}`. -/
theorem mark_self_transfer {K : Subgroup G} {K' : Subgroup G'}
    (hKK' : T.rows (⟦⟨K, 1⟩⟧ : CharPairClass G ℂˣ) =
      (⟦⟨K', 1⟩⟧ : CharPairClass G' ℂˣ)) :
    Nat.card (fixedPoints K' (G' ⧸ K')) =
      Nat.card (fixedPoints K (G ⧸ K)) := by
  -- the `(sub K)`-mark of `K'` equals the diagonal mark of `K`
  have hmark : Nat.card (fixedPoints (T.sub K) (G' ⧸ K')) =
      Nat.card (fixedPoints K (G ⧸ K)) := by
    have h1 := T.mark_row_entry hKK' K 1
    rw [species_basisElt_one_char] at h1
    exact_mod_cast h1
  -- so it is nonzero: `sub K` is subconjugate to `K'`
  have hne : Nat.card (fixedPoints (T.sub K) (G' ⧸ K')) ≠ 0 := by
    rw [hmark]
    exact mark_self_ne_zero K
  obtain ⟨g', hg'⟩ := (mark_ne_zero_iff (T.sub K) K').mp hne
  -- order chain: `|K| ≤ |sub K| ≤ |K'| = |K|`
  obtain ⟨M, hM⟩ := T.exists_rows_eq_markClass (T.sub K)
  have hMcard : Nat.card M = Nat.card (T.sub K) :=
    T.subgroup_card_eq hM
  have hKcard : Nat.card K = Nat.card K' := T.subgroup_card_eq hKK'
  -- `K ≼ M`: the `(sub K)`-diagonal mark is nonzero and reads `mark_K(M)`
  have hKM : Nat.card (fixedPoints K (G ⧸ M)) ≠ 0 := by
    have h1 := T.mark_row_entry hM K 1
    have h2 : Nat.card (fixedPoints (T.sub K) (G' ⧸ T.sub K)) ≠ 0 :=
      mark_self_ne_zero _
    rw [species_basisElt_one_char] at h1
    intro hzero
    rw [hzero] at h1
    have h3 : (Nat.card (fixedPoints (T.sub K) (G' ⧸ T.sub K)) : ℂ) = 0 := by
      exact_mod_cast h1
    exact h2 (by exact_mod_cast h3)
  obtain ⟨a, ha⟩ := (mark_ne_zero_iff K M).mp hKM
  -- order chain: `|K| ≤ |M| = |sub K| ≤ |K'| = |K|`
  have hle1 : Nat.card K ≤ Nat.card M := card_le_of_subconj ha
  have hle2 : Nat.card (T.sub K) ≤ Nat.card K' := card_le_of_subconj hg'
  have hsubKcard : Nat.card (T.sub K) = Nat.card K' := by omega
  -- hence `sub K` is conjugate to `K'`
  have hmap := map_conj_eq_of_subconj_card hg' hsubKcard
  -- conjugation preserves marks: the diagonal transfers
  have hgen : ∀ (H₀ : Subgroup G') (e : H₀), H₀ = K' →
      species H₀ e (basisElt K' (1 : K' →* ℂˣ)) =
        (Nat.card (fixedPoints K' (G' ⧸ K')) : ℂ) := by
    intro H₀ e hH₀
    subst hH₀
    exact species_basisElt_one_char _ _ e
  have hconj := species_conj (T.sub K) (T.el (1 : K)) g'⁻¹
    (basisElt K' (1 : K' →* ℂˣ))
  rw [hgen _ _ hmap, species_basisElt_one_char] at hconj
  have hfinal : (Nat.card (fixedPoints K' (G' ⧸ K')) : ℂ) =
      (Nat.card (fixedPoints K (G ⧸ K)) : ℂ) := by
    rw [hconj]
    exact_mod_cast congrArg Nat.cast hmark
  exact_mod_cast hfinal

/-- **Normalizer orders transfer**: `|N(K')| = |N(K)|` for matched mark
classes. -/
theorem normalizer_card_transfer {K : Subgroup G} {K' : Subgroup G'}
    (hKK' : T.rows (⟦⟨K, 1⟩⟧ : CharPairClass G ℂˣ) =
      (⟦⟨K', 1⟩⟧ : CharPairClass G' ℂˣ)) :
    Nat.card (Subgroup.normalizer (K' : Set G')) =
      Nat.card (Subgroup.normalizer (K : Set G)) := by
  have h1 := card_fixedPoints_coset K
  have h2 := card_fixedPoints_coset K'
  rw [← h1, ← h2, T.mark_self_transfer hKK', T.subgroup_card_eq hKK']

end SpeciesTableIso

/-! ## Conjugacy-class counting -/

omit [Fintype G] in
/-- Equality of mark classes is subgroup conjugacy. -/
theorem markClass_eq_iff {L₂ L : Subgroup G} :
    (⟦⟨L₂, 1⟩⟧ : CharPairClass G ℂˣ) = (⟦⟨L, 1⟩⟧ : CharPairClass G ℂˣ) ↔
      ∃ a : G, ∀ k : G, k ∈ L₂ ↔ a * k * a⁻¹ ∈ L := by
  rw [Quotient.eq]
  constructor
  · rintro ⟨a, hmem, -⟩
    exact ⟨a, hmem⟩
  · rintro ⟨a, hmem⟩
    refine ⟨a, hmem, fun k hk => ?_⟩
    rw [MonoidHom.one_apply, MonoidHom.one_apply]

omit [Fintype G] in
/-- Membership in a conjugated subgroup. -/
theorem mem_map_conj_iff {L : Subgroup G} (a k : G) :
    k ∈ L.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * k * a ∈ L := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 : (MulAut.conj a).toMonoidHom x = a * x * a⁻¹ := rfl
    rw [h1]
    have h2 : a⁻¹ * (a * x * a⁻¹) * a = x := by group
    rw [h2]
    exact hx
  · intro hk
    refine ⟨a⁻¹ * k * a, hk, ?_⟩
    change a * (a⁻¹ * k * a) * a⁻¹ = k
    group

omit [Fintype G] in
/-- Normalizer elements fix the subgroup under conjugation. -/
theorem map_conj_of_mem_normalizer {L : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (L : Set G)) :
    L.map (MulAut.conj n).toMonoidHom = L := by
  ext k
  rw [mem_map_conj_iff]
  rw [Subgroup.mem_normalizer_iff] at hn
  constructor
  · intro h1
    have h2 := (hn (n⁻¹ * k * n)).mp h1
    have h3 : n * (n⁻¹ * k * n) * n⁻¹ = k := by group
    rwa [h3] at h2
  · intro h1
    refine (hn (n⁻¹ * k * n)).mpr ?_
    have h3 : n * (n⁻¹ * k * n) * n⁻¹ = k := by group
    rw [h3]
    exact h1

omit [Fintype G] in
/-- Conjugation along a product splits. -/
theorem map_conj_mul (L : Subgroup G) (a b : G) :
    L.map (MulAut.conj (a * b)).toMonoidHom =
      (L.map (MulAut.conj b).toMonoidHom).map
        (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext k
  change (MulAut.conj (a * b)) k = (MulAut.conj a) ((MulAut.conj b) k)
  rw [map_mul]
  rfl

omit [Fintype G] in
/-- **The conjugacy class of `L` has `|G|/|N(L)|` members**
(multiplicative form). -/
theorem card_conjClass_mul (L : Subgroup G) :
    Nat.card {L₂ : Subgroup G //
        (⟦⟨L₂, 1⟩⟧ : CharPairClass G ℂˣ) = ⟦⟨L, 1⟩⟧} *
      Nat.card (Subgroup.normalizer (L : Set G)) = Nat.card G := by
  classical
  set N := Subgroup.normalizer (L : Set G) with hN
  -- bijection with `G ⧸ N` via `out`-representatives
  let F : G ⧸ N → {L₂ : Subgroup G //
      (⟦⟨L₂, 1⟩⟧ : CharPairClass G ℂˣ) = ⟦⟨L, 1⟩⟧} := fun q =>
    ⟨L.map (MulAut.conj q.out).toMonoidHom, by
      rw [markClass_eq_iff]
      refine ⟨q.out⁻¹, fun k => ?_⟩
      rw [mem_map_conj_iff]
      constructor
      · intro h1
        have h2 : q.out⁻¹ * k * q.out⁻¹⁻¹ = q.out⁻¹ * k * q.out := by
          rw [inv_inv]
        rw [h2]
        exact h1
      · intro h1
        have h2 : q.out⁻¹ * k * q.out⁻¹⁻¹ = q.out⁻¹ * k * q.out := by
          rw [inv_inv]
        rwa [h2] at h1⟩
  have hFinj : Function.Injective F := by
    intro q q₂ hqq
    have h1 : L.map (MulAut.conj q.out).toMonoidHom =
        L.map (MulAut.conj q₂.out).toMonoidHom :=
      congrArg Subtype.val hqq
    -- `q₂.out⁻¹ * q.out ∈ N`
    have h2 : q₂.out⁻¹ * q.out ∈ N := by
      change q₂.out⁻¹ * q.out ∈ Subgroup.normalizer (L : Set G)
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have h3 : q.out * h * q.out⁻¹ ∈
            L.map (MulAut.conj q.out).toMonoidHom := by
          rw [mem_map_conj_iff]
          have h4 : q.out⁻¹ * (q.out * h * q.out⁻¹) * q.out = h := by
            group
          rwa [h4]
        rw [h1, mem_map_conj_iff] at h3
        have h5 : q₂.out⁻¹ * (q.out * h * q.out⁻¹) * q₂.out =
            (q₂.out⁻¹ * q.out) * h * (q₂.out⁻¹ * q.out)⁻¹ := by
          group
        rwa [h5] at h3
      · intro hh
        have h3 : (q₂.out⁻¹ * q.out) * h * (q₂.out⁻¹ * q.out)⁻¹ ∈ L := hh
        have h5 : q₂.out⁻¹ * (q.out * h * q.out⁻¹) * q₂.out =
            (q₂.out⁻¹ * q.out) * h * (q₂.out⁻¹ * q.out)⁻¹ := by
          group
        rw [← h5] at h3
        have h6 : q.out * h * q.out⁻¹ ∈
            L.map (MulAut.conj q₂.out).toMonoidHom := by
          rw [mem_map_conj_iff]
          exact h3
        rw [← h1, mem_map_conj_iff] at h6
        have h7 : q.out⁻¹ * (q.out * h * q.out⁻¹) * q.out = h := by group
        rwa [h7] at h6
    have h8 : (q₂.out : G ⧸ N) = (q.out : G ⧸ N) :=
      (QuotientGroup.eq).mpr h2
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h8
    exact h8.symm
  have hFsurj : Function.Surjective F := by
    rintro ⟨L₂, hcls⟩
    obtain ⟨c, hc⟩ := markClass_eq_iff.mp hcls
    refine ⟨((c⁻¹ : G) : G ⧸ N), ?_⟩
    refine Subtype.ext ?_
    change L.map (MulAut.conj (((c⁻¹ : G) : G ⧸ N)).out).toMonoidHom = L₂
    -- the representative differs from `c⁻¹` by a normalizer element
    have hout : ((((c⁻¹ : G) : G ⧸ N)).out : G ⧸ N) =
        ((c⁻¹ : G) : G ⧸ N) := QuotientGroup.out_eq' _
    have hrel : (((c⁻¹ : G) : G ⧸ N)).out⁻¹ * c⁻¹ ∈ N :=
      (QuotientGroup.eq).mp hout
    -- write `out = c⁻¹ * n⁻¹` with `n := out⁻¹ c⁻¹ ∈ N`
    have hsplit : (((c⁻¹ : G) : G ⧸ N)).out =
        c⁻¹ * ((((c⁻¹ : G) : G ⧸ N)).out⁻¹ * c⁻¹)⁻¹ := by group
    rw [hsplit, map_conj_mul,
      map_conj_of_mem_normalizer (Subgroup.inv_mem _ hrel)]
    ext k
    rw [mem_map_conj_iff]
    have h1 : c⁻¹⁻¹ * k * c⁻¹ = c * k * c⁻¹ := by rw [inv_inv]
    rw [h1]
    exact (hc k).symm
  have hcard : Nat.card {L₂ : Subgroup G //
      (⟦⟨L₂, 1⟩⟧ : CharPairClass G ℂˣ) = ⟦⟨L, 1⟩⟧} =
      Nat.card (G ⧸ N) :=
    (Nat.card_eq_of_bijective F ⟨hFinj, hFsurj⟩).symm
  rw [hcard]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup N).symm

/-- Conjugate subgroups (equal mark classes) have equal order. -/
theorem card_eq_of_markClass_eq {L₂ L : Subgroup G}
    (h : (⟦⟨L₂, 1⟩⟧ : CharPairClass G ℂˣ) = ⟦⟨L, 1⟩⟧) :
    Nat.card L₂ = Nat.card L := by
  obtain ⟨a, ha⟩ := markClass_eq_iff.mp h
  have h1 : Nat.card L₂ ≤ Nat.card L := by
    refine card_le_of_subconj (g := a⁻¹) fun x hx => ?_
    have h2 : a⁻¹⁻¹ * x * a⁻¹ = a * x * a⁻¹ := by rw [inv_inv]
    rw [h2]
    exact (ha x).mp hx
  have h2 : Nat.card L ≤ Nat.card L₂ := by
    refine card_le_of_subconj (g := a) fun y hy => ?_
    refine (ha (a⁻¹ * y * a)).mpr ?_
    have hgy : a * (a⁻¹ * y * a) * a⁻¹ = y := by group
    rw [hgy]
    exact hy
  omega

/-- The `h = 1` species of any class reads the marks of its underlying
subgroup: `φ_{H,1}(classElt c) = #(G/c.out.1)^H`. -/
theorem species_one_classElt (c : CharPairClass G ℂˣ) (H : Subgroup G) :
    species H 1 (classElt c) =
      (Nat.card (fixedPoints H (G ⧸ c.out.1)) : ℂ) := by
  have hc : classElt c = basisElt c.out.1 c.out.2 := rfl
  rw [hc, species_one_basisElt]

/-- **Marks determine the subgroup class**: two subgroups with the same
fixed-point counts on every `H` define the same mark class (`species_injective`
plus the character-independence of `φ_{H,1}[K,·]`). -/
theorem markClass_eq_of_marks_eq {K₁ K₂ : Subgroup G}
    (hmark : ∀ H : Subgroup G,
      Nat.card (fixedPoints H (G ⧸ K₁)) = Nat.card (fixedPoints H (G ⧸ K₂))) :
    (⟦⟨K₁, 1⟩⟧ : CharPairClass G ℂˣ) = ⟦⟨K₂, 1⟩⟧ := by
  have hbe : basisElt K₁ (1 : K₁ →* ℂˣ) = basisElt K₂ (1 : K₂ →* ℂˣ) := by
    apply species_injective
    funext H h
    dsimp only
    rw [species_basisElt_one_char, species_basisElt_one_char, hmark H]
  have h1 : classElt (⟦⟨K₁, 1⟩⟧ : CharPairClass G ℂˣ) =
      classElt (⟦⟨K₂, 1⟩⟧ : CharPairClass G ℂˣ) := by
    rw [classElt_mk, classElt_mk]; exact hbe
  exact linearIndependent_classElt.injective h1

namespace SpeciesTableIso

variable (T : SpeciesTableIso G G')

include T in
/-- **The transport of subgroup counts**: two groups with isomorphic
species tables have the same number of subgroups of every order — the
machine-checked form of the block-correspondence reduction. -/
theorem card_subgroups_eq (n : ℕ) :
    Nat.card {L : Subgroup G // Nat.card L = n} =
      Nat.card {L' : Subgroup G' // Nat.card L' = n} := by
  classical
  haveI hfin : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G))
      SetLike.coe_injective
  haveI hfin' : Finite (Subgroup G') :=
    Finite.of_injective (fun H : Subgroup G' => (H : Set G'))
      SetLike.coe_injective
  haveI : Fintype (Subgroup G) := Fintype.ofFinite _
  haveI : Fintype (Subgroup G') := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Fintype.card_subtype]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun L : Subgroup G => (⟦⟨L, 1⟩⟧ : CharPairClass G ℂˣ))
    (t := (univ.filter (fun L : Subgroup G => Nat.card L = n)).image
      (fun L => (⟦⟨L, 1⟩⟧ : CharPairClass G ℂˣ)))
    (fun L hL => Finset.mem_image_of_mem _ hL)]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun L' : Subgroup G' => (⟦⟨L', 1⟩⟧ : CharPairClass G' ℂˣ))
    (t := (univ.filter (fun L' : Subgroup G' => Nat.card L' = n)).image
      (fun L' => (⟦⟨L', 1⟩⟧ : CharPairClass G' ℂˣ)))
    (fun L' hL' => Finset.mem_image_of_mem _ hL')]
  refine Finset.sum_bij (fun c _ => T.rows c) ?_ ?_ ?_ ?_
  · -- maps to
    intro c hc
    obtain ⟨L, hLmem, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨L', hL'⟩ := T.isMarkClass_rows (⟨L, rfl⟩ :
      IsMarkClass (⟦⟨L, 1⟩⟧ : CharPairClass G ℂˣ))
    rw [hL']
    refine Finset.mem_image_of_mem _ ?_
    rw [Finset.mem_filter] at hLmem ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← T.subgroup_card_eq hL']
    exact hLmem.2
  · -- injective
    intro c₁ h₁ c₂ h₂ he
    exact T.rows.injective he
  · -- surjective
    intro c' hc'
    obtain ⟨L', hL'mem, rfl⟩ := Finset.mem_image.mp hc'
    obtain ⟨L, hL⟩ := T.exists_rows_eq_markClass L'
    refine ⟨(⟦⟨L, 1⟩⟧ : CharPairClass G ℂˣ), ?_, hL⟩
    refine Finset.mem_image_of_mem _ ?_
    rw [Finset.mem_filter] at hL'mem ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [T.subgroup_card_eq hL]
    exact hL'mem.2
  · -- fiber sizes agree
    intro c hc
    obtain ⟨L, hLmem, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨L', hL'⟩ := T.isMarkClass_rows (⟨L, rfl⟩ :
      IsMarkClass (⟦⟨L, 1⟩⟧ : CharPairClass G ℂˣ))
    rw [Finset.mem_filter] at hLmem
    have hLn : Nat.card L = n := hLmem.2
    -- both fibers are full conjugacy classes
    have hfibG : ((univ.filter (fun L₂ : Subgroup G =>
        Nat.card L₂ = n)).filter (fun L₂ =>
          (⟦⟨L₂, 1⟩⟧ : CharPairClass G ℂˣ) = ⟦⟨L, 1⟩⟧)) =
        univ.filter (fun L₂ : Subgroup G =>
          (⟦⟨L₂, 1⟩⟧ : CharPairClass G ℂˣ) = ⟦⟨L, 1⟩⟧) := by
      ext L₂
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨-, h2⟩
        exact h2
      · intro h2
        exact ⟨(card_eq_of_markClass_eq h2).trans hLn, h2⟩
    have hL'n : Nat.card L' = n := by
      rw [← T.subgroup_card_eq hL']
      exact hLn
    have hfibG' : ((univ.filter (fun L₂ : Subgroup G' =>
        Nat.card L₂ = n)).filter (fun L₂ =>
          (⟦⟨L₂, 1⟩⟧ : CharPairClass G' ℂˣ) =
            T.rows (⟦⟨L, 1⟩⟧ : CharPairClass G ℂˣ))) =
        univ.filter (fun L₂ : Subgroup G' =>
          (⟦⟨L₂, 1⟩⟧ : CharPairClass G' ℂˣ) = ⟦⟨L', 1⟩⟧) := by
      ext L₂
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hL']
      constructor
      · rintro ⟨-, h2⟩
        exact h2
      · intro h2
        exact ⟨(card_eq_of_markClass_eq h2).trans hL'n, h2⟩
    rw [hfibG, hfibG']
    -- both class sizes satisfy `size · |N| = |group|` with equal `|N|`
    have hSG : (univ.filter (fun L₂ : Subgroup G =>
        (⟦⟨L₂, 1⟩⟧ : CharPairClass G ℂˣ) = ⟦⟨L, 1⟩⟧)).card =
        Nat.card {L₂ : Subgroup G //
          (⟦⟨L₂, 1⟩⟧ : CharPairClass G ℂˣ) = ⟦⟨L, 1⟩⟧} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hSG' : (univ.filter (fun L₂ : Subgroup G' =>
        (⟦⟨L₂, 1⟩⟧ : CharPairClass G' ℂˣ) = ⟦⟨L', 1⟩⟧)).card =
        Nat.card {L₂ : Subgroup G' //
          (⟦⟨L₂, 1⟩⟧ : CharPairClass G' ℂˣ) = ⟦⟨L', 1⟩⟧} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hSG, hSG']
    have h1 := card_conjClass_mul L
    have h2 := card_conjClass_mul L'
    have hN := T.normalizer_card_transfer hL'
    have hGcard := T.card_eq
    have hNpos : 0 < Nat.card (Subgroup.normalizer (L : Set G)) :=
      Nat.card_pos
    rw [hN, ← hGcard] at h2
    rw [← h2] at h1
    exact Nat.eq_of_mul_eq_mul_right hNpos h1

include T in
/-- The reverse form of `species_one_rows`: the marks column of `T c` reads,
at `H'`, the marks of `c` at the matched subgroup `sub' H'`. -/
theorem species_one_rows' (e : CharPairClass G ℂˣ) (H' : Subgroup G') :
    species H' 1 (classElt (T.rows e)) =
      species (T.sub' H') 1 (classElt e) := by
  have h : species (T.sub' H') 1 (classElt (T.rows.symm (T.rows e))) =
      species H' 1 (classElt (T.rows e)) := T.symm.species_one_rows (T.rows e) H'
  rw [Equiv.symm_apply_apply] at h
  exact h.symm

include T in
/-- **The block correspondence**: the row
bijection commutes with passing to a row's underlying subgroup class. So `T`
sends the block of rows sitting over a subgroup class to the block over the
matched class — making the block structure (in particular the abelian-vs-
nonabelian distinction, `p³` vs `< p³` degree-1 rows) table-transportable. -/
theorem markBelow_rows (c : CharPairClass G ℂˣ) :
    T.rows (⟦⟨c.out.1, 1⟩⟧ : CharPairClass G ℂˣ) =
      (⟦⟨(T.rows c).out.1, 1⟩⟧ : CharPairClass G' ℂˣ) := by
  have hrowsmark : IsMarkClass (T.rows ⟦⟨c.out.1, 1⟩⟧) :=
    T.isMarkClass_rows ⟨c.out.1, rfl⟩
  have hconst : ∀ (H' : Subgroup G') (h' : H'),
      species H' h' (classElt (T.rows ⟦⟨c.out.1, 1⟩⟧)) =
        species H' 1 (classElt (T.rows ⟦⟨c.out.1, 1⟩⟧)) :=
    (mem_range_eta_iff_species_const _).mp
      ((isMarkClass_iff_mem_range_eta _).mp hrowsmark)
  have hkey : classElt (T.rows (⟦⟨c.out.1, 1⟩⟧ : CharPairClass G ℂˣ)) =
      classElt (⟦⟨(T.rows c).out.1, 1⟩⟧ : CharPairClass G' ℂˣ) := by
    apply species_injective
    funext H' h'
    dsimp only
    rw [show classElt (⟦⟨(T.rows c).out.1, 1⟩⟧ : CharPairClass G' ℂˣ) =
        basisElt (T.rows c).out.1 1 from classElt_mk _,
      species_basisElt_one_char, hconst H' h',
      species_one_rows' T ⟦⟨c.out.1, 1⟩⟧ H',
      show classElt (⟦⟨c.out.1, 1⟩⟧ : CharPairClass G ℂˣ) =
        basisElt c.out.1 1 from classElt_mk _,
      species_one_basisElt]
    have e1 : species H' 1 (classElt (T.rows c)) =
        (Nat.card (fixedPoints (T.sub' H') (G ⧸ c.out.1)) : ℂ) := by
      rw [species_one_rows' T c H', species_one_classElt]
    have e2 : species H' 1 (classElt (T.rows c)) =
        (Nat.card (fixedPoints H' (G' ⧸ (T.rows c).out.1)) : ℂ) :=
      species_one_classElt (T.rows c) H'
    rw [← e1, e2]
  exact linearIndependent_classElt.injective hkey

include T in
/-- **The block sizes are a species-table invariant**: the number of rows
sitting over a subgroup class is preserved by `T` (the degree-1-row-count that
separates the abelian maximal subgroup from the nonabelian ones). -/
theorem card_fiber_eq (K : Subgroup G) :
    Nat.card {c : CharPairClass G ℂˣ //
        (⟦⟨c.out.1, 1⟩⟧ : CharPairClass G ℂˣ) = ⟦⟨K, 1⟩⟧} =
      Nat.card {c' : CharPairClass G' ℂˣ //
        (⟦⟨c'.out.1, 1⟩⟧ : CharPairClass G' ℂˣ) =
          T.rows ⟦⟨K, 1⟩⟧} := by
  refine Nat.card_congr (T.rows.subtypeEquiv fun c => ?_)
  rw [← T.markBelow_rows c]
  exact (T.rows.injective.eq_iff).symm

end SpeciesTableIso

end DRing

end LeanDring
