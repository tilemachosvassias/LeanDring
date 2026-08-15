/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.BridgeCounts
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Index

-- Several statements below do not mention the section's `[Fintype _]` /
-- group binders, but their proofs need them for instance synthesis, so the
-- binders cannot be `omit`ted.  The linters' suggested rewrite to `[Finite _]`
-- plus `Fintype.ofFinite` is a genuine refactor, not a cleanup.
set_option linter.unusedFintypeInType false

/-!
# The abelianization order is a mark-table invariant in odd order

**Paper Lemma 3.14** (`lem:ab-from-marks`): if `G` has odd order then
`|G^ab|` is determined by the table of marks of `G`; consequently two odd
order groups with isomorphic tables of marks have equal abelianization
orders.

The formalization follows the paper proof but *removes* its third
visibility step (the quotient mark table as a submatrix). The point is
that the paper's set `𝒮 = {N ⊴ G : G/N abelian}` can be described without
ever forming `G/N`: subgroups of `G/N` are exactly the `K/N` with
`N ≤ K ≤ G`, and `K/N ⊴ G/N ↔ K ⊴ G`, so

  `G/N` has all subgroups normal  ↔  every `K ≥ N` is normal in `G`,

a condition inside the subgroup lattice of `G` alone (`NormalAbove`).
What remains are the paper's first two visibility statements, both proved
here from the marks:

* `normal_iff_markOn_self` — **normality is visible**: `K ⊴ G` iff the
  diagonal mark `#(G/K)^K = [N_G(K):K]` equals the trivial mark
  `#(G/K)^1 = [G:K]`, i.e. iff the conjugacy class of `K` is a singleton;
* `le_iff_markOn_ne_zero` — **containment below a normal subgroup is
  visible**: for `K ⊴ G`, `#(G/K)^U ≠ 0` iff `U ≤ K` (`mark_ne_zero_iff`
  of `BridgeCounts` plus normality);
* `markNormalAbove_iff_normalAbove` — hence `NormalAbove` itself is a
  property of the mark table (`MarkNormalAbove`).

The group-theoretic pivot — a group of **odd** order is abelian iff all of
its subgroups are normal — is quoted from Dedekind's classification of
Hamiltonian groups, which Mathlib does not have (there is no
`IsHamiltonian` for groups; `NormalizerCondition` exists but is far
weaker).

*Why it is not simply proved here.* At odd order the
Hamiltonian classification is not actually needed: `Q₈` cannot occur, and
the argument reduces to two steps. Step 1 — all subgroups normal ⟹ all
Sylows normal ⟹ `G` is the direct product of its Sylows — is available,
being two clauses of Mathlib's `Group.isNilpotent_of_finite_tfae`, and is
carried out in `LeanDring/Even/DedekindOdd.lean`
(`dedekindOdd_of_pgroup`). Step 2 is the residue: *an odd `p`-group with
every subgroup normal is abelian*. Its usual proof needs the structure of
`Aut(C_{p^k})` for odd `p` — that the `p`-part of `(ℤ/p^k)ˣ` is exactly
`{r : r ≡ 1 mod p}`, so conjugation gives `b⁻¹ab = a^r` with `p ∣ r-1`.
Mathlib does not package that, but the even-order layer now proves it:
`unitsReduce_eq_one_of_orderOf_eq_pow`
(`LeanDring/Even/ZModUnitsPPow.lean`) and its conjugation form
`exists_conj_exponent_one_mod_prime`
(`LeanDring/Even/DedekindOrderP.lean`). What is still cited is therefore
only the last step, isolated as `Even.DedekindOddPGroup`.

It is therefore carried as an **explicit hypothesis**
`OddDedekind`, in the style of `P4Classification` in
`LeanDring.P4.Capstone` — a cited classical input, never an axiom
(Robinson, *A Course in the Theory of Groups*, §5.3: a finite group all of
whose subgroups are normal is abelian or `Q₈ × E × A` with `E` elementary
abelian `2`-group, and the latter has even order). Everything else is
proved. The reduction of the hypothesis to quotients is done here
(`commutator_le_of_normalAbove`), so `OddDedekind` is used only in its
plain classical form; `LeanDring/Even/DedekindOdd.lean` reduces it further
still, deriving it from the `p`-group residue by
`oddDedekind_of_pgroup`.

An *isomorphism of tables of marks* is modelled as `MarkTableIso`: a
bijection of subgroups matching every mark entry. This is equivalent to
the classical notion (a mark-preserving bijection of conjugacy classes of
subgroups): marks depend only on the classes of their two arguments and
class lengths are mark-determined, so a class bijection lifts to a
subgroup bijection. It is inhabited (`MarkTableIso.refl`).

Main results:

* `card_abelianization_eq_markOn_bot_commutator` — unconditionally,
  `|G^ab|` is the mark of the trivial subgroup on `G/G'`;
* `MarkTableIso.map_commutator` — under `OddDedekind` and odd order the
  bijection carries `G'` to `H'`;
* `MarkTableIso.card_abelianization_eq` — **Lemma 3.14**.
-/

namespace LeanDring

open MulAction

open scoped commutatorElement

universe u

namespace DRing

variable {G G' : Type u} [Group G] [Fintype G] [Group G'] [Fintype G']

-- `Nat.card`-valued marks do not need `Fintype` in their *types*, but the
-- ambient finiteness is what makes them the entries of a finite table, and
-- every neighbouring file in `Theory/DRing` carries the same section
-- variable; keep the signatures uniform.

/-! ## Marks of transitive `G`-sets -/

/-- The mark of `U` on the transitive `G`-set `G/K`: the number of
`U`-fixed cosets. This is the `(U, K)` entry of the table of marks. -/
noncomputable def markOn (U K : Subgroup G) : ℕ :=
  Nat.card (fixedPoints U (G ⧸ K))

omit [Fintype G] in
theorem fixedPoints_bot_quotient (K : Subgroup G) :
    fixedPoints (⊥ : Subgroup G) (G ⧸ K) = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  intro g
  obtain ⟨g, hg⟩ := g
  rw [Subgroup.mem_bot] at hg
  subst hg
  exact one_smul G x

omit [Fintype G] in
/-- The trivial subgroup marks the index: `#(G/K)^1 = [G:K]`. -/
theorem markOn_bot (K : Subgroup G) : markOn (⊥ : Subgroup G) K = K.index := by
  rw [markOn, fixedPoints_bot_quotient]
  exact Nat.card_congr (Equiv.Set.univ _)

theorem markOn_bot_ne_zero (K : Subgroup G) : markOn (⊥ : Subgroup G) K ≠ 0 := by
  rw [markOn_bot]
  exact Subgroup.index_ne_zero_of_finite

/-! ## Visibility 1: normality -/

/-- **Normality is visible in the table of marks**: `K` is normal exactly
when its diagonal mark `#(G/K)^K = [N_G(K):K]` equals the trivial mark
`#(G/K)^1 = [G:K]` — equivalently, when the conjugacy class of `K` has
length `[G:N_G(K)] = 1`. -/
theorem normal_iff_markOn_self (K : Subgroup G) :
    K.Normal ↔ markOn K K = markOn (⊥ : Subgroup G) K := by
  have hfix : (∀ x : G ⧸ K, x ∈ fixedPoints K (G ⧸ K)) ↔ K.Normal := by
    constructor
    · intro h
      refine ⟨fun n hn g => ?_⟩
      have h1 := h ((g⁻¹ : G) : G ⧸ K) ⟨n, hn⟩
      have h2 : ((n * g⁻¹ : G) : G ⧸ K) = ((g⁻¹ : G) : G ⧸ K) := h1
      have h3 := (QuotientGroup.eq).mp h2
      have h4 : (n * g⁻¹)⁻¹ * g⁻¹ = g * n⁻¹ * g⁻¹ := by group
      rw [h4] at h3
      have h5 : g * n * g⁻¹ = (g * n⁻¹ * g⁻¹)⁻¹ := by group
      rw [h5]
      exact K.inv_mem h3
    · intro hK x n
      induction x using QuotientGroup.induction_on with
      | H g =>
        change (((n : G) * g : G) : G ⧸ K) = (g : G ⧸ K)
        refine (QuotientGroup.eq).mpr ?_
        have h1 : ((n : G) * g)⁻¹ * g = g⁻¹ * (n : G)⁻¹ * g := by group
        rw [h1]
        have h2 := hK.conj_mem _ (K.inv_mem n.2) g⁻¹
        have h3 : g⁻¹ * (n : G)⁻¹ * g⁻¹⁻¹ = g⁻¹ * (n : G)⁻¹ * g := by
          rw [inv_inv]
        rwa [h3] at h2
  constructor
  · intro hK
    have huniv : fixedPoints K (G ⧸ K) = Set.univ :=
      Set.eq_univ_of_forall (hfix.mpr hK)
    rw [markOn, markOn, huniv, fixedPoints_bot_quotient]
  · intro hcard
    refine hfix.mp ?_
    have hle : (Set.univ : Set (G ⧸ K)).ncard ≤ (fixedPoints K (G ⧸ K)).ncard := by
      have h1 : (fixedPoints K (G ⧸ K)).ncard = markOn K K := rfl
      have h2 : (Set.univ : Set (G ⧸ K)).ncard = markOn (⊥ : Subgroup G) K := by
        rw [markOn, fixedPoints_bot_quotient]
        rfl
      rw [h1, h2, hcard]
    have := Set.eq_of_subset_of_ncard_le (Set.subset_univ (fixedPoints K (G ⧸ K)))
      hle (Set.toFinite _)
    intro x
    rw [this]
    trivial

/-! ## Visibility 2: containment below a normal subgroup -/

/-- **Containment among normal subgroups is visible**: for `K` normal,
`#(G/K)^U ≠ 0` (i.e. `U` is subconjugate to `K`) is exactly `U ≤ K`. -/
theorem le_iff_markOn_ne_zero {U K : Subgroup G} (hK : K.Normal) :
    U ≤ K ↔ markOn U K ≠ 0 := by
  rw [markOn, mark_ne_zero_iff]
  constructor
  · intro hle
    exact ⟨1, fun x hx => by simpa using hle hx⟩
  · rintro ⟨g, hg⟩ x hx
    have h1 := hK.conj_mem _ (hg x hx) g
    have h2 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [h2] at h1

/-- Containment always gives a nonzero mark (no normality needed). -/
theorem markOn_ne_zero_of_le {U K : Subgroup G} (hle : U ≤ K) : markOn U K ≠ 0 := by
  rw [markOn, mark_ne_zero_iff]
  exact ⟨1, fun x hx => by simpa using hle hx⟩

/-- Subconjugacy in mark form: a nonzero mark exhibits a conjugate of `K`
containing `U`. -/
theorem exists_conj_of_markOn_ne_zero {U K : Subgroup G} (h : markOn U K ≠ 0) :
    ∃ g : G, U ≤ K.map (MulAut.conj g).toMonoidHom := by
  rw [markOn, mark_ne_zero_iff] at h
  obtain ⟨g, hg⟩ := h
  exact ⟨g, fun x hx => (mem_map_conj_iff g x).mpr (hg x hx)⟩

omit [Fintype G] in
/-- Normality passes back along conjugation. -/
theorem normal_of_normal_map_conj {K : Subgroup G} {g : G}
    (h : (K.map (MulAut.conj g).toMonoidHom).Normal) : K.Normal := by
  refine ⟨fun n hn a => ?_⟩
  have hmem : g * n * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom := by
    refine (mem_map_conj_iff g _).mpr ?_
    have : g⁻¹ * (g * n * g⁻¹) * g = n := by group
    rwa [this]
  have hconj := h.conj_mem _ hmem (g * a * g⁻¹)
  have hval : (g * a * g⁻¹) * (g * n * g⁻¹) * (g * a * g⁻¹)⁻¹ =
      g * (a * n * a⁻¹) * g⁻¹ := by group
  rw [hval] at hconj
  have := (mem_map_conj_iff g (g * (a * n * a⁻¹) * g⁻¹)).mp hconj
  have hsimp : g⁻¹ * (g * (a * n * a⁻¹) * g⁻¹) * g = a * n * a⁻¹ := by group
  rwa [hsimp] at this

/-! ## The paper's set `𝒮`, without forming the quotient -/

/-- `NormalAbove N`: every subgroup of `G` containing `N` is normal.
For `N ⊴ G` this says exactly that every subgroup of `G/N` is normal,
since the subgroups of `G/N` are the `K/N` with `N ≤ K` and `K/N ⊴ G/N`
iff `K ⊴ G`. It is the paper's membership condition `N ∈ 𝒮` once
Dedekind's theorem is available. -/
def NormalAbove (N : Subgroup G) : Prop := ∀ K : Subgroup G, N ≤ K → K.Normal

/-- The mark-table reading of `NormalAbove`: every subgroup with a nonzero
mark on `G/N`'s row is normal, both conditions read off the table by
`normal_iff_markOn_self` and `mark_ne_zero_iff`. -/
def MarkNormalAbove (N : Subgroup G) : Prop :=
  ∀ K : Subgroup G, markOn N K ≠ 0 → markOn K K = markOn (⊥ : Subgroup G) K

/-- **The condition `N ∈ 𝒮` is a property of the table of marks.** -/
theorem markNormalAbove_iff_normalAbove (N : Subgroup G) :
    MarkNormalAbove N ↔ NormalAbove N := by
  constructor
  · intro h K hle
    exact (normal_iff_markOn_self K).mpr (h K (markOn_ne_zero_of_le hle))
  · intro h K hne
    obtain ⟨g, hg⟩ := exists_conj_of_markOn_ne_zero hne
    exact (normal_iff_markOn_self K).mp (normal_of_normal_map_conj (h _ hg))

/-! ## The pivot: Dedekind's theorem in odd order -/

/-- **Dedekind's theorem, odd case** — the one classical input, carried as
an explicit hypothesis (never an axiom), exactly as `P4Classification` is
in `LeanDring.P4.Capstone`: a finite group of odd order all of whose
subgroups are normal is abelian.

This is immediate from Dedekind's classification of groups with all
subgroups normal (Robinson, §5.3): such a group is abelian or
`Q₈ × E × A` with `E` an elementary abelian `2`-group, and the second
alternative has even order. Mathlib has no Hamiltonian/Dedekind group
theory, and formalizing the classification is out of scope here. -/
def OddDedekind : Prop :=
  ∀ (Q : Type u) [Group Q] [Finite Q], Odd (Nat.card Q) →
    (∀ S : Subgroup Q, S.Normal) → ∀ a b : Q, a * b = b * a

omit [Fintype G] in
/-- Easy direction of the pivot, in lattice form: if `G' ≤ N` then every
subgroup above `N` is normal (no parity needed). -/
theorem normalAbove_of_commutator_le {N : Subgroup G} (h : commutator G ≤ N) :
    NormalAbove N := by
  intro K hle
  refine ⟨fun n hn g => ?_⟩
  have hcomm : ⁅g, n⁆ ∈ commutator G :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n)
  have hcommK : ⁅g, n⁆ ∈ K := hle (h hcomm)
  have hval : g * n * g⁻¹ = ⁅g, n⁆ * n := by
    rw [commutatorElement_def]; group
  rw [hval]
  exact K.mul_mem hcommK hn

/-- Hard direction of the pivot, with the quotient reduction done here: if
every subgroup above `N` is normal and `|G|` is odd, then `G/N` is abelian,
i.e. `G' ≤ N`. Uses `OddDedekind` only in its plain classical form. -/
theorem commutator_le_of_normalAbove (hdk : OddDedekind.{u})
    (hodd : Odd (Nat.card G)) {N : Subgroup G} (h : NormalAbove N) :
    commutator G ≤ N := by
  haveI hN : N.Normal := h N le_rfl
  haveI : Finite (G ⧸ N) := Quotient.finite _
  -- odd order passes to the quotient
  have hdvd : Nat.card (G ⧸ N) ∣ Nat.card G := by
    have := N.index_dvd_card
    rwa [Subgroup.index] at this
  have hoddQ : Odd (Nat.card (G ⧸ N)) := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hc] at hodd
    exact (Nat.odd_mul.mp hodd).1
  -- every subgroup of `G/N` is normal
  have hall : ∀ S : Subgroup (G ⧸ N), S.Normal := by
    intro S
    have hNle : N ≤ S.comap (QuotientGroup.mk' N) := by
      intro x hx
      have : (QuotientGroup.mk' N) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      change (QuotientGroup.mk' N) x ∈ S
      rw [this]
      exact S.one_mem
    have hKnormal : (S.comap (QuotientGroup.mk' N)).Normal := h _ hNle
    have hmap : (S.comap (QuotientGroup.mk' N)).map (QuotientGroup.mk' N) = S :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) S
    have := hKnormal.map (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    rwa [hmap] at this
  have hcomm := hdk (G ⧸ N) hoddQ hall
  -- an abelian quotient forces `G' ≤ N`
  rw [commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [← QuotientGroup.eq_one_iff]
  have hmk : ((⁅g₁, g₂⁆ : G) : G ⧸ N) = ⁅(g₁ : G ⧸ N), (g₂ : G ⧸ N)⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [hmk, commutatorElement_eq_one_iff_mul_comm]
  exact hcomm _ _

/-- **The pivot**, combined: for odd `|G|`, `N ∈ 𝒮` iff `G' ≤ N`. -/
theorem normalAbove_iff_commutator_le (hdk : OddDedekind.{u})
    (hodd : Odd (Nat.card G)) (N : Subgroup G) :
    NormalAbove N ↔ commutator G ≤ N :=
  ⟨commutator_le_of_normalAbove hdk hodd, normalAbove_of_commutator_le⟩

/-! ## `|G^ab|` as a mark entry -/

omit [Fintype G] in
/-- `|G^ab| = [G : G']` is the mark of the trivial subgroup on `G/G'`.
No parity hypothesis. -/
theorem card_abelianization_eq_markOn_bot_commutator :
    Nat.card (Abelianization G) = markOn (⊥ : Subgroup G) (commutator G) := by
  rw [markOn_bot]
  rfl

/-! ## Isomorphisms of tables of marks -/

/-- An **isomorphism of tables of marks**: a bijection of subgroups
matching every mark entry.

Classically a mark-table isomorphism is a mark-preserving bijection of
*conjugacy classes* of subgroups; the two notions agree, since marks
depend only on the classes of their two arguments and class lengths are
mark-determined (`normal_iff_markOn_self` is the singleton case), so a
class bijection lifts to a bijection of subgroups. -/
structure MarkTableIso (G G' : Type u) [Group G] [Fintype G]
    [Group G'] [Fintype G'] where
  /-- The bijection of subgroups. -/
  σ : Subgroup G ≃ Subgroup G'
  /-- Every mark entry is matched. -/
  markOn_eq : ∀ U K : Subgroup G, markOn U K = markOn (σ U) (σ K)

namespace MarkTableIso

/-- The identity mark-table isomorphism (so the notion is inhabited). -/
def refl (G : Type u) [Group G] [Fintype G] : MarkTableIso G G where
  σ := Equiv.refl _
  markOn_eq _ _ := rfl

variable (T : MarkTableIso G G')

/-- The inverse bijection also matches marks. -/
theorem markOn_symm (U' K' : Subgroup G') :
    markOn U' K' = markOn (T.σ.symm U') (T.σ.symm K') := by
  have := T.markOn_eq (T.σ.symm U') (T.σ.symm K')
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
  exact this.symm

/-- The transposed mark-table isomorphism. -/
def symm : MarkTableIso G' G where
  σ := T.σ.symm
  markOn_eq := T.markOn_symm

/-- The trivial subgroup is mark-visible: `σ ⊥ = ⊥`. -/
theorem map_bot : T.σ (⊥ : Subgroup G) = ⊥ := by
  have hne : markOn (T.σ ⊥) (⊥ : Subgroup G') ≠ 0 := by
    have h1 := T.markOn_eq ⊥ (T.σ.symm ⊥)
    rw [Equiv.apply_symm_apply] at h1
    rw [← h1]
    exact markOn_bot_ne_zero _
  have := (le_iff_markOn_ne_zero (U := T.σ ⊥) (K := (⊥ : Subgroup G'))
    (Subgroup.normal_bot)).mpr hne
  exact le_bot_iff.mp this

/-- Membership of `𝒮` transports across the table. -/
theorem markNormalAbove_map (N : Subgroup G) :
    MarkNormalAbove N ↔ MarkNormalAbove (T.σ N) := by
  constructor
  · intro h K' hne
    have hK : markOn N (T.σ.symm K') ≠ 0 := by
      rw [T.markOn_eq, Equiv.apply_symm_apply]
      exact hne
    have hdiag := h _ hK
    have h1 : markOn K' K' = markOn (T.σ.symm K') (T.σ.symm K') :=
      T.markOn_symm K' K'
    have h2 : markOn (⊥ : Subgroup G') K' =
        markOn (⊥ : Subgroup G) (T.σ.symm K') := by
      have := T.markOn_eq ⊥ (T.σ.symm K')
      rw [T.map_bot, Equiv.apply_symm_apply] at this
      exact this.symm
    rw [h1, h2, hdiag]
  · intro h K hne
    have hK' : markOn (T.σ N) (T.σ K) ≠ 0 := by rw [← T.markOn_eq]; exact hne
    have hdiag := h _ hK'
    have h1 : markOn K K = markOn (T.σ K) (T.σ K) := T.markOn_eq K K
    have h2 : markOn (⊥ : Subgroup G) K = markOn (⊥ : Subgroup G') (T.σ K) := by
      have := T.markOn_eq ⊥ K
      rwa [T.map_bot] at this
    rw [h1, h2, hdiag]

/-- **The commutator subgroup is mark-visible in odd order**: the table
bijection carries `G'` to `H'`. It is the minimum of `𝒮`, and both
membership in `𝒮` and the order relation below a normal subgroup are read
off the table. -/
theorem map_commutator (hdk : OddDedekind.{u}) (hodd : Odd (Nat.card G))
    (hodd' : Odd (Nat.card G')) :
    T.σ (commutator G) = commutator G' := by
  -- `G'` lies in `𝒮`, hence so does its image, hence `H' ≤ σ G'`
  have hS : NormalAbove (commutator G) := normalAbove_of_commutator_le le_rfl
  have hS' : NormalAbove (T.σ (commutator G)) :=
    (markNormalAbove_iff_normalAbove _).mp
      ((T.markNormalAbove_map _).mp ((markNormalAbove_iff_normalAbove _).mpr hS))
  have hge : commutator G' ≤ T.σ (commutator G) :=
    commutator_le_of_normalAbove hdk hodd' hS'
  -- symmetrically, the preimage `M` of `H'` lies in `𝒮`, so `G' ≤ M`
  set M : Subgroup G := T.σ.symm (commutator G') with hM
  have hSM' : NormalAbove (commutator G') := normalAbove_of_commutator_le le_rfl
  have hSM : NormalAbove M := by
    refine (markNormalAbove_iff_normalAbove _).mp ?_
    refine (T.markNormalAbove_map M).mpr ?_
    rw [hM, Equiv.apply_symm_apply]
    exact (markNormalAbove_iff_normalAbove _).mpr hSM'
  have hle : commutator G ≤ M := commutator_le_of_normalAbove hdk hodd hSM
  -- transport that containment across the table
  haveI hMnormal : M.Normal := hSM M le_rfl
  have hmark : markOn (commutator G) M ≠ 0 :=
    (le_iff_markOn_ne_zero hMnormal).mp hle
  have hmark' : markOn (T.σ (commutator G)) (commutator G') ≠ 0 := by
    have := T.markOn_eq (commutator G) M
    rw [hM, Equiv.apply_symm_apply] at this
    rw [← this]
    exact hmark
  have hle' : T.σ (commutator G) ≤ commutator G' :=
    (le_iff_markOn_ne_zero (Subgroup.commutator_normal ⊤ ⊤)).mpr hmark'
  exact le_antisymm hle' hge

include T in
/-- **Paper Lemma 3.14.** Two groups of odd order with isomorphic tables
of marks have equal abelianization orders. Conditional only on the
classical input `OddDedekind` (Dedekind's theorem in odd order). -/
theorem card_abelianization_eq (hdk : OddDedekind.{u}) (hodd : Odd (Nat.card G))
    (hodd' : Odd (Nat.card G')) :
    Nat.card (Abelianization G) = Nat.card (Abelianization G') := by
  rw [card_abelianization_eq_markOn_bot_commutator,
    card_abelianization_eq_markOn_bot_commutator]
  have h1 := T.markOn_eq ⊥ (commutator G)
  rw [T.map_bot, T.map_commutator hdk hodd hodd'] at h1
  exact h1

end MarkTableIso

end DRing

end LeanDring
