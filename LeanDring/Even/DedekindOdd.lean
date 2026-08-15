/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Sylow
import LeanDring.Theory.DRing.MarksAbelianization

-- Several statements below do not mention the section's `[Fintype _]` /
-- group binders, but their proofs need them for instance synthesis, so the
-- binders cannot be `omit`ted.  The linters' suggested rewrite to `[Finite _]`
-- plus `Fintype.ofFinite` is a genuine refactor, not a cleanup.
set_option linter.unusedSectionVars false

/-!
# Dedekind's theorem in odd order: the reduction to `p`-groups

**EVEN-ORDER LAYER.** No `sorry`, three standard axioms.

`LeanDring.DRing.OddDedekind` — a finite group of odd order all of whose
subgroups are normal is abelian — is carried as a hypothesis by
`LeanDring/Theory/DRing/MarksAbelianization.lean`, and is one of the four external
inputs the paper declares.

This file removes the *first half* of the obstruction. The classical
route goes through Dedekind's classification of Hamiltonian groups
([Robinson96] 5.3.7), which
Mathlib does not have; but at odd order that classification is not needed,
and the argument splits in two:

1. **the reduction** — all subgroups normal ⟹ all Sylows normal ⟹ `G` is
   the direct product of its Sylows, each of which inherits both oddness
   and the normality hypothesis. This is `dedekindOdd_of_pgroup` below,
   and it is *proved*, resting on Mathlib's
   `Group.isNilpotent_of_finite_tfae`;
2. **the `p`-group core** — an odd `p`-group with every subgroup normal
   is abelian. This is the hypothesis `DedekindOddPGroup` below, and it is
   what remains.

So the external input is now pinned to a single, sharply stated fact
about `p`-groups rather than to the full Hamiltonian classification. The
residual proof needs the structure of `Aut(C_{p^k})` — that a unit of
`p`-power order reduces to `1` mod `p`, so conjugation reads
`b⁻¹ab = a^r` with `p ∣ r-1`. Mathlib does not package that, but it is
now proved here as
`Even.unitsReduce_eq_one_of_orderOf_eq_pow` (`LeanDring/Even/ZModUnitsPPow.lean`).
What is left of `DedekindOddPGroup` is therefore the commutator argument
built on top of it, not the arithmetic input.
-/

namespace LeanDring

namespace Even

universe u

/-- **The residual core of Dedekind's theorem at odd order**: an odd
`p`-group in which every subgroup is normal is abelian.

This is all that is left of `OddDedekind` after `dedekindOdd_of_pgroup`
below. It is genuinely a `p`-group statement: the usual proof runs
through the structure of `Aut(C_{p^k})` for odd `p`. -/
def DedekindOddPGroup : Prop :=
  ∀ (p : ℕ) (P : Type u) [Group P] [Finite P], p.Prime → IsPGroup p P →
    Odd (Nat.card P) → (∀ S : Subgroup P, S.Normal) → ∀ a b : P, a * b = b * a


variable {G : Type u} [Group G] [Finite G]

/-- If every subgroup of `G` is normal, every subgroup of a subgroup `K`
is normal in `K`. -/
theorem forall_normal_subgroupOf (hall : ∀ S : Subgroup G, S.Normal)
    (K : Subgroup G) : ∀ S : Subgroup K, S.Normal := by
  intro S
  constructor
  intro n hn g
  -- push `S` down to `G`, use normality there, and pull back
  have hmapn : (S.map K.subtype : Subgroup G).Normal := hall _
  have hn' : (n : G) ∈ S.map K.subtype := ⟨n, hn, rfl⟩
  have := hmapn.conj_mem _ hn' (g : G)
  obtain ⟨s, hs, hseq⟩ := this
  have : (⟨(g : G) * (n : G) * (g : G)⁻¹, by
    exact (K.mul_mem (K.mul_mem g.2 n.2) (K.inv_mem g.2))⟩ : K) = s := by
    exact Subtype.ext hseq.symm
  rw [show g * n * g⁻¹ = (⟨(g : G) * (n : G) * (g : G)⁻¹, by
    exact (K.mul_mem (K.mul_mem g.2 n.2) (K.inv_mem g.2))⟩ : K) from rfl, this]
  exact hs

/-- **The reduction, proved.** Granted the `p`-group core, Dedekind's
theorem at odd order follows: all subgroups normal makes every Sylow
normal, hence `G` a direct product of its Sylows, and each Sylow is an
odd `p`-group inheriting the normality hypothesis. -/
theorem dedekindOdd_of_pgroup (hcore : DedekindOddPGroup.{u})
    (hodd : Odd (Nat.card G)) (hall : ∀ S : Subgroup G, S.Normal)
    (a b : G) : a * b = b * a := by
  classical
  -- every Sylow subgroup is normal, so `G` is nilpotent
  have hsyl : ∀ (p : ℕ) (_ : Fact p.Prime) (P : Sylow p G),
      (↑P : Subgroup G).Normal := fun p _ P => hall _
  have hnil : Group.IsNilpotent G :=
    ((Group.isNilpotent_of_finite_tfae (G := G)).out 3 0).mp hsyl
  -- each Sylow is abelian, by the core hypothesis
  have hab : ∀ (p : ℕ) (_ : Fact p.Prime) (P : Sylow p G),
      ∀ x y : (↑P : Subgroup G), x * y = y * x := by
    intro p hp P x y
    have hPodd : Odd (Nat.card (↑P : Subgroup G)) := by
      have hdvd : Nat.card (↑P : Subgroup G) ∣ Nat.card G :=
        Subgroup.card_subgroup_dvd_card _
      obtain ⟨c, hc⟩ := hdvd
      rw [hc] at hodd
      exact (Nat.odd_mul.mp hodd).1
    exact hcore p _ hp.out P.isPGroup' hPodd
      (forall_normal_subgroupOf hall _) x y
  -- a nilpotent group all of whose Sylows are abelian is abelian
  obtain ⟨e⟩ := ((Group.isNilpotent_of_finite_tfae (G := G)).out 0 4).mp hnil
  -- the dependent product of the Sylows is commutative, pointwise
  have hpi : ∀ u v : (∀ p : (Nat.card G).primeFactors, ∀ P : Sylow (p : ℕ) G,
      (↑P : Subgroup G)), u * v = v * u := by
    intro u v
    funext p P
    haveI : Fact (Nat.Prime (p : ℕ)) := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    exact hab (p : ℕ) inferInstance P (u p P) (v p P)
  -- transport along `e`
  have := hpi (e.symm a) (e.symm b)
  have hab' : a * b = b * a := by
    have h1 : e (e.symm a * e.symm b) = a * b := by simp
    have h2 : e (e.symm b * e.symm a) = b * a := by simp
    rw [← h1, ← h2, this]
  exact hab'

/-- **The payoff: the paper's external input shrinks.**

`DRing.OddDedekind` — the hypothesis carried by
`LeanDring/Theory/DRing/MarksAbelianization.lean`, and caveat (iv) of the paper —
follows from the strictly weaker `DedekindOddPGroup`. So what must be
cited is no longer Dedekind's theorem in odd order, but only its
`p`-group case; the reduction between them is formalized above.

The theorem is not proved here, deliberately: it is classical
([Robinson96] 5.3.7) and outside
this paper's contribution, exactly as the classification of groups of
order `p⁴` ([AGW16]), CFSG and Boltje's criterion ([Boltje04]) are. What this file buys is a
smaller citation, not a discharged one. -/
theorem oddDedekind_of_pgroup (hcore : DedekindOddPGroup.{u}) :
    DRing.OddDedekind.{u} :=
  fun _ _ _ hodd hall a b => dedekindOdd_of_pgroup hcore hodd hall a b

end Even

end LeanDring

/-! ## Axiom audit -/

#print axioms LeanDring.Even.forall_normal_subgroupOf
#print axioms LeanDring.Even.dedekindOdd_of_pgroup
#print axioms LeanDring.Even.oddDedekind_of_pgroup
