/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Even.Separation

-- Several statements below do not mention the section's `[Fintype _]` /
-- group binders, but their proofs need them for instance synthesis, so the
-- binders cannot be `omit`ted.  The linters' suggested rewrite to `[Finite _]`
-- plus `Fintype.ofFinite` is a genuine refactor, not a cleanup.
set_option linter.unusedFintypeInType false

/-!
# Order transfer: Müller's Satz 2.3.4, formalized as a conductor frame

**EVEN-ORDER LAYER.** Inside the root module's build closure and audit:
no `sorry`, three standard axioms. The results here are
verified *implications*; their hypotheses are named `Prop`s (see §7.6 of
the paper).

Müller (diss. Jena 2008, §2.3) proves that `D(G)` determines `|G|`:
**Satz 2.3.3** computes the conductor (Führer) of the primitive idempotent
`e_{(H,hH')}` as `(N_G(H,hH'): H')`, and **Satz 2.3.4** concludes
`|G| = min { n: n·e_s integral for all species s }` — the maximum
conductor, attained at the trivial pair `(1,1)` where the index is
`(G: 1) = |G|`.

This file formalizes the *frame* of that proof in purely ring-theoretic
terms (no species labels, so transfer along an abstract isomorphism is
unconditional):

* `Isolates p x n` — `x` witnesses the value `n` at the integer point `p`
  while every other complex point kills `x`; ring-theoretically,
  `x = n·e_p` for the primitive idempotent at `p`.
* `conductor p` — the least positive isolated value at `p` (Müller's
  Führer of `e_p`, for rational species).
* `mullerOrder R` — the supremum of the conductors over all integer
  points: Müller's intrinsic description of the group order.
* `mullerOrder_eq_of_ringEquiv` — **[PROVEN]** `mullerOrder` is a ring
  isomorphism invariant.  Pure transfer, no hypotheses.
* `MullerIsolation` — **[OPEN formally; Müller Satz 2.3.3 / formula
  (2.8)]** every integer point of `D(G)` is isolated with value `|G|`
  (the explicit idempotent formula makes `|G|·e_s` integral).
* `MullerTrivialBound` — **[OPEN formally; Müller Satz 2.3.1 = Boltje
  Cor. 2.8, "only if" direction at the trivial pair]** some integer point
  of `D(G)` admits only isolated values divisible by `|G|`.  Hand route
  through the existing corpus: the trivial species is
  `mark_⊥ ∘ forget`; an `x` isolated there has all marks of `forget x`
  vanishing except at the trivial subgroup
  (`species_one_eq_mark_forget`), and Burnside-mark triangularity forces
  `|G| ∣ mark_⊥`.
* `mullerOrder_dring_eq_card` — **[PROVEN]** from the two halves,
  `mullerOrder (D(G)) = |G|`.
* `orderTransfer_of_muller` — **[PROVEN]** hence `OrderTransfer`
  (`LeanDring/Even/Separation.lean`) follows from the two Müller halves.

Nothing here is new mathematics: the two open Props are exactly the two
halves of Müller's §2.3 proof, and filling them (formalizing (2.8) and
the easy direction of the Boltje congruence criterion) closes
`OrderTransfer` outright.
-/


namespace LeanDring

namespace Even

universe u

section Conductor

variable (R : Type u) [CommRing R]

/-- The complexification of an integer point. -/
def complexify (p : R →+* ℤ) : R →+* ℂ := (Int.castRingHom ℂ).comp p

variable {R}

/-- `x` isolates the integer point `p` with value `n`: `p x = n`, and
every complex point other than (the complexification of) `p` kills `x`.
Equivalently `x = n · e_p` for the primitive idempotent supported at
`p`. -/
def Isolates (p : R →+* ℤ) (x : R) (n : ℕ) : Prop :=
  p x = (n : ℤ) ∧ ∀ q : R →+* ℂ, q ≠ complexify R p → q x = 0

variable (R)

/-- The conductor of an integer point: the least positive value isolated
at it (`0` if none).  This is Müller's Führer of the primitive idempotent
`e_p` (Satz 2.3.3: for `p = s_{(H,hH')}` it equals
`(N_G(H,hH'): H')`). -/
noncomputable def conductor (p : R →+* ℤ) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ ∃ x : R, Isolates p x n}

/-- **Müller's intrinsic order** (Satz 2.3.4 = [Mueller2011] Thm. 3.6): the supremum of the
conductors of the integer points. -/
noncomputable def mullerOrder : ℕ :=
  sSup (Set.range fun p : R →+* ℤ => conductor R p)

variable {R}

variable {S : Type u} [CommRing S]

/-- Isolation transports forward along a ring isomorphism. -/
theorem Isolates.map (Φ : R ≃+* S) {p : S →+* ℤ} {x : R} {n : ℕ}
    (h : Isolates (p.comp (Φ : R →+* S)) x n) : Isolates p (Φ x) n := by
  refine ⟨h.1, fun q hq => ?_⟩
  refine h.2 (q.comp (Φ : R →+* S)) fun hcon => hq (RingHom.ext fun s => ?_)
  have h1 := DFunLike.congr_fun hcon (Φ.symm s)
  simpa [complexify] using h1

/-- Isolation transports backward along a ring isomorphism. -/
theorem Isolates.comp_equiv (Φ : R ≃+* S) {p : S →+* ℤ} {y : S} {n : ℕ}
    (h : Isolates p y n) : Isolates (p.comp (Φ : R →+* S)) (Φ.symm y) n := by
  refine ⟨by simpa using h.1, fun q hq => ?_⟩
  have hqS : q.comp (Φ.symm : S →+* R) ≠ complexify S p := by
    intro hcon
    refine hq (RingHom.ext fun r => ?_)
    have h1 := DFunLike.congr_fun hcon (Φ r)
    simpa [complexify] using h1
  simpa using h.2 _ hqS

/-- Conductors correspond along a ring isomorphism. -/
theorem conductor_comp_equiv (Φ : R ≃+* S) (p : S →+* ℤ) :
    conductor R (p.comp (Φ : R →+* S)) = conductor S p := by
  unfold conductor
  congr 1
  ext n
  exact ⟨fun ⟨hn, x, hx⟩ => ⟨hn, Φ x, hx.map Φ⟩,
    fun ⟨hn, y, hy⟩ => ⟨hn, Φ.symm y, hy.comp_equiv Φ⟩⟩

/-- **`mullerOrder` is a ring-isomorphism invariant.**  No hypotheses:
this is the transfer half of Satz 2.3.4. -/
theorem mullerOrder_eq_of_ringEquiv (Φ : R ≃+* S) :
    mullerOrder R = mullerOrder S := by
  unfold mullerOrder
  congr 1
  ext n
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.comp (Φ.symm : S →+* R), conductor_comp_equiv Φ.symm p⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p.comp (Φ : R →+* S), conductor_comp_equiv Φ p⟩

variable (R) in
/-- The number of integer points of conductor `c`.  For `c = 1`, by
Müller's Satz 2.3.3/2.3.7 this counts the conjugacy classes of perfect
self-normalizing subgroups. -/
noncomputable def conductorMultiplicity (c : ℕ) : ℕ :=
  Nat.card {p : R →+* ℤ // conductor R p = c}

/-- **Every conductor multiplicity is a ring-isomorphism invariant.**
This is what turns a difference of conductor multiplicities into a proof
that two D-rings are not isomorphic. -/
theorem conductorMultiplicity_eq_of_ringEquiv (Φ : R ≃+* S) (c : ℕ) :
    conductorMultiplicity R c = conductorMultiplicity S c :=
  Nat.card_congr
    { toFun := fun p => ⟨p.1.comp (Φ.symm : S →+* R),
        by rw [conductor_comp_equiv Φ.symm p.1]; exact p.2⟩
      invFun := fun q => ⟨q.1.comp (Φ : R →+* S),
        by rw [conductor_comp_equiv Φ q.1]; exact q.2⟩
      left_inv := fun p => Subtype.ext (RingHom.ext fun r => by simp)
      right_inv := fun q => Subtype.ext (RingHom.ext fun s => by simp) }

end Conductor

/-- **[OPEN formally — Müller Satz 2.3.3 via formula (2.8)]** Every
integer point of `D(G)` is isolated with value `|G|`: the explicit
primitive-idempotent formula shows `|G| · e_s` lies in the lattice. -/
def MullerIsolation : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∀ p : DRing G →+* ℤ, ∃ x : DRing G, Isolates p x (Nat.card G)

/-- **[OPEN formally — Müller Satz 2.3.1 (Boltje Cor. 2.8), easy
direction, at the trivial pair]** Some integer point of `D(G)` admits
only isolated values divisible by `|G|` — the trivial species, whose
congruence is exactly the Burnside congruence at the trivial subgroup. -/
def MullerTrivialBound : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∃ p : DRing G →+* ℤ, ∀ (x : DRing G) (n : ℕ),
      Isolates p x n → Nat.card G ∣ n

/-- **Satz 2.3.4, assembled**: from the two Müller halves,
`mullerOrder (D(G)) = |G|`. -/
theorem mullerOrder_dring_eq_card
    (hiso : MullerIsolation.{u}) (hbd : MullerTrivialBound.{u})
    (G : Type u) [Group G] [Fintype G] :
    mullerOrder (DRing G) = Nat.card G := by
  have hcard : 0 < Nat.card G := Nat.card_pos
  have hle : ∀ p : DRing G →+* ℤ, conductor (DRing G) p ≤ Nat.card G :=
    fun p => Nat.sInf_le ⟨hcard, hiso G p⟩
  obtain ⟨p₀, hp₀⟩ := hbd G
  have hp₀c : conductor (DRing G) p₀ = Nat.card G := by
    refine le_antisymm (hle p₀) (le_csInf ⟨Nat.card G, hcard, hiso G p₀⟩ ?_)
    rintro n ⟨hn, x, hx⟩
    exact Nat.le_of_dvd hn (hp₀ x n hx)
  refine le_antisymm (csSup_le ⟨_, ⟨p₀, rfl⟩⟩ ?_) (le_csSup ?_ ⟨p₀, hp₀c⟩)
  · rintro n ⟨p, rfl⟩; exact hle p
  · exact ⟨Nat.card G, by rintro n ⟨p, rfl⟩; exact hle p⟩

/-- **Order transfer from Müller's §2.3**, modulo the two typed halves:
`D(G) ≅ D(H) ⟹ |G| = |H|`. -/
theorem orderTransfer_of_muller
    (hiso : MullerIsolation.{u}) (hbd : MullerTrivialBound.{u}) :
    OrderTransfer.{u} := by
  intro G H _ _ _ _ hD
  obtain ⟨Φ⟩ := hD
  rw [← mullerOrder_dring_eq_card hiso hbd G,
    ← mullerOrder_dring_eq_card hiso hbd H]
  exact mullerOrder_eq_of_ringEquiv Φ

end Even

end LeanDring
