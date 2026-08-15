/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Even.MullerBound

/-!
# The isolation half of Satz 2.3.4: the trivial pair, done; the rest reduced

**EVEN-ORDER LAYER.** Inside the root module's build closure and audit:
no `sorry`, three standard axioms. The results here are
verified *implications*; their hypotheses are named `Prop`s (see §7.6 of
the paper).

`LeanDring/Even/MullerBound.lean` proves `MullerTrivialBound`.  This file addresses
the remaining half, `MullerIsolation` — Müller's explicit idempotent
formula (2.8) — and gets three things:

* `isolates_trivialPoint` — **[PROVEN]** at the *trivial* pair the
  idempotent formula is not needed: the class of the regular `G`-set,
  `η([G/1]) ∈ D(G)`, isolates `p₀ = mark_⊥ ∘ forget` with value `|G|`.
  All other complex points are species `φ_{H,h}` with `H ≠ ⊥`
  (`OddOrder.everyComplexPointIsSpecies`, kernel-checked in the corpus),
  and those vanish on `η([G/1])`;
* `conductor_trivialPoint` — **[PROVEN, unconditional]**
  `conductor (D(G)) p₀ = |G|`: Müller's Führer of the trivial pair,
  both halves (`≤` from the isolation above, `≥` from
  `dvd_of_isolates_trivialPoint`).  This is the "attained at the trivial
  pair" clause of Satz 2.3.4, now a theorem;
* `MullerConductorBound` — the residual open content of Satz 2.3.4 in its
  weakest form: *no* integer point has conductor exceeding `|G|`.  It is
  implied by `MullerIsolation` (`mullerConductorBound_of_isolation`) and
  suffices for everything: `mullerOrder_eq_card_of_conductorBound`,
  `orderTransfer_of_conductorBound`.

For the isolation statement itself the reduction is to one clean typed
`Prop`:

* `SpeciesIsolation` — **[OPEN formally; Müller formula (2.8)]** for
  every species `φ_{H,h}` some `x ∈ D(G)` takes the value `|G|` there and
  `0` at every other complex point (i.e. `|G| · e_{(H,hH')}` lies in the
  lattice — exactly what (2.8) computes);
* `mullerIsolation_of_speciesIsolation` — **[PROVEN]** with the corpus's
  spectrum theorem `OddOrder.everyComplexPointIsSpecies`, that Prop gives
  `MullerIsolation`, hence `OrderTransfer`
  (`orderTransfer_of_speciesIsolation`).

The idempotent formula (2.8) is *not* formalized here.  What the file
does establish is that (a) the trivial pair is closed without it, and
(b) everything else is one labelled statement about species, with the
point/label translation — where the conjugacy bookkeeping lives —
discharged by the kernel.
-/

set_option linter.unusedFintypeInType false

namespace LeanDring

namespace Even

open MulAction FinGSet MonRing DRing

universe u

/-! ## The trivial pair is isolated, unconditionally -/

section TrivialPair

variable (G : Type u) [Group G] [Fintype G]

/-- The class of the regular `G`-set inside `D(G)`. -/
noncomputable def regularClass : DRing G :=
  MonRing.eta (GrothendieckRing.of (Skel.mk (regularGSet G)))

/-- **[PROVEN] The trivial integer point is isolated with value `|G|`.**
`η([G/1])` has trivial-species value `|G|`, and every other complex point
of `D(G)` is a species `φ_{H,h}` with `H ≠ ⊥`, which sees no fixed point
of the regular `G`-set. -/
theorem isolates_trivialPoint :
    Isolates (trivialPoint G) (regularClass G) (Nat.card G) := by
  set b : BurnsideRing G := GrothendieckRing.of (Skel.mk (regularGSet G)) with hb
  constructor
  · change trivialPoint G (MonRing.eta b) = (Nat.card G : ℤ)
    simp only [trivialPoint, RingHom.coe_comp, Function.comp_apply]
    rw [MonRing.forget_eta, hb, BurnsideRing.mark_of, Skel.mark_mk, fix_bot,
      card_regularGSet, Nat.card_eq_fintype_card]
  · intro q hq
    obtain ⟨H, h, rfl⟩ := OddOrder.everyComplexPointIsSpecies G q
    rcases eq_or_ne H ⊥ with rfl | hH
    · have h1 : h = 1 := Subtype.ext (Subgroup.mem_bot.mp h.2)
      rw [h1] at hq
      exact absurd (complexify_trivialPoint (G := G)).symm hq
    · have hsp := DFunLike.congr_fun (DRing.species_comp_eta H h) b
      simp only [RingHom.coe_comp, Function.comp_apply] at hsp
      change DRing.species H h (MonRing.eta b) = 0
      rw [hsp, hb, BurnsideRing.mark_of, Skel.mark_mk,
        fix_regularGSet_of_ne_bot hH]
      norm_num

/-- **[PROVEN, unconditional] The Führer of the trivial pair is `|G|`** —
Müller's Satz 2.3.3 at `(1,1)`, and the "attained at the trivial pair"
clause of Satz 2.3.4. -/
theorem conductor_trivialPoint :
    conductor (DRing G) (trivialPoint G) = Nat.card G := by
  have hmem : Nat.card G ∈
      {n : ℕ | 0 < n ∧ ∃ x : DRing G, Isolates (trivialPoint G) x n} :=
    ⟨Nat.card_pos, regularClass G, isolates_trivialPoint G⟩
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨Nat.card G, hmem⟩ ?_)
  rintro n ⟨hn, x, hx⟩
  exact Nat.le_of_dvd hn (dvd_of_isolates_trivialPoint x n hx)

end TrivialPair

/-! ## The residual half of Satz 2.3.4 -/

/-- **[OPEN formally — Müller Satz 2.3.3 via formula (2.8)]** No integer
point of `D(G)` has conductor exceeding `|G|`.  This is the weakest form
of the residual content: it is implied by `MullerIsolation` and already
suffices for `mullerOrder (D(G)) = |G|`, because the value `|G|` is
attained (`conductor_trivialPoint`, proven). -/
def MullerConductorBound : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (p : DRing G →+* ℤ),
    conductor (DRing G) p ≤ Nat.card G

theorem mullerConductorBound_of_isolation (hiso : MullerIsolation.{u}) :
    MullerConductorBound.{u} :=
  fun G _ _ p => Nat.sInf_le ⟨Nat.card_pos, hiso G p⟩

/-- **[PROVEN] Satz 2.3.4 from the conductor bound alone** — the lower
half is now a theorem, so only the bound is assumed. -/
theorem mullerOrder_eq_card_of_conductorBound (hbd : MullerConductorBound.{u})
    (G : Type u) [Group G] [Fintype G] :
    mullerOrder (DRing G) = Nat.card G := by
  refine le_antisymm (csSup_le ⟨_, ⟨trivialPoint G, rfl⟩⟩ ?_)
    (le_csSup ⟨Nat.card G, ?_⟩ ⟨trivialPoint G, conductor_trivialPoint G⟩)
  · rintro n ⟨p, rfl⟩
    exact hbd G p
  · rintro n ⟨p, rfl⟩
    exact hbd G p

/-- **[PROVEN] Order transfer from the conductor bound alone.** -/
theorem orderTransfer_of_conductorBound (hbd : MullerConductorBound.{u}) :
    OrderTransfer.{u} := by
  intro G H _ _ _ _ hD
  obtain ⟨Φ⟩ := hD
  rw [← mullerOrder_eq_card_of_conductorBound hbd G,
    ← mullerOrder_eq_card_of_conductorBound hbd H]
  exact mullerOrder_eq_of_ringEquiv Φ

/-! ## The species form of the isolation half -/

/-- **[OPEN formally — Müller formula (2.8)]** Every species of `D(G)` is
isolated with value `|G|`: some `x ∈ D(G)` has `φ_{H,h}(x) = |G|` and is
killed by every other complex point.  (Ring-theoretically: `|G| · e_s`
lies in the lattice, which is what (2.8) computes — the conductor
`(N_G(H,hH'): H')` divides `|G|`.)  Conjugate pairs define the *same*
ring homomorphism, so no conjugacy bookkeeping is needed in this
statement. -/
def SpeciesIsolation : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (H : Subgroup G) (h : H),
    ∃ x : DRing G, DRing.species H h x = (Nat.card G : ℂ) ∧
      ∀ q : DRing G →+* ℂ, q ≠ DRing.species H h → q x = 0

/-- **[PROVEN] `SpeciesIsolation ⟹ MullerIsolation`**, via the corpus's
complex spectrum classification (`OddOrder.everyComplexPointIsSpecies`):
the complexification of an integer point *is* a species, so the two
statements differ only by the point/label translation. -/
theorem mullerIsolation_of_speciesIsolation (hsp : SpeciesIsolation.{u}) :
    MullerIsolation.{u} := by
  intro G _ _ p
  obtain ⟨H, h, hp⟩ := OddOrder.everyComplexPointIsSpecies G (complexify (DRing G) p)
  obtain ⟨x, hval, hkill⟩ := hsp G H h
  refine ⟨x, ?_, fun q hq => hkill q fun hcon => hq ?_⟩
  · have h1 : ((p x : ℤ) : ℂ) = (Nat.card G : ℂ) := by
      have h2 : complexify (DRing G) p x = DRing.species H h x := by rw [hp]
      exact h2.trans hval
    exact_mod_cast h1
  · rw [hcon, ← hp]

/-- **[PROVEN] Order transfer, reduced to formula (2.8).** -/
theorem orderTransfer_of_speciesIsolation (hsp : SpeciesIsolation.{u}) :
    OrderTransfer.{u} :=
  orderTransfer_of_conductorBound
    (mullerConductorBound_of_isolation (mullerIsolation_of_speciesIsolation hsp))

end Even

end LeanDring
