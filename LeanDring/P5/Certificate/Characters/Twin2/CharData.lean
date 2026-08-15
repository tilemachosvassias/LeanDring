/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.ConjClasses
import LeanDring.P5.Certificate.Characters.Twin1.CharData

/-!
# Linear-character data for the 148 representatives of `Coordinate 2` (q=2)

This is the **q=2 twin** of
`LeanDring.P5.Certificate.Characters.Twin1.CharData`
(SmallGroup(3125,69) vs (3125,68)). The
subgroup-conjugacy *skeleton* is byte-identical to the q=1 twin (`classRepsData`
coincides; the 676 subgroups are the same sets, in the same order), but the pc
**collection relations differ**: q=1 has `f₂⁵ = f₅` whereas q=2 has `f₂⁵ = f₅²`.
This propagates into the certified character data in three graded ways, measured
by the generator `LeanDring.P5.Certificate.Generators.Twin2.GenChar` over all
148 representatives:

* **echelon bases** `repBases2` — differ in **50** reps (the canonical echelon
  form depends on the group law; same subgroup, different pcgs);
* **power relation rows** `powRowsE2` (the `g_i^5` normal forms) — differ in
  **106** reps;
* **commutator rows** `commRowsE2` — differ in **0** reps (byte-identical to q=1:
  the twins share their commutator structure, only the fifth-power map changes);
* **character vector sets** — differ in **34** reps (all with `k ≤ 3` generators:
  `{28…52} ∪ {64,67,73,76,90,95,100,105,110}`); the counts always match.

The linear characters are again modelled as exponent vectors over `ZMod 25` on the
echelon generators, valid because `exp(H^ab) ∣ 25` for every subgroup here (the
group `Coordinate 2` has exponent dividing 25, `mpow25_all` in
`LeanDring.P5.Certificate.Characters.Twin2.CharExp`).

## Twin divergence (this file's headline)

The character **counts** are invariant across the twin
(`Σ_r |H^ab| = 5236`, distribution `{1:1, 5:12, 25:117, 125:18}` of `|H^ab|`,
order-fibres `{1:148, 5:3688, 25:1400}`) — proved by *reusing* the q=1
`charCounts`/`charFibre` (they are literally the same lists). The character
**vector sets** coincide for 114 of the 148 representatives but genuinely
**differ** for 34 of them — the classes
`{28…52} ∪ {64,67,73,76,90,95,100,105,110}` — where the changed power relation
carves out a different (equinumerous) solution set of the `ZMod 25` system. This
is the first layer of the twin construction at which the two groups produce
*different* certified data, not merely relabelled data.

This file certifies the **pilot** (reps 0, 1, 28) under the genuine q=2 checker
`charOK2` and the **aggregate counts**. Rep 28 (cyclic-`C₂₅`-type) is one of the
divergent classes: its q=2 character list `chars28_2` is kernel-checked
`charOK2`-valid and is a *different list* from the q=1 `chars28`.
-/

namespace LeanDring.P5Presentation

namespace Q2

open Fin.NatCast
open LeanDring.P5Presentation (dotZ zc)

set_option maxRecDepth 100000

/-! ## The q=2 exponent-vector character model over `ZMod 25` -/

/-- q=2 pcgs exponents (echelon sift with the q=2 group law `clearStep 2`). -/
def expNat2 (B : List Coordinates) (x : Coordinates) : List Nat :=
  (B.foldl (fun (acc : Coordinates × List Nat) p =>
      (clearStep 2 p acc.1, acc.2 ++ [(coordAt acc.1 (pivotDepth p)).val])) (x, [])).2

/-- The q=2 pcgs exponents as elements of `ZMod 25`. -/
def expVec2 (B : List Coordinates) (x : Coordinates) : List (ZMod 25) :=
  (expNat2 B x).map (fun n => (n : ZMod 25))

/-- **The q=2 collection-relation checker.** `charOK2 B e = true` iff the exponent
vector `e` satisfies every q=2 power relation `Σ e_m a_m = 5 e_i` and every
commutator relation `Σ e_m b_m = 0` of the echelon basis `B` — the pcgs exponents
`a_m, b_m` now read off the **q=2** group law (`mpow 2`, `commutatorC`). -/
def charOK2 (B : List Coordinates) (e : List (ZMod 25)) : Bool :=
  (List.range B.length).all (fun i =>
    decide (dotZ e (expVec2 B (mpow 2 (B.getD i zc) 5)) = 5 * e.getD i 0)) &&
  (List.range B.length).all (fun i =>
    (List.range B.length).all (fun j =>
      !(Nat.blt i j) ||
        decide (dotZ e (expVec2 B (commutatorC (B.getD i zc) (B.getD j zc))) = 0)))

/-- The candidate character exponent of `x` over the q=2 basis. -/
def charForm2 (B : List Coordinates) (e : List (ZMod 25)) (x : Coordinates) : ZMod 25 :=
  dotZ e (expVec2 B x)

/-- **The isolated extension obligation (q=2).** For a `charOK2`-valid vector `e`,
the candidate exponent `charForm2 B e` is additive on `H = ⟨B⟩` (elements sifting
to `1` against `B` under the q=2 group law). From it, `x ↦ ζ₂₅^{f_e(x)}` is a
genuine homomorphism `H →* ℂˣ`. The q=2 twin of `CharExtendsAt`. -/
def CharExtendsAt2 (B : List Coordinates) (e : List (ZMod 25)) : Prop :=
  charOK2 B e = true →
    ∀ x y : Coordinates, siftB 2 B x = true → siftB 2 B y = true →
      charForm2 B e (mulC 2 x y) = charForm2 B e x + charForm2 B e y

/-! ## Pilot: fully kernel-checked q=2 character lists for `reps 0, 1, 28` -/

/-- Echelon basis of `reps 1`. Rep 1 is a **non-divergent** class, so this q=2
echelon basis coincides with the q=1 twin's `B1`. -/
def B1 : List Coordinates := [(0, 0, 1, 4, 4)]

/-- Echelon basis of `reps 28` under the **q=2** group law. Rep 28's echelon basis
is one of the 50 that **differ** from the q=1 twin: here `(0,1,4,4,0)` where the
q=1 twin has `(0,1,4,4,2)` (same subgroup as a set, different echelon form). -/
def B28 : List Coordinates := [(0, 1, 4, 4, 0), (0, 0, 0, 0, 1)]

/-- The single character of the trivial subgroup `reps 0`. -/
def chars0 : List (List (ZMod 25)) := [[]]

/-- The 5 characters of `reps 1`. Rep 1 is a **non-divergent** class, so this list
is byte-identical to the q=1 twin's `chars1`. -/
def chars1 : List (List (ZMod 25)) := [[0], [5], [10], [15], [20]]

/-- The 25 characters of `reps 28` under the **q=2** collection relations. Rep 28
is a **divergent** class: this list differs from the q=1 twin's `chars28`
(same cardinality 25, different vectors) — see `chars28_ne_q1`. -/
def chars28_2 : List (List (ZMod 25)) :=
  [[0,0], [1,15], [2,5], [3,20], [4,10], [5,0], [6,15], [7,5], [8,20], [9,10],
   [10,0], [11,15], [12,5], [13,20], [14,10], [15,0], [16,15], [17,5], [18,20], [19,10],
   [20,0], [21,15], [22,5], [23,20], [24,10]]

-- The pilot bases are exactly the class representatives' echelon bases (`Q2.getB` at
-- the `classRepsData` index), tying the pilot to `reps 1` / `reps 28`, and — since
-- the skeleton is byte-identical — equal to the q=1 twin's `B1`/`B28`.
theorem B1_eq_getB : B1 = getB (classRepsData.getD 1 0) := by decide
theorem B28_eq_getB : B28 = getB (classRepsData.getD 28 0) := by decide
theorem B1_eq_q1 : B1 = LeanDring.P5Presentation.B1 := by decide
/-- Rep 28's echelon basis genuinely differs across the twin (one of 50 such). -/
theorem B28_ne_q1 : B28 ≠ LeanDring.P5Presentation.B28 := by decide

-- Every listed vector is a valid q=2 character (kills all q=2 collection relations).
theorem chars0_valid : chars0.all (charOK2 []) = true := by decide
theorem chars1_valid : chars1.all (charOK2 B1) = true := by decide
theorem chars28_valid : chars28_2.all (charOK2 B28) = true := by decide

-- The character lists are duplicate-free …
theorem chars1_nodup : chars1.Nodup := by decide
theorem chars28_nodup : chars28_2.Nodup := by decide

-- … and have the expected cardinality `|H^ab|`.
theorem chars0_count : chars0.length = 1 := by decide
theorem chars1_count : chars1.length = 5 := by decide
theorem chars28_count : chars28_2.length = 25 := by decide

/-- **Concrete twin divergence, certified.** The q=2 character list of `reps 28`
is not the q=1 character list — the collection relation `f₂⁵ = f₅²` (vs `f₅`)
changes which exponent vectors solve the system, at equal cardinality. -/
theorem chars28_ne_q1 : chars28_2 ≠ LeanDring.P5Presentation.chars28 := by decide

/-- Rep 1 (non-divergent) has the *same* character list in both twins. -/
theorem chars1_eq_q1 : chars1 = LeanDring.P5Presentation.chars1 := by decide

/-! ## Aggregate character-count data (invariant across the twin)

The counts are group-theoretic invariants that coincide for the two twins, so we
*reuse* the q=1 `charCounts`/`charFibre` lists verbatim and restate the totals in
the q=2 namespace. -/

/-- q=2 character counts `= |H^ab|` per representative — identical list to q=1. -/
abbrev charCounts : List Nat := LeanDring.P5Presentation.charCounts
/-- q=2 order-fibres per representative — identical list to q=1. -/
abbrev charFibre : List (Nat × Nat × Nat) := LeanDring.P5Presentation.charFibre

/-- **Headline count.** `Σ_r |H^ab| = 5236` over the 148 q=2 representatives. -/
theorem charCount_total : charCounts.sum = 5236 := LeanDring.P5Presentation.charCount_total

/-- **Fibre split by character order** `{1 : 148, 5 : 3688, 25 : 1400}`. -/
theorem charFibre_totals :
    (charFibre.map (·.1)).sum = 148 ∧
    (charFibre.map (·.2.1)).sum = 3688 ∧
    (charFibre.map (·.2.2)).sum = 1400 :=
  LeanDring.P5Presentation.charFibre_totals

end Q2

end LeanDring.P5Presentation
