/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# The fast entry evaluator — the pure-`ℕ` bridge

A pure-`ℕ` re-expression of the entry exponent, `entryExpFast`, with a
once-proved bridge equating it to the trusted `entryExp`:

`entryExpFast_eq : entryExpFast (e.map ZMod.val) … = entryExp …`.

`entryExpFast` calls the group product `mulC`/`invC` directly and takes the
character dot product in `ℕ`, never entering the `CommRing (ZMod 25)` instance
tower.  Because the fast primitive is proved *equal* to `entryExp`,
`entryCode_eq_species` still governs the species value unchanged, and the
per-column data extractors `colData1`/`colData2` below feed the column
certificates of `Twin1/ColCert.lean`.
-/

set_option linter.style.longLine false

namespace LeanDring.P5Presentation

open scoped BigOperators

/-! ## The pure-`ℕ` dot-product bridge -/

/-- **The core `ℕ`/`ZMod` bridge.** The `val` of a `ZMod 25` dot product equals the
pure-`ℕ` dot product of the two `val`-vectors, reduced `% 25`. One list induction,
`% 25`-congruence at each step. -/
theorem sum_zipWith_val (e w : List (ZMod 25)) :
    ((List.zipWith (· * ·) e w).sum).val
      = (List.zipWith (· * ·) (List.map ZMod.val e) (List.map ZMod.val w)).sum % 25 := by
  induction e generalizing w with
  | nil => simp
  | cons x xs ih =>
      cases w with
      | nil => simp
      | cons y ys =>
          simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons]
          rw [ZMod.val_add, ZMod.val_mul, ih ys]
          conv_rhs => rw [Nat.add_mod]

/-- **The fast entry-exponent function (q = 1).** The group product `mulC`/`invC`
is called directly (no `HMul`/`Inv` instance indirection) and the character dot
product is taken in `ℕ` (`val`-vectors, reduced `% 25` once), never touching the
`CommRing (ZMod 25)` tower. -/
def entryExpFast (eNat : List ℕ) (B : List Coordinates) (h : Coordinate 1)
    {T : Type*} (t : T → Coordinate 1) (i : T) : ℕ :=
  (List.zipWith (· * ·) eNat
    (List.map ZMod.val (expVec B ((t i)⁻¹ * h * (t i))))).sum % 25

/-- **The abstracted fast evaluator for precomputed column data.** -/
def fastCode {ι : Type*} (D : ι → List ℕ) (eNat : List ℕ) (i : ι) : ℕ :=
  (List.zipWith (· * ·) eNat (D i)).sum % 25

/-- **The generic congruence lemma for twin-equal cells.** -/
theorem entry_eq_of_data_eq {ι : Type*} [Fintype ι] {D₁ D₂ : ι → List ℕ} {e₁ e₂ : List ℕ}
    (hD : D₁ = D₂) (he : e₁ = e₂) :
    P5CyclotomicCode.sumPowers (fastCode D₁ e₁) = P5CyclotomicCode.sumPowers (fastCode D₂ e₂) := by
  congr

/-- **The fast/trusted exponent bridge (q = 1).** `entryExpFast (e.map ZMod.val) …`
equals the trusted `entryExp …`, pointwise. Once-proved; used for every cell. -/
theorem entryExpFast_eq (rK : Fin 148) (e : List (ZMod 25)) (h : Coordinate 1)
    {T : Type*} (t : T → Coordinate 1) (i : T) :
    entryExpFast (List.map ZMod.val e) (basisAt rK) h t i = entryExp rK e h t i := by
  unfold entryExpFast entryExp
  rw [charForm, dotZ, sum_zipWith_val]

/-- **Column Data Extractor (q = 1).** The pure-ℕ exponent vector sequence over the transversal. -/
def colData1 (rK : Fin 148) (h : Coordinate 1) {T : Type*} (t : T → Coordinate 1) (i : T) : List ℕ :=
  List.map ZMod.val (expVec (basisAt rK) ((t i)⁻¹ * h * (t i)))

/-- **The Code Bridge (q = 1).** `entryCode` equals `sumPowers (fastCode D e)`. -/
theorem entryCode_eq_fastCode (rK : Fin 148) (e : List (ZMod 25)) (h : Coordinate 1)
    {T : Type*} [Fintype T] (t : T → Coordinate 1) :
    entryCode rK e h t = P5CyclotomicCode.sumPowers (fastCode (colData1 rK h t) (List.map ZMod.val e)) := by
  unfold entryCode
  congr 1
  funext i
  exact (entryExpFast_eq rK e h t i).symm

/-- **The fast entry-exponent function (q = 2).** Same, with the q=2 group law and
q=2 pcgs echelon vector `expVec2`. -/
def entryExpFast2 (eNat : List ℕ) (B : List Coordinates) (h : Coordinate 2)
    {T : Type*} (t : T → Coordinate 2) (i : T) : ℕ :=
  (List.zipWith (· * ·) eNat
    (List.map ZMod.val (Q2.expVec2 B ((t i)⁻¹ * h * (t i))))).sum % 25

/-- **The fast/trusted exponent bridge (q = 2).** -/
theorem entryExpFast2_eq (rK : Fin 148) (e : List (ZMod 25)) (h : Coordinate 2)
    {T : Type*} (t : T → Coordinate 2) (i : T) :
    entryExpFast2 (List.map ZMod.val e) (Q2.basisAt2 rK) h t i = Q2.entryExp2 rK e h t i := by
  unfold entryExpFast2 Q2.entryExp2
  rw [Q2.charForm2, dotZ, sum_zipWith_val]

/-- **Column Data Extractor (q = 2).** -/
def colData2 (rK : Fin 148) (h : Coordinate 2) {T : Type*} (t : T → Coordinate 2) (i : T) : List ℕ :=
  List.map ZMod.val (Q2.expVec2 (Q2.basisAt2 rK) ((t i)⁻¹ * h * (t i)))

/-- **The Code Bridge (q = 2).** -/
theorem entryCode2_eq_fastCode (rK : Fin 148) (e : List (ZMod 25)) (h : Coordinate 2)
    {T : Type*} [Fintype T] (t : T → Coordinate 2) :
    Q2.entryCode rK e h t = P5CyclotomicCode.sumPowers (fastCode (colData2 rK h t) (List.map ZMod.val e)) := by
  unfold Q2.entryCode
  congr 1
  funext i
  exact (entryExpFast2_eq rK e h t i).symm

end LeanDring.P5Presentation
