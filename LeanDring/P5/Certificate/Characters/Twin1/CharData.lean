/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.ConjugacyClasses.Twin1.ConjClasses
import Mathlib.Data.ZMod.Basic

/-!
# Linear-character data for the 148 subgroup-class representatives

For each conjugacy-class representative `H = reps r` of `Coordinate 1`
(order `5^5`), its **linear characters** `H →* ℂˣ` are modelled as exponent
vectors over `ZMod 25` on the `k` canonical (pcgs) generators
`g_0 … g_{k-1}` of `H`'s `Cgs`: a vector `e` means `χ(g_i) = ζ₂₅^{e_i}`.
This is faithful because `exp(H^ab) ∣ 25` for every subgroup `H` here
(verified: the character count over `ZMod 25` and over `ZMod 125` coincide,
so no abelianization has an element of order `125`).

## The collection-relation checker

A vector `e` defines a homomorphism iff it kills every relation of the pc
*collection* presentation of `H` — read off from `H`'s echelon basis `B`:

* **power** `g_i^5 = ∏_{m>i} g_m^{a_m}`  ⇒  `Σ_m e_m·a_m = 5·e_i`;
* **commutator** `[g_i,g_j] = ∏_m g_m^{b_m}`  ⇒  `Σ_m e_m·b_m = 0`
  (the target `ℂˣ` is abelian, so commutators map to `1`).

Both are **linear** conditions over `ZMod 25` in `e`, encoded by `charOK`.
The pcgs exponents `a_m, b_m` are extracted by `expNat` (the kernel-reducible
echelon sift with exponent tracking).

## What is certified here

* `charOK` — the kernel-cheap Boolean checker (definition).
* **Pilot** (`reps 0, 1, 28`): the emitted character vectors are `charOK`-valid,
  pairwise distinct, and their number equals `|H^ab|` (`1, 5, 25`), all by
  kernel `decide`. `reps 28` is the cyclic `C₂₅` case (a character of order 25).
* **Full certification for all 148 reps** lives in
  `LeanDring.P5.Certificate.Characters.Twin1.CharAssembly` (data + fast
  row-checker in `…Twin1.CharCert`, sift-heavy decides chunked across
  `…Twin1.CharRows.Chunk01`–`Chunk04`, `…Twin1.CharBasis.Chunk01`–`Chunk04`,
  `…Twin1.CharValid`, `…Twin1.CharNodup` and `…Twin1.CharCount`):
  for every `r : Fin 148`, `charsAt r` is `charOK`-valid (`charsAt_valid`),
  duplicate-free (`charsAt_nodup`), of length `charCounts r` (`charsAt_count`),
  over the genuine echelon basis of `reps r` (`basisAt_eq`); and the total
  `5236` is rederived from these certified counts (`charsTotal_certified`).
* **Aggregate data** `charCounts` / `charFibre` (148 entries, generator-emitted
  and re-checked here): `Σ = 5236 = Σ_r |H^ab|`, split by character order
  `{1 : 148, 5 : 3688, 25 : 1400}`; per-entry `o₁ = 1` (the trivial character)
  and `o₁+o₅+o₂₅ = |H^ab|`.

## The one isolated obligation (`CharExtendsAt`)

That a `charOK`-valid vector actually *extends* to a homomorphism
`H →* ℂˣ` — the pc-presentation "abelianized-relators ⇒ well-defined character"
step — is stated precisely as `CharExtendsAt` here and discharged in
`LeanDring.P5.Certificate.Characters.Twin1.CharExtend` (its converse, every hom
restricts to a `charOK` vector, is elementary). Combined with
`LeanDring.DRing.card_charHom_eq_card_abelianization` (`|Hom(H,ℂˣ)| = |H^ab|`)
it upgrades the pilot/aggregate counts to the character count. GAP cross-check:
`Σ_r |H^ab| = 5236`; the order-1 (148) and order-25 (1400) fibres coincide with
the pair-class fibres, while order-5 (3688) collapses to 1176 under the
normalizer action on characters.
-/

namespace LeanDring.P5Presentation

open Fin.NatCast

-- emitted data literals; lines are machine-generated
set_option linter.style.longLine false
set_option maxRecDepth 100000

/-- The identity coordinate. -/
def zc : Coordinates := (0, 0, 0, 0, 0)

/-! ## The exponent-vector character model over `ZMod 25` -/

/-- pcgs exponents (one `ℕ` per pivot of the echelon basis `B`) of `x`:
the exponent of `g_m` in the normal form of `x` against `B`. -/
def expNat (B : List Coordinates) (x : Coordinates) : List Nat :=
  (B.foldl (fun (acc : Coordinates × List Nat) p =>
      (clearStep 1 p acc.1, acc.2 ++ [(coordAt acc.1 (pivotDepth p)).val])) (x, [])).2

/-- The pcgs exponents as elements of `ZMod 25`. -/
def expVec (B : List Coordinates) (x : Coordinates) : List (ZMod 25) :=
  (expNat B x).map (fun n => (n : ZMod 25))

/-- Dot product over `ZMod 25`. -/
def dotZ (e v : List (ZMod 25)) : ZMod 25 := (e.zipWith (· * ·) v).sum

/-- **The collection-relation checker.** `charOK B e = true` iff the exponent
vector `e` (length `= B.length`) satisfies every power relation
`Σ e_m a_m = 5 e_i` and every commutator relation `Σ e_m b_m = 0` of the
echelon basis `B`. Kernel-decidable: only `ZMod 25` arithmetic and the
exponent sift. -/
def charOK (B : List Coordinates) (e : List (ZMod 25)) : Bool :=
  (List.range B.length).all (fun i =>
    decide (dotZ e (expVec B (mpow 1 (B.getD i zc) 5)) = 5 * e.getD i 0)) &&
  (List.range B.length).all (fun i =>
    (List.range B.length).all (fun j =>
      !(Nat.blt i j) ||
        decide (dotZ e (expVec B (commutatorC (B.getD i zc) (B.getD j zc))) = 0)))

/-! ## The isolated extension obligation

The lone group-theoretic step of the character count: a `charOK`-valid exponent
vector really defines a homomorphism. Stated per representative `H = reps r`
with basis `B` (see the module header). -/

/-- The candidate character exponent of `x`: the `ZMod 25` value `f_e(x)` with
`χ(x) = ζ₂₅^{f_e(x)}`, read off the pcgs exponents of `x` against `B`. -/
def charForm (B : List Coordinates) (e : List (ZMod 25)) (x : Coordinates) : ZMod 25 :=
  dotZ e (expVec B x)

/-- **The isolated extension obligation.** For a `charOK`-valid vector `e`, the
candidate exponent `charForm B e` is *additive* on the subgroup `H = ⟨B⟩`
(elements sifting to `1` against `B`): `f_e(x·y) = f_e(x) + f_e(y)`. This is
precisely the pc-collection "abelianized relators ⇒ well-defined character"
step; from it, `x ↦ ζ₂₅^{f_e(x)}` is a genuine homomorphism `H →* ℂˣ`, and
(with `card_charHom_eq_card_abelianization`) the `charOK`-valid vectors biject
with `H →* ℂˣ`. Its converse — a homomorphism restricts to a `charOK` vector —
is elementary. Discharged in
`LeanDring.P5.Certificate.Characters.Twin1.CharExtend`. -/
def CharExtendsAt (B : List Coordinates) (e : List (ZMod 25)) : Prop :=
  charOK B e = true →
    ∀ x y : Coordinates, siftB 1 B x = true → siftB 1 B y = true →
      charForm B e (mulC 1 x y) = charForm B e x + charForm B e y

/-! ## Pilot: fully kernel-checked character lists for `reps 0, 1, 28` -/

/-- Echelon basis of `reps 1` (the cyclic `C₅` representative, `|H^ab| = 5`). -/
def B1 : List Coordinates := [(0, 0, 1, 4, 4)]

/-- Echelon basis of `reps 28` (the cyclic `C₂₅` representative, `|H^ab| = 25`). -/
def B28 : List Coordinates := [(0, 1, 4, 4, 2), (0, 0, 0, 0, 1)]

/-- The 5 characters of `reps 1` as `ZMod 25` exponent vectors. -/
def chars1 : List (List (ZMod 25)) := [[0], [5], [10], [15], [20]]

/-- The 25 characters of `reps 28` as `ZMod 25` exponent vectors. -/
def chars28 : List (List (ZMod 25)) :=
  [[0,0],[5,0],[10,0],[15,0],[20,0],[1,5],[6,5],[11,5],[16,5],[21,5],
   [2,10],[7,10],[12,10],[17,10],[22,10],[3,15],[8,15],[13,15],[18,15],[23,15],
   [4,20],[9,20],[14,20],[19,20],[24,20]]

/-- The single character of the trivial subgroup `reps 0`. -/
def chars0 : List (List (ZMod 25)) := [[]]

-- The embedded pilot bases are exactly the class representatives' echelon bases
-- (`getB` at the `classRepsData` index), tying the pilot to `reps 1` / `reps 28`.
theorem B1_eq_getB : B1 = getB (classRepsData.getD 1 0) := by decide
theorem B28_eq_getB : B28 = getB (classRepsData.getD 28 0) := by decide

-- Every listed vector is a valid character (kills all collection relations).
theorem chars0_valid : chars0.all (charOK []) = true := by decide
theorem chars1_valid : chars1.all (charOK B1) = true := by decide
theorem chars28_valid : chars28.all (charOK B28) = true := by decide

-- The character lists are duplicate-free …
theorem chars1_nodup : chars1.Nodup := by decide
theorem chars28_nodup : chars28.Nodup := by decide

-- … and have the expected cardinality `|H^ab|`.
theorem chars0_count : chars0.length = 1 := by decide
theorem chars1_count : chars1.length = 5 := by decide
theorem chars28_count : chars28.length = 25 := by decide

/-! ## Aggregate character-count data for all 148 representatives

Generator-emitted (compiled `#eval`, untrusted), re-checked here as certified
arithmetic facts. Entry `r` is indexed by `classRepsData` order. -/

/-- `charCounts r = |H^ab|` for `H = reps r` (`= #` linear characters). -/
def charCounts : List Nat := [1, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 125, 25, 25, 125, 25, 25, 25, 25, 25, 125, 25, 25, 125, 25, 25, 25, 125, 25, 25, 25, 25, 125, 25, 25, 25, 25, 125, 25, 25, 25, 25, 125, 25, 25, 25, 25, 125, 25, 25, 25, 25, 125, 25, 25, 25, 25, 125, 25, 25, 25, 25, 25, 125, 125, 125, 125, 125, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 125, 25, 25, 25, 25, 25, 125]

/-- `charFibre r = (o₁, o₅, o₂₅)`: characters of `reps r` by their order. -/
def charFibre : List (Nat × Nat × Nat) := [(1,0,0), (1,4,0), (1,4,0), (1,4,0), (1,4,0), (1,4,0), (1,4,0), (1,4,0), (1,4,0), (1,4,0), (1,4,0), (1,4,0), (1,4,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,4,20), (1,4,20), (1,4,20), (1,4,20), (1,4,20), (1,4,20), (1,4,20), (1,4,20), (1,4,20), (1,4,20), (1,4,20), (1,4,20), (1,4,20), (1,4,20), (1,4,20), (1,4,20), (1,4,20), (1,4,20), (1,4,20), (1,4,20), (1,4,20), (1,4,20), (1,4,20), (1,4,20), (1,4,20), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,100), (1,24,0), (1,24,0), (1,24,100), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,100), (1,24,0), (1,24,0), (1,24,100), (1,24,0), (1,24,0), (1,24,0), (1,124,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,124,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,100), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,100), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,100), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,100), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,100), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,124,0), (1,124,0), (1,124,0), (1,124,0), (1,124,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,124,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,24,0), (1,124,0)]

theorem charCounts_length : charCounts.length = 148 := by decide
theorem charFibre_length : charFibre.length = 148 := by decide

/-- **Headline count.** `Σ_r |H^ab| = 5236` over the 148 representatives. -/
theorem charCount_total : charCounts.sum = 5236 := by decide

/-- The fibre triples sum entrywise to the count of each representative, and the
first component is always `1` (the trivial character). -/
theorem charFibre_consistent :
    (charCounts.zip charFibre).all
      (fun p => decide (p.2.1 = 1) && decide (p.2.1 + p.2.2.1 + p.2.2.2 = p.1)) = true := by
  decide

/-- **Fibre split by character order.** `{order 1 : 148, 5 : 3688, 25 : 1400}`;
the three total `5236`, cross-checking `charCount_total`. -/
theorem charFibre_totals :
    (charFibre.map (·.1)).sum = 148 ∧
    (charFibre.map (·.2.1)).sum = 3688 ∧
    (charFibre.map (·.2.2)).sum = 1400 := by
  refine ⟨by decide, by decide, by decide⟩

end LeanDring.P5Presentation
