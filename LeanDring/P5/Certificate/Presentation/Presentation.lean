/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Compact presentations for the order-`5^5` pair

The two groups compared by the certificate share a five-generator power-commutator
presentation, taken from GAP's `SmallGroup(3125,68)` and `SmallGroup(3125,69)`.
The two differ in a single exponent: the relation `f₁^5 = f₄^q` (zero-based
generator indices) has `q = 1` for the first group and `q = 2` for the second.
`relator` lists the fifteen power and conjugation relators, and `Group q` is the
resulting presented group.

`normalForm` sends a five-tuple of `Fin 5` coordinates to the collected word
`f₁^a f₂^b f₃^c f₄^d f₅^e`.  The main result is `normalForm_bijective`: for
`q = 1, 2` these 3125 collected words are exactly the elements of `Group q`,
each occurring once.  Surjectivity follows from the five collection identities
`normalForm_step` by induction on free words; injectivity from the right action
of `Group q` on the coordinate space, under which the collected word for `x`
carries the zero coordinate back to `x`.
-/

namespace LeanDring.P5Presentation

/-- Names of the five pc generators. -/
abbrev Gen := Fin 5

private def w (i : Gen) : FreeGroup Gen := FreeGroup.of i

private def equation (lhs rhs : FreeGroup Gen) : FreeGroup Gen :=
  lhs * rhs⁻¹

private def conjugate (x y : FreeGroup Gen) : FreeGroup Gen :=
  y⁻¹ * x * y

/-- The fifteen power/conjugation relations in the pc presentation. -/
inductive RelatorTag
  | pow0 | pow1 | pow2 | pow3 | pow4
  | conj01 | conj02 | conj03 | conj04
  | conj12 | conj13 | conj14
  | conj23 | conj24 | conj34
  deriving DecidableEq

/-- Relator word associated to a presentation parameter `q`.  Generator
indices are zero-based: GAP's exceptional relation `f₂^5 = f₅^q` is
`w 1 ^ 5 = w 4 ^ q` here. -/
def relator (q : ℕ) : RelatorTag → FreeGroup Gen
  | .pow0 => equation (w 0 ^ 5) 1
  | .pow1 => equation (w 1 ^ 5) (w 4 ^ q)
  | .pow2 => equation (w 2 ^ 5) 1
  | .pow3 => equation (w 3 ^ 5) 1
  | .pow4 => equation (w 4 ^ 5) 1
  | .conj01 => equation (conjugate (w 0) (w 1)) (w 0 * (w 3)⁻¹)
  | .conj02 => equation (conjugate (w 0) (w 2)) (w 0)
  | .conj03 => equation (conjugate (w 0) (w 3)) (w 0 * (w 4)⁻¹)
  | .conj04 => equation (conjugate (w 0) (w 4)) (w 0)
  | .conj12 => equation (conjugate (w 1) (w 2)) (w 1 * (w 4)⁻¹)
  | .conj13 => equation (conjugate (w 1) (w 3)) (w 1)
  | .conj14 => equation (conjugate (w 1) (w 4)) (w 1)
  | .conj23 => equation (conjugate (w 2) (w 3)) (w 2)
  | .conj24 => equation (conjugate (w 2) (w 4)) (w 2)
  | .conj34 => equation (conjugate (w 3) (w 4)) (w 3)

/-- The finite set of relators for parameter `q`. -/
def relations (q : ℕ) : Set (FreeGroup Gen) := Set.range (relator q)

/-- Abstract group with the extracted pc presentation. -/
abbrev Group (q : ℕ) := PresentedGroup (relations q)

/-- Image of the `i`th pc generator in the presented group. -/
def gen (q : ℕ) (i : Gen) : Group q := PresentedGroup.of i

/-- Coordinates for the pc normal form.  This type has exactly `5^5 = 3125`
elements, and `normalForm_bijective` shows `normalForm` below is a bijection
onto `Group q` for `q = 1, 2`. -/
abbrev Coordinates := Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5

/-- The ordered pc word `f₁^a f₂^b f₃^c f₄^d f₅^e`. -/
def normalForm (q : ℕ) (x : Coordinates) : Group q :=
  gen q 0 ^ (x.1 : ℕ) *
  gen q 1 ^ (x.2.1 : ℕ) *
  gen q 2 ^ (x.2.2.1 : ℕ) *
  gen q 3 ^ (x.2.2.2.1 : ℕ) *
  gen q 4 ^ (x.2.2.2.2 : ℕ)

/-- The candidate normal-form coordinate space has the target cardinality. -/
theorem card_coordinates : Fintype.card Coordinates = 3125 := by
  norm_num [Coordinates, Fintype.card_prod]

theorem normalForm_zero (q : ℕ) :
    normalForm q (0, 0, 0, 0, 0) = 1 := by
  simp [normalForm]

private def coord (a b c d e : Fin 5) : Coordinates := (a, b, c, d, e)

private def mod5 (q : ℕ) : Fin 5 := ⟨q % 5, Nat.mod_lt _ (by norm_num)⟩

@[simp] private theorem five_nsmul_fin5 (x : Fin 5) : 5 • x = 0 := by
  fin_cases x <;> decide

@[simp] private theorem five_zsmul_fin5 (x : Fin 5) : (5 : ℤ) • x = 0 := by
  fin_cases x <;> decide

@[simp] private theorem ten_zsmul_fin5 (x : Fin 5) : (10 : ℤ) • x = 0 := by
  fin_cases x <;> decide

/-- Collected coordinates after right multiplication by one pc generator.
`normalForm_step` proves that these five formulas agree with multiplication in
the presented group. -/
def step (q : ℕ) : Gen → Coordinates → Coordinates
  | 0, (a, b, c, d, e) => coord (a + 1) b c (d + b) (e + d)
  | 1, (a, b, c, d, e) =>
      coord a (b + 1) c d (e + c + if b = 4 then mod5 q else 0)
  | 2, (a, b, c, d, e) => coord a b (c + 1) d e
  | 3, (a, b, c, d, e) => coord a b c (d + 1) e
  | 4, (a, b, c, d, e) => coord a b c d (e + 1)

/-- Explicit inverse collection step. -/
def stepInv (q : ℕ) : Gen → Coordinates → Coordinates
  | 0, (a, b, c, d', e') =>
      let d := d' - b
      coord (a - 1) b c d (e' - d)
  | 1, (a, b', c, d, e') =>
      let b := b' - 1
      coord a b c d (e' - c - if b = 4 then mod5 q else 0)
  | 2, (a, b, c, d, e) => coord a b (c - 1) d e
  | 3, (a, b, c, d, e) => coord a b c (d - 1) e
  | 4, (a, b, c, d, e) => coord a b c d (e - 1)

theorem stepInv_step (q : ℕ) (i : Gen) (x : Coordinates) :
    stepInv q i (step q i x) = x := by
  fin_cases i <;> rcases x with ⟨a, b, c, d, e⟩ <;>
    simp [step, stepInv, coord]
  all_goals abel

theorem step_stepInv (q : ℕ) (i : Gen) (x : Coordinates) :
    step q i (stepInv q i x) = x := by
  fin_cases i <;> rcases x with ⟨a, b, c, d, e⟩ <;>
    simp [step, stepInv, coord]
  all_goals abel_nf

/-- Right multiplication by each generator is an executable permutation of
the 3125 candidate normal forms. -/
def stepEquiv (q : ℕ) (i : Gen) : Coordinates ≃ Coordinates where
  toFun := step q i
  invFun := stepInv q i
  left_inv := stepInv_step q i
  right_inv := step_stepInv q i

/-- Every listed relator holds in the presented group by construction. -/
theorem relator_eq_one (q : ℕ) (t : RelatorTag) :
    PresentedGroup.mk (relations q) (relator q t) = 1 := by
  exact PresentedGroup.one_of_mem ⟨t, rfl⟩

private theorem equation_holds (q : ℕ) (t : RelatorTag)
    (lhs rhs : FreeGroup Gen) (h : relator q t = equation lhs rhs) :
    PresentedGroup.mk (relations q) lhs = PresentedGroup.mk (relations q) rhs := by
  apply PresentedGroup.mk_eq_mk_of_mul_inv_mem
  exact ⟨t, h⟩

theorem gen_pow_five (q : ℕ) :
    gen q 0 ^ 5 = 1 ∧ gen q 1 ^ 5 = gen q 4 ^ q ∧
    gen q 2 ^ 5 = 1 ∧ gen q 3 ^ 5 = 1 ∧ gen q 4 ^ 5 = 1 := by
  constructor
  · exact equation_holds q .pow0 _ _ rfl
  constructor
  · exact equation_holds q .pow1 _ _ rfl
  constructor
  · exact equation_holds q .pow2 _ _ rfl
  constructor
  · exact equation_holds q .pow3 _ _ rfl
  · exact equation_holds q .pow4 _ _ rfl

theorem gen_conjugates (q : ℕ) :
    (gen q 1)⁻¹ * gen q 0 * gen q 1 = gen q 0 * (gen q 3)⁻¹ ∧
    (gen q 2)⁻¹ * gen q 0 * gen q 2 = gen q 0 ∧
    (gen q 3)⁻¹ * gen q 0 * gen q 3 = gen q 0 * (gen q 4)⁻¹ ∧
    (gen q 4)⁻¹ * gen q 0 * gen q 4 = gen q 0 ∧
    (gen q 2)⁻¹ * gen q 1 * gen q 2 = gen q 1 * (gen q 4)⁻¹ ∧
    (gen q 3)⁻¹ * gen q 1 * gen q 3 = gen q 1 ∧
    (gen q 4)⁻¹ * gen q 1 * gen q 4 = gen q 1 ∧
    (gen q 3)⁻¹ * gen q 2 * gen q 3 = gen q 2 ∧
    (gen q 4)⁻¹ * gen q 2 * gen q 4 = gen q 2 ∧
    (gen q 4)⁻¹ * gen q 3 * gen q 4 = gen q 3 := by
  constructor
  · exact equation_holds q .conj01 _ _ rfl
  constructor
  · exact equation_holds q .conj02 _ _ rfl
  constructor
  · exact equation_holds q .conj03 _ _ rfl
  constructor
  · exact equation_holds q .conj04 _ _ rfl
  constructor
  · exact equation_holds q .conj12 _ _ rfl
  constructor
  · exact equation_holds q .conj13 _ _ rfl
  constructor
  · exact equation_holds q .conj14 _ _ rfl
  constructor
  · exact equation_holds q .conj23 _ _ rfl
  constructor
  · exact equation_holds q .conj24 _ _ rfl
  · exact equation_holds q .conj34 _ _ rfl

private theorem commute_of_inv_mul_mul_eq {A : Type*} [_root_.Group A] {a b : A}
    (h : b⁻¹ * a * b = a) : Commute a b := by
  rw [commute_iff_eq]
  calc
    a * b = b * (b⁻¹ * a * b) := by group
    _ = b * a := by rw [h]

private theorem commute_34 (q : ℕ) : Commute (gen q 3) (gen q 4) :=
  commute_of_inv_mul_mul_eq (gen_conjugates q).2.2.2.2.2.2.2.2.2

private theorem commute_24 (q : ℕ) : Commute (gen q 2) (gen q 4) :=
  commute_of_inv_mul_mul_eq (gen_conjugates q).2.2.2.2.2.2.2.2.1

private theorem commute_23 (q : ℕ) : Commute (gen q 2) (gen q 3) :=
  commute_of_inv_mul_mul_eq (gen_conjugates q).2.2.2.2.2.2.2.1

private theorem commute_14 (q : ℕ) : Commute (gen q 1) (gen q 4) :=
  commute_of_inv_mul_mul_eq (gen_conjugates q).2.2.2.2.2.2.1

private theorem commute_13 (q : ℕ) : Commute (gen q 1) (gen q 3) :=
  commute_of_inv_mul_mul_eq (gen_conjugates q).2.2.2.2.2.1

private theorem commute_04 (q : ℕ) : Commute (gen q 0) (gen q 4) :=
  commute_of_inv_mul_mul_eq (gen_conjugates q).2.2.2.1

private theorem commute_02 (q : ℕ) : Commute (gen q 0) (gen q 2) :=
  commute_of_inv_mul_mul_eq (gen_conjugates q).2.1

private theorem gen3_pow_fin_add (q : ℕ) (a b : Fin 5) :
    gen q 3 ^ ((a + b : Fin 5) : ℕ) =
      gen q 3 ^ (a : ℕ) * gen q 3 ^ (b : ℕ) := by
  rw [← pow_add, pow_eq_pow_mod (a.val + b.val) (gen_pow_five q).2.2.2.1]
  rfl

private theorem gen4_pow_fin_add (q : ℕ) (a b : Fin 5) :
    gen q 4 ^ ((a + b : Fin 5) : ℕ) =
      gen q 4 ^ (a : ℕ) * gen q 4 ^ (b : ℕ) := by
  rw [← pow_add, pow_eq_pow_mod (a.val + b.val) (gen_pow_five q).2.2.2.2]
  rfl

private theorem gen4_pow_fin_add_q (q : ℕ) (a b : Fin 5) :
    gen q 4 ^ ((a + b + mod5 q : Fin 5) : ℕ) =
      gen q 4 ^ q * (gen q 4 ^ (a : ℕ) * gen q 4 ^ (b : ℕ)) := by
  rw [← pow_add, ← pow_add,
    pow_eq_pow_mod (q + (a.val + b.val)) (gen_pow_five q).2.2.2.2]
  congr 1
  simp [mod5, Fin.add_def, Nat.add_mod, add_comm]

private theorem move_one_across_two (q n : ℕ) :
    gen q 2 ^ n * gen q 1 = gen q 1 * gen q 2 ^ n * gen q 4 ^ n := by
  have hconj := (gen_conjugates q).2.2.2.2.1
  have hyz : gen q 1 * gen q 2 =
      gen q 2 * gen q 1 * (gen q 4)⁻¹ := by
    calc
      gen q 1 * gen q 2 = gen q 2 * ((gen q 2)⁻¹ * gen q 1 * gen q 2) := by group
      _ = gen q 2 * (gen q 1 * (gen q 4)⁻¹) := by rw [hconj]
      _ = _ := by group
  have hzy : gen q 2 * gen q 1 = gen q 1 * gen q 2 * gen q 4 := by
    calc
      gen q 2 * gen q 1 = (gen q 2 * gen q 1 * (gen q 4)⁻¹) * gen q 4 := by group
      _ = (gen q 1 * gen q 2) * gen q 4 := by rw [← hyz]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      calc
        gen q 2 ^ n * gen q 2 * gen q 1 =
            gen q 2 ^ n * (gen q 2 * gen q 1) := mul_assoc _ _ _
        _ = gen q 2 ^ n * (gen q 1 * gen q 2 * gen q 4) := by rw [hzy]
        _ = (gen q 2 ^ n * gen q 1) * gen q 2 * gen q 4 := by group
        _ = (gen q 1 * gen q 2 ^ n * gen q 4 ^ n) * gen q 2 * gen q 4 := by rw [ih]
        _ = gen q 1 * (gen q 2 ^ n * gen q 2) *
            (gen q 4 ^ n * gen q 4) := by
              calc
                _ = gen q 1 * gen q 2 ^ n *
                    (gen q 4 ^ n * gen q 2) * gen q 4 := by group
                _ = gen q 1 * gen q 2 ^ n *
                    (gen q 2 * gen q 4 ^ n) * gen q 4 := by
                      rw [((commute_24 q).symm.pow_left n).eq]
                _ = _ := by group

private theorem move_zero_across_three (q n : ℕ) :
    gen q 3 ^ n * gen q 0 = gen q 0 * gen q 3 ^ n * gen q 4 ^ n := by
  have hconj := (gen_conjugates q).2.2.1
  have hux : gen q 3 * gen q 0 = gen q 0 * gen q 3 * gen q 4 := by
    have hxu : gen q 0 * gen q 3 =
        gen q 3 * gen q 0 * (gen q 4)⁻¹ := by
      calc
        gen q 0 * gen q 3 = gen q 3 * ((gen q 3)⁻¹ * gen q 0 * gen q 3) := by group
        _ = gen q 3 * (gen q 0 * (gen q 4)⁻¹) := by rw [hconj]
        _ = _ := by group
    calc
      gen q 3 * gen q 0 = (gen q 3 * gen q 0 * (gen q 4)⁻¹) * gen q 4 := by group
      _ = (gen q 0 * gen q 3) * gen q 4 := by rw [← hxu]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      calc
        gen q 3 ^ n * gen q 3 * gen q 0 =
            gen q 3 ^ n * (gen q 3 * gen q 0) := mul_assoc _ _ _
        _ = gen q 3 ^ n * (gen q 0 * gen q 3 * gen q 4) := by rw [hux]
        _ = (gen q 3 ^ n * gen q 0) * gen q 3 * gen q 4 := by group
        _ = (gen q 0 * gen q 3 ^ n * gen q 4 ^ n) * gen q 3 * gen q 4 := by rw [ih]
        _ = gen q 0 * (gen q 3 ^ n * gen q 3) *
            (gen q 4 ^ n * gen q 4) := by
              have hc : gen q 4 ^ n * gen q 3 = gen q 3 * gen q 4 ^ n :=
                ((commute_34 q).symm.pow_left n).eq
              calc
                _ = gen q 0 * gen q 3 ^ n * (gen q 4 ^ n * gen q 3) * gen q 4 := by group
                _ = gen q 0 * gen q 3 ^ n * (gen q 3 * gen q 4 ^ n) * gen q 4 := by rw [hc]
                _ = _ := by group

private theorem move_zero_across_one (q n : ℕ) :
    gen q 1 ^ n * gen q 0 = gen q 0 * gen q 1 ^ n * gen q 3 ^ n := by
  have hconj := (gen_conjugates q).1
  have hyx : gen q 1 * gen q 0 = gen q 0 * gen q 1 * gen q 3 := by
    have hxy : gen q 0 * gen q 1 =
        gen q 1 * gen q 0 * (gen q 3)⁻¹ := by
      calc
        gen q 0 * gen q 1 = gen q 1 * ((gen q 1)⁻¹ * gen q 0 * gen q 1) := by group
        _ = gen q 1 * (gen q 0 * (gen q 3)⁻¹) := by rw [hconj]
        _ = _ := by group
    calc
      gen q 1 * gen q 0 = (gen q 1 * gen q 0 * (gen q 3)⁻¹) * gen q 3 := by group
      _ = (gen q 0 * gen q 1) * gen q 3 := by rw [← hxy]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      calc
        gen q 1 ^ n * gen q 1 * gen q 0 =
            gen q 1 ^ n * (gen q 1 * gen q 0) := mul_assoc _ _ _
        _ = gen q 1 ^ n * (gen q 0 * gen q 1 * gen q 3) := by rw [hyx]
        _ = (gen q 1 ^ n * gen q 0) * gen q 1 * gen q 3 := by group
        _ = (gen q 0 * gen q 1 ^ n * gen q 3 ^ n) * gen q 1 * gen q 3 := by rw [ih]
        _ = gen q 0 * (gen q 1 ^ n * gen q 1) *
            (gen q 3 ^ n * gen q 3) := by
              have hc : gen q 3 ^ n * gen q 1 = gen q 1 * gen q 3 ^ n :=
                ((commute_13 q).symm.pow_left n).eq
              calc
                _ = gen q 0 * gen q 1 ^ n * (gen q 3 ^ n * gen q 1) * gen q 3 := by group
                _ = gen q 0 * gen q 1 ^ n * (gen q 1 * gen q 3 ^ n) * gen q 3 := by rw [hc]
                _ = _ := by group

theorem normalForm_step_four (q : ℕ) (x : Coordinates) :
    normalForm q (step q 4 x) = normalForm q x * gen q 4 := by
  rcases x with ⟨a, b, c, d, e⟩
  fin_cases e
  · simp [normalForm, step, coord]
  · simp [normalForm, step, coord, pow_succ, mul_assoc]
  · simp [normalForm, step, coord, pow_succ, mul_assoc]
  · simp [normalForm, step, coord, pow_succ, mul_assoc]
  · change normalForm q (a, b, c, d, 0) =
      normalForm q (a, b, c, d, 4) * gen q 4
    simp only [normalForm, Fin.val_zero, pow_zero, mul_one]
    norm_num
    let P := gen q 0 ^ (a : ℕ) * gen q 1 ^ (b : ℕ) *
      gen q 2 ^ (c : ℕ) * gen q 3 ^ (d : ℕ)
    change P = P * gen q 4 ^ 4 * gen q 4
    rw [mul_assoc P]
    rw [← pow_succ, (gen_pow_five q).2.2.2.2, mul_one]

theorem normalForm_step_three (q : ℕ) (x : Coordinates) :
    normalForm q (step q 3 x) = normalForm q x * gen q 3 := by
  rcases x with ⟨a, b, c, d, e⟩
  have hc : gen q 4 ^ (e : ℕ) * gen q 3 =
      gen q 3 * gen q 4 ^ (e : ℕ) :=
    ((commute_34 q).symm.pow_left (e : ℕ)).eq
  fin_cases d
  · simp [normalForm, step, coord, hc, mul_assoc]
  · simp [normalForm, step, coord, hc, pow_succ, mul_assoc]
  · simp [normalForm, step, coord, hc, pow_succ, mul_assoc]
  · simp [normalForm, step, coord, hc, pow_succ, mul_assoc]
  · change normalForm q (a, b, c, 0, e) =
      normalForm q (a, b, c, 4, e) * gen q 3
    simp only [normalForm, Fin.val_zero, pow_zero, mul_one]
    norm_num
    let P := gen q 0 ^ (a : ℕ) * gen q 1 ^ (b : ℕ) * gen q 2 ^ (c : ℕ)
    change P * gen q 4 ^ (e : ℕ) =
      (P * gen q 3 ^ 4 * gen q 4 ^ (e : ℕ)) * gen q 3
    rw [mul_assoc (P * gen q 3 ^ 4), hc]
    rw [mul_assoc P, ← mul_assoc (gen q 3 ^ 4), ← pow_succ,
      (gen_pow_five q).2.2.2.1, one_mul, mul_assoc]

theorem normalForm_step_two (q : ℕ) (x : Coordinates) :
    normalForm q (step q 2 x) = normalForm q x * gen q 2 := by
  rcases x with ⟨a, b, c, d, e⟩
  have hc4 : gen q 4 ^ (e : ℕ) * gen q 2 =
      gen q 2 * gen q 4 ^ (e : ℕ) :=
    ((commute_24 q).symm.pow_left (e : ℕ)).eq
  have hc3 : gen q 3 ^ (d : ℕ) * gen q 2 =
      gen q 2 * gen q 3 ^ (d : ℕ) :=
    ((commute_23 q).symm.pow_left (d : ℕ)).eq
  have hs : gen q 3 ^ (d : ℕ) * gen q 4 ^ (e : ℕ) * gen q 2 =
      gen q 2 * (gen q 3 ^ (d : ℕ) * gen q 4 ^ (e : ℕ)) := by
    calc
      _ = gen q 3 ^ (d : ℕ) * (gen q 4 ^ (e : ℕ) * gen q 2) := mul_assoc _ _ _
      _ = gen q 3 ^ (d : ℕ) * (gen q 2 * gen q 4 ^ (e : ℕ)) := by rw [hc4]
      _ = (gen q 3 ^ (d : ℕ) * gen q 2) * gen q 4 ^ (e : ℕ) :=
        (mul_assoc _ _ _).symm
      _ = (gen q 2 * gen q 3 ^ (d : ℕ)) * gen q 4 ^ (e : ℕ) := by rw [hc3]
      _ = _ := mul_assoc _ _ _
  fin_cases c
  · simp [normalForm, step, coord, hs, mul_assoc]
  · simp [normalForm, step, coord, hs, pow_succ, mul_assoc]
  · simp [normalForm, step, coord, hs, pow_succ, mul_assoc]
  · simp [normalForm, step, coord, hs, pow_succ, mul_assoc]
  · change normalForm q (a, b, 0, d, e) =
      normalForm q (a, b, 4, d, e) * gen q 2
    simp only [normalForm, Fin.val_zero, pow_zero, mul_one]
    norm_num
    let P := gen q 0 ^ (a : ℕ) * gen q 1 ^ (b : ℕ)
    change P * gen q 3 ^ (d : ℕ) * gen q 4 ^ (e : ℕ) =
      (P * gen q 2 ^ 4 * gen q 3 ^ (d : ℕ) * gen q 4 ^ (e : ℕ)) * gen q 2
    rw [mul_assoc (P * gen q 2 ^ 4 * gen q 3 ^ (d : ℕ)), hc4]
    rw [mul_assoc (P * gen q 2 ^ 4) (gen q 3 ^ (d : ℕ))]
    rw [← mul_assoc (gen q 3 ^ (d : ℕ)) (gen q 2), hc3]
    have hp : gen q 2 ^ 4 * gen q 2 = 1 := by
      rw [← pow_succ, (gen_pow_five q).2.2.1]
    calc
      P * gen q 3 ^ (d : ℕ) * gen q 4 ^ (e : ℕ) =
          P * 1 * (gen q 3 ^ (d : ℕ) * gen q 4 ^ (e : ℕ)) := by group
      _ = P * (gen q 2 ^ 4 * gen q 2) *
          (gen q 3 ^ (d : ℕ) * gen q 4 ^ (e : ℕ)) := by rw [hp]
      _ = P * gen q 2 ^ 4 *
          (gen q 2 * gen q 3 ^ (d : ℕ) * gen q 4 ^ (e : ℕ)) := by group

private theorem move_one_across_suffix (q : ℕ) (c d e : Fin 5) :
    gen q 2 ^ (c : ℕ) * gen q 3 ^ (d : ℕ) * gen q 4 ^ (e : ℕ) * gen q 1 =
      gen q 1 * gen q 2 ^ (c : ℕ) * gen q 3 ^ (d : ℕ) *
        (gen q 4 ^ (e : ℕ) * gen q 4 ^ (c : ℕ)) := by
  have hv : gen q 4 ^ (e : ℕ) * gen q 1 =
      gen q 1 * gen q 4 ^ (e : ℕ) :=
    ((commute_14 q).symm.pow_left (e : ℕ)).eq
  have hu : gen q 3 ^ (d : ℕ) * gen q 1 =
      gen q 1 * gen q 3 ^ (d : ℕ) :=
    ((commute_13 q).symm.pow_left (d : ℕ)).eq
  have hz := move_one_across_two q (c : ℕ)
  calc
    _ = gen q 2 ^ (c : ℕ) * gen q 3 ^ (d : ℕ) *
        (gen q 4 ^ (e : ℕ) * gen q 1) := by group
    _ = gen q 2 ^ (c : ℕ) * gen q 3 ^ (d : ℕ) *
        (gen q 1 * gen q 4 ^ (e : ℕ)) := by rw [hv]
    _ = gen q 2 ^ (c : ℕ) * (gen q 3 ^ (d : ℕ) * gen q 1) *
        gen q 4 ^ (e : ℕ) := by group
    _ = gen q 2 ^ (c : ℕ) * (gen q 1 * gen q 3 ^ (d : ℕ)) *
        gen q 4 ^ (e : ℕ) := by rw [hu]
    _ = (gen q 2 ^ (c : ℕ) * gen q 1) * gen q 3 ^ (d : ℕ) *
        gen q 4 ^ (e : ℕ) := by group
    _ = (gen q 1 * gen q 2 ^ (c : ℕ) * gen q 4 ^ (c : ℕ)) *
        gen q 3 ^ (d : ℕ) * gen q 4 ^ (e : ℕ) := by rw [hz]
    _ = _ := by
      have hcu : gen q 4 ^ (c : ℕ) * gen q 3 ^ (d : ℕ) =
          gen q 3 ^ (d : ℕ) * gen q 4 ^ (c : ℕ) :=
        (((commute_34 q).symm.pow_left (c : ℕ)).pow_right (d : ℕ)).eq
      calc
        _ = gen q 1 * gen q 2 ^ (c : ℕ) *
            (gen q 4 ^ (c : ℕ) * gen q 3 ^ (d : ℕ)) * gen q 4 ^ (e : ℕ) := by group
        _ = gen q 1 * gen q 2 ^ (c : ℕ) *
            (gen q 3 ^ (d : ℕ) * gen q 4 ^ (c : ℕ)) * gen q 4 ^ (e : ℕ) := by rw [hcu]
        _ = _ := by group

theorem normalForm_step_one (q : ℕ) (x : Coordinates) :
    normalForm q (step q 1 x) = normalForm q x * gen q 1 := by
  rcases x with ⟨a, b, c, d, e⟩
  let X := gen q 0 ^ (a : ℕ)
  let Y := gen q 1
  let Z := gen q 2 ^ (c : ℕ)
  let U := gen q 3 ^ (d : ℕ)
  let V := gen q 4
  have hs := move_one_across_suffix q c d e
  have hcollect :
      (X * Y ^ (b : ℕ) * Z * U * V ^ (e : ℕ)) * Y =
        X * (Y ^ (b : ℕ) * Y) * Z * U *
          (V ^ (e : ℕ) * V ^ (c : ℕ)) := by
    calc
      _ = X * Y ^ (b : ℕ) *
          (Z * U * V ^ (e : ℕ) * Y) := by group
      _ = X * Y ^ (b : ℕ) *
          (Y * Z * U * (V ^ (e : ℕ) * V ^ (c : ℕ))) := by rw [hs]
      _ = _ := by group
  change normalForm q (step q 1 (a, b, c, d, e)) =
    (X * Y ^ (b : ℕ) * Z * U * V ^ (e : ℕ)) * Y
  rw [hcollect]
  fin_cases b
  · simp [normalForm, step, coord, X, Y, Z, U, V, gen4_pow_fin_add, mul_assoc]
  · simp [normalForm, step, coord, X, Y, Z, U, V, gen4_pow_fin_add, pow_succ, mul_assoc]
  · simp [normalForm, step, coord, X, Y, Z, U, V, gen4_pow_fin_add, pow_succ, mul_assoc]
  · simp [normalForm, step, coord, X, Y, Z, U, V, gen4_pow_fin_add, pow_succ, mul_assoc]
  · change normalForm q (a, 0, c, d, e + c + mod5 q) =
      X * (Y ^ 4 * Y) * Z * U * (V ^ (e : ℕ) * V ^ (c : ℕ))
    rw [← pow_succ, (gen_pow_five q).2.1]
    simp only [normalForm, Fin.val_zero, pow_zero, mul_one, X, Z, U, V]
    rw [gen4_pow_fin_add_q]
    have hZ : gen q 4 ^ q * gen q 2 ^ (c : ℕ) = gen q 2 ^ (c : ℕ) * gen q 4 ^ q :=
      (((commute_24 q).symm.pow_left q).pow_right (c : ℕ)).eq
    have hU : gen q 4 ^ q * gen q 3 ^ (d : ℕ) = gen q 3 ^ (d : ℕ) * gen q 4 ^ q :=
      (((commute_34 q).symm.pow_left q).pow_right (d : ℕ)).eq
    have hZU : gen q 4 ^ q * gen q 2 ^ (c : ℕ) * gen q 3 ^ (d : ℕ) =
        gen q 2 ^ (c : ℕ) * gen q 3 ^ (d : ℕ) * gen q 4 ^ q := by
      calc
        _ = (gen q 2 ^ (c : ℕ) * gen q 4 ^ q) * gen q 3 ^ (d : ℕ) := by rw [hZ]
        _ = gen q 2 ^ (c : ℕ) * (gen q 4 ^ q * gen q 3 ^ (d : ℕ)) := mul_assoc _ _ _
        _ = gen q 2 ^ (c : ℕ) * (gen q 3 ^ (d : ℕ) * gen q 4 ^ q) := by rw [hU]
        _ = _ := (mul_assoc _ _ _).symm
    calc
      _ = gen q 0 ^ (a : ℕ) * gen q 2 ^ (c : ℕ) * gen q 3 ^ (d : ℕ) *
          (gen q 4 ^ q * (gen q 4 ^ (e : ℕ) * gen q 4 ^ (c : ℕ))) := by group
      _ = gen q 0 ^ (a : ℕ) *
          (gen q 2 ^ (c : ℕ) * gen q 3 ^ (d : ℕ) * gen q 4 ^ q) *
          (gen q 4 ^ (e : ℕ) * gen q 4 ^ (c : ℕ)) := by group
      _ = gen q 0 ^ (a : ℕ) *
          (gen q 4 ^ q * gen q 2 ^ (c : ℕ) * gen q 3 ^ (d : ℕ)) *
          (gen q 4 ^ (e : ℕ) * gen q 4 ^ (c : ℕ)) := by rw [hZU]
      _ = _ := by group

private theorem move_zero_across_suffix (q : ℕ) (b c d e : Fin 5) :
    gen q 1 ^ (b : ℕ) * gen q 2 ^ (c : ℕ) * gen q 3 ^ (d : ℕ) *
        gen q 4 ^ (e : ℕ) * gen q 0 =
      gen q 0 * gen q 1 ^ (b : ℕ) * gen q 2 ^ (c : ℕ) *
        (gen q 3 ^ (b : ℕ) * gen q 3 ^ (d : ℕ)) *
        (gen q 4 ^ (e : ℕ) * gen q 4 ^ (d : ℕ)) := by
  have hv : gen q 4 ^ (e : ℕ) * gen q 0 =
      gen q 0 * gen q 4 ^ (e : ℕ) :=
    ((commute_04 q).symm.pow_left (e : ℕ)).eq
  have hu := move_zero_across_three q (d : ℕ)
  have hz : gen q 2 ^ (c : ℕ) * gen q 0 =
      gen q 0 * gen q 2 ^ (c : ℕ) :=
    ((commute_02 q).symm.pow_left (c : ℕ)).eq
  have hy := move_zero_across_one q (b : ℕ)
  have hzu : gen q 3 ^ (b : ℕ) * gen q 2 ^ (c : ℕ) =
      gen q 2 ^ (c : ℕ) * gen q 3 ^ (b : ℕ) :=
    ((commute_23 q).symm.pow_left (b : ℕ)).pow_right (c : ℕ) |>.eq
  calc
    _ = gen q 1 ^ (b : ℕ) * gen q 2 ^ (c : ℕ) * gen q 3 ^ (d : ℕ) *
        (gen q 4 ^ (e : ℕ) * gen q 0) := by group
    _ = gen q 1 ^ (b : ℕ) * gen q 2 ^ (c : ℕ) * gen q 3 ^ (d : ℕ) *
        (gen q 0 * gen q 4 ^ (e : ℕ)) := by rw [hv]
    _ = gen q 1 ^ (b : ℕ) * gen q 2 ^ (c : ℕ) *
        (gen q 3 ^ (d : ℕ) * gen q 0) * gen q 4 ^ (e : ℕ) := by group
    _ = gen q 1 ^ (b : ℕ) * gen q 2 ^ (c : ℕ) *
        (gen q 0 * gen q 3 ^ (d : ℕ) * gen q 4 ^ (d : ℕ)) *
        gen q 4 ^ (e : ℕ) := by rw [hu]
    _ = gen q 1 ^ (b : ℕ) * (gen q 2 ^ (c : ℕ) * gen q 0) *
        gen q 3 ^ (d : ℕ) * (gen q 4 ^ (e : ℕ) * gen q 4 ^ (d : ℕ)) := by group
    _ = gen q 1 ^ (b : ℕ) * (gen q 0 * gen q 2 ^ (c : ℕ)) *
        gen q 3 ^ (d : ℕ) * (gen q 4 ^ (e : ℕ) * gen q 4 ^ (d : ℕ)) := by rw [hz]
    _ = (gen q 1 ^ (b : ℕ) * gen q 0) * gen q 2 ^ (c : ℕ) *
        gen q 3 ^ (d : ℕ) * (gen q 4 ^ (e : ℕ) * gen q 4 ^ (d : ℕ)) := by group
    _ = (gen q 0 * gen q 1 ^ (b : ℕ) * gen q 3 ^ (b : ℕ)) *
        gen q 2 ^ (c : ℕ) * gen q 3 ^ (d : ℕ) *
        (gen q 4 ^ (e : ℕ) * gen q 4 ^ (d : ℕ)) := by rw [hy]
    _ = _ := by
      calc
        _ = gen q 0 * gen q 1 ^ (b : ℕ) *
            (gen q 3 ^ (b : ℕ) * gen q 2 ^ (c : ℕ)) * gen q 3 ^ (d : ℕ) *
            (gen q 4 ^ (e : ℕ) * gen q 4 ^ (d : ℕ)) := by group
        _ = gen q 0 * gen q 1 ^ (b : ℕ) *
            (gen q 2 ^ (c : ℕ) * gen q 3 ^ (b : ℕ)) * gen q 3 ^ (d : ℕ) *
            (gen q 4 ^ (e : ℕ) * gen q 4 ^ (d : ℕ)) := by rw [hzu]
        _ = _ := by group

-- flexible simp feeds a rw chain; rewriting as simp only is brittle here
theorem normalForm_step_zero (q : ℕ) (x : Coordinates) :
    normalForm q (step q 0 x) = normalForm q x * gen q 0 := by
  rcases x with ⟨a, b, c, d, e⟩
  let X := gen q 0
  let Y := gen q 1 ^ (b : ℕ)
  let Z := gen q 2 ^ (c : ℕ)
  let U := gen q 3
  let V := gen q 4
  have hs := move_zero_across_suffix q b c d e
  have hdb : U ^ (d : ℕ) * U ^ (b : ℕ) =
      U ^ (b : ℕ) * U ^ (d : ℕ) := by
    rw [← pow_add, ← pow_add, Nat.add_comm]
  have hcollect :
      (X ^ (a : ℕ) * Y * Z * U ^ (d : ℕ) * V ^ (e : ℕ)) * X =
        (X ^ (a : ℕ) * X) * Y * Z *
          (U ^ (b : ℕ) * U ^ (d : ℕ)) *
          (V ^ (e : ℕ) * V ^ (d : ℕ)) := by
    calc
      _ = X ^ (a : ℕ) *
          (Y * Z * U ^ (d : ℕ) * V ^ (e : ℕ) * X) := by group
      _ = X ^ (a : ℕ) *
          (X * Y * Z * (U ^ (b : ℕ) * U ^ (d : ℕ)) *
            (V ^ (e : ℕ) * V ^ (d : ℕ))) := by rw [hs]
      _ = _ := by group
  change normalForm q (step q 0 (a, b, c, d, e)) =
    (X ^ (a : ℕ) * Y * Z * U ^ (d : ℕ) * V ^ (e : ℕ)) * X
  rw [hcollect]
  fin_cases a
  · simp only [normalForm, Fin.isValue, step, coord, Fin.zero_eta, zero_add,
      Fin.coe_ofNat_eq_mod, Nat.one_mod, pow_one, mul_assoc, gen3_pow_fin_add,
      gen4_pow_fin_add, pow_zero, one_mul, mul_right_inj, X, Y, Z, U, V]
    rw [← mul_assoc, hdb, mul_assoc]
  · simp only [normalForm, Fin.isValue, step, coord, Fin.mk_one, Fin.reduceAdd,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, pow_succ, pow_zero,
      one_mul, mul_assoc, gen3_pow_fin_add, gen4_pow_fin_add, mul_right_inj,
      X, Y, Z, U, V]
    rw [← mul_assoc, hdb, mul_assoc]
  · simp only [normalForm, Fin.isValue, step, coord, Fin.reduceFinMk, Fin.reduceAdd,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, pow_succ, pow_zero,
      one_mul, mul_assoc, gen3_pow_fin_add, gen4_pow_fin_add, mul_right_inj,
      X, Y, Z, U, V]
    rw [← mul_assoc, hdb, mul_assoc]
  · simp only [normalForm, Fin.isValue, step, coord, Fin.reduceFinMk, Fin.reduceAdd,
      Fin.coe_ofNat_eq_mod, Nat.mod_succ, pow_succ, pow_zero,
      one_mul, mul_assoc, gen3_pow_fin_add, gen4_pow_fin_add, mul_right_inj,
      X, Y, Z, U, V]
    rw [← mul_assoc, hdb, mul_assoc]
  · change normalForm q (0, b, c, d + b, e + d) =
      (X ^ 4 * X) * Y * Z * (U ^ (b : ℕ) * U ^ (d : ℕ)) *
        (V ^ (e : ℕ) * V ^ (d : ℕ))
    rw [← pow_succ, (gen_pow_five q).1]
    simp only [normalForm, Fin.val_zero, pow_zero, one_mul, Y, Z, U, V]
    rw [gen3_pow_fin_add, gen4_pow_fin_add]
    group

/-- The five executable coordinate steps agree with right multiplication by
the corresponding pc generators in the presented group. -/
theorem normalForm_step (q : ℕ) (i : Gen) (x : Coordinates) :
    normalForm q (step q i x) = normalForm q x * gen q i := by
  fin_cases i
  · exact normalForm_step_zero q x
  · exact normalForm_step_one q x
  · exact normalForm_step_two q x
  · exact normalForm_step_three q x
  · exact normalForm_step_four q x

/-- The inverse coordinate step agrees with right multiplication by the
inverse pc generator. -/
theorem normalForm_stepInv (q : ℕ) (i : Gen) (x : Coordinates) :
    normalForm q (stepInv q i x) = normalForm q x * (gen q i)⁻¹ := by
  have h := normalForm_step q i (stepInv q i x)
  rw [step_stepInv] at h
  apply (eq_mul_inv_iff_mul_eq).2
  exact h.symm

private theorem freeWord_collect (q : ℕ) (w : FreeGroup Gen) :
    ∀ x : Coordinates, ∃ y : Coordinates,
      normalForm q y = normalForm q x * PresentedGroup.mk (relations q) w := by
  induction w using FreeGroup.induction_on with
  | C1 =>
      intro x
      exact ⟨x, by simp⟩
  | of i =>
      intro x
      refine ⟨step q i x, ?_⟩
      change normalForm q (step q i x) = normalForm q x * gen q i
      exact normalForm_step q i x
  | inv_of i _ =>
      intro x
      refine ⟨stepInv q i x, ?_⟩
      change normalForm q (stepInv q i x) = normalForm q x * (gen q i)⁻¹
      exact normalForm_stepInv q i x
  | mul w₁ w₂ ih₁ ih₂ =>
      intro x
      obtain ⟨y, hy⟩ := ih₁ x
      obtain ⟨z, hz⟩ := ih₂ y
      refine ⟨z, ?_⟩
      rw [map_mul]
      calc
        normalForm q z = normalForm q y * PresentedGroup.mk (relations q) w₂ := hz
        _ = (normalForm q x * PresentedGroup.mk (relations q) w₁) *
            PresentedGroup.mk (relations q) w₂ := by rw [hy]
        _ = _ := mul_assoc _ _ _

/-- Every element of the pc presentation has a collected five-coordinate
normal form.  This is proved by free-word induction from the five multiplication
bridges, rather than by a cardinality computation. -/
theorem normalForm_surjective (q : ℕ) : Function.Surjective (normalForm q) := by
  intro g
  induction g using PresentedGroup.induction_on with
  | H w =>
      obtain ⟨x, hx⟩ := freeWord_collect q w (0, 0, 0, 0, 0)
      refine ⟨x, ?_⟩
      simpa [normalForm_zero] using hx

private def freeCoordinateAction (q : ℕ) :
    FreeGroup Gen →* (Equiv.Perm Coordinates)ᵐᵒᵖ :=
  FreeGroup.lift (fun i => MulOpposite.op (stepEquiv q i))

set_option maxHeartbeats 500000 in
-- Expanding the two finite parameter cases and all fifteen permutation
-- relators requires more elaboration than the default, while each resulting
-- goal is discharged symbolically (not by exhaustive coordinate evaluation).
private theorem relations_act_trivially (q : ℕ) (hq : q = 1 ∨ q = 2)
    (r : FreeGroup Gen) (hr : r ∈ relations q) :
    freeCoordinateAction q r = 1 := by
  rcases hq with rfl | rfl <;> obtain ⟨t, rfl⟩ := hr
  all_goals
  cases t <;> apply MulOpposite.unop_injective <;> apply Equiv.ext <;>
    intro x <;> rcases x with ⟨a, b, c, d, e⟩
  case pow0 =>
    simp [freeCoordinateAction, relator, equation, w, stepEquiv, step, coord, pow_succ]
    abel_nf
    simp
  case pow1 =>
    fin_cases b <;>
      simp [freeCoordinateAction, relator, equation, w, stepEquiv, step, stepInv,
        coord, mod5, pow_succ] <;> abel_nf <;> decide +revert
  case pow2 =>
    simp [freeCoordinateAction, relator, equation, w, stepEquiv, step, coord, pow_succ]
    abel_nf
    simp
  case pow3 =>
    simp [freeCoordinateAction, relator, equation, w, stepEquiv, step, coord, pow_succ]
    abel_nf
    simp
  case pow4 =>
    simp [freeCoordinateAction, relator, equation, w, stepEquiv, step, coord, pow_succ]
    abel_nf
    simp
  case conj01 =>
    fin_cases b <;> fin_cases e <;>
      simp [freeCoordinateAction, relator, equation, conjugate, w,
      stepEquiv, step, stepInv, coord, mod5] <;> abel_nf <;> decide +revert
  case conj12 =>
    fin_cases b <;> fin_cases e <;>
      simp [freeCoordinateAction, relator, equation, conjugate, w,
      stepEquiv, step, stepInv, coord, mod5] <;> abel_nf <;> decide +revert
  all_goals
    simp [freeCoordinateAction, relator, equation, conjugate, w, stepEquiv,
      step, stepInv, coord, mod5] <;> abel_nf <;> simp

private theorem relations_act_trivially_68 (r : FreeGroup Gen)
    (hr : r ∈ relations 1) : freeCoordinateAction 1 r = 1 :=
  relations_act_trivially 1 (Or.inl rfl) r hr

private theorem relations_act_trivially_69 (r : FreeGroup Gen)
    (hr : r ∈ relations 2) : freeCoordinateAction 2 r = 1 :=
  relations_act_trivially 2 (Or.inr rfl) r hr

/-- The coordinate right action descended through either target presentation. -/
def coordinateAction (q : ℕ) (hq : q = 1 ∨ q = 2) :
    Group q →* (Equiv.Perm Coordinates)ᵐᵒᵖ :=
  PresentedGroup.toGroup (relations_act_trivially q hq)

theorem coordinateAction_gen (q : ℕ) (hq : q = 1 ∨ q = 2) (i : Gen) :
    coordinateAction q hq (gen q i) = MulOpposite.op (stepEquiv q i) := by
  rfl

private theorem step0_pow_zero (q : ℕ) (a : Fin 5) :
    (stepEquiv q 0 ^ (a : ℕ)) (0, 0, 0, 0, 0) = (a, 0, 0, 0, 0) := by
  fin_cases a <;> simp [pow_succ, stepEquiv, step, coord]

private theorem step1_pow_after_zero (q : ℕ) (a b : Fin 5) :
    (stepEquiv q 1 ^ (b : ℕ)) (a, 0, 0, 0, 0) = (a, b, 0, 0, 0) := by
  fin_cases b <;> simp [pow_succ, stepEquiv, step, coord]

private theorem step2_pow_after_one (q : ℕ) (a b c : Fin 5) :
    (stepEquiv q 2 ^ (c : ℕ)) (a, b, 0, 0, 0) = (a, b, c, 0, 0) := by
  fin_cases c <;> simp [pow_succ, stepEquiv, step, coord]

private theorem step3_pow_after_two (q : ℕ) (a b c d : Fin 5) :
    (stepEquiv q 3 ^ (d : ℕ)) (a, b, c, 0, 0) = (a, b, c, d, 0) := by
  fin_cases d <;> simp [pow_succ, stepEquiv, step, coord]

private theorem step4_pow_after_three (q : ℕ) (a b c d e : Fin 5) :
    (stepEquiv q 4 ^ (e : ℕ)) (a, b, c, d, 0) = (a, b, c, d, e) := by
  fin_cases e <;> simp [pow_succ, stepEquiv, step, coord]

/-- Acting by a collected normal form carries the zero coordinate to the
coordinate that defined it. -/
theorem coordinateAction_normalForm (q : ℕ) (hq : q = 1 ∨ q = 2)
    (x : Coordinates) :
    MulOpposite.unop (coordinateAction q hq (normalForm q x))
        (0, 0, 0, 0, 0) = x := by
  rcases x with ⟨a, b, c, d, e⟩
  simp [normalForm, map_mul, map_pow, coordinateAction_gen, step0_pow_zero,
    step1_pow_after_zero, step2_pow_after_one, step3_pow_after_two,
    step4_pow_after_three]

/-- Uniqueness of collected coordinates for either target presentation. -/
theorem normalForm_injective (q : ℕ) (hq : q = 1 ∨ q = 2) :
    Function.Injective (normalForm q) := by
  intro x y hxy
  have ha := congrArg (coordinateAction q hq) hxy
  have hu := congrArg MulOpposite.unop ha
  have hz := congrArg (fun p : Equiv.Perm Coordinates => p (0, 0, 0, 0, 0)) hu
  simpa [coordinateAction_normalForm q hq] using hz

/-- The five-coordinate normal form is bijective for either target parameter. -/
theorem normalForm_bijective (q : ℕ) (hq : q = 1 ∨ q = 2) :
    Function.Bijective (normalForm q) :=
  ⟨normalForm_injective q hq, normalForm_surjective q⟩

/-- Certified normal-form equivalence for `SmallGroup(3125,68)`'s presentation. -/
noncomputable def normalFormEquiv68 : Coordinates ≃ Group 1 :=
  Equiv.ofBijective (normalForm 1) (normalForm_bijective 1 (Or.inl rfl))

/-- Certified normal-form equivalence for `SmallGroup(3125,69)`'s presentation. -/
noncomputable def normalFormEquiv69 : Coordinates ≃ Group 2 :=
  Equiv.ofBijective (normalForm 2) (normalForm_bijective 2 (Or.inr rfl))

/-- Lean model for the presentation extracted from `SmallGroup(3125,68)`. -/
abbrev G68 := Group 1

/-- Lean model for the presentation extracted from `SmallGroup(3125,69)`. -/
abbrev G69 := Group 2

end LeanDring.P5Presentation
