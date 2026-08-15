/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.Gauss.GaussSign
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.DirectSum.Module

/-!
# The sign of the quadratic Gauss sum (Schur's proof)

**Gauss's theorem** ([BEW98] Thm 1.5.2): for an odd prime `p`,

`g(p) = ∑_n exp(2πi n²/p) = √p` if `p ≡ 1 (mod 4)`, `= i·√p` if `p ≡ 3`.

We formalize Schur's matrix proof. Let `F` be the DFT matrix
`F j k = ψ(jk)` (`ψ = stdAddChar`). Then:

* `trace F = g` (the Gauss sum in its `n²` form);
* `F² = p·J` (`J` = the negation permutation), so `F⁴ = p²`;
* every eigenvalue of `F` lies in `{√p, -√p, i√p, -i√p}`, and `ℂ^p` is
  spanned by the four eigenspaces (explicit Lagrange projections — pure
  matrix algebra from `F⁴ = p²`);
* in an eigenbasis, `trace F`, `trace F²` and `det F` become bookkeeping in
  the four multiplicities `d₀..d₃`;
* `det F` is a **Vandermonde determinant**, whose phase is computed exactly:
  `det F = R·i^{p(p-1)/2}` with `R > 0` — the only analytic input being
  `sin x > 0` on `(0, π)`;
* the resulting parity constraints force the sign.

Like `GaussSign.lean`, this file is self-contained over Mathlib (no D-ring
imports) and is intended as a stand-alone number-theory contribution.
-/

namespace LeanDring.GaussSign

open scoped Real
open Complex ZMod Finset

variable (p : ℕ) [Fact p.Prime]

/-! ## Preliminaries -/

/-- The standard additive character is nontrivial. -/
theorem stdAddChar_ne_one : (stdAddChar : AddChar (ZMod p) ℂ) ≠ 1 := by
  have h := ZMod.isPrimitive_stdAddChar p
  have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have h2 := h h1
  rwa [AddChar.mulShift_one] at h2

theorem ringChar_zmod_ne_two' (hp2 : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  exact hp2

variable {p} in
/-- Square-counting: `∑ₘ ψ(m²) = g(χ₂, ψ)` for nontrivial `ψ` (standalone
copy of the fiber-count argument, to keep this file Mathlib-only). -/
theorem sum_stdAddChar_sq (hp2 : p ≠ 2) :
    ∑ m : ZMod p, (stdAddChar : AddChar (ZMod p) ℂ) (m ^ 2) = gauss p := by
  classical
  set ψ : AddChar (ZMod p) ℂ := stdAddChar with hψdef
  have hψ : ψ ≠ 1 := stdAddChar_ne_one p
  have hfib : ∑ m : ZMod p, ψ (m ^ 2) =
      ∑ x : ZMod p, ∑ m ∈ univ.filter (fun m : ZMod p => m ^ 2 = x),
        ψ (m ^ 2) :=
    (Finset.sum_fiberwise_of_maps_to (fun m _ => mem_univ _) _).symm
  have hinner : ∀ x : ZMod p,
      (∑ m ∈ univ.filter (fun m : ZMod p => m ^ 2 = x), ψ (m ^ 2)) =
        (χℂ p x + 1) * ψ x := by
    intro x
    have hval : ∀ m ∈ univ.filter (fun m : ZMod p => m ^ 2 = x),
        ψ (m ^ 2) = ψ x := by
      intro m hm
      rw [(Finset.mem_filter.mp hm).2]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hcount := quadraticChar_card_sqrts (F := ZMod p)
      (ringChar_zmod_ne_two' p hp2) x
    have hset : {y : ZMod p | y ^ 2 = x}.toFinset =
        univ.filter (fun m : ZMod p => m ^ 2 = x) := by
      ext y
      simp
    rw [hset] at hcount
    have hcast : ((univ.filter (fun m : ZMod p => m ^ 2 = x)).card : ℂ) =
        (((univ.filter (fun m : ZMod p => m ^ 2 = x)).card : ℤ) : ℂ) := by
      push_cast
      rfl
    rw [hcast, hcount]
    push_cast
    rfl
  rw [hfib, Finset.sum_congr rfl fun x _ => hinner x]
  have hsplit : ∑ x : ZMod p, (χℂ p x + 1) * ψ x =
      (∑ x : ZMod p, χℂ p x * ψ x) + ∑ x : ZMod p, ψ x := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [hsplit, AddChar.sum_eq_zero_of_ne_one hψ, add_zero]
  rfl

/-! ## The DFT matrix and its algebraic identities -/

/-- The DFT matrix `F j k = ψ(jk)`. -/
noncomputable def dftMatrix : Matrix (ZMod p) (ZMod p) ℂ :=
  Matrix.of fun j k => stdAddChar (j * k)

/-- The negation permutation matrix. -/
noncomputable def negMatrix : Matrix (ZMod p) (ZMod p) ℂ :=
  Matrix.of fun j k => if j + k = 0 then 1 else 0

variable {p} in
/-- `trace F = g`: the Gauss sum is the trace of the DFT matrix. -/
theorem trace_dftMatrix (hp2 : p ≠ 2) : (dftMatrix p).trace = gauss p := by
  have h : (dftMatrix p).trace = ∑ j : ZMod p, stdAddChar (j ^ 2) := by
    simp only [Matrix.trace, Matrix.diag, dftMatrix, Matrix.of_apply, sq]
  rw [h, sum_stdAddChar_sq hp2]

/-- Character orthogonality: `∑ₓ ψ(xb) = p·[b = 0]`. -/
theorem sum_stdAddChar_mul (b : ZMod p) :
    ∑ x : ZMod p, (stdAddChar : AddChar (ZMod p) ℂ) (x * b) =
      if b = 0 then (p : ℂ) else 0 := by
  classical
  have h := AddChar.sum_mulShift b (ZMod.isPrimitive_stdAddChar p)
  rw [ZMod.card] at h
  exact_mod_cast h

/-- `F² = p·J`. -/
theorem dftMatrix_sq : dftMatrix p * dftMatrix p = (p : ℂ) • negMatrix p := by
  ext j k
  have hsum : ∀ m : ZMod p,
      (stdAddChar : AddChar (ZMod p) ℂ) (j * m) * stdAddChar (m * k) =
        stdAddChar (m * (j + k)) := by
    intro m
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp only [Matrix.mul_apply, dftMatrix, Matrix.of_apply]
  rw [Finset.sum_congr rfl fun m _ => hsum m, sum_stdAddChar_mul]
  simp only [Matrix.smul_apply, negMatrix, Matrix.of_apply, smul_eq_mul]
  split_ifs <;> simp

/-- `J² = 1`. -/
theorem negMatrix_sq : negMatrix p * negMatrix p = 1 := by
  classical
  ext j k
  rw [Matrix.mul_apply]
  have h : ∀ m : ZMod p, (negMatrix p) j m * (negMatrix p) m k =
      if m = -j then (if j = k then (1 : ℂ) else 0) else 0 := by
    intro m
    simp only [negMatrix, Matrix.of_apply]
    by_cases hm : m = -j
    · subst hm
      rw [if_pos (by ring), if_pos rfl, one_mul]
      congr 1
      simp [neg_add_eq_zero]
    · rw [if_neg fun hc => hm (eq_neg_of_add_eq_zero_right hc), zero_mul,
        if_neg hm]
  rw [Finset.sum_congr rfl fun m _ => h m, Finset.sum_ite_eq' univ (-j)]
  simp [Matrix.one_apply]

variable {p} in
/-- `F⁴ = p²·1`. -/
theorem dftMatrix_pow_four :
    dftMatrix p ^ 4 = ((p : ℂ) ^ 2) • 1 := by
  have h4 : dftMatrix p ^ 4 = (dftMatrix p * dftMatrix p) *
      (dftMatrix p * dftMatrix p) := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two, pow_two]
  rw [h4, dftMatrix_sq, smul_mul_smul_comm, negMatrix_sq, ← pow_two]

variable {p} in
/-- `trace F² = p` (for odd `p`, only `j = 0` contributes). -/
theorem trace_dftMatrix_sq (hp2 : p ≠ 2) :
    (dftMatrix p * dftMatrix p).trace = (p : ℂ) := by
  classical
  rw [dftMatrix_sq, Matrix.trace_smul]
  have h : (negMatrix p).trace = 1 := by
    have hdiag : ∀ j : ZMod p, (negMatrix p) j j = if j = 0 then (1 : ℂ) else 0 := by
      intro j
      simp only [negMatrix, Matrix.of_apply]
      congr 1
      simp only [eq_iff_iff]
      constructor
      · intro hj
        -- `2j = 0` forces `j = 0` for odd `p`
        have h2 : (2 : ZMod p) * j = 0 := by
          rw [two_mul]
          exact hj
        have h2ne : (2 : ZMod p) ≠ 0 := by
          have hnd : ¬ (p ∣ 2) := fun hdvd =>
            hp2 ((Nat.prime_dvd_prime_iff_eq
              (Fact.out : p.Prime) Nat.prime_two).mp hdvd)
          intro hc
          exact hnd ((ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast hc))
        rcases mul_eq_zero.mp h2 with h2' | h
        · exact absurd h2' h2ne
        · exact h
      · intro hj
        rw [hj, add_zero]
    rw [Matrix.trace]
    simp only [Matrix.diag]
    rw [Finset.sum_congr rfl fun j _ => hdiag j, Finset.sum_ite_eq' univ (0 : ZMod p)]
    simp
  rw [h, smul_eq_mul, mul_one]

/-! ## The four eigenvalues and the Lagrange spanning identity -/

/-- `s = √p`, as a complex number. -/
noncomputable def sqp : ℂ := (Real.sqrt p : ℂ)

theorem sqp_pos : 0 < Real.sqrt p :=
  Real.sqrt_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos)

theorem sqp_ne_zero : sqp p ≠ 0 := by
  simp only [sqp, ne_eq, Complex.ofReal_eq_zero]
  exact ne_of_gt (sqp_pos p)

omit [Fact p.Prime] in
theorem sqp_sq : sqp p ^ 2 = (p : ℂ) := by
  have h : Real.sqrt p ^ 2 = (p : ℝ) := Real.sq_sqrt (by positivity)
  rw [sqp, ← Complex.ofReal_pow, h, Complex.ofReal_natCast]

/-- The four candidate eigenvalues `iᵏ·√p`, `k = 0, 1, 2, 3`. -/
noncomputable def evals (i : Fin 4) : ℂ := Complex.I ^ (i : ℕ) * sqp p

omit [Fact p.Prime] in
theorem evals_pow_four (i : Fin 4) : evals p i ^ 4 = (p : ℂ) ^ 2 := by
  rw [evals, mul_pow, ← pow_mul, mul_comm (i : ℕ) 4, pow_mul,
    Complex.I_pow_four, one_pow, one_mul,
    show sqp p ^ 4 = (sqp p ^ 2) ^ 2 by ring, sqp_sq]

omit [Fact p.Prime] in
theorem I_pow_inj {a b : ℕ} (ha : a < 4) (hb : b < 4)
    (h : Complex.I ^ a = Complex.I ^ b) : a = b := by
  interval_cases a <;> interval_cases b <;>
    simp_all [pow_succ, pow_zero, one_mul, Complex.I_mul_I, Complex.ext_iff] <;>
    norm_num at h

theorem evals_injective : Function.Injective (evals p) := by
  intro i j hij
  have hs := sqp_ne_zero p
  have hI : Complex.I ^ (i : ℕ) = Complex.I ^ (j : ℕ) :=
    mul_right_cancel₀ hs hij
  exact Fin.ext (I_pow_inj i.isLt j.isLt hI)

/-- The (inverse-free) Lagrange numerators `F³ + cF² + c²F + c³`. -/
noncomputable def lagr (i : Fin 4) : Matrix (ZMod p) (ZMod p) ℂ :=
  dftMatrix p ^ 3 + evals p i • dftMatrix p ^ 2 +
    (evals p i) ^ 2 • dftMatrix p + (evals p i) ^ 3 • 1

/-- `F·Lᵢ = cᵢ·Lᵢ`: the Lagrange numerators are eigen-matrices, from
`F⁴ = p²` (telescoping). -/
theorem dft_mul_lagr (i : Fin 4) :
    dftMatrix p * lagr p i = evals p i • lagr p i := by
  have h4 : dftMatrix p ^ 4 = (evals p i) ^ 4 • (1 : Matrix (ZMod p) (ZMod p) ℂ) := by
    rw [dftMatrix_pow_four, evals_pow_four]
  simp only [lagr, mul_add, smul_add, mul_smul_comm, mul_one, smul_smul]
  rw [show dftMatrix p * dftMatrix p ^ 3 = dftMatrix p ^ 4 by rw [← pow_succ'],
    show dftMatrix p * dftMatrix p ^ 2 = dftMatrix p ^ 3 by rw [← pow_succ'],
    h4,
    show evals p i * evals p i ^ 2 = evals p i ^ 3 by ring,
    show evals p i * evals p i ^ 3 = evals p i ^ 4 by ring,
    show dftMatrix p * dftMatrix p = dftMatrix p ^ 2 from (pow_two _).symm,
    show evals p i * evals p i = evals p i ^ 2 from (pow_two _).symm]
  abel

omit [Fact p.Prime] in
/-- Power sums: `∑ᵢ (Iⁱ)ᵏ = 0` for `k = 1, 2, 3`. -/
theorem sum_I_pow_mul (k : ℕ) (hk : k = 1 ∨ k = 2 ∨ k = 3) :
    ∑ i : Fin 4, (Complex.I ^ (i : ℕ)) ^ k = 0 := by
  rw [Fin.sum_univ_four]
  rcases hk with rfl | rfl | rfl <;>
    norm_num [pow_succ, pow_zero, one_mul, Complex.I_mul_I, Complex.ext_iff]

/-- **The spanning identity**: `∑ᵢ Iⁱ·Lᵢ = 4√p³·1` (the inverse-free form of
`∑ᵢ (4cᵢ³)⁻¹·Lᵢ = 1`). -/
theorem lagr_combo :
    ∑ i : Fin 4, Complex.I ^ (i : ℕ) • lagr p i =
      (4 * sqp p ^ 3) • (1 : Matrix (ZMod p) (ZMod p) ℂ) := by
  have e1 : ∑ i : Fin 4, Complex.I ^ (i : ℕ) • lagr p i =
      (∑ i : Fin 4, Complex.I ^ (i : ℕ)) • dftMatrix p ^ 3 +
      (∑ i : Fin 4, Complex.I ^ (i : ℕ) * evals p i) • dftMatrix p ^ 2 +
      (∑ i : Fin 4, Complex.I ^ (i : ℕ) * evals p i ^ 2) • dftMatrix p +
      (∑ i : Fin 4, Complex.I ^ (i : ℕ) * evals p i ^ 3) • 1 := by
    simp only [lagr, smul_add, smul_smul, Finset.sum_add_distrib,
      Finset.sum_smul]
  have c0 : ∑ i : Fin 4, Complex.I ^ (i : ℕ) = 0 := by
    have := sum_I_pow_mul 1 (Or.inl rfl)
    simpa using this
  have c1 : ∑ i : Fin 4, Complex.I ^ (i : ℕ) * evals p i = 0 := by
    have h : ∀ i : Fin 4, Complex.I ^ (i : ℕ) * evals p i =
        (Complex.I ^ (i : ℕ)) ^ 2 * sqp p := by
      intro i
      rw [evals]
      ring
    rw [Finset.sum_congr rfl fun i _ => h i, ← Finset.sum_mul,
      sum_I_pow_mul 2 (Or.inr (Or.inl rfl)), zero_mul]
  have c2 : ∑ i : Fin 4, Complex.I ^ (i : ℕ) * evals p i ^ 2 = 0 := by
    have h : ∀ i : Fin 4, Complex.I ^ (i : ℕ) * evals p i ^ 2 =
        (Complex.I ^ (i : ℕ)) ^ 3 * sqp p ^ 2 := by
      intro i
      rw [evals]
      ring
    rw [Finset.sum_congr rfl fun i _ => h i, ← Finset.sum_mul,
      sum_I_pow_mul 3 (Or.inr (Or.inr rfl)), zero_mul]
  have c3 : ∑ i : Fin 4, Complex.I ^ (i : ℕ) * evals p i ^ 3 = 4 * sqp p ^ 3 := by
    have h : ∀ i : Fin 4, Complex.I ^ (i : ℕ) * evals p i ^ 3 =
        (Complex.I ^ (i : ℕ)) ^ 4 * sqp p ^ 3 := by
      intro i
      rw [evals]
      ring
    have h4 : ∀ i : Fin 4, (Complex.I ^ (i : ℕ)) ^ 4 = 1 := by
      intro i
      rw [← pow_mul, mul_comm, pow_mul, Complex.I_pow_four, one_pow]
    rw [Finset.sum_congr rfl fun i _ => h i,
      Finset.sum_congr rfl fun i _ => by rw [h4 i, one_mul],
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [e1, c0, c1, c2, c3, zero_smul, zero_smul, zero_smul, zero_add,
    zero_add, zero_add]

/-! ## The eigenspace decomposition -/

/-- The DFT endomorphism of `ℂ^p`. -/
noncomputable def dftEnd : Module.End ℂ (ZMod p → ℂ) :=
  Matrix.toLin' (dftMatrix p)

/-- The four candidate eigenspaces. -/
noncomputable def eigSp (i : Fin 4) : Submodule ℂ (ZMod p → ℂ) :=
  Module.End.eigenspace (dftEnd p) (evals p i)

theorem lagr_mulVec_mem (i : Fin 4) (v : ZMod p → ℂ) :
    (lagr p i).mulVec v ∈ eigSp p i := by
  rw [eigSp, Module.End.mem_eigenspace_iff]
  change (Matrix.toLin' (dftMatrix p)) ((lagr p i).mulVec v) = _
  rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, dft_mul_lagr,
    Matrix.smul_mulVec]

/-- **Spanning**: the four eigenspaces span `ℂ^p` (via the Lagrange
combination). -/
theorem iSup_eigSp : (⨆ i, eigSp p i) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hne : (4 * sqp p ^ 3) ≠ 0 := by
    have := sqp_ne_zero p
    intro hc
    apply this
    have h4 : (4 : ℂ) ≠ 0 := by norm_num
    rcases mul_eq_zero.mp hc with hc' | hc'
    · exact absurd hc' h4
    · exact pow_eq_zero_iff (by norm_num) |>.mp hc'
  have hcombo := congrArg (fun M : Matrix (ZMod p) (ZMod p) ℂ =>
    Matrix.toLin' M v) (lagr_combo p)
  simp only [map_sum, _root_.map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, Matrix.toLin'_one, LinearMap.id_apply] at hcombo
  -- hcombo : ∑ i, I^i • (toLin' (lagr i)) v = (4√p³) • v
  have hv : v = (4 * sqp p ^ 3)⁻¹ •
      ∑ i : Fin 4, Complex.I ^ (i : ℕ) • (lagr p i).mulVec v := by
    rw [show ∑ i : Fin 4, Complex.I ^ (i : ℕ) • (lagr p i).mulVec v =
        ∑ i : Fin 4, Complex.I ^ (i : ℕ) • (Matrix.toLin' (lagr p i)) v from
      Finset.sum_congr rfl fun i _ => by rw [Matrix.toLin'_apply],
      hcombo, inv_smul_smul₀ hne]
  rw [hv]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ ?_)
  exact Submodule.mem_iSup_of_mem i (lagr_mulVec_mem p i v)

/-- **Independence**: eigenspaces for distinct eigenvalues. -/
theorem indep_eigSp : iSupIndep (eigSp p) :=
  (Module.End.eigenspaces_iSupIndep (dftEnd p)).comp (evals_injective p)

theorem internal_eigSp : DirectSum.IsInternal (eigSp p) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨indep_eigSp p, iSup_eigSp p⟩

/-- The four eigenvalue multiplicities. -/
noncomputable def mult (i : Fin 4) : ℕ := Module.finrank ℂ (eigSp p i)

/-- An eigenbasis of `ℂ^p`, collected from bases of the four eigenspaces. -/
noncomputable def eigBasis : Module.Basis (Σ i : Fin 4, Fin (mult p i)) ℂ (ZMod p → ℂ) :=
  (internal_eigSp p).collectedBasis (fun i => Module.finBasis ℂ (eigSp p i))

theorem eigBasis_mem (x : Σ i : Fin 4, Fin (mult p i)) :
    eigBasis p x ∈ eigSp p x.1 :=
  (internal_eigSp p).collectedBasis_mem _ x

theorem dftEnd_eigBasis (x : Σ i : Fin 4, Fin (mult p i)) :
    dftEnd p (eigBasis p x) = evals p x.1 • eigBasis p x :=
  Module.End.mem_eigenspace_iff.mp (eigBasis_mem p x)

/-- In the eigenbasis, the DFT is diagonal. -/
theorem toMatrix_dftEnd :
    LinearMap.toMatrix (eigBasis p) (eigBasis p) (dftEnd p) =
      Matrix.diagonal (fun x : Σ i : Fin 4, Fin (mult p i) => evals p x.1) := by
  ext x y
  rw [LinearMap.toMatrix_apply, dftEnd_eigBasis, _root_.map_smul,
    Module.Basis.repr_self,
    Finsupp.smul_apply, Finsupp.single_apply, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    simp
  · rw [if_neg fun hc => hxy hc.symm, if_neg hxy, smul_zero]

/-! ## The four multiplicity equations -/

/-- Diagonal sums over the sigma index reduce to multiplicity-weighted
sums. -/
theorem sigma_sum_eval (g : Fin 4 → ℂ) :
    (∑ x : Σ i : Fin 4, Fin (mult p i), g x.1) =
      ∑ i : Fin 4, (mult p i : ℂ) * g i := by
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Equation 1**: `∑ multᵢ = p`. -/
theorem sum_mult : (∑ i, mult p i) = p := by
  have h1 : Module.finrank ℂ (ZMod p → ℂ) = p := by
    rw [Module.finrank_pi, ZMod.card]
  have h2 := Module.finrank_eq_card_basis (eigBasis p)
  rw [h1, Fintype.card_sigma] at h2
  simpa using h2.symm

variable {p} in
/-- **Equation 2**: `g = ∑ multᵢ·cᵢ` (the trace in the eigenbasis). -/
theorem gauss_eq_sum_mult (hp2 : p ≠ 2) :
    gauss p = ∑ i, (mult p i : ℂ) * evals p i := by
  have h1 : LinearMap.trace ℂ _ (dftEnd p) = (dftMatrix p).trace :=
    Matrix.trace_toLin'_eq _
  have h2 : LinearMap.trace ℂ _ (dftEnd p) =
      Matrix.trace (LinearMap.toMatrix (eigBasis p) (eigBasis p) (dftEnd p)) :=
    LinearMap.trace_eq_matrix_trace ℂ (eigBasis p) _
  rw [toMatrix_dftEnd, Matrix.trace_diagonal, sigma_sum_eval] at h2
  rw [← trace_dftMatrix hp2, ← h1, h2]

variable {p} in
/-- **Equation 3**: `p = ∑ multᵢ·cᵢ²` (the trace of `F²`). -/
theorem sum_mult_sq (hp2 : p ≠ 2) :
    (p : ℂ) = ∑ i, (mult p i : ℂ) * (evals p i) ^ 2 := by
  have hcomp : dftEnd p ∘ₗ dftEnd p =
      Matrix.toLin' (dftMatrix p * dftMatrix p) := by
    rw [Matrix.toLin'_mul]
    rfl
  have h1 : LinearMap.trace ℂ _ (Matrix.toLin' (dftMatrix p * dftMatrix p)) =
      (dftMatrix p * dftMatrix p).trace :=
    Matrix.trace_toLin'_eq _
  have h2 : LinearMap.trace ℂ _ (dftEnd p ∘ₗ dftEnd p) =
      Matrix.trace (LinearMap.toMatrix (eigBasis p) (eigBasis p)
        (dftEnd p ∘ₗ dftEnd p)) :=
    LinearMap.trace_eq_matrix_trace ℂ (eigBasis p) _
  rw [LinearMap.toMatrix_comp _ (eigBasis p) _, toMatrix_dftEnd,
    Matrix.diagonal_mul_diagonal] at h2
  have h3 : Matrix.trace (Matrix.diagonal
      (fun x : Σ i : Fin 4, Fin (mult p i) => evals p x.1 * evals p x.1)) =
      ∑ i, (mult p i : ℂ) * (evals p i) ^ 2 := by
    rw [Matrix.trace_diagonal,
      show (fun x : Σ i : Fin 4, Fin (mult p i) => evals p x.1 * evals p x.1) =
        fun x : Σ i : Fin 4, Fin (mult p i) => (evals p x.1) ^ 2 from
        funext fun x => (sq (evals p x.1)).symm]
    exact sigma_sum_eval p (fun i => evals p i ^ 2)
  rw [h3] at h2
  rw [← trace_dftMatrix_sq hp2, ← h1, ← hcomp, h2]

/-- **Equation 4**: `det F = ∏ cᵢ^multᵢ`. -/
theorem det_eq_prod_mult :
    (dftMatrix p).det = ∏ i, (evals p i) ^ (mult p i) := by
  have h1 : LinearMap.det (dftEnd p) = (dftMatrix p).det := LinearMap.det_toLin' _
  have h2 : LinearMap.det (dftEnd p) =
      ((LinearMap.toMatrix (eigBasis p) (eigBasis p)) (dftEnd p)).det :=
    (LinearMap.det_toMatrix _ _).symm
  rw [toMatrix_dftEnd, Matrix.det_diagonal, ← Finset.univ_sigma_univ,
    Finset.prod_sigma] at h2
  have h3 : ∀ i : Fin 4,
      (∏ _j : Fin (mult p i), evals p i) = (evals p i) ^ (mult p i) := by
    intro i
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_congr rfl fun i _ => h3 i] at h2
  rw [← h1, h2]

/-! ## Pair sums (the combinatorics of the Vandermonde phase) -/

section PairSums

omit [Fact p.Prime]

/-- Swap the two summation orders over strict pairs. -/
theorem sum_Iio_swap (f : Fin p → Fin p → ℕ) :
    (∑ i : Fin p, ∑ j ∈ Finset.Iio i, f i j) =
      ∑ i : Fin p, ∑ j ∈ Finset.Ioi i, f j i := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨x.2, x.1⟩) (fun x => ⟨x.2, x.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Iio,
      Finset.mem_Ioi, true_and] at hx ⊢
    exact hx
  · rintro ⟨i, j⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Iio,
      Finset.mem_Ioi, true_and] at hx ⊢
    exact hx
  · rintro ⟨i, j⟩ _
    rfl
  · rintro ⟨i, j⟩ _
    rfl
  · rintro ⟨i, j⟩ _
    rfl

/-- `Ioi i` and `Iio i` partition the complement of the diagonal. -/
theorem sum_Ioi_add_sum_Iio (g : Fin p → Fin p → ℕ) (i : Fin p) :
    (∑ j ∈ Finset.Ioi i, g i j) + (∑ j ∈ Finset.Iio i, g i j) + g i i =
      ∑ j : Fin p, g i j := by
  have hdisj : Disjoint (Finset.Ioi i) (Finset.Iio i) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    simp only [Finset.mem_Ioi] at ha
    simp only [Finset.mem_Iio] at ha'
    exact absurd (ha.trans ha') (lt_irrefl _)
  have hunion : (Finset.Ioi i) ∪ (Finset.Iio i) = Finset.univ.erase i := by
    ext a
    simp only [Finset.mem_union, Finset.mem_Ioi, Finset.mem_Iio,
      Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro (h | h)
      · exact ne_of_gt h
      · exact ne_of_lt h
    · intro h
      rcases lt_or_gt_of_ne h with h' | h'
      · exact Or.inr h'
      · exact Or.inl h'
  rw [← Finset.sum_union hdisj, hunion,
    Finset.sum_erase_add _ _ (Finset.mem_univ i)]

/-- `2·#pairs = p(p-1)`. -/
theorem two_mul_card_pairs :
    2 * (∑ i : Fin p, (Finset.Ioi i).card) = p * (p - 1) := by
  classical
  have hswap : (∑ i : Fin p, (Finset.Iio i).card) =
      ∑ i : Fin p, (Finset.Ioi i).card := by
    simp only [Finset.card_eq_sum_ones]
    exact sum_Iio_swap p (fun _ _ => 1)
  rcases Nat.eq_zero_or_pos p with hp0 | hp0
  · subst hp0
    simp
  have hsplit : ∀ i : Fin p,
      (Finset.Ioi i).card + (Finset.Iio i).card + 1 = p := by
    intro i
    have h := sum_Ioi_add_sum_Iio p (fun _ _ => 1) i
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ,
      Fintype.card_fin] at h
    exact h
  have hagg : (∑ i : Fin p, (Finset.Ioi i).card) +
      (∑ i : Fin p, (Finset.Iio i).card) + p = p * p := by
    have h1 : ∑ i : Fin p, ((Finset.Ioi i).card + (Finset.Iio i).card + 1) =
        ∑ _i : Fin p, p :=
      Finset.sum_congr rfl fun i _ => hsplit i
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one, smul_eq_mul] at h1
    exact h1
  rw [hswap] at hagg
  have hpp : p * p = p * (p - 1) + p := by
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  omega

/-- `2·∑_{i<j}(i+j) = 2(p-1)·∑i` — each index lies in `p-1` pairs. -/
theorem two_mul_sum_pairs_add :
    2 * (∑ i : Fin p, ∑ j ∈ Finset.Ioi i, ((i : ℕ) + (j : ℕ))) +
      2 * (∑ i : Fin p, (i : ℕ)) =
      2 * (p * ∑ i : Fin p, (i : ℕ)) := by
  classical
  set T := ∑ i : Fin p, (i : ℕ) with hT
  set S := ∑ i : Fin p, ∑ j ∈ Finset.Ioi i, ((i : ℕ) + (j : ℕ)) with hS
  have hswap : (∑ i : Fin p, ∑ j ∈ Finset.Iio i, ((i : ℕ) + (j : ℕ))) = S := by
    rw [hS, sum_Iio_swap p (fun i j => (i : ℕ) + (j : ℕ))]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      omega
  have h2 : ∑ i : Fin p, ((∑ j ∈ Finset.Ioi i, ((i : ℕ) + (j : ℕ))) +
      (∑ j ∈ Finset.Iio i, ((i : ℕ) + (j : ℕ))) + ((i : ℕ) + (i : ℕ))) =
      S + S + 2 * T := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hswap, ← hS,
      Finset.sum_add_distrib, ← hT]
    omega
  have h3 : ∑ i : Fin p, ((∑ j ∈ Finset.Ioi i, ((i : ℕ) + (j : ℕ))) +
      (∑ j ∈ Finset.Iio i, ((i : ℕ) + (j : ℕ))) + ((i : ℕ) + (i : ℕ))) =
      ∑ i : Fin p, (p * (i : ℕ) + T) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_Ioi_add_sum_Iio p (fun a b => (a : ℕ) + (b : ℕ)) i,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, ← hT]
  have h4 : ∑ i : Fin p, (p * (i : ℕ) + T) = p * T + p * T := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hT, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have := h2.symm.trans (h3.trans h4)
  omega

/-- Gauss: `2·∑_{i : Fin p} i = p(p-1)`. -/
theorem two_mul_sum_range : 2 * (∑ i : Fin p, (i : ℕ)) = p * (p - 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => i) p, ← Finset.sum_range_id_mul_two p]
  ring

end PairSums

/-! ## `det F` as a Vandermonde determinant -/

/-- The index equivalence `Fin p ≃ ZMod p`. -/
noncomputable def zmodEquiv : Fin p ≃ ZMod p where
  toFun a := ((a : ℕ) : ZMod p)
  invFun x := ⟨x.val, x.val_lt⟩
  left_inv a := by
    ext
    exact ZMod.val_cast_of_lt a.isLt
  right_inv x := ZMod.natCast_rightInverse x

/-- `det F` is the Vandermonde determinant of the `p`-th roots of unity. -/
theorem det_dft_eq_vandermonde :
    (dftMatrix p).det =
      (Matrix.vandermonde (fun a : Fin p =>
        (stdAddChar : AddChar (ZMod p) ℂ) ((a : ℕ) : ZMod p))).det := by
  rw [← Matrix.det_submatrix_equiv_self (zmodEquiv p) (dftMatrix p)]
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply, dftMatrix, Matrix.of_apply,
    Matrix.vandermonde_apply, zmodEquiv, Equiv.coe_fn_mk]
  rw [show (((a : ℕ) : ZMod p)) * ((b : ℕ) : ZMod p) =
      ((b : ℕ) : ZMod p) * ((a : ℕ) : ZMod p) from mul_comm _ _]
  have h := AddChar.mulShift_spec' (stdAddChar : AddChar (ZMod p) ℂ)
    (b : ℕ) (((a : ℕ) : ZMod p))
  rw [AddChar.mulShift_apply] at h
  exact h

/-- The root-of-unity values. -/
theorem stdAddChar_natCast (a : ℕ) :
    (stdAddChar : AddChar (ZMod p) ℂ) ((a : ℕ) : ZMod p) =
      Complex.exp (2 * Real.pi * Complex.I * a / p) := by
  have h := ZMod.stdAddChar_coe (N := p) (a : ℤ)
  push_cast at h
  exact_mod_cast h

/-! ## The phase of the Vandermonde determinant -/

variable {p} in
/-- One Vandermonde factor, in polar form: the only analytic input is
`sin > 0` on `(0, π)` (used later); here the exact half-angle split. -/
theorem vand_factor (a b : Fin p) :
    Complex.exp (2 * Real.pi * Complex.I * b / p) -
      Complex.exp (2 * Real.pi * Complex.I * a / p) =
      Complex.exp ((Real.pi * Complex.I / p) * ((a : ℕ) + (b : ℕ))) *
        ((2 * Complex.I) *
          (Real.sin (Real.pi * ((b : ℕ) - (a : ℕ)) / p) : ℂ)) := by
  have hp0 : (p : ℂ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hsin : ∀ z : ℂ, 2 * Complex.I * Complex.sin z =
      Complex.exp (z * Complex.I) - Complex.exp (-(z * Complex.I)) := by
    intro z
    rw [Complex.sin]
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  have key : Complex.exp ((Real.pi * Complex.I / p) * ((a : ℕ) + (b : ℕ))) *
      ((2 * Complex.I) *
        (Real.sin (Real.pi * ((b : ℕ) - (a : ℕ)) / p) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * b / p) -
        Complex.exp (2 * Real.pi * Complex.I * a / p) := by
    rw [Complex.ofReal_sin, hsin, mul_sub, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    · congr 1
      push_cast
      field_simp
      ring
    · congr 1
      push_cast
      field_simp
      ring
  exact key.symm

variable {p} in
/-- **The determinant phase**: `det F = R·I^{#pairs}` with `R > 0`. -/
theorem det_dft_phase (hp2 : p ≠ 2) :
    ∃ R : ℝ, 0 < R ∧
      (dftMatrix p).det =
        (R : ℂ) * Complex.I ^ (∑ i : Fin p, (Finset.Ioi i).card) := by
  classical
  have hp0 : (0 : ℕ) < p := (Fact.out : p.Prime).pos
  have hp0R : (0 : ℝ) < p := by exact_mod_cast hp0
  -- the sine product and its positivity
  set Rsin : ℝ := ∏ i : Fin p, ∏ j ∈ Finset.Ioi i,
    Real.sin (Real.pi * ((j : ℕ) - (i : ℕ)) / p) with hRsin
  have hsin_pos : 0 < Rsin := by
    rw [hRsin]
    refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_
    have hij : i < j := Finset.mem_Ioi.mp hj
    have h1 : (0 : ℝ) < (j : ℕ) - (i : ℕ) := by
      have : (i : ℕ) < (j : ℕ) := hij
      have := Nat.cast_lt (α := ℝ) |>.mpr this
      linarith
    have h2 : ((j : ℕ) : ℝ) - (i : ℕ) < p := by
      have hj' : (j : ℕ) < p := j.isLt
      have hj'' : ((j : ℕ) : ℝ) < p := by exact_mod_cast hj'
      have hi0 : (0 : ℝ) ≤ (i : ℕ) := by positivity
      linarith
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [div_lt_iff₀ hp0R]
      calc Real.pi * ((j : ℕ) - (i : ℕ)) < Real.pi * p := by
            have := Real.pi_pos
            exact mul_lt_mul_of_pos_left h2 this
        _ = Real.pi * p := rfl
  -- the total pair-sum exponential is 1
  obtain ⟨m, hm⟩ : ∃ m, p = 2 * m + 1 := by
    have hodd := (Fact.out : p.Prime).odd_of_ne_two hp2
    obtain ⟨m, hm⟩ := hodd
    exact ⟨m, by omega⟩
  set S : ℕ := ∑ i : Fin p, ∑ j ∈ Finset.Ioi i, ((i : ℕ) + (j : ℕ)) with hSdef
  have hSc : (S : ℂ) = 2 * p * (m : ℂ) ^ 2 := by
    have h1 := two_mul_sum_pairs_add p
    have h2 := two_mul_sum_range p
    rw [← hSdef] at h1
    set T : ℕ := ∑ i : Fin p, (i : ℕ) with hTdef
    have h1z : 2 * (S : ℤ) + 2 * T = 2 * (p * T) := by exact_mod_cast h1
    have h2z : 2 * (T : ℤ) = p * ((p : ℤ) - 1) := by
      have hcast : ((p : ℤ) - 1) = ((p - 1 : ℕ) : ℤ) := by
        have h1p : (1 : ℕ) ≤ p := hp0
        push_cast [Nat.cast_sub h1p]
        ring
      rw [hcast]
      exact_mod_cast h2
    have hmz : (p : ℤ) = 2 * m + 1 := by exact_mod_cast hm
    have hSz : 2 * (S : ℤ) = 4 * ((p : ℤ) * (m : ℤ) ^ 2) := by
      linear_combination h1z + ((p : ℤ) - 1) * h2z +
        (p : ℤ) * ((p : ℤ) - 1 + 2 * m) * hmz
    set X : ℤ := (p : ℤ) * (m : ℤ) ^ 2 with hX
    have hSX : (S : ℤ) = 2 * X := by omega
    have hcc : ((S : ℤ) : ℂ) = ((2 * X : ℤ) : ℂ) := by exact_mod_cast hSX
    rw [hX] at hcc
    push_cast at hcc
    rw [hcc]
    ring
  -- Step 1: the determinant as the double product of root differences
  have hdet : (dftMatrix p).det =
      ∏ i : Fin p, ∏ j ∈ Finset.Ioi i,
        (Complex.exp (2 * Real.pi * Complex.I * j / p) -
          Complex.exp (2 * Real.pi * Complex.I * i / p)) := by
    rw [det_dft_eq_vandermonde, Matrix.det_vandermonde]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => by
      rw [stdAddChar_natCast, stdAddChar_natCast]
  -- Step 2: polar form of each factor
  have hdet2 : (dftMatrix p).det =
      ∏ i : Fin p, ∏ j ∈ Finset.Ioi i,
        (Complex.exp ((Real.pi * Complex.I / p) * ((i : ℕ) + (j : ℕ))) *
          (2 * Complex.I *
            (Real.sin (Real.pi * ((j : ℕ) - (i : ℕ)) / p) : ℂ))) := by
    rw [hdet]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ =>
      vand_factor i j
  -- Step 3: split into exponential, constant and sine parts
  have hsplit : (dftMatrix p).det =
      (∏ i : Fin p, ∏ j ∈ Finset.Ioi i,
        Complex.exp ((Real.pi * Complex.I / p) * ((i : ℕ) + (j : ℕ)))) *
      ((∏ i : Fin p, ∏ j ∈ Finset.Ioi i, (2 * Complex.I : ℂ)) *
       (∏ i : Fin p, ∏ j ∈ Finset.Ioi i,
         ((Real.sin (Real.pi * ((j : ℕ) - (i : ℕ)) / p)) : ℂ))) := by
    rw [hdet2]
    simp only [Finset.prod_mul_distrib]
  -- Step 4: the exponential part is 1
  have hE : (∏ i : Fin p, ∏ j ∈ Finset.Ioi i,
      Complex.exp ((Real.pi * Complex.I / p) * ((i : ℕ) + (j : ℕ)))) = 1 := by
    have h1 : ∀ i : Fin p,
        (∏ j ∈ Finset.Ioi i,
          Complex.exp ((Real.pi * Complex.I / p) * ((i : ℕ) + (j : ℕ)))) =
        Complex.exp (∑ j ∈ Finset.Ioi i,
          (Real.pi * Complex.I / p) * ((i : ℕ) + (j : ℕ))) :=
      fun i => (Complex.exp_sum _ _).symm
    rw [Finset.prod_congr rfl fun i _ => h1 i, ← Complex.exp_sum]
    have h2 : (∑ i : Fin p, ∑ j ∈ Finset.Ioi i,
        (Real.pi * Complex.I / p) * ((i : ℕ) + (j : ℕ))) =
        (Real.pi * Complex.I / p) * (S : ℂ) := by
      have hcast : ((S : ℕ) : ℂ) =
          ∑ i : Fin p, ∑ j ∈ Finset.Ioi i, (((i : ℕ) : ℂ) + ((j : ℕ) : ℂ)) := by
        rw [hSdef]
        push_cast
        rfl
      rw [hcast, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    have hpC : (p : ℂ) ≠ 0 := by
      exact_mod_cast hp0.ne'
    rw [h2, hSc,
      show (Real.pi * Complex.I / p) * (2 * p * (m : ℂ) ^ 2) =
        ((m ^ 2 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
        push_cast
        field_simp]
    exact Complex.exp_eq_one_iff.mpr ⟨(m ^ 2 : ℤ), by push_cast; ring⟩
  -- Step 5: the constant part
  have hC : (∏ i : Fin p, ∏ j ∈ Finset.Ioi i, (2 * Complex.I : ℂ)) =
      (2 * Complex.I) ^ (∑ i : Fin p, (Finset.Ioi i).card) := by
    simp only [Finset.prod_const]
    exact Finset.prod_pow_eq_pow_sum _ _ _
  -- Step 6: the sine part
  have hW : (∏ i : Fin p, ∏ j ∈ Finset.Ioi i,
      ((Real.sin (Real.pi * ((j : ℕ) - (i : ℕ)) / p)) : ℂ)) = (Rsin : ℂ) := by
    rw [hRsin]
    push_cast
    rfl
  refine ⟨2 ^ (∑ i : Fin p, (Finset.Ioi i).card) * Rsin, by positivity, ?_⟩
  rw [hsplit, hE, one_mul, hC, hW, mul_pow]
  push_cast
  ring

/-! ## Powers of `I` modulo 4 -/

omit [Fact p.Prime] in
theorem I_pow_mod {a : ℕ} : Complex.I ^ a = Complex.I ^ (a % 4) := by
  conv_lhs => rw [← Nat.div_add_mod a 4]
  rw [pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]

omit [Fact p.Prime] in
theorem I_pow_eq_iff {a b : ℕ} : Complex.I ^ a = Complex.I ^ b ↔ a % 4 = b % 4 := by
  constructor
  · intro h
    rw [I_pow_mod (a := a), I_pow_mod (a := b)] at h
    exact I_pow_inj (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h
  · intro h
    rw [I_pow_mod (a := a), I_pow_mod (a := b), h]

/-! ## The endgame: extracting the sign -/

variable {p}

/-- The trace equation, in integer form:
`g = √p·(A + B·i)`, `A = d₀ - d₂`, `B = d₁ - d₃`. -/
theorem gauss_expand (hp2 : p ≠ 2) :
    gauss p = sqp p * ((((mult p 0 : ℤ) - (mult p 2 : ℤ) : ℤ) : ℂ) +
      (((mult p 1 : ℤ) - (mult p 3 : ℤ) : ℤ) : ℂ) * Complex.I) := by
  rw [gauss_eq_sum_mult hp2, Fin.sum_univ_four]
  have h0 : evals p 0 = sqp p := by
    have he : evals p 0 = Complex.I ^ (0 : ℕ) * sqp p := rfl
    rw [he, pow_zero, one_mul]
  have h1 : evals p 1 = Complex.I * sqp p := by
    have he : evals p 1 = Complex.I ^ (1 : ℕ) * sqp p := rfl
    rw [he, pow_one]
  have h2 : evals p 2 = -sqp p := by
    have he : evals p 2 = Complex.I ^ (2 : ℕ) * sqp p := rfl
    rw [he, Complex.I_sq, neg_one_mul]
  have h3 : evals p 3 = -(Complex.I * sqp p) := by
    have he : evals p 3 = Complex.I ^ (3 : ℕ) * sqp p := rfl
    rw [he, show Complex.I ^ (3 : ℕ) = -Complex.I by
      rw [pow_succ, Complex.I_sq, neg_one_mul], neg_mul]
  rw [h0, h1, h2, h3]
  push_cast
  ring

/-- The circle equation `A² + B² = 1`. -/
theorem sq_add_sq_eq_one (hp2 : p ≠ 2) :
    ((mult p 0 : ℤ) - mult p 2) ^ 2 + ((mult p 1 : ℤ) - mult p 3) ^ 2 = 1 := by
  set A : ℤ := (mult p 0 : ℤ) - mult p 2 with hA
  set B : ℤ := (mult p 1 : ℤ) - mult p 3 with hB
  have hnorm := norm_gaussSum_quadratic hp2
  rw [gauss_expand hp2] at hnorm
  rw [norm_mul] at hnorm
  have hs : ‖sqp p‖ = Real.sqrt p := by
    rw [sqp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sqp_pos p)]
  have hz : ‖((A : ℂ) + (B : ℂ) * Complex.I)‖ ^ 2 = (A : ℝ) ^ 2 + (B : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hre : ((A : ℂ) + (B : ℂ) * Complex.I).re = (A : ℝ) := by
      simp
    have him : ((A : ℂ) + (B : ℂ) * Complex.I).im = (B : ℝ) := by
      simp
    rw [hre, him]
    ring
  have hsp : (0 : ℝ) < Real.sqrt p := sqp_pos p
  have hkey : Real.sqrt p * ‖((A : ℂ) + (B : ℂ) * Complex.I)‖ = Real.sqrt p := by
    rw [← hs]
    exact hnorm.symm ▸ (by rw [hs])
  have hone : ‖((A : ℂ) + (B : ℂ) * Complex.I)‖ = 1 :=
    mul_left_cancel₀ (ne_of_gt hsp) (by rw [hkey, mul_one])
  have : (A : ℝ) ^ 2 + (B : ℝ) ^ 2 = 1 := by
    rw [← hz, hone, one_pow]
  exact_mod_cast this

/-- The `trace F²` equation in integer form:
`(d₀ + d₂) - (d₁ + d₃) = 1`. -/
theorem mult_diff_eq_one (hp2 : p ≠ 2) :
    ((mult p 0 : ℤ) + mult p 2) - ((mult p 1 : ℤ) + mult p 3) = 1 := by
  have h := sum_mult_sq hp2
  rw [Fin.sum_univ_four] at h
  have h0 : (evals p 0) ^ 2 = (p : ℂ) := by
    have he : evals p 0 = Complex.I ^ (0 : ℕ) * sqp p := rfl
    rw [he, pow_zero, one_mul, sqp_sq]
  have h1 : (evals p 1) ^ 2 = -(p : ℂ) := by
    have he : evals p 1 = Complex.I ^ (1 : ℕ) * sqp p := rfl
    rw [he, pow_one, mul_pow, Complex.I_sq, sqp_sq, neg_one_mul]
  have h2 : (evals p 2) ^ 2 = (p : ℂ) := by
    have he : evals p 2 = Complex.I ^ (2 : ℕ) * sqp p := rfl
    rw [he, mul_pow, ← pow_mul, show (2 : ℕ) * 2 = 4 from rfl,
      Complex.I_pow_four, one_mul, sqp_sq]
  have h3 : (evals p 3) ^ 2 = -(p : ℂ) := by
    have he : evals p 3 = Complex.I ^ (3 : ℕ) * sqp p := rfl
    rw [he, mul_pow, ← pow_mul, show (3 : ℕ) * 2 = 6 from rfl,
      show Complex.I ^ (6 : ℕ) = -1 by
        rw [show (6 : ℕ) = 4 + 2 from rfl, pow_add, Complex.I_pow_four,
          one_mul, Complex.I_sq],
      sqp_sq, neg_one_mul]
  rw [h0, h1, h2, h3] at h
  have hpC : (p : ℂ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  -- `p = ((d₀+d₂) - (d₁+d₃))·p`
  have hkey : (p : ℂ) * 1 = (p : ℂ) *
      ((((mult p 0 : ℤ) + mult p 2) - ((mult p 1 : ℤ) + mult p 3) : ℤ) : ℂ) := by
    push_cast
    linear_combination h
  have := mul_left_cancel₀ hpC hkey
  exact_mod_cast this.symm

/-- The determinant, expanded over the four eigenvalues. -/
theorem det_expand :
    (dftMatrix p).det =
      Complex.I ^ (mult p 1 + 2 * mult p 2 + 3 * mult p 3) * sqp p ^ p := by
  rw [det_eq_prod_mult, Fin.prod_univ_four]
  have h0 : evals p 0 = Complex.I ^ (0 : ℕ) * sqp p := rfl
  have h1 : evals p 1 = Complex.I ^ (1 : ℕ) * sqp p := rfl
  have h2 : evals p 2 = Complex.I ^ (2 : ℕ) * sqp p := rfl
  have h3 : evals p 3 = Complex.I ^ (3 : ℕ) * sqp p := rfl
  have hsum := sum_mult p
  rw [Fin.sum_univ_four] at hsum
  rw [h0, h1, h2, h3]
  calc (Complex.I ^ (0 : ℕ) * sqp p) ^ mult p 0 *
        (Complex.I ^ (1 : ℕ) * sqp p) ^ mult p 1 *
        (Complex.I ^ (2 : ℕ) * sqp p) ^ mult p 2 *
        (Complex.I ^ (3 : ℕ) * sqp p) ^ mult p 3 =
      Complex.I ^ (mult p 1 + 2 * mult p 2 + 3 * mult p 3) *
        sqp p ^ (mult p 0 + mult p 1 + mult p 2 + mult p 3) := by
        ring
    _ = Complex.I ^ (mult p 1 + 2 * mult p 2 + 3 * mult p 3) * sqp p ^ p := by
        rw [hsum]

/-- **The phase equation**: `I^{d₁+2d₂+3d₃} = I^{#pairs}`. -/
theorem I_pow_mult_eq (hp2 : p ≠ 2) :
    Complex.I ^ (mult p 1 + 2 * mult p 2 + 3 * mult p 3) =
      Complex.I ^ (∑ i : Fin p, (Finset.Ioi i).card) := by
  obtain ⟨R, hR, hphase⟩ := det_dft_phase hp2
  have hdet := det_expand (p := p)
  have heq : Complex.I ^ (mult p 1 + 2 * mult p 2 + 3 * mult p 3) * sqp p ^ p =
      (R : ℂ) * Complex.I ^ (∑ i : Fin p, (Finset.Ioi i).card) := by
    rw [← hdet, hphase]
  have hnorm : Real.sqrt p ^ p = R := by
    have hn := congrArg norm heq
    rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, Complex.norm_I,
      one_pow, one_pow, one_mul, mul_one] at hn
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] at hn
    rw [show ‖sqp p‖ = Real.sqrt p from by
      rw [sqp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sqp_pos p)]] at hn
    exact hn
  have hsne : (sqp p ^ p : ℂ) ≠ 0 :=
    pow_ne_zero _ (sqp_ne_zero p)
  have heq2 : Complex.I ^ (mult p 1 + 2 * mult p 2 + 3 * mult p 3) * sqp p ^ p =
      Complex.I ^ (∑ i : Fin p, (Finset.Ioi i).card) * sqp p ^ p := by
    rw [heq, ← hnorm]
    rw [show ((Real.sqrt p ^ p : ℝ) : ℂ) = sqp p ^ p from by
      rw [sqp]
      push_cast
      rfl]
    ring
  exact mul_right_cancel₀ hsne heq2

/-- The pure sign arithmetic: the five numeric constraints force the
unique solution. -/
theorem sign_arithmetic {P d0 d1 d2 d3 S0 : ℕ}
    (hsum : d0 + d1 + d2 + d3 = P)
    (hdiff : ((d0 : ℤ) + d2) - ((d1 : ℤ) + d3) = 1)
    (hcirc : ((d0 : ℤ) - d2) ^ 2 + ((d1 : ℤ) - d3) ^ 2 = 1)
    (hphase : (d1 + 2 * d2 + 3 * d3) % 4 = S0 % 4)
    (hS0 : 2 * S0 = P * (P - 1)) :
    (P % 4 = 1 → (d0 : ℤ) - d2 = 1 ∧ (d1 : ℤ) - d3 = 0) ∧
    (P % 4 = 3 → (d0 : ℤ) - d2 = 0 ∧ (d1 : ℤ) - d3 = 1) := by
  have hA1 : -1 ≤ (d0 : ℤ) - d2 := by nlinarith [sq_nonneg ((d1 : ℤ) - d3)]
  have hA2 : (d0 : ℤ) - d2 ≤ 1 := by nlinarith [sq_nonneg ((d1 : ℤ) - d3)]
  have hB1 : -1 ≤ (d1 : ℤ) - d3 := by nlinarith [sq_nonneg ((d0 : ℤ) - d2)]
  have hB2 : (d1 : ℤ) - d3 ≤ 1 := by nlinarith [sq_nonneg ((d0 : ℤ) - d2)]
  constructor
  · intro h4
    obtain ⟨m, hm⟩ : ∃ m, P = 4 * m + 1 := ⟨P / 4, by omega⟩
    have hAval : (d0 : ℤ) - d2 = 1 ∨ (d0 : ℤ) - d2 = -1 := by omega
    have hBsq : ((d1 : ℤ) - d3) ^ 2 = 0 := by
      rcases hAval with h | h <;> nlinarith
    have hBval : (d1 : ℤ) - d3 = 0 := sq_eq_zero_iff.mp hBsq
    have hS0m : S0 % 4 = (2 * m) % 4 := by
      have hstep : 4 * m + 1 - 1 = 4 * m := by omega
      have hprod : (4 * m + 1) * (4 * m + 1 - 1) = 4 * (m * (4 * m + 1)) := by
        rw [hstep]
        ring
      rw [hm] at hS0
      obtain ⟨Am, hAm⟩ : ∃ x, m * (4 * m + 1) = x := ⟨_, rfl⟩
      rw [hprod, hAm] at hS0
      have hAmm : Am % 2 = m % 2 := by
        rw [← hAm, Nat.mul_mod, show (4 * m + 1) % 2 = 1 by omega, mul_one]
        omega
      omega
    refine ⟨?_, hBval⟩
    rcases hAval with h | h
    · exact h
    · exfalso
      omega
  · intro h4
    obtain ⟨m, hm⟩ : ∃ m, P = 4 * m + 3 := ⟨P / 4, by omega⟩
    have hBval : (d1 : ℤ) - d3 = 1 ∨ (d1 : ℤ) - d3 = -1 := by omega
    have hAsq : ((d0 : ℤ) - d2) ^ 2 = 0 := by
      rcases hBval with h | h <;> nlinarith
    have hAval : (d0 : ℤ) - d2 = 0 := sq_eq_zero_iff.mp hAsq
    have hS0m : S0 % 4 = (2 * m + 3) % 4 := by
      have hstep : 4 * m + 3 - 1 = 4 * m + 2 := by omega
      have hprod : (4 * m + 3) * (4 * m + 3 - 1) =
          2 * (8 * (m * m) + 10 * m + 3) := by
        rw [hstep]
        ring
      rw [hm] at hS0
      obtain ⟨M2, hM2⟩ : ∃ x, m * m = x := ⟨_, rfl⟩
      rw [hprod, hM2] at hS0
      omega
    refine ⟨hAval, ?_⟩
    rcases hBval with h | h
    · exact h
    · exfalso
      omega

/-- **Gauss's sign theorem**:
`∑_n exp(2πi n²/p) = √p` for `p ≡ 1 (mod 4)`, `= i√p` for `p ≡ 3`. -/
theorem gauss_eq (hp2 : p ≠ 2) :
    gauss p = if p % 4 = 1 then ((Real.sqrt p : ℝ) : ℂ)
      else Complex.I * ((Real.sqrt p : ℝ) : ℂ) := by
  classical
  -- gather the numeric equations
  have hsum : mult p 0 + mult p 1 + mult p 2 + mult p 3 = p := by
    have h := sum_mult p
    rw [Fin.sum_univ_four] at h
    exact h
  have hdiff := mult_diff_eq_one hp2
  have hcirc := sq_add_sq_eq_one hp2
  have hphase : (mult p 1 + 2 * mult p 2 + 3 * mult p 3) % 4 =
      (∑ i : Fin p, (Finset.Ioi i).card) % 4 := by
    have h := I_pow_mult_eq hp2
    rw [I_pow_eq_iff] at h
    exact h
  have hS0 := two_mul_card_pairs p
  have hgauss := gauss_expand hp2
  -- the sign arithmetic
  have hkey := sign_arithmetic hsum hdiff hcirc hphase hS0
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by
    have h2 := (Fact.out : p.Prime).two_le
    have hodd : p % 2 = 1 :=
      Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp2)
    omega
  rcases hp4 with h4 | h4
  · rw [if_pos h4]
    obtain ⟨hA, hB⟩ := hkey.1 h4
    rw [hgauss, hA, hB]
    rw [sqp]
    push_cast
    ring
  · rw [if_neg (by omega)]
    obtain ⟨hA, hB⟩ := hkey.2 h4
    rw [hgauss, hA, hB]
    rw [sqp]
    push_cast
    ring

end LeanDring.GaussSign
