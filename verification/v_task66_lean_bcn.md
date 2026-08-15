# v_task66 — Theorem BC-n formalized in Lean 4: `LeanDring/Even/BCSeparation.lean`

Date 2026-08-08.  File: `lean_dring/LeanDring/Even/BCSeparation.lean`
(new, 300 lines).  Checked with `taskset -c 0 lake env lean
LeanDring/Even/BCSeparation.lean` (Lean 4.32.0 / Mathlib v4.32.0), serial,
one process.  **0 errors, 0 warnings, 0 `sorry`.**

Formalizes NOTES §4bl + addendum (`v_task64_bc3_repair.md`, audited in
`v_task65_bcn_audit.md`) *modulo* two named group-theoretic inputs.

---

## 1. Proven outright in Lean (no axioms beyond the standard three)

**Arithmetic core** (ℕ throughout; `ε` is encoded by a shift hypothesis
`hw : w + 1 = q^n ∨ w = q^n + 1`, and `v` by `2v = q^n·w`, so no truncated
subtraction and no division anywhere):

| lemma | statement |
|---|---|
| `iota q n` | `∑_{i<2n} q^i` — geometric-sum form of `ι₁ = (q^{2n}−1)/(q−1)` |
| `iota_coprime_base` | `n ≥ 1 → gcd(ι₁, q) = 1` (via `ι₁ = q·S + 1`, `geom_sum_succ`) |
| `add_one_lt_iota` | `q ≥ 2, n ≥ 2 → q^n + 1 < ι₁` (the `q^0` and `q^{2n−1}` terms alone) |
| `lt_iota` | `w < ι₁` for `w = q^n ∓ 1` |
| `not_dvd_of_two_mul_eq` | **`ι₁ ∤ v`** — `ι₁ ∣ v ⟹ ι₁ ∣ 2v = q^n w`, coprimality ⟹ `ι₁ ∣ w`, contradicting `0 < w < ι₁` |
| `lt_pow_two_mul` | **`v < q^{2n}`** |
| `one_lt_of_two_mul_eq` | **`1 < v`** (`q ≥ 3`), so the witness is not the trivial conductor |

**D-ring interface** (this is the real plug-in, not cosmetic):

* `IsIndexValue G x := ∃ c, conductorMultiplicity (DRing G) c ≠ 0 ∧ c * x = |G|`
  — `x = |G| / c` is the `ind*` value of §4aj, read off a conductor value via
  Müller Satz 2.3.3 (`conductor (H, hH') = (N_G(H,hH') : H')`).  Quantifying
  over *conductor values* is exactly quantifying over all pairs, i.e. the
  v_task65-repaired form.
* `IsIndexValue.transfer` — **PROVEN**: an index value transports along
  `DRing G ≃+* DRing H` between equal-order groups.  Its only input is the
  kernel-checked `conductorMultiplicity_eq_of_ringEquiv`
  (`Even/OrderTransfer.lean:150`).

**Erratum repair, formalized as far as it is stateable in Mathlib:**

* `PairNormalizer H h : Set G := {g | g ∈ N_G(H) ∧ ⁅g,h⁆ ∈ ⁅H,H⁆}` and
  `pairNormalizer_le_normalizer : ∀ g ∈ PairNormalizer H h, g ∈ N_G(H)`
  — **PROVEN** (definitional).  Honest note: this is the repair's *statement*,
  not its consequence; the consequence ("every conductor value is a multiple
  of `[G : N_G(H)]`") needs Müller's Satz 2.3.3 dictionary, which is not
  formalized, and is therefore absorbed into the C-side hypothesis below,
  which is *stated in already-repaired form* (over all conductor values).

**Assembly**:

```
theorem bcSeparation {B C} [Group B] [Group C] [Fintype B] [Fintype C]
    {q n v w : ℕ} (hq : 3 ≤ q) (hn : 3 ≤ n)
    (hw : w + 1 = q ^ n ∨ w = q ^ n + 1) (hv : 2 * v = q ^ n * w)
    (hcard : Nat.card B = Nat.card C)
    (hB : BAnisotropicWitness B v) (hC : CIndexDichotomy C q n) :
    IsEmpty (DRing B ≃+* DRing C)
```

plus `not_nonempty_dringEquiv_of_bcSeparation` (the `¬ Nonempty` form used by
the rest of the corpus).  Proof: transfer the witness to `C`, then the
dichotomy gives `v = 1` (killed by `one_lt_of_two_mul_eq`) or `ι₁ ∣ v` (killed
by `not_dvd_of_two_mul_eq`), the range side-condition being
`lt_pow_two_mul`.

## 2. What remains hypothesis (the "known theorems" package) — exactly three

1. `hcard : Nat.card B = Nat.card C` — `|Ω_{2n+1}(q)| = |PSp_{2n}(q)|`,
   classical order formulas.
2. `BAnisotropicWitness B v := IsIndexValue B v` — §4bl §2 / v_task65 §1:
   the anisotropic-point orbit `q^n(q^n−ε)/2` of `Ω_{2n+1}(q)`, witnessed by
   `H = ⟨−r_e⟩` with `N_B(H) = C_B(z_e) = Stab_B(⟨e⟩)`.  GAP-verified
   `q = 3,5,7,9` (`n = 3`) and `n = 4, q = 3`.
3. `CIndexDichotomy C q n := ∀ x, IsIndexValue C x → x < q^{2n} → x = 1 ∨ ι₁ ∣ x`
   — §4bl §3 + the v_task65 §3 repair: `P₁` is the only maximal subgroup of
   `Sp_{2n}(q)` of index `< q^{2n}` (Aschbacher/Kleidman–Liebeck at order
   level; BHR 8.28/8.29 orders at `n = 3`; Liebeck's `S`-bound for `n ≥ 4`),
   pushed over all conductor pairs by `N_G(H,hH') ≤ N_G(H)`.  Machine-checked
   `n ∈ [3,8]`, odd prime powers `q < 200`.

Note the parameters `q, n` enter only arithmetically: `q` is a bare `ℕ` with
`3 ≤ q` (no prime-power or oddness hypothesis is needed — oddness is what makes
`v` an integer, and that is already encoded by `2v = q^n·w`).

## 3. Axiom audit

`AxiomAudit.lean` audits the root module, which does **not** import the `Even/`
exploratory layer (no `Even` theorem is registered there — `SimpleRigidity`,
`OrderTransfer` included).  Following that convention, the `#print axioms`
block lives at the end of `BCSeparation.lean` itself; output of the single-file
check:

```
'LeanDring.Even.iota_coprime_base'      : [propext, Classical.choice, Quot.sound]
'LeanDring.Even.add_one_lt_iota'        : [propext, Classical.choice, Quot.sound]
'LeanDring.Even.lt_iota'                : [propext, Classical.choice, Quot.sound]
'LeanDring.Even.not_dvd_of_two_mul_eq'  : [propext, Classical.choice, Quot.sound]
'LeanDring.Even.lt_pow_two_mul'         : [propext, Classical.choice, Quot.sound]
'LeanDring.Even.one_lt_of_two_mul_eq'   : [propext, Quot.sound]
'LeanDring.Even.pairNormalizer_le_normalizer' : [propext, Classical.choice, Quot.sound]
'LeanDring.Even.IsIndexValue.transfer'  : [propext, Classical.choice, Quot.sound]
'LeanDring.Even.bcSeparation'           : [propext, Classical.choice, Quot.sound]
'LeanDring.Even.not_nonempty_dringEquiv_of_bcSeparation' : [propext, Classical.choice, Quot.sound]
```

No custom axiom, no `sorry`.  (`sorry` occurs twice in the file — both times in
prose inside docstrings.)

## 4. Honest notes on alignment with the real DRing machinery

* **Genuine, not cosmetic**: the contradiction is produced by
  `conductorMultiplicity_eq_of_ringEquiv`, the same kernel-checked invariance
  that `simpleGroupTheorem` and `TwinSeparation` run on.  `IsIndexValue` is a
  thin, faithful wrapper of `conductorMultiplicity` plus `Nat.card`.
* **The soft joint** is the identification `ind* = |G| / conductor`, i.e.
  Müller Satz 2.3.3.  It is *not* formalized anywhere in the corpus
  (`ConductorDictionary` in `SimpleRigidity.lean` is the analogous unformalized
  input for conductor `1`).  Consequently hypotheses 2 and 3 are stated in
  conductor language and their group-theoretic *content* (orbits, maximal
  subgroups) is what a reader must supply — as with every other Lie-type input
  in this project, since Mathlib has no Lie-type groups.
* **The pair erratum** is handled by construction rather than by proof: the
  C-side hypothesis quantifies over conductor values (all pairs), so the
  identity-coset-only reading of `I(G)` that v_task65 flagged cannot recur.
  `pairNormalizer_le_normalizer` records the group-theoretic half formally, but
  it is definitional and does not shrink the assumed surface by itself.
* **Not proven here**: that `hB` and `hC` are jointly *satisfiable* for the
  actual groups — that is the mathematical content, and it is external.  The
  Lean theorem says: whatever pair of finite groups satisfies these three
  named facts, its D-rings are non-isomorphic.

## 5. Reproduce

```
cd lean_dring && taskset -c 0 lake env lean LeanDring/Even/BCSeparation.lean
```

(~1 min after a warm Mathlib cache; single process, per the standing no-parallel-Lean rule.)
