# v_task67 — Theorem AT (endgame) formalized in Lean 4: `LeanDring/Even/ATSeparation.lean`

Date 2026-08-08.  File: `lean_dring/LeanDring/Even/ATSeparation.lean` (new,
~260 lines).  Checked with

```
cd lean_dring && taskset -c 0 lake build LeanDring.Even.BCSeparation
              && taskset -c 0 lake env lean LeanDring/Even/ATSeparation.lean
```

(Lean 4.32.0 / Mathlib v4.32.0, serial, one taskset-pinned process at a time.)
**0 errors, 0 warnings, 0 `sorry`.**  `BCSeparation.lean` was rebuilt first (it
had no `.olean`; it is outside the root import graph) and re-checked: unchanged,
still 0 errors / 0 `sorry`, same axiom output as v_task66.  No refactor was
needed — `ATSeparation` simply `import`s `LeanDring.Even.BCSeparation` and
reuses `IsIndexValue` / `IsIndexValue.transfer` verbatim.

Formalizes the **endgame** of NOTES §4ba + addenda (v_task47, repaired by the
v_task48 audit, hypothesis (H2′) discharged by v_task49): the SPEC / GAP /
squeeze chain that killed the last two open rows.

---

## 1. The two binomial identities (the mathematical point of the file)

The informal statement of the squeeze — "`ρ` lies in `(n−3, 0.3(n−3)(n−4))`,
hence `C(n,3)ρ` lies in the hole `(4C(n,4), 6C(n,5))`" — looks like it needs
rational arithmetic.  It does not: the two hole endpoints are *exactly*
`C(n,3)` times the two `ρ`-bounds.  Both identities are proven in ℕ from
`Nat.choose_succ_right_eq` (`C(n,k+1)·(k+1) = C(n,k)·(n−k)`), with no
side-condition on `n` at all (truncated subtraction makes them true for small
`n` too, both sides being `0`):

| lemma | statement |
|---|---|
| `choose_three_mul_sub` | `C(n,3)·(n−3) = 4·C(n,4) = holeLo n` |
| `choose_three_mul_sub_sub` | `C(n,3)·(n−3)·(n−4) = 20·C(n,5)`, i.e. `6C(n,5) = (3/10)·C(n,3)(n−3)(n−4) = holeHi n` |

Consequently the hole is `(C(n,3)(n−3), (3/10)C(n,3)(n−3)(n−4))` on the nose,
and the `3/10` is cleared everywhere by carrying the factor `10` (`10ρ < 3(…)`).
No division, no rationals, no rounding anywhere in the file.

## 2. Everything else proven outright (no axioms beyond the standard three)

| lemma | statement | note |
|---|---|---|
| `holeLo n`, `holeHi n` | `4C(n,4)`, `6C(n,5)` | both are *attained* values of `I(A_n)` (`4 ∈ V₄`, `6 = min V₅`), so the hole is open at both ends |
| `choose_three_pos`, `holeLo_pos` | positivity | |
| `holeLo_lt_holeHi` | **`4C(n,4) < 6C(n,5)` for `n ≥ 8`** | derived from the identities: `×10` reduces it to `10 < 3(n−4)`, i.e. `n > 22/3`.  Confirms the brief's arithmetic check. |
| `choose_three_lt_choose_four` | `C(n,3) < C(n,4)` for `n ≥ 8` | again from `4C(n,4) = C(n,3)(n−3)` |
| `choose_chain` | `C(n,3) < C(n,4) < 3C(n,4) < 4C(n,4) = holeLo n` | records that all three `s = 4` SPEC values (`V₄ = {1,3,4}`) sit at or below the left endpoint, and the `s = 3` value strictly below |
| `squeeze` | **`n−3 < ρ` and `10ρ < 3(n−3)(n−4)` ⟹ `holeLo n < C(n,3)·ρ < holeHi n`** (`n ≥ 5`) | the arithmetic core; both conclusions strict |

**Strictness is load-bearing.**  v_task48 §2b flagged the `s = 5` boundary:
`6C(n,5) = C(n,5)·min V₅` is an attained value, and so is `4C(n,4)`.  A
non-strict squeeze would prove nothing.  The Lean statement uses `<` on both
sides and derives it from `<` hypotheses, so the boundary case cannot be
smuggled in.

## 3. The hypothesis package — exactly three

1. `hcard : Nat.card A = Nat.card T` — the twin has the order of `A_n`
   (order transfer, §4a).
2. ```
   SpectrumHole A n := ∀ x, IsIndexValue A x → x ≤ holeLo n ∨ holeHi n ≤ x
   ```
   **[OPEN formally]** = Theorem SPEC (repaired: `I(A_n) ⊆ ⋃_s C(n,s)(V_s ∪ ½V_s)`)
   + Theorem GAP + Lemma V-BIG (`min V_s > s⁶`, hypothesis-free and CFSG-free
   after v_task49).  Stated as a property *at a given `n`*, deliberately.
3. ```
   TwinWitness T n ρ := IsIndexValue T (C(n,3)*ρ) ∧ n−3 < ρ ∧ 10ρ < 3(n−3)(n−4)
   ```
   **[OPEN formally]** = the abelian Lie witnesses (`Z(Syl_p) ≤ L₃(q)`, ratio
   `q+1`, `N = B` — the v_task48 §3 point that the higher-rank "`N = P`"
   intuition fails in rank 2; `U_{P₂} ≤ L₅(q)`, ratio `q²+1`) transported by
   TR-1 (`ind*_T(A) = ℓ*·f_A·[S:N_S(A)]`) and TO′-0, plus R1
   (`ℓ*f₁ι₁ = C(n,3)`) and the Q-LB / MASTER bounds on `q` which supply the two
   inequalities.

**Range honesty (recorded in the file's header, not buried).**  `SpectrumHole`
is *false at `n = 10`*: `I(A₁₀) ∩ (840,1512) = {945, 1350}` (v_task48 §6).
Theorem GAP holds only above an explicit threshold (`n₀ = 10⁶+5` under (AB);
`n ≥ 178089` hypothesis-free), the range `9 ≤ n ≤ 10¹¹` being covered by the
exact scan of v_task45 instead.  Hence `SpectrumHole` is a *hypothesis at the
given `n`*, never a schema; the file's numeric hypothesis `10 ≤ n` is only what
the arithmetic needs, and carries no claim that the package is satisfiable at
`n = 10`.

## 4. Assembly

```
theorem atSeparation {A T} [Group A] [Group T] [Fintype A] [Fintype T]
    {n ρ : ℕ} (hn : 10 ≤ n)
    (hcard : Nat.card A = Nat.card T)
    (hA : SpectrumHole A n) (hT : TwinWitness T n ρ) :
    IsEmpty (DRing A ≃+* DRing T)
```

plus `not_nonempty_dringEquiv_of_atSeparation`.  Proof: transport the witness
`C(n,3)·ρ` from `T` back to `A` along `Φ.symm` via `IsIndexValue.transfer`
(whose only input is the kernel-checked `conductorMultiplicity_eq_of_ringEquiv`
in `Even/OrderTransfer.lean`), apply `squeeze`, contradict `SpectrumHole`.
Note the transfer direction: the witness lives on the twin, the hole on `A_n`,
so the isomorphism is used *backwards* — `Φ.symm` with `hcard.symm`.

## 5. Axiom audit

```
'LeanDring.Even.choose_three_mul_sub'                     : [propext, Quot.sound]
'LeanDring.Even.choose_three_mul_sub_sub'                 : [propext, Quot.sound]
'LeanDring.Even.choose_three_pos'                         : [propext]
'LeanDring.Even.holeLo_pos'                               : [propext, Quot.sound]
'LeanDring.Even.holeLo_lt_holeHi'                         : [propext, Quot.sound]
'LeanDring.Even.choose_three_lt_choose_four'              : [propext, Quot.sound]
'LeanDring.Even.choose_chain'                             : [propext, Quot.sound]
'LeanDring.Even.squeeze'                                  : [propext, Quot.sound]
'LeanDring.Even.atSeparation'                             : [propext, Classical.choice, Quot.sound]
'LeanDring.Even.not_nonempty_dringEquiv_of_atSeparation'  : [propext, Classical.choice, Quot.sound]
```

No custom axiom, no `sorryAx`.  The whole arithmetic core is `Classical.choice`-free.

## 6. Feasibility: what a FULL Lean proof of Theorem SPEC would need

Honest assessment.  Theorem SPEC is the one hypothesis here that is *pure
`S_n` combinatorics* — no Lie theory, no CFSG — so it is the only one that
Mathlib could plausibly support.  It is nevertheless a substantial project.

### 6a. What Mathlib already gives (genuinely helpful)

* `Equiv.Perm α`, `Equiv.Perm.support` (`DecidableEq`/`Fintype`), and the
  support API (`support_mul_le`, `support_conj : (σ * τ * σ⁻¹).support =
  σ.support.map σ`, `Disjoint.commute`, cycle type, `Equiv.Perm.sign`).
* `alternatingGroup α` with `Equiv.Perm.mem_alternatingGroup`, and
  `alternatingGroup.isSimple` (needed nowhere here, but the index-2
  infrastructure `Subgroup.index`, `Subgroup.index_eq_two_iff` is).
* `Subgroup.normalizer`, `Subgroup.index`, `Subgroup.relindex`, and the
  orbit–stabilizer machinery `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`
  — enough to get "conjugacy-class size = `[G : N_G(H)]`" for the conjugation
  action on subgroups (`ConjAct`, `Subgroup.card_conjugates`-style lemmas exist).
* `Equiv.Perm.subtypePerm` / `Equiv.Perm.ofSubtype` and the
  `Equiv.Perm.viaEmbedding` family — the `S_s ↪ S_n` embedding used to speak of
  "`A ≤ Sym(Ω)` for `Ω ⊆ [n]`".
* `Nat.choose`, `Nat.descFactorial` and the identity `n^{(s)} = s!·C(n,s)`.

### 6b. What is missing and must be built (the real cost)

1. **Canonical support of a subgroup.**  `supp H := ⋃_{h ∈ H} h.support`, and
   `g ∈ N(H) → g` permutes `supp H`.  Easy (a day), but it is new API: Mathlib
   has support for *elements*, not for subgroups.
2. **The class-count formula.**  "the `S_n`-class of `A` has size
   `n^{(s)}/|N_{S_s}(A)|`" (§4as Step 1).  This is an orbit computation over
   the set of pairs *(s-subset `Ω`, subgroup of `Sym Ω`)* with a transitivity
   claim: `S_n` acts transitively on such pairs with fixed abstract
   `Sym Ω`-class.  Doable with `MulAction` but fiddly — the bijection between
   "`S_n`-conjugates of `A`" and "`n^{(s)}/|N_{S_s}(A)|` marked copies" is the
   kind of counting Mathlib does not automate.  Estimate: 2–4 weeks.
3. **The `A_n`-vs-`S_n` halving.**  `ind(A) = n^{(s)}/|N_{S_s}(A)|` when
   `n − s ≥ 2` (an odd transposition in `Ω^c` centralises `A`), and the
   `s ∈ {n−1,n}` dichotomy `N_{S_s}(A) ⊆ A_n ⟹` halve.  This is exactly the
   v_task48 §1 erratum, and formalizing it is the *good* news: it is a clean
   `Subgroup.index_eq_two` argument, ~1 week, and the formal version cannot
   repeat the original slip.
4. **`V_s` as a genuine finite set, and the Müller dictionary.**  Two separate
   problems.  (i) `V_s := {n^{(s)}/(s!·|N_{S_s}(A)|) : A}` must be shown to
   depend only on `s` — that follows from (2), fine.  (ii) But the theorem is
   about `I(A_n)` = the `ind*` values *read off conductors of `D(A_n)`*, and
   the identification `ind* = |G|/conductor` is **Müller Satz 2.3.3, which is
   formalized nowhere in this corpus** (same soft joint as v_task66 §4, same as
   `ConductorDictionary` in `SimpleRigidity.lean`).  Until that is formalized,
   a Lean "Theorem SPEC" would be a statement about normalizer indices, not
   about `D(A_n)`, and the bridge to `SpectrumHole` would remain assumed.
   This is the dominant cost and it is *not* `S_n` combinatorics.
5. **Theorem GAP on top of SPEC** additionally needs Lemma V-BIG
   (`min V_s > s⁶`), whose proof (v_task49) uses Bochert's 1889 primitivity
   bound, a wreath-product index bound, and `|Aut(A)| ≤ |A|^{log₂|A|}` for
   abelian `A`.  **Bochert is not in Mathlib** and is a nontrivial
   formalization in its own right (primitive groups, minimal degree — Mathlib
   has `IsPreprimitive` in the `Mathlib.GroupTheory.GroupAction` area but not
   the classical bounds).  Plus explicit numeric thresholds (`s₀ = 15876`)
   requiring `Nat`-level estimates on factorials and `2^{s/2}` — tedious but
   mechanical with `Nat.factorial` lemmas and `norm_num`.
6. **The `9 ≤ n ≤ 10¹¹` scan** is not formalizable as stated (a C program over
   `10¹¹` values of `n`); it would have to be replaced by a proof, or accepted
   as an oracle. Certifying it would be a separate project of comparable size
   to all of the above.

### 6c. Verdict

* **SPEC's support formula alone** (items 1–3): realistic, ~1–2 months of
  focused Lean work, and genuinely worthwhile — it is the piece where a
  factor-2 error already occurred once (v_task48 §1) and where Mathlib's `S_n`
  API is strong enough to carry it.
* **`SpectrumHole` as used here** (items 1–6): not realistic in the near term.
  The blocker is not the combinatorics; it is (4ii) the missing
  conductor↔`ind*` dictionary and (5) Bochert.  Estimate 1–2 person-years, and
  the dictionary would have to be done first since *every* `Even/` file in this
  layer (BCSeparation included) hangs off the same joint.
* **Recommended next Lean step** is therefore *not* SPEC but the dictionary:
  formalizing Müller Satz 2.3.3 (`conductor(H, hH') = (N_G(H,hH') : H')`) would
  convert `IsIndexValue` from a faithful-but-uninterpreted wrapper into the
  real `ind*`, and would upgrade both `BCSeparation` and `ATSeparation` from
  "conditional on a dictionary" to "conditional on group theory only".

## 7. Reproduce

```
cd lean_dring
taskset -c 0 lake build LeanDring.Even.BCSeparation
taskset -c 0 lake env lean LeanDring/Even/ATSeparation.lean
```

Single process throughout, per the standing no-parallel-Lean rule.
