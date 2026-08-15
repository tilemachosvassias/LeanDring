# bc_separation_recheck — independent re-derivation of Theorem BC-n (bc_separation), with errata

Scripts `witness_recheck.g` (GAP 4.16, CTblLib),
`maximal_index_bounds.py`; outputs `witness_recheck_out.txt`,
`maximal_index_bounds_out.txt`.  Everything below was re-derived
independently of the bc_separation scripts, which were read only afterwards, for
comparison.

## Outcome

Theorem BC-n stands: `D(B_n(q)) ≇ D(C_n(q))` for all `n ≥ 3`, all odd `q`.
One genuine **erratum** (§3: the exclusion is stated over `I(S)` but must be
stated over the whole conductor multiset), repairable in one paragraph with
no change to the conclusion; two presentational tightenings (§1b, §2a).  The
exclusion is a *dichotomy over all subgroups*, not an inventory, so it has no
"omitted column" failure mode.

---

## 1. The B-side witness

**(a) `det z_e = 1`.**  `z_e = −r_e`, `det(−1_{2n+1}) = (−1)^{2n+1} = −1`,
`det r_e = −1`, product `+1`.  Equivalently `z_e` is `−1` on the `2n`-dim
`e^⊥`.  GAP: `det z = 1` in all 8 rows (q = 3,5,7,9). ✓

**(b) Spinor norm — verified, with a normalisation erratum.**
`z_e` is the product of the `2n` reflections in an orthogonal basis of
`e^⊥`, so `θ(z_e) ≡ ∏Q(f_i) ≡ disc(e^⊥)` and `disc(V) ≡ Q(e)·disc(e^⊥)`,
giving `z_e ∈ Ω ⟺ Q(e) ≡ disc(V)` mod squares — **exactly one** square
class. ✓

Here `r_e` is rebuilt from the reflection formula
`v ↦ v − (B(v,e)/Q(e))·e` (`B = Q + Qᵀ`), verified it is orthogonal, and
compared `disc(e^⊥) ∈ □?` against `z_e ∈ Ω`: **agreement in all 8 rows**.

*Erratum (presentational).* The write-up says "`θ(z_e) ≡ disc(V)·Q(e)`"
without pinning `disc`.  It must be the **quadratic-form** discriminant
(`det` of the Gram of `Q`), not `det` of the polar form `B = Q+Qᵀ`: the two
differ by `2^{2n+1}`, i.e. by the class of `2`.  Using `det B` naively
predicts the *wrong* class at `q = 3` and `q = 9`.  With the `2^{2n+1}`
factor restored, the rule reproduces the GAP column exactly:

| q | `det B` □? | `2^7` □? | `disc(V)` □? | `z_e ∈ Ω` on | ε realised |
|---|---|---|---|---|---|
| 3 | yes | no  | **no**  | nonsquare | `v = 351` (`ε = +1`) |
| 5 | no  | no  | **yes** | square    | `v = 7875` (`ε = −1`) |
| 7 | no  | yes | **no**  | nonsquare | `v = 58653` (`ε = +1`) |
| 9 | yes | yes | **yes** | square    | `v = 266085` (`ε = −1`) |

So "the ε and class flip with q mod 4" is really *the class of
2 times the class of `det B`*; both GAP data points (351 on the nonsquare
class at q = 3, 7875 on the square class at q = 5) are **consistent** with
the formula.  Which ε is realised is irrelevant — the exclusion (§2) kills
both.

**(c) `N_S(⟨z_e⟩) = C_S(z_e) = Stab_S(⟨e⟩)` — verified; this step was
asserted rather than computed in `bc_separation`.**  `|⟨z_e⟩| = 2` so `N = C` automatically.  For
`C = Stab`: `C_{O(V)}(z_e) = O(⟨e⟩) × O(e^⊥) = Stab_{O(V)}(⟨e⟩)` (both are
the stabiliser of the decomposition `⟨e⟩ ⊥ e^⊥`); intersecting the *same*
equality with `Ω` gives `C_Ω(z_e) = Stab_Ω(⟨e⟩)` — **no index-2 drop**, the
possible index-2 doubling does not occur.

The `bc_separation` script never computed a centraliser: it printed
`Stabilizer(G, point)` and *asserted* it equals `C_S(z_e)`.  The script here
computes `Centralizer(G,z)` and `Normalizer(G,⟨z⟩)` directly:

```
q=3: |C_G(z)| = |N_G(<z>)| = |Stab_G(<e>)| = 13063680,  [G:C] = 351
q=5: 29016000000                                        [G:C] = 7875
q=7: 4662288691200                                      [G:C] = 58653
q=9: 203039372390400                                    [G:C] = 266085
```

all three equal in every case. ✓  (Cross-check: `2.U₄(3).2₂ ≤ O₇(3)` of
index 351 is exactly this stabiliser, and it *is* in the CTblLib ATLAS
maxes list for `O7(3)` — the bc_separation remark that "O7(3) has no stored
maxes" is an AtlasRep artifact; CTblLib has the full list.)

Non-splitting of the `SO`-orbit: `Stab_{SO}(⟨e⟩) ≅ O^ε_{2n}(q)` contains
reflections of both spinor norms (`2n ≥ 4`), so it is not inside `Ω` and
the orbit is the *full* square class. ✓ GAP: orbit sizes `351+378 = 729`,
`7750+7875 = 15625`, `58653+58996 = 117649` `= q^{2n}` ✓.

**(d) `ind*` weighting.**  `H = ⟨z_e⟩` abelian ⟹ `|H'| = 1` ⟹
`ind* = [S:N_S(H)]` (definition of `ind*`, `bc_separation` §1). ✓

**Extra: n = 4 checked** (not done in bc_separation, which stopped at n = 3).
`Ω₉(3)`: the realised orbit is `3321 = v_{−1}`, `ι₁ = 3280 ∤ 3321`,
`q^{2n} = 6561`. The witness is not an n = 3 accident. ✓

## 2. The C-side exclusion — verified (with a tightening)

**(a) "P₁ is the only maximal of `Sp_{2n}(q)` of index `< q^{2n}`,
q odd, n ≥ 3" — verified.**

*Anchor, exhaustively, from the complete ATLAS list (CTblLib `Maxes`):*
`S6(3)` has 11 classes of maximals, indices
`364, 1120, 3640, 7371, 110565, 155520, 189540, 408240, 4199040(×2),
76422528`.  **Exactly one is below `q⁶ = 729`, namely `364 = [S:P₁]`.** ✓
(bc_separation read this off AtlasRep SLPs and got `364, 1120` — consistent,
but its list was truncated; CTblLib's is complete and confirms.)

*General n, class by class* (`maximal_index_bounds.py` step (B)): the index
bounds are rebuilt from Kleidman–Liebeck Table 3.5.C orders — **including
the two classes bc_separation's table omits, `C₄` (`Sp_{2a} ⊗ O_b`) and `C₇`
(tensor-induced)** — with a generous slack factor `8n·log_p q` on every
non-parabolic order, so the printed index is a genuine lower bound.
`n ∈ [3,8]`, all odd prime powers `q < 200`, 318 pairs: **2 flags, both
artifacts of that slack, both disposed of exactly**:

* `C₆` `2^{1+2n}.O^-_{2n}(2)`: with the exact normaliser order the index
  at the tightest point (`n=3, q=3`) is `≥ 1382 > 729`; and `C₆` does not
  even occur in `Sp₆(3)` (`|2^{1+6}.O⁻₆(2)| = 6635520 ∤ |Sp₆(3)|`, and it
  is absent from the ATLAS list).  No case below `q^{2n}` anywhere.
* `S` class at `n = 3`: bc_separation's "`|M| ≤ 4f·max(...)` so index `≫ q⁶`
  for every `q ≥ 3`" is **not** valid as a single max-order bound — at
  `q = 3` the `2.J₂` order alone leaves only a factor `≈ 315`, i.e. inside
  `q⁶ = 729` once outer slack is applied.  Redone **per candidate** with
  the BHR 8.28/8.29 orders (`Sym⁵SL₂(q)`, `SL₂(13)`, `2.L₂(7)`, `2.A₇`,
  `2.U₄(2)`, `6.L₃(4)`, `2.J₂`): **0 flags over all odd `q < 200`**.  The
  conclusion is right; the stated justification was too coarse.

The tightest *exact* case is as bc_separation says: `[Sp₆:P₃] = (q+1)(q²+1)
(q³+1) = q⁶+q⁵+q⁴+2q³+q²+q+1 > q⁶`, an identity, not a numerical
accident. ✓  Liebeck's `S`-bound `|M| < q^{3d} = q^{6n}` gives index
`≥ q^{2n²−5n} ≥ q^{2n} ⟺ n ≥ 4` ✓ — so `n = 3` genuinely needs BHR, as
stated.

**`G₂(q) < Sp₆(q)` at odd q — refuted, as required.**  The 6-dimensional
module for `G₂(q)` is symplectic only in characteristic 2 (it is the
quotient of the 7-dim module by its radical, which exists only when
`p = 2`); for odd `q`, `G₂(q) < Ω₇(q)` and *not* `Sp₆(q)`.  Confirmation
in the data: `G2(3)` appears in the `O7(3)` maxes list (index 1080) and
**not** in the `S6(3)` list. ✓  (Had it been there, its index would be
`~q³` and the theorem would die; it is not.)

**(b) `ι₁ ∤ v_ε` — verified, and by the right (arithmetic) argument.**
A pure size argument is insufficient
(`v_ε/ι₁ ≈ q/2` is an integer-sized candidate).  The correct proof, which
**bc_separation does give** in its §4: `2v_ε = q^n(q^n−ε)` and `gcd(ι₁,q) = 1`,
so `ι₁ | v_ε ⟹ ι₁ | (q^n−ε)/2`; but
`0 < (q^n−ε)/2 < q^n ≤ q^{2n−1} < ι₁` for `n ≥ 2`.  Contradiction. ∎
Machine check: `n ∈ [3,12]`, odd prime powers `q < 400`, both ε — 1780
triples, 0 divisibilities, `gcd(ι₁,q) = 1` and `ι₁ > (q^n−ε)/2 > 0`
verified in every one. ✓

**(c) `PSp` vs `Sp` — verified.**  Indices are unchanged by the central
quotient; maximals of the simple group `PSp_{2n}(q)` are the images of the
maximals of `Sp_{2n}(q)` containing `Z`, and Aschbacher's theorem applies
to `PSp` itself (no novelty issue, since novelties are maximal only in
larger almost-simple groups).  `v_ε` and `ι₁` are computed in `PSp`
throughout. ✓

**Dichotomy, restated (and it is the load-bearing statement):**  for
`1 ≠ H ≤ S = PSp_{2n}(q)`, either `[S:N_S(H)] ≥ q^{2n}` (⟹ `ind* ≥ q^{2n}
> v_ε`) or `N_S(H) ≤ P₁^g` (⟹ `ι₁ | [S:N_S(H)] | ind*`).  `H ⊴ S` forces
`H = S`, `ind* = |S|`. ✓  Note the `|H'| > 1` weighting is harmless
precisely because divisibility is preserved by multiplication.

## 3. D-invariance of `I(S)` — **ERRATUM** (repairable, conclusion stands)

The chain `conductor multiset → ind*` is sound: by Müller Satz 2.3.3 the
pair `(H, hH')` has conductor `(N_G(H,hH') : H')`, `N_G(H,H') = N_G(H)`;
`conductorMultiplicity_eq_of_ringEquiv` (`OrderTransfer.lean:150`,
kernel-checked) plus order transfer makes the multiset an invariant, and
`|B_n(q)| = |C_n(q)|` so index-level comparison is legitimate.  No `(AB)`
hypothesis is consumed: the witness is abelian, and the exclusion
quantifies over **all** `H`. ✓

**The gap.**  `I(G)` is defined using only the *identity* coset
`hH' = H'`.  The D-invariant is the *full* conductor multiset, which also
contains `(N_G(H,hH') : H')` for `h ∉ H'`.  So "`v_ε ∉ I(C_n(q))`" does
**not**, as written, exclude the conductor `|S|/v_ε` from `D(C_n(q))` — it
could in principle be carried by a non-identity coset.  bc_separation asserts
the step without addressing this.

**The repair (one paragraph, no new input).**  For any pair `(H, hH')`,
`N_G(H,hH') ≤ N_G(H)`, so the associated value
`x := |S| / conductor = [S:N_S(H,hH')]·|H'|` is a **multiple of
`[S:N_S(H)]`**.  If `x < q^{2n}` then `[S:N_S(H)] ≤ x < q^{2n}`, so by the
dichotomy of §2 either `H ∈ {1, S}` (giving `x = 1` and `x = |S|`, neither
equal to `v_ε`) or `ι₁ | [S:N_S(H)] | x`.  Hence **every** conductor value
of `D(PSp_{2n}(q))` below `q^{2n}` other than `1` is divisible by `ι₁`,
and `v_ε` is not.  The theorem is restored verbatim.

Recommendation: state Lemma C-below over generalised pairs, or define
`I(G)` as the full `{|G|/c}` set from the start.

## 4. Scope and the q = 3 anchor

`q` even: `B_n(2^f) ≅ C_n(2^f)`, vacuous ✓.  `n = 2`: excluded, and
correctly so — `PSp₄(3)` has minimal degree 27 `< ι₁ = 40`, so the
dichotomy fails at `n = 2` (and `B₂ ≅ C₂` anyway).  `n ≥ 3`: the
`PSp_{2n}(3)` minimal degree is `ι₁` again (`= 364` at `n = 3`, ATLAS),
so no `q = 3` exception on the symplectic side.

`q = 3, n = 3` anchor, both directions:
* `351 ∈ I(Ω₇(3))` — direct orbit/centraliser computation, and `2.U₄(3).2₂`
  of index 351 in the ATLAS `O7(3)` maxes ✓;
* `I(PSp₆(3)) ∩ [1,729) ⊆ {364}` — from the *complete* ATLAS maxes list
  (only maximal below 729 is `P₁`, index 364; `2·364 = 728 < 729` is the
  only other candidate multiple).  `351 ∉` ✓.

The KL 5.2.2 exception is correctly located: it is the **orthogonal** side
(`Ω_{2n+1}(3)` has minimal degree `3^n(3^n−1)/2 < ι₁`), and it *is* this
witness.  The symplectic side has no such exception — which is exactly why
the argument works.

## 5. Search for a counterexample — nothing found

Places probed for an "omitted column" of the kind that broke the earlier
`mult₁` route:

* **`C₈` (`O^ε_{2n}(q) < Sp_{2n}(q)`, index exactly `q^n(q^n∓1)/2 = v_ε`).**
  This would have been a perfect, fatal, omission — the C-side maximal of
  precisely the witness index.  It does **not** exist for odd `q`: the
  polarisation of a quadratic form in odd characteristic is *symmetric*,
  not alternating, so `C₈` for `Sp` is a characteristic-2 class only.
  Confirmed in the data: no subgroup of index 351 or 378 in `S6(3)`.
  **This is the structural heart of the theorem** and it is sound: `Sp` has
  no anisotropic points *and* no quadratic-form stabilisers.
* `G₂(q) < Sp₆(q)` at odd `q` — refuted (§2a).
* Non-abelian `H` with `|H'| > 1` engineered to hit `v_ε` — covered by
  divisibility (§2 dichotomy).
* Non-identity cosets — the one real erratum, §3, repaired.
* `C₄`/`C₇` (absent from bc_separation's table) — indices verified far above
  `q^{2n}`.
* `n = 4` witness — verified independently, not an `n = 3` accident.

## Summary of the steps

| item | status |
|---|---|
| 1a `det z_e = 1` | verified |
| 1b spinor norm / square class | verified; erratum on `disc` normalisation (factor `2^{2n+1}`), data consistent |
| 1c `N = C = Stab`, orbit size, no index-2 drop | verified (computed directly; `bc_separation` had asserted it) |
| 1d `ind*` weight for abelian `H` | verified |
| 2a only-`P₁` below `q^{2n}` | verified; tightening required for `C₆` and for the `n=3` `S` class (`bc_separation`'s single max-order bound is too coarse at `q = 3`); `C₄`,`C₇` omitted from its table |
| 2b `ι₁ ∤ v_ε` | verified (arithmetic form, correct in `bc_separation`) |
| 2c `PSp` bookkeeping | verified |
| 3 D-invariance of the exclusion | erratum — must range over all conductor pairs, not `I(S)`; repaired above |
| 4 scope + `q=3` anchor | verified |
| 5 search for a counterexample | none found |
| **Theorem BC-n** | stands, modulo the §3 restatement and the cited classification of maximal subgroups of `Sp_{2n}(q)` |
