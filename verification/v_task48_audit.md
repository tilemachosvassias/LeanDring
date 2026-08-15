# v_task48 — ADVERSARIAL AUDIT of v_task47 (claimed closure of Theorem AT
# for all `n ≥ 9`)

Date 2026-08-08.  **NOTES.md not edited.**  All checks below were re-derived
or recomputed independently; no script of v_task47 was executed.

| file | what it does |
|---|---|
| `v_task48_spec.g` / `_out.txt` | independent exhaustive `V_s`, `s = 3..10`; exhaustive `I(A_9)` (and `I(A_10)`); diff against `⋃_s C(n,s)V_s` and against the hole |
| `v_task48_squeeze.py` / `_out.txt` | the squeeze in EXACT integer/rational arithmetic, every live `f`, `n = 10^11..10^40`; plus a rigorous all-`n` replacement for v_task47's finite grid |
| `v_task48_lie.g` / `_out.txt` | the two Lie witnesses re-checked at parameters v_task47 did not test (`L₃(q)`, `q ≤ 64`; `L₅(3)`, `L₇(2)`) |

## Verdict summary

| # | item | verdict |
|---|---|---|
| 1 | Theorem SPEC | **ERRATUM (fixable)** — FALSE as stated; explicit counterexamples in `I(A₉)` |
| 2a | `V_s` table, `s ≤ 9` | **CONFIRMED** (reproduced exactly, independent script) |
| 2b | Theorem GAP interval arithmetic | **CONFIRMED** (incl. the `s=5` boundary) |
| 2c | Lemma V-BIG (abelian), and explicit `n₀` | **CONFIRMED after repair**; `n₀ = 10⁶ + 5`, author left it implicit |
| 2d | reliance on (H2) = (AB) | **ERRATUM (fixable, but a real hypothesis change)** — (AB) *as stated in v_task38* does **not** cover what Theorem GAP needs |
| 3 | Lie witnesses | **CONFIRMED** (group theory correct; `N_{L₃(q)}(Z(Syl_p)) = B` is right) |
| 4 | squeeze arithmetic | **CONFIRMED**, and upgraded from a grid to a proof |
| 5 | interfaces (TR-1, TO′-0, `f₁`/`f_A`, graph aut) | **CONFIRMED** |

**Overall: Theorem AT closes for all `n ≥ 9` after the repairs recorded here,
with one honest hypothesis change: (H2) must be strengthened from
`ind*(H) ≥ 3C(n,4)` to `ind*(H) ≥ 6C(n,5)` for non-abelian `H` of support
`≥ 9` (equivalently, the non-abelian case of Lemma V-BIG must be finished).
v_task47's statement that "no new hypothesis is introduced" is incorrect.**
No break of the mathematics was found.

---

## 1. Theorem SPEC is FALSE as stated — a factor-2 error at `s ∈ {n−1, n}`

v_task47 proves the support formula only for `s ≤ n−2` (its own proof says
"of order `|N_{S_s}(H)|(n−s)!/2` **when `n − s ≥ 2`**") and then asserts

  `I(A_n) = ⋃_{s=3}^{n} C(n,s)·V_s`,

extending the union to `s = n−1, n` where the derivation does not apply.

Re-derivation.  For `s ∈ {n−1, n}` one has `N_{A_n}(H) = N_{S_s}(H) ∩ A_n`,
so
* if `N_{S_s}(H) ⊄ A_n`: `ind*(H) = C(n,s)·w`, `w ∈ V_s`  (SPEC holds);
* if `N_{S_s}(H) ≤ A_n`: **`ind*(H) = C(n,s)·w / 2`**.

The halved values are genuinely new elements of `I(A_n)`.  Corrected form:

>  `I(A_n) = ⋃_{s=3}^{n−2} C(n,s)V_s  ∪  ⋃_{s∈{n−1,n}} C(n,s)·(V_s ∪ ½V_s)`,
>  and in particular `I(A_n) ⊆ ⋃_{s=3}^{n} C(n,s)·(V_s ∪ ½V_s)`.

**Machine counterexample** (`v_task48_spec_out.txt`, exhaustive over all
conjugacy classes of subgroups of `A₉`):

  `I(A₉)` contains **135** and **8640**, neither of which lies in
  `⋃_{s=3}^{9} C(9,s)V_s`.

Both are exactly the predicted halvings at `s = n−1 = 8`:
`135 = (9·30)/2` with `30 = min V_8`, and `8640 = (9·1920)/2` with
`1920 ∈ V_8`.  (`270` and `17280` appear in the union but not in `I(A₉)` —
the same phenomenon seen from the other side.)

**Impact on Theorem GAP: none.**  The extra values are `≥ ½·C(n,s)·min V_s`
at `s ≥ n−1`, and V-BIG gives `½ min V_s > s⁶/2 ≫ 6C(n,5)` in that regime.
Every downstream use is of the containment `⊆`, which the corrected form
still supplies (with `V_s ∪ ½V_s`).  Fixable erratum; SPEC's statement and
Lemma V-BIG's consumption both need the `½`.

## 2. Theorem GAP

### 2a. `V_s` reproduced

Written from the definition, not from `v_task47_spec_Vs.g`:

```
V_3 = [1]                       V_4 = [1,3,4]        V_5 = [6,30,60]
V_6 = [10,15,20,45,60,90,180,360]
min V_7 = 35    min V_8 = 30    min V_9 = 280        min V_10 = 945
```

Identical to v_task47's table in every entry. **CONFIRMED.**

### 2b. Interval arithmetic, done independently

The hole is `(4C(n,4), 6C(n,5))`, i.e. after dividing by `C(n,3)`,
`ρ ∈ (n−3, 0.3(n−3)(n−4))` — both endpoint identities verified
(`C(n,5)/C(n,3) = (n−3)(n−4)/20`).

* `s = 3`: `C(n,3) < 4C(n,4)` for `n ≥ 8`. Out.
* `s = 4`: values `C(n,4), 3C(n,4), 4C(n,4)`; the largest is the **left
  endpoint**, excluded by openness.
* `s = 5`: `C(n,5)·{6,30,60}`; the smallest is `6C(n,5)` = the **right
  endpoint**, excluded by openness.  This is the boundary case flagged in
  the audit brief: it is genuinely a two-sided touch, and the argument
  survives **only** because the interval is open at both ends.  It does
  survive: the squeeze (§4) produces strict inequalities `ρ_min > n−3` and
  `ρ_max < 0.3(n−3)(n−4)`, so it never needs the endpoints.  *Recommendation:
  the write-up should say explicitly that both endpoints of the hole are
  attained values of `I(A_n)` and that only strict inequalities may be used.*
* `6 ≤ s ≤ n−6`: `ind* ≥ C(n,s)·1 ≥ C(n,6) = C(n,5)(n−5)/6 > 6C(n,5)` for
  `n > 41`.  Uses `min V_s ≥ 1` only — **valid for non-abelian `H` too**.
* `s ≥ n−5`: needs V-BIG. See 2c/2d.

The case list is exhaustive.  **CONFIRMED.**

### 2c. Lemma V-BIG (abelian) and the explicit `n₀`

Re-derived.  The regular-orbit/holomorph input is correct: `H` abelian and
transitive on an orbit ⟹ regular there, and `|N_{Sym(O)}(A)| = |Hol(A)| =
d·|Aut(A)| ≤ d·d^{log₂ d}` (using `|Aut(A)| ≤ |A|^{log₂|A|}` for abelian `A`).

One flaw and one simplification:

* **Case 2 as written is wrong.**  "`s − dm ≥ 20` ⟹ `C(s,dm) = C(s,s−dm) ≥
  C(s,20)`" needs `s − dm ≤ s/2`, which is not assumed; if `dm < s/2` the
  binomial can be as small as `C(s,2)`.
* **Case 2 is also unnecessary.**  The case-3 bound
  `[S_s:N] ≥ s!/(∏_d (d!)^{m_d} m_d!) ≥ s!/(d₀^s (s/2)!)` uses only
  (a) `N ≤ ∏_d (S_d wr S_{m_d})`, (b) every orbit has size `≤ d₀` (from
  `d < d₀`), (c) every orbit has size `≥ 2` (fixed-point-freeness), hence
  `r ≤ s/2`.  It never uses `s − dm ≤ 19`.  So cases 2 and 3 merge into a
  single "`d < d₀`" case and the flaw disappears.

Numerics of the merged case at the stated floor `s = 10⁶`:
`log₂[S_s:N] ≥ (s/2)log₂ s − s(log₂ d₀ + log₂ e) ≈ 9.97·10⁶ − 7.3·10⁶ > 0`,
and hugely above `6log₂ s = 120`.  **Holds.**

**Explicit `n₀` (the flagged thin point (ii)).**  V-BIG is proven for
`s ≥ 10⁶`; Theorem GAP invokes it at `s ≥ n−5`; the middle case needs
`n > 41`.  Therefore

>  **`n₀ = 10⁶ + 5`**, and `n₀ ≤ 10¹¹` with eleven orders of magnitude to
>  spare, so the v_task45 scan floor covers `[9, n₀]` comfortably.

(The `n = 10` intruders are consistent with this: `min V_10 = 945`,
independently recomputed here, and `945 ∈ (4C(10,4), 6C(10,5)) = (840,1512)`
— it is a genuine `s = n` value, not an artefact.)  **CONFIRMED after repair.**

### 2d. The (AB) reliance is understated — a real hypothesis change

v_task47 writes: "Since the whole program already carries (AB) as hypothesis
**(H2)**, the abelian form is what Theorem AT actually consumes, and **no new
hypothesis is introduced**."  This is **incorrect**.  (H2) is stated in
`v_task38_theorem_at_assembly.md` §"(H2)" as

> no non-abelian `H ≤ A_n` with `|supp H| ≥ 9` has `ind*(H) < 3C(n,4)`.

That excludes non-abelian values **below** `3C(n,4)`.  Theorem GAP needs them
excluded from the **interval** `(4C(n,4), 6C(n,5))`, which lies entirely
*above* `3C(n,4)`.  A non-abelian `H` of support `≥ 9` with, say,
`ind*(H) = 5C(n,4)` is fully compatible with (H2) and would sit inside the
hole, destroying the squeeze.  So the abelian-only V-BIG does **not** suffice
under the program's existing hypothesis.

Where exactly is the exposure?  Only at `s ≥ n−5` (supports `≤ 8` are
exhaustively computed for **all** `H` — `min V_6..V_8 = 10,35,30`, and
`C(n,s)·min V_s ≥ C(n,6) > 6C(n,5)` there; and `6 ≤ s ≤ n−6` uses no
abelianness).  Two clean repairs, either suffices:

* **(R-a)** strengthen the hypothesis to
  **(H2′): no non-abelian `H ≤ A_n` with `|supp H| ≥ 9` has
  `ind*(H) < 6C(n,5)`.**
  Note `6C(n,5) > 3C(n,4)` for `n ≥ 14`, so (H2′) ⟹ (H2) and no other part of
  the program is disturbed by the swap.
* **(R-b)** finish V-BIG for non-abelian `H`.  This is closer than v_task47
  suggests: the author flags *case 3* as the missing piece, but by 2c the
  `d < d₀` bound `s!/(d₀^s(s/2)!)` is **hypothesis-free** — it holds verbatim
  for non-abelian `H`.  What remains is only the `d ≥ d₀` case, where the
  author's sketch (`|H′| ≥ d!/2` if the dominant constituent contains `A_d`;
  otherwise `N_{S_d}(H^O)` is proper transitive, index `≥ min(⌊(d+1)/2⌋!,
  2^{d/2})` by Bochert + the imprimitive bound) is the standard argument and
  looks completable.

Recorded as **ERRATUM (fixable)**, but it does change the stated input list of
Theorem AT and must not be papered over.

## 3. The Lie witnesses — CONFIRMED

**`L₃(q)`, `A = Z(Syl_p) `.**  The audit brief's worry ("`N(Z(U))` should be
the parabolic `P`, not `B`") is **unfounded for `L₃`**, and v_task47 is right.
Independent derivation: `Z(U) = X_γ = {I + tE₁₃}` is the group of
transvections with **centre** the line `⟨e₁⟩` and **axis** the hyperplane
`⟨e₁,e₂⟩`.  Conjugation moves the pair (centre, axis), so `g` normalises
`X_γ` iff `g` stabilises **both** the line and the plane — i.e. the full flag.
Hence `N_S(X_γ) = B`, `[S:B] = (q+1)(q²+q+1) = (q+1)ι₁`.  In `L₃` the long
root subgroup determines a complete flag, which is why the "`N = P`" intuition
(correct in higher rank / for `G₂`) does not apply here.

Independent machine confirmation at parameters v_task47 did **not** test
(`v_task48_lie_out.txt`): `q = 29, 31, 32, 37, 41, 49, 64` — `[S:N] =
(q+1)(q²+q+1)` in all seven, `Z(U)` elementary abelian of order `q`.

**`L₅(q)`, `A = U_{P₂}`.**  Borel–Tits gives `N_S(U_{P₂}) = P₂`;
`[S:P₂] = [5,2]_q = (q²+1)·[5]_q`, ratio `q²+1`.  Independently confirmed for
`L₅(3)` (`|U| = 3⁶ = 729`, abelian, `[S:N] = 1210 = [5,2]_3`, ratio `10 = q²+1`)
— a case v_task47 did not test (it tested `L₅(2)` only in dimension 5).
*Note*: my `L₅(4)` check is invalid (the generator construction spans only the
prime field, giving `|U| = 64`); v_task47's PART C has the same construction
but tested only prime `q`, so its data are unaffected.

**Fusion survival.**  TR-1 gives `ind*_T(A) = ℓ*·|A^{Ā}| = ℓ*·f_A·[S:N_S(A)]`
with `f_A = [Ā : S·N_Ā(A)] ∈ [1, |Out(S)|]` — an orbit-size identity, so the
value is in `I(T)` for **every** admissible `Ā`, and the squeeze quantifies
over the whole range `f_A ∈ [1,|Out|]`, `f₁ ∈ {1,2}`.  No `Ā` escapes.
**CONFIRMED.**

## 4. The squeeze arithmetic — CONFIRMED, and upgraded to a proof

`v_task47_ranges.py` is floating-point and finite (a grid to `n = 10^(10⁶)`).
Two defects: it tests `ρ_max < 0.3n²` where the requirement is
`ρ_max < 0.3(n−3)(n−4)` (slightly **anti**-conservative), and a grid is not a
proof for all `n`.  Both are repaired here.

**Exact arithmetic** (`v_task48_squeeze.py` Part A; `fractions.Fraction`,
unbounded integers, exact integer `k`-th roots, no floats in any comparison;
minimal admissible `q` from Q-LB / MASTER, maximal from `q² < C(n,3)/2` /
`q⁴ < C(n,3)`, every live `f`):

| `n` | row 2 worst `ρ_min/(n−3)` | row 2 worst `ρ_max/(0.3(n−3)(n−4))` | row 3 worst lo | row 3 worst hi |
|---|---|---|---|---|
| `10¹¹` | **1.488902** (f=26) | 9.68e−4 (f=53) | 1.697930 (f=13) | 1.12e−3 |
| `10¹²` | 1.553502 (f=29) | 3.35e−4 | 1.771570 | 3.95e−4 |
| `10¹⁵` | 1.732640 (f=36) | 1.31e−5 | 1.974476 | 1.55e−5 |
| `10²⁰` | 1.994967 (f=47) | 5.60e−8 | 2.272406 | 6.67e−8 |
| `10⁴⁰` | 2.805704 (f=94) | 1.14e−17 | 3.193717 | 1.35e−17 |

The flagged 1.49 is **confirmed exactly** (`ρ_min/(n−3) = 148890166387/99999999997
= 1.4889016…`), it is the true infimum over `f` (neighbours: f=24 → 1.49243,
f=25 → 1.48998, f=27 → 1.48898, f=28 → 1.49006), and it is `> 1`.  The margin
is **not** monotone in `f` (it dips to a minimum near `f ≈ 26` and rises on
both sides) — v_task47 never claimed `f`-monotonicity, only `n`-monotonicity,
which the table bears out.  All `f` were checked, not only `f = 26`.

**All-`n` proof replacing the grid** (Part B).  Lower side, two branches:
1. *Uniform in `n`.*  `q^{1/f} = p ≥ 2` gives `q² ≥ 2fn²/8.1` (row 2) and
   `q⁴ ≥ 2fn(n−2)/3.13` (row 3), hence
   `ρ_min/(n−3) ≥ 0.2484√f` (row 2), `≥ 0.3997√f·√(1−2/n)` (row 3).
   `> 1` for **all `n`** once `f ≥ 17` (row 2: 1.0242) resp. `f ≥ 7`
   (row 3: 1.0575).
2. *Small `f`.*  The pure Q-LB / MASTER bound is
   `(f/8.1)^{f/(2f−1)}·n^{1/(2f−1)}/2` resp. its row-3 analogue — **strictly
   increasing in `n`** at fixed `f`.  So checking `f ≤ 16` (row 2) and
   `f ≤ 6` (row 3) at `n = 10¹¹` suffices; exact values there are
   `1.608 … 913.4` and `2.112 … 1084.6`, all `> 1`.

Upper side, uniform: `f ≤ log₂ q` and `q < n^{3/2}/√12` (row 2),
`q² < n^{3/2}/√6` (row 3) give `ρ_max < 6.2·n^{3/2}log₂ n`, so
`ρ_max/(0.3(n−3)(n−4)) ≤ 21·log₂ n/√n`, decreasing for `n ≥ e²`, and
`≤ 2.4·10⁻³` at `n = 10¹¹`.

**So the squeeze holds for every `n ≥ 10¹¹` — proven, not sampled.**  The
`10^(10⁶)` grid can be dropped from the write-up in favour of the above.

**Scan coverage below `10¹¹`.**  `v_task45_scan_out.txt` reports 16 contiguous
chunks covering `10 … 10¹¹` with `SURVIVORS row2=0 row3=0` in every chunk and
in the total line; the scan is complete in `q` by construction (it enumerates
divisors of `C(n,3)/f₁` and solves for `q` exactly, `f₁ ∈ {1,2}`), hence
complete in `f`.  Together with `n₀ = 10⁶+5 ≤ 10¹¹`, the two ranges overlap
by five orders of magnitude.  **CONFIRMED.**

## 5. Interfaces — CONFIRMED

* **TR-1 direction.**  `|A^Ā| = f_A·|A^S|` with `f_A = [Ā:S N_Ā(A)] ≥ 1`: the
  `Ā`-orbit is a **union** of `f_A` `S`-classes, so outer automorphisms
  *multiply* the value.  v_task47's calling this a "fusion number" is
  terminologically odd (fusion normally merges), but the arithmetic direction
  used is right.
* **Pair vs simple `ι₁`, graph automorphism.**  The R1 equation is
  `ℓ*·f₁·ι₁ = C(n,3)` with `ι₁ = [S:N_S(A₁)] = q²+q+1` the **simple-group**
  value and `f₁ ∈ {1,2}` **already** the pair/graph-automorphism factor
  (v_task38 §1.4 table).  So the feared "if `Ā` contains the graph aut then
  `ι₁` doubles and the equation reads `2ℓ*f₁ι₁`" is a double count: the
  doubling *is* `f₁ = 2`.  And `ρ_A = (f_A/f₁)(q+1)` is bounded over the whole
  rectangle `f_A ∈ [1,|Out|] × f₁ ∈ {1,2}`, so both `Ā`-shapes are covered.
  (For `L₃`, `A₁ = U_{P₁}` is abelian of order `q²` with `[S:P₁] = q²+q+1`, so
  TR-1 applies to the `ι₁`-witness too — internally consistent.)
* **TO′-0.**  Statement: `P = ⋃_O ℓ_O·I(K_{i_O} ≤ Ā_{i_O}) ⊆ I(T)`, and
  `D(T) ≅ D(A_n)` ⟹ every element of `P` is an `ind*`-value of `A_n`.  The
  witness value is `ℓ*·f_A·[S:N_S(A)] ∈ ℓ*·I(K ≤ Ā) ⊆ P` because `A ≤ S ≤ K_{i}`
  on the `O*` orbit.  So it is in `I(A_n)`, exactly as the squeeze requires.
  **CONFIRMED.**
* **(AB) usage** — see 2d; this is the one interface that does not check out.

## 6. Other observations (no break)

* `v_task47_lie_witness_out.txt` PART A contains a hand-inserted bracketed
  line "[q=13 of PART A aborted…]" in what is otherwise machine output.  The
  numerical data are unaffected (they stop at `q = 11`), but editing a
  `_out.txt` by hand is against the project's own evidence conventions.
* The `L₃` abelian-spectrum claim "the two smallest values are `q²+q+1` and
  `(q+1)(q²+q+1)` for every `q ≥ 3`" is COMPUTED only for `3 ≤ q ≤ 11`, and
  fails at `q = 2` (`ι₂(L₃(2)) = 8`).  The squeeze does not use minimality —
  only that `(q+1)ι₁` **is** a value — so this is harmless; it should be
  labelled [COMPUTED, small `q`] rather than used as a general fact.
* The `n = 9` exhaustive run confirms `I(A₉) ∩ (504,756) = ∅` (no intruders,
  all `H`), independently reproducing v_task47's `n = 9` check.
* The `n = 10` exhaustive run (completed after the above was drafted) gives
  `I(A₁₀) ∩ (840,1512) = {945, 1350}` — exactly v_task47's two intruders,
  independently reproduced, and both are large-support values
  (`945 = min V_10` at `s = n`).  At `n = 10` no SPEC halving occurs, so the
  `s ∈ {n−1,n}` erratum of §1 is invisible there; `n = 9` is where it shows.
