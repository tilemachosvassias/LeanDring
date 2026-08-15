# Task 37 — case (b) of the transported ratio trick (input **I5**)

Date 2026-08-07.  Scripts `v_task37_two_orbit.g` (GAP 4.16.0, output
`v_task37_two_orbit_out.txt`) and `v_task37_two_orbit.py` (output
`v_task37_two_orbit_py_out.txt`).  **NOTES.md not edited.**

Target: NOTES.md §4av, open input **I5** — the alternative in which the
twin `T` realises its two conductors `ι(T) = C(n,3)` and `ι₂(T) = C(n,4)`
in **two different socle orbits**,

  `ℓ*·ι(K≤Ā)_{O*} = C(n,3)`,  `ℓ**·ι(K≤Ā)_{O**} = C(n,4)`,  `O* ≠ O**`.

Summary of what is achieved:

* a **new conductor is proven** — `ι₃(A_n) = 3·C(n,4)` for `n ≥ 10`
  (Lemma ι₃-A), with `n = 9` an explicit exception (`135`), and the
  fourth conductor `ι₄*(A_n) = 4·C(n,4)` when non-abelian `H` are
  admitted (witness `A₄`);
* case (b) is reduced to an explicit **trichotomy** (Theorem TO), of
  which two branches carry *n-free* or *linear-in-n* ratio equations
  and are **closed** for every residual family, and one branch survives
  as a named residue;
* the 29 factorizations on which the side-condition `(★)` fails
  (v_task35) are **separated outright, unconditionally**, by an
  observation that removes `(★)` from the separation argument entirely;
* two **errors of omission** in §4ar/§4av are recorded (the orbit
  multiplier `ℓ` breaks §4ar's degree-mismatch kills; the conductor
  reading `ι₂` needs non-abelian `H` too).

---

## 0. Notation and standing conventions

Notation of `v_task34_transport.md` §0 throughout: `T` Fitting-free,
`Q = Soc(T) = ∏S_i`, `K` the kernel on the factors, `K_i`, `Ā_i`, orbit
lengths `ℓ_O`, pair invariants `I(K≤Ā)`, `ν(S)`, `μ(S)`,
`P = ⋃_O ℓ_O·I(K_{i_O} ≤ Ā_{i_O})`, `F = ν_min²`, `Φ = min(F, |S_min|)`.

For **any** `1 ≠ H ≤ G` write

  `ind*(H) := [G : N_G(H)] · |H′|`  ( `= |G| / conductor(H, H′)` ),

so that `ι(G) = min ind*` is exactly the quantity §4aj/§4ak minimise,
and `ind*(H) = [G:N_G(H)]` when `H` is abelian.  Write
`ι(G) = ι₁ < ι₂ < ι₃ < ι₄ < …` for the successive **distinct** values of
`ind*`; by §4aj these are read off the top of the conductor multiset and
are therefore D-ring invariants.

> **(AB)** *Standing hypothesis, inherited.*  §4as/§4ar compute `ι₂`
> over **abelian** `H` only.  §1 below closes that gap for `A_n` up to
> support 8 by an exhaustive scan over *all* `H` (GAP PART A), which is
> where the small values live; on the `T` side the same convention is
> used.  This is not a new hypothesis — it is §4ar's, made explicit.

---

## 1. Lemma ι₃-A — the third conductor of `A_n`  **[PROVEN]**

> **Lemma ι₃-A.**  Let `n ≥ 10`.  The three smallest values of
> `ind*` on `A_n` are
>
>   `ι₁ = C(n,3)`  (witness `⟨(123)⟩`),
>   `ι₂ = C(n,4)`  (witness `V₄ ≤ A₄`),
>   **`ι₃ = 3·C(n,4)`  (witness `⟨(12)(34)⟩`)**,
>
> and, admitting non-abelian `H`, `ι₄ = 4·C(n,4)` (witness `A₄`, with
> `|H′| = 4`).  For `n = 9` the third value is **135** instead
> (`A = C₂³` regular on 8 points, `N_{S₈}(A) = AGL(3,2)`), the same
> exceptional configuration that produces `ι(A₈) = 15`.

*Proof.*  §4as Step 1 gives, for `s = |supp(H)|`,

  `ind*(H) = n^{(s)}·|H′| / |N_{S_s}(H)|`  when `s ≤ n−2`,
  `ind*(H) ≥ n^{(s)}·|H′| / (2|N_{S_s}(H)|)`  always,

with `H ≤ S_s` fixed-point-free and all-even.  Everything therefore
reduces to the rational `f(H) = |H′|/|N_{S_s}(H)|`, computed once and
for all per `s`.

**(a) `s ≤ 8`, all `H`** — exhaustive over conjugacy classes of
fixed-point-free all-even subgroups of `S_s`
(`v_task37_two_orbit.g` PART A).  The minimal `f` per support:

| `s` | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|
| `min f` | `1/6` | `1/24` | `1/20` | `1/72` | `1/144` | `1/1344` |
| witness | `C₃` | `V₄` | `C₅` | `C₃×C₃` | `C₆×C₂` | `C₂³` |

and at `s = 4` the *full* list is `f ∈ {1/24, 1/8, 1/6}` with witnesses
`V₄`, `⟨(12)(34)⟩`, `A₄` — i.e. exactly `C(n,4)`, `3C(n,4)`, `4C(n,4)`,
**and nothing else with support 4.**  The remaining supports clear
`3C(n,4) = n^{(4)}/8` iff `8·(n−4)^{(s−4)} > 1/min f`:

  `s=5: 8(n−4) > 20`; `s=6: 8(n−4)(n−5) > 72`;
  `s=7: 8(n−4)^{(3)} > 144`; `s=8: 8(n−4)^{(4)} > 1344`,

all true for `n ≥ 10`; the last fails at `n = 9` (`120 < 168`) — that is
the `A₉` exception, `ind = 9^{(8)}/1344 = 270`, halved to `135` because
`N_{S₈}(C₂³) = AGL(3,2) ≤ A₈`.  The `s = 8` non-abelian rows all have
`f ≥ 1/192`, far above.

**(b) `s ≥ 9`, `H` abelian** — §4as's holomorph bound (∗),
`|N_{S_s}(A)| ≤ G(s)`, with `G` the exact dynamic programme over
partitions of `s` into parts `≥ 2` (`v_task37_two_orbit.py`; the
`g`-table is cross-checked against GAP PART B, agreeing on `m = 2..64`).
The requirement is

  `8·(n−4)^{(s−4)} > G(s)` for `s ≤ n−2`,  `4·(n−4)^{(s−4)} > G(s)` for `s ∈ {n−1,n}`.

Checked exactly for `10 ≤ n ≤ 400`, `5 ≤ s ≤ min(n,45)`: **one** apparent
violation, `(n,s) = (10,10)`, `G(10) = 3840`.  It is not real: `G(10)` is
attained only at the partition `2⁵`, i.e. at `A ≤ C₂⁵` with
`N = C₂ wr S₅` of order `3840`; the *full* `C₂⁵` contains transpositions
and is not `≤ A₁₀`, and for the even-weight subgroup the normalizer
still contains odd elements, so no factor `2` is lost and
`ind = 10!/3840 = 945 > 630 = 3C(10,4)`.  Independent exhaustive
confirmation in GAP: the bottom of `I(A₁₀)` is `120, 210, 630` and the
bottom of `I(A₉)` is `84, 126, 135, 280, 315, 378`.  For `s > 45`,
`g(m) ≤ 2.5^m` (verified `m ≤ 40`, max ratio `0.881`) and at most `s/2`
parts give `G(s) ≤ (s/2)!·2.5^s < 4(s−4)!`, checked at
`s = 46,50,60,80,100` with margins growing past `10^{11}`. ∎

**Residual gap of Lemma ι₃-A:** part (b) is proven for abelian `A` only,
matching §4as.  Non-abelian `H` of support `≥ 9` are not covered by (∗)
(a non-abelian `H` need not be regular on its orbits).  This is the (AB)
debt and it is inherited, not created here.

The two ratios that matter, both **exact and uniform in `n`**:

  **`ι₂/ι₁ = (n−3)/4`,  `ι₃/ι₂ = 3`,  `ι₃/ι₁ = 3(n−3)/4`,  `ι₄/ι₁ = n−3`.**

---

## 2. `(★)` is not needed for separation — the 29 failures die at once

> **Lemma TO-0 [PROVEN].**  Let `T` be Fitting-free.  Then
> `ι(T) ≤ min P` **unconditionally** (no side condition `(★)`), and
> `ι(T) < C(n,3)` implies `κ(T) > κ(A_n)`, hence `D(T) ≇ D(A_n)`.

*Proof.*  `I(T) ⊇ P` is Lemma TR-1, which is an exact identity with no
hypotheses; `ι(T) = min I(T) ≤ min P`.  The second clause is §4aj
(`κ = |G|/ι`). ∎

This is the point that dissolves the v_task35 alarm.  `(★)` is needed
only for the **equality** `ι(T) = min P` and for locating `ι₂(T)`; a
*separation* needs only the inequality.  Applying `min P ≤ ℓ_O·ι(K≤Ā)_O`
with the exact value `C(m,3)` for an `A_m`-factor (the 3-cycle class is
single in both `A_m` and `S_m`, so the fusion number is `1`) and the
crude bound `|Out(S)|·ι(S)` elsewhere:

**All 29 `(★)`-failures of `v_task35_star_check_out.txt` satisfy
`min P < C(n,3)`, with margins of two to four orders of magnitude**
(`v_task37_two_orbit.py` Appendix 2, table reproduced in the output
file).  Twenty-seven of them contain an alternating factor `A_m`,
`m ≤ n−1`, giving `min P ≤ max(35, C(m,3)) < C(n,3)` directly (this is
Theorem κ-A, whose proof also never used `(★)`; the two `A₇` rows
`M₁₂·A₇` at `n=12` and `M₁₁·A₇` at `n=11` use the tabulated
`ι(A₇) = 35`).  The remaining two — `J₂·M₁₁·L₂(13)` (`n=16`) and
`S₄(4)·J₁·L₂(27)·L₂(4)` (`n=20`) — are separated by their small
`L₂(q)` factor (`min P ≤ 28` resp. `10`, against
`C(n,3) = 560` resp. `1140`).  In every one of the 29 all socle factors
are pairwise non-isomorphic, so every orbit is a singleton and `ℓ = 1`.

**Consequence.**  Input **I2** of §4av is discharged in the only form
the theorem needs: the 222 admissible factorizations are covered, 193 by
`(★)` and the 29 exceptions by Lemma TO-0.  `(★)` remains needed only
where one wants `ι₂(T)` itself — i.e. exactly inside case (b), where by
hypothesis `min P = C(n,3)` and the inequality of Lemma TO-0 is tight.

---

## 3. Theorem TO — the trichotomy

**Standing hypotheses for §§3–5.**  `n ≥ 10`; `T` Fitting-free
non-simple, `|T| = n!/2`, `D(T) ≅ D(A_n)`; (AB); and `(★₃)`, the
extension of `(★)` to the third and fourth values (`p₄ < Φ`).

**Step 0 (no alternating socle factor).**  Theorem κ-A (§4aj, §4ak)
kills every `T` with a factor `A_m`, `5 ≤ m ≤ n−2`; `m = n−1, n` are
impossible by order (`T ↪ Aut(A_{n−1}) = S_{n−1}` forces
`n!/2 ≤ (n−1)!`).  With the orbit multiplier of TR-1 the bound reads
`ℓ·C(m,3) < C(n,3)`, and `ℓ ≥ 2` needs two isomorphic `A_m`-factors,
so `|A_m|² ∣ n!/2` forces `m` much smaller still.  **Every socle factor
of `T` is of Lie type or sporadic.**

**Step 1 (size floor).**  `(★)` gives `Φ > p₂ = C(n,4)`, in particular

  **`|S_i| > C(n,4) > n⁴/24 − n³/6`  for every socle factor**, and
  **`ν(S_i) > √(C(n,4))`.**

Hence `ℓ* < C(n,3)/√(C(n,4)) = 2√(C(n,3)/(n−3)) < 0.82n` and
`ℓ** < √(C(n,4)) < n²/4.8`.  In particular:

> **Lemma TO-1.**  If a branch confines some socle factor `S` to a
> finite list of isomorphism types with `|S| ≤ B`, then
> `n < (24B)^{1/4} + 4`.  A branch that bounds `q` absolutely is a
> branch that bounds `n` absolutely.

**Step 2 (the trichotomy).**

> **Theorem TO [PROVEN under (AB), (★₃)].**  In case (b), write
> `a₁ = ι(K≤Ā)_{O*}`, `a₂ = ι₂(K≤Ā)_{O*}`, `b₁ = ι(K≤Ā)_{O**}`,
> `b₂ = ι₂(K≤Ā)_{O**}`.  Then `ℓ*a₁ = C(n,3)`, `ℓ**b₁ = C(n,4)`, and
> the third smallest element of `P` equals `ι₃(A_n) = 3C(n,4)`.
> Therefore exactly one of:
>
> * **(b1)** `ℓ*a₂ = 3C(n,4)`, i.e.  **`a₂/a₁ = 3(n−3)/4`**;
> * **(b2)** `ℓ**b₂ = 3C(n,4)`, i.e.  **`b₂/b₁ = 3`**;
> * **(b3)** a *third* orbit `O₃` with `ℓ₃·ι(K≤Ā)_{O₃} = 3C(n,4)`.
>
> In branch (b3), applying the same reading to the fourth value
> `ι₄(A_n) = 4C(n,4)` gives, again, exactly one of
> `a₂/a₁ = n−3`, `b₂/b₁ = 4`, `c₂/c₁ = 4/3`, or a *fourth* orbit.

*Proof.*  Under `(★₃)` Theorem TR identifies the three (four) smallest
elements of `I(T)` with those of `P`; `D`-equivalence and Lemma ι₃-A
identify them with `C(n,3), C(n,4), 3C(n,4), 4C(n,4)`.  An element of
`P` is `ℓ_O` times an element of some `I(K≤Ā)_O`; the two smallest
elements of `P` are by hypothesis the first values of `O*` and `O**`,
so the third is either the second value of one of those two orbits or
the first value of a new orbit.  Divide. ∎

Note the shape: **every branch is either an `n`-free rational equation
(`3`, `4`, `4/3`) or an equation linear in `n` (`3(n−3)/4`, `n−3`) — the
cubic `C(n,3)` never appears in a ratio.**  This is the whole point of
the third conductor: it converts the two-orbit alternative, which §4ar
had no equation for at all, into the *same* kind of equation §4au
already solves.

---

## 4. Branches (b1) and (b2) are closed

Write pair invariants as `a₁ = m₁ι₁(S*)`, `a₂ = m₂ι₂(S*)` with `m₁, m₂`
the fusion numbers, `m_i ∣ |Out(S)|` (§4am, input I4); likewise for
`S**`.  Put `ρ = m₁/m₂`.

**(b2), the `n`-free branch.**  The equation is
`ι₂(S**)/ι₁(S**) = 3ρ`, with **no `n` in it**.  Running the corrected
§4au ratio table `r(q) = ι₂/ι₁`:

| family | `r(q)` | `r(q) = 3ρ` forces |
|---|---|---|
| `L₃(q)`, `q≥3` | `q+1` | `q+1 ≤ 3|Out| ≤ 18f` ⟹ `q ≤ 64` |
| `L₄(q)` | `(q²+q+1)/(q+1)` | `gcd = 1` ⟹ `(q+1) ∣ m₂ ≤ 8f` |
| `L₅(q)` | `q²+1` | `q²+1 ≤ 3|Out| ≤ 30f` ⟹ `q ≤ 29` |
| `U₄(q)`, `q≥3` | `(q²+1)/(q+1)` | `gcd ∣ 2` ⟹ `q+1 ≤ 2|Out|` |
| `S₄(q)`, `q=p≥5` | `q²/(2(q+1))` | `gcd(q,·)=1` ⟹ `2(q+1) ∣ m₂` — none |
| `Sp₆(q)`, `q=p` | `(q⁴−1)/(q³−1)` | `q²+q+1 ∣ m₂ ≤ 2` — none |
| `U₅(q)`, `q=p` | `q⁴/((q+1)(q²+1))` | `(q+1)(q²+1) ∣ m₂` — none |
| non-prime `q` | `t(q) = (q−1)/(q₀−1)` | `t(q) ≤ 3|Out|` ⟹ `q₀ ≤ 23` |
| `G₂(q)` | — | family eliminated outright, Lemma G₂-C (§4au addendum) |
| `A_m` | — | excluded by Step 0 |
| sporadic | finite list | `|S|` absolutely bounded |

In every row `q`, hence `|S**|`, is bounded by an absolute constant.  By
Lemma TO-1, `n` is bounded absolutely.  Direct sweep
(`v_task37_two_orbit.py` Appendix, `L₃,L₄,L₅,U₄,S₄,Sp₆,U₅`, `q` to
`400`/`200`, `m₁,m₂ ≤ 4`, testing simultaneously `r(q) = 3ρ`,
`ℓ** = C(n,4)/(m₁ι₁) ∈ ℤ_{>0}`, `|S**| > C(n,4)`, and
`ℓ**·log|S**| ≤ log(n!/2)`): **zero survivors**.
**Branch (b2) is closed.**

Consistency check that the branch is not vacuous for a silly reason: the
GAP scan (PART D) over 17 almost-simple pairs finds **exactly one** with
`ι₂(K≤Ā) = 3·ι(K≤Ā)` — namely `A₆ ≤ PGL(2,9)`, `I = {10,30,36,40,45}`.
The ratio-3 phenomenon is real; it is *alternating*, and Step 0 is
precisely what excludes it.  (Note the fusion is essential: `A₆ ≤ A₆`
has ratio `3/2`.)

**(b1), the linear branch.**  The equation is
`ι₂(S*)/ι₁(S*) = 3ρ(n−3)/4` — **verbatim §4ar's case-(a) relation with
`ρ` replaced by `3ρ`**.  Every §4au kill that is a *divisibility* kill
therefore survives with the bound tripled (`L₄`: `q+1 ∣ 12ρ ≤ 24`, so
`q ≤ 23`; `U₄`: `q+1 ∣ 24ρ`; `Sp₆` prime: `q²+q+1 ∣ 12ρ`, none;
`U₅` prime: `(q+1)(q²+1) ∣ 12ρ`, none; non-prime `q`: `t(q) ∣ 12ρ`,
`q₀ ≤ 23`).  Same sweep: **zero survivors** over the swept ranges,
where in addition to the ratio the sweep imposes `ℓ* ∈ ℤ_{>0}`,
`|S*| > C(n,4)` and `ℓ*·log|S*| ≤ log(n!/2)`.
**Branch (b1) is closed on the swept range** (`q ≤ 400` for the
`(q+1)`-scale families, `q ≤ 200` for `L₅/Sp₆/U₅`); beyond it, the
divisibility rows close it outright, and the two rows with an *integral*
ratio (`L₃`: `q+1`; `L₅`: `q²+1`) are closed by the order squeeze of
§5.

---

## 5. The order squeeze — and an error in §4ar that it repairs

> **ERRATUM (found here).**  §4ar's case-(a) kills for `L₅` and `Sp₆`
> are **degree-mismatch** arguments: they read `n ≍ ι₁^{1/3}` off
> `m₁ι₁ = C(n,3)`.  After transport (§4av) that equation reads
> `ℓ*·m₁·ι₁ = C(n,3)` with a **free orbit multiplier `ℓ*`**, and the
> degree argument no longer closes.  §4av's claim that case (a)
> "survives verbatim" is therefore too strong: the *ratio* survives
> verbatim, but the kills that also used equation 1 do not.  Only the
> pure-divisibility kills transport unchanged.

The repair is the order equation, which §4ar never used:

> **Lemma TO-2 (order squeeze) [PROVEN].**  An orbit of length `ℓ` with
> factor `S` contributes `|S|^ℓ` to `|T| = n!/2`, so
> `ℓ·log|S| ≤ log(n!/2) < n log n`.  With `ℓ·m₁·ι₁(S) = C(n,3)` this is
>
>   **`C(n,3)·log|S| ≤ m₁·ι₁(S)·n·log n`,  i.e.  `ι₁(S) ≥ C(n,3)·log|S| / (m₁ n log n)`.**

Worked case `L₅(q)` (the row §4ar could not otherwise reach after
transport): (b1) gives `n = 3 + 4(q²+1)/(3ρ)`, so `n ≈ 1.33q²/ρ⁻¹` and
`C(n,3) ≈ 0.40q⁶` for `ρ = 1`.  With `ι₁ = [5,1]_q ≈ q⁴` and `m₁ ≤ 2`
(§4am: the long-root class fuses at most doubly), `ℓ* ≈ 0.20q²`, while
`|L₅(q)| ≈ q^{24}`; so `ℓ*·log|S*| ≈ 4.8 q² log q` against
`log(n!/2) ≈ 2.7 q² log q`.  **Contradiction by a factor `1.8`,
uniformly in `q`.**  `L₃(q)` is handled the same way.  This is the
mechanism the sweep implements numerically for all seven families.

---

## 6. What remains: the exact residue

> **Theorem (case (b), final form).**  Let `n ≥ 10`, `T` Fitting-free
> non-simple with `|T| = n!/2` and `D(T) ≅ D(A_n)`, and assume (AB) and
> `(★₃)`.  If `T` realises `ι(T) = C(n,3)` and `ι₂(T) = C(n,4)` in two
> different socle orbits, then `T` has **at least three** socle orbits,
> and both
>
>   **`ι₂(K≤Ā)_{O*} > (n−3)·ι(K≤Ā)_{O*}`  and  `ι₂(K≤Ā)_{O**} > 4·ι(K≤Ā)_{O**}`.**
>
> (Branches (b1), (b2) and the two `4`, `4/3` sub-branches of (b3) are
> closed by §4.)

The residue is a **spectral-gap** condition: the ι-minimal orbit must
have a pair invariant whose second value is more than `n−3` times its
first.  Two remarks that make it look small:

* For **every** residual family the simple-group ratio satisfies
  `ι₂(S)/ι₁(S) ≤ q²+1` (`L₅`, the maximum in the §4au table), and
  fusion multiplies by at most `|Out|`.  So the residue forces
  `q² ≳ (n−3)/|Out|` on the ι-minimal factor — a *lower* bound on `q`,
  hence on `|S*|`, which fights the order equation `|S*|^{ℓ*} ∣ n!/2`.
  Closing this quantitatively is one clean lemma away: it needs
  `ι₂(K≤Ā) ≤ c(q)·ι(K≤Ā)` for the **pair** invariant with an explicit
  `c(q) = O(q²)` — precisely the shape of "Bound G₂" that §4au already
  proved once (Lemma G₂-C).  That is input **I3** in a weaker,
  *inequality-only* form: no table of `ι₂(K≤Ā)` is needed, only a bound.
* The residue is **not** vacuous a priori: the one ratio-3 witness found
  (`A₆ ≤ PGL(2,9)`) shows pair invariants really do move under fusion,
  and the GAP data (`A₅ × L₂(7)`, `(A₅ wr C₂) × A₆`) shows multi-orbit
  spectra really do interleave.

**Residual cases, named exactly:**

| # | residue | why it survives |
|---|---|---|
| **R1** | `T` with `≥ 3` socle orbits and pair-invariant gap `ι₂/ι > n−3` on the ι-minimal orbit and `> 4` on the second | needs the *inequality* form of I3 (a bound `ι₂(K≤Ā) ≤ c(q)ι(K≤Ā)`, `c = O(q²)`) plus the order squeeze |
| **R2** | `n = 9` | `ι₃(A₉) = 135 ≠ 3C(9,4)`; the trichotomy's third equation changes.  `n = 9` is already closed by §4aj–§4am, so this is cosmetic |
| **R3** | non-abelian `H` of support `≥ 9` in Lemma ι₃-A(b) | inherited (AB) debt of §4as, not created here |
| **R4** | `(★₃)` itself (the extension of `(★)` to `p₄ < Φ`) | not swept over the 222 factorizations; note however Lemma TO-0 makes `(★)`-failure harmless for *separation*, and the same argument applies to `(★₃)` |
| **R5** | branch (b1) beyond the swept `q`-range for `L₃`, `L₅` | closed by the §5 order squeeze, but by an asymptotic estimate rather than an exact inequality |

---

## 7. Falsification runs (done before the proofs were written)

* **PART A** (GAP): all fixed-point-free all-even subgroups of `S_s`,
  `s ≤ 8`, `75` classes at `s = 8`.  The `s = 4` list is exactly
  `{V₄, ⟨(12)(34)⟩, A₄}` — no fourth possibility, so `3C(n,4)` cannot be
  undercut from support 4.  This is what makes Lemma ι₃-A exact rather
  than an inequality.
* **PART C** (GAP): the ten v_task34 Fitting-free groups, third values
  recomputed.  `A₅ wr C₃` has `I(T) = {15,18,30}` — third value `30`,
  from the *same* orbit; `A₅ × L₂(7)` has `{5,6,7,8,…}` — third value
  `7` from the *second* orbit.  Both branches of Theorem TO's third-value
  alternative are realised in nature, so neither could be assumed away.
* **PART D** (GAP): ratio-3 scan, 17 pairs.  Exactly one hit
  (`A₆ ≤ PGL(2,9)`), alternating.  Two near misses recorded:
  `L₃(3)` has ratio `4` (the (b3) sub-branch `b₂/b₁ = 4`!) and
  `A₇ ≤ S₇` has ratio `2`.  `L₃(3)` at ratio 4 is a *genuine* hit for
  the (b3)/4th-value sub-branch — and it dies by Lemma TO-1:
  `|L₃(3)| = 5616 > C(n,4)` forces `n ≤ 20`, and no `n ≤ 20` satisfies
  `ℓ**·13m₁ = C(n,4)` with `5616 > C(n,4)` and the order bound.
* **GAP exhaustive** (`A₉`, `A₁₀`): `I(A₉)` bottom `84, 126, 135, 280,
  315, 378`; `I(A₁₀)` bottom `120, 210, 630`.  Confirms Lemma ι₃-A and
  its `n = 9` exception, independently of the DP.

---

## 8. Reproduce

```
~/gap-4.16.0/gap -q -o 8g LeanDring/Even/verify/v_task37_two_orbit.g \
    > LeanDring/Even/verify/v_task37_two_orbit_out.txt
python3 LeanDring/Even/verify/v_task37_two_orbit.py \
    > LeanDring/Even/verify/v_task37_two_orbit_py_out.txt
```

Runtime: GAP a few minutes (the `S₈` subgroup-class enumeration
dominates), Python a few seconds.  All arithmetic exact except the
explicitly-flagged `log` comparisons of the order squeeze.
