# v_task84 — ADVERSARIAL AUDIT of the never-audited pieces of the Theorem AT chain

Date 2026-08-09.  **NOTES.md not edited.**
Scope: `v_task41_r1_census.md`, `v_task43_r6_nu.md`, `v_task44_dioph.md`,
`v_task45_ellstar.md`, `v_task46_uniform_c.md`, `v_task49_vbig_nonab.md`, and
the corresponding NOTES sections §4ax addenda, §4az + addenda, §4ba addendum 2.

Method: every load-bearing statement was **re-derived from its hypotheses**, and
every number was **recomputed from scratch** by code that does not read the
audited scripts.  Where a write-up gives an object (a curve, a map, a constant),
the object was reconstructed independently and only then compared.

| file | what it does |
|---|---|
| `v_task84_thresholds.py` / `_out.txt` | exact-integer recomputation of every numeric threshold in v_task49 (crude and sharpened `s₀`, the partition bound, the case-A inequality, the monotonicity crossovers, Corollary GAP-FREE) |
| `v_task84_s12.g` / `_out.txt` | inequalities (I)–(VI) re-implemented from the statements: exhaustive for `s = 5..9`, and the requested extension to **`s = 12`** over an adversarial sample (all 133 transitive groups inside `A₁₂`, orbit-type products, 4000 random subgroups) |
| `v_task84_s10.g` / `_out.txt` | independent exhaustive recomputation of `V₁₀` |
| `v_task84_curves.sage` / `_out.txt` | v_task44 re-done end to end: cubic → Weierstrass by Sage's own Nagell transform, rank/gens/saturation, the `q`-map, `P∞`, own `κ`/`Q₀`, own inequality (I), **own LLL + exact CVP (Fincke–Pohst) reduction**, enumeration, brute-force control |
| `v_task84_arith.py` / `_out.txt` | v_task45/46: Lemma Φ, (SZ), Lemma NC and NC-gen⁺ side conditions, (SZ′) constants, MASTER/SIZE-UP/Q-LB/Lemma Q constant chase, Theorem W, Theorem L3₂-gen closed form, **the Theorem U threshold logic** |
| `v_task84_ccscan.c` / `_out.txt` | brute-force integral points of `C_c : k³−k = c(q²+q+1)` for all admissible `c ≤ 216` — independent reconstruction of v_task46's table |
| `v_task84_ct.g`, `v_task84_ct2.g` / `_out.txt` | Lemma CT, CT-×, PSN-×, A-2, Criterion CT with controls (the `L₂(512)` control in part 1 exhausted the workspace and is dropped; part 2 carries the rest) |
| `v_task84_nu.g` / `_out.txt` | v_task43's four `ν` values and the R6-CERT window arithmetic |

---

## 0.  Verdict, stated first

> **The Theorem AT chain stands.**  No error was found that changes the status of
> Theorem AT, of the (H2′) discharge, or of the C₆/C₁₂ closures' *conclusions*.
>
> **Two real defects were found, one of them in a load-bearing proof step:**
>
> 1. **v_task44 inequality (I) uses a height-difference bound in the wrong
>    direction.**  It adds "the CPS bound `ĥ ≤ h(x) + 2.4614`".  Cremona–Prickett–
>    Siksek bounds `h(P) ≤ ĥ(P) + B`, the *opposite* inequality (this is also
>    exactly what Sage's `CPS_height_bound` documents and what the numerics show:
>    over `|n_i| ≤ 5` the observed minimum of `ĥ − h` is `−2.46130`, i.e. the CPS
>    constant is essentially sharp *in its own direction*).  The constant
>    `C₁ = 12.4978` is therefore **not proven**.  *Repaired here*: with Silverman's
>    bound (`|h − ĥ| ≤ 7.0215`) and a **reduced** `x`-map that the write-up missed
>    (linear/linear instead of quadratic/quadratic), the correct inequality is
>    stronger than the write-up's, and the reduction still terminates.  **Theorem
>    C₆ and its `C₁₂` analogue survive**; see §2.
> 2. **v_task46's Theorem U is not proven.**  Its arithmetic is impeccable — the
>    `1994³−1994 = 30·Φ₃(16256)` identity and the whole `c ≤ 216` table were
>    reproduced here from scratch — but the *threshold* it compares against is
>    evaluated at the wrong point.  Requirement (ii) must hold at
>    `n_min(c) = max(N₀, c/2.26)`, and `N₀ = 10¹¹` is free (the v_task45 scan).
>    At `c = 30` the real requirement is then `B(30) < 30.12`, while the witness
>    only forces `B(30) ≥ 12.39`.  **The witness bites only if one insists on
>    closing the row from `n = 1995` upward.**  See §4.
>
> Neither defect propagates: (1) is repairable and repaired; (2) concerns only
> the *route inventory* for rows 2/3, which are OPEN either way.
>
> Everything else audited — **v_task49 in full**, v_task41's Lemmas CT / CT-× /
> PSN-× / ORB / Criterion CT, v_task43's `ν` values and R6-CERT, v_task45's
> Lemmas BP / NC / Φ / W / L3₂-gen — **checks out**, with a handful of cosmetic
> slips listed in §6.

---

## 1.  v_task49 — non-abelian V-BIG.  VERDICT: **CONFIRMED**

This is the highest-stakes item (it discharged (H2′)).  I could not break it.

### 1.1  The structure of the proof, re-derived

* **Reduction 1** `|N| ≤ ∏_e (e!)^{m_e} m_e!` — correct (`N` permutes orbits of
  equal size).
* **Reduction 2 / (★)** — re-derived line by line.  The three steps that could
  hide an error all hold: `ker(π: N → Sym(W)) ≤ Sym(Ω∖W)`; the block-fixing part
  of `N_{Sym(W)}(H^W)` embeds in `∏ N_{Sym(O_i)}(K_i)` (restriction is injective
  there); `(dm)! ≥ (d!)^m m!` is the partition count.  `|H′| ≥ |K_i′|` because
  `H ↠ K_i` carries `H′` onto `K_i′`.
* **Case A.**  `∏(e!)^{m_e} ≤ D^s` (uses `Σ e·m_e = s`, i.e. fixed-point-freeness),
  `∏ m_e! ≤ r! ≤ ⌊s/2⌋!` (uses `e_i ≥ 2`), `s!/⌊s/2⌋! ≥ (s/2)^{s/2}` and
  `D^s ≤ s^{s/2}/2^s`.  Ratio `2^{s/2}`.  Verified **exactly** (`s ≤ 3000`,
  no failures), and the sharpened `(9/8)^{s/2}` form too.
* **Case B1 — the step the audit brief suspected.**  The brief's worry
  ("`K∩A_d = 1 ⟹ [K,A_d] = 1` needs normality both ways") does **not** apply:
  the write-up never makes that inference.  The actual argument is
  `K ⊴ N_d` and `A_d ≤ N_d` ⟹ `K ∩ A_d ⊴ A_d` (conjugation by `a ∈ A_d ≤ N_d`
  preserves both factors) ⟹ by simplicity `K∩A_d ∈ {1, A_d}` ⟹ if `1` then
  `K ↪ S_d/A_d`, so `|K| ≤ 2`, impossible for `K` transitive of degree
  `d ≥ 3`.  **Correct as written.**
* **Case B2 primitive.**  Bochert 1889 is correctly stated (Wielandt Thm 14.2:
  `G` primitive of degree `d`, `A_d ⊄ G` ⟹ `[S_d:G] ≥ ⌊(d+1)/2⌋!`), and B2's
  hypothesis is exactly `A_d ⊄ N_d`.
  **New observation (robustness):** the primitive branch is *never* the binding
  one.  For every `d ≥ 5`, `⌊(d+1)/2⌋! > 2^{d/2−1}`, so `min(·,·)` in B2 is
  always the *imprimitive* value.  At `d = 212` (the value at `s = s₀`) Bochert
  gives a 171-digit index against a 32-digit requirement.  Even Praeger–Saxl
  (`|G| < 4^d`) leaves ~240 orders of magnitude of slack.  **The one classical
  (H1) citation in v_task49 carries no weight at all.**
* **Case B2 imprimitive.**  Re-derived: `P(d;a,b) = ∏_{i=0}^{b−2} C(d−ia−1,a−1)`,
  each factor `≥ C(2a−1,a−1) ≥ 2^{a−1}`, hence `P ≥ 2^{(a−1)(b−1)}`, and
  `(a−1)(b−1) = d+1−(a+b) ≥ d/2−1`.  All three sub-claims verified **exactly**
  for every `d ≤ 2000` and every factorisation: 0 failures.
* **§5 sharpening.**  Re-derived.  The step `m(d/2−1) = (md/2)(1−2/d) ≥
  (s/4)(1−2/d) = s/4 − s/(2d)` is right (it is *not* the naive `s/4 − m`, which
  would be vacuous), and `C(s,dm) ≥ (s/dm)^{dm} > 2^{dm} ≥ 2^d`.

### 1.2  The thresholds, recomputed in exact integers

| condition | last failing `s`, recomputed | v_task49 |
|---|---|---|
| `2^{s/2} > s⁶` (case A, crude) | **74** | 75 (off by one) |
| `d!/2 > s⁶` (B1, crude) | 1763 | 1763 ✓ |
| `min(⌊(d+1)/2⌋!, 2^{d/2−1}) > s⁶` (B2, crude) | **178083** | 178083 ✓ |
| **crude `s₀`** | **178084** | 178084 ✓ |
| `(9/8)^{s/2} > s⁶` | 661 | 661 ✓ |
| `d!/2 > s⁶` (sharpened) | **812** | 840 (both non-binding) |
| `2^{s/8} > s⁶` | 417 | 417 ✓ |
| `2^{⌊2√s/3⌋} > s⁶` | 15875 | 15875 ✓ |
| **sharpened `s₀`** | **15876** | 15876 ✓ |

At `s₀ = 178084 = 422²`: `D = 211`, `d = 212`, `2^{105} = 4.0565·10³¹` against
`s₀⁶ = 3.1897·10³¹` — a margin of 27 %, and at `s₀−1` it fails.  The
extension to all `s` by monotonicity is sound: `√s/4 − 1 − 6log₂s` has
derivative `> 0` for `√s > 48/ln2 = 69.25` (v_task49 says 69.3 ✓) and is
`+45.5` at `s = 4·10⁵`, the end of the exact scan.

### 1.3  Machine re-verification of (I)–(VI)

Re-implemented from the *statements* in the write-up, not from
`v_task49_chain.g`.

```
s = 5  fpf classes = 4  (non-abelian 3)   min V_5 = 6     VIOLATIONS = 0
s = 6  fpf classes = 13 (non-abelian 9)   min V_6 = 10    VIOLATIONS = 0
s = 7  fpf classes = 18 (non-abelian 15)  min V_7 = 35    VIOLATIONS = 0
s = 8  fpf classes = 97 (non-abelian 79)  min V_8 = 30    VIOLATIONS = 0
s = 9  fpf classes = 89 (non-abelian 78)  min V_9 = 280   VIOLATIONS = 0
s = 10 (separate run, exhaustive)         min V_10 = 945, |V_10| = 32
s = 12 (adversarial sample) 3317 fpf subgroups, 2784 non-abelian, VIOLATIONS = 0
```

`min V_7,…,V_10 = 35, 30, 280, 945` reproduce v_task47/48/49 exactly.

**On the requested `s = 12` extension.**  `ConjugacyClassesSubgroups(A₁₂)` is out
of reach (v_task49 already reported `s = 11` at ~15 min / 24 GB).  The audit
therefore ran (I)–(VI) over an adversarial sample: **all 133 transitive groups of
degree 12 contained in `A₁₂`**, orbit-type direct products over 15 partitions of
12, and 4000 random subgroups — 3317 fixed-point-free subgroups in all, 84 %
non-abelian.  **Zero violations.**  The sample minimum of `v(H)` is 5775 (well
below `12⁶`, consistent with v_task49's own remark that a threshold is
unavoidable).  This is a genuine extension of the checked range but *not* an
exhaustive census of `s = 12`; that remains infeasible.

### 1.4  Corollary GAP-FREE

Re-derived and checked: `C(n,6) > 6C(n,5) ⟺ n > 41`; `6C(n,5) < s⁶/2` for all
`n ≤ s+5`, `s ≥ 4`; the `s ≥ n−5 ≥ s₀` bookkeeping is right.  Note that
`H ≤ A_n` of support `s` really does restrict to `A_s` (cycle type is
preserved), so V-BIG applies.

**Verdict: v_task49 is correct, and the (H2′) discharge stands.**

---

## 2.  v_task44 — the C₆ and C₁₂ closures

### 2.1  What was reconstructed independently, and matched

Starting from the plane cubic `m³ − mz² = 6(q³+q²z+qz²+z³)` and its rational
point `(−1:0:1)`, Sage's Nagell transform gives a Weierstrass model whose
**minimal model is exactly `y² = x³ + 72x − 5148`** — v_task44's curve, obtained
without using v_task44.  Then, all independently:

| quantity | recomputed | v_task44 |
|---|---|---|
| conductor / disc / torsion | 3983580 / **−11472710400** / 1 | ✓ / ✓ (<0) / ✓ |
| `rank(proof=True)` | **3** | 3 ✓ |
| generators | `(16,10), (21,75), (24,102)` | ✓ |
| saturation index of those three | **1** (so they are a basis) | (asserted) ✓ |
| `λ_min` of the height pairing | 0.650430615543109 | 0.6504306 ✓ |
| real period `ω₁` | 0.598835521104865 | 0.5988355 ✓ |
| CPS bound | 2.461410286907625 | 2.4614103 ✓ |
| the `q`-map | `(−2x²+x+287y−20664)/(2x²+288x−289y−20520)` | **identical** ✓ |
| `z(P∞)` | 0.244514435513116 | 0.2445144 ✓ |
| `P∞` numerically | `(18.5035198650911, −50.1945528860143)` | `= (12θ−θ², 12θ−72)`, `θ=6^{1/3}` ✓ |
| number of **real** poles of `q` on `E(R)` | **1** (found by scanning `E(R)`) | 1 ✓ |
| own `κ` | 0.109322347736144 | 0.10932 ✓ |

`P∞` was additionally verified **exactly** by hand in `Z[θ]`, `θ³=6`:
`x³+72x−5148 = 144θ²−1728θ+5184 = (12θ−72)² = y²`, and
`2x²+288x−289y−20520 = 0` identically.  So the pole structure claim
("three poles, conjugate over `Q(6^{1/3})`, exactly one real because
`disc E < 0`") is correct, and it is the load-bearing structural insight of the
whole closure.

**The `q`-map's bijectivity spot-check the brief asked for** (three known points):
`(1,3) ↦ (16,10) = G₁`, `(0,2) ↦ (21,75) = G₂`, `(−3,−5) ↦ (24,−102) = −G₃`,
and further `(−1,1) ↦ (156,1950)`, `(−1,−1) ↦ (132,−1518)`,
`(−8,−14) ↦ x = 981/49`, `(−1,0) ↦ O`.  All seven claimed points are on the
curve (`m³−m = 6(q³+q²+q+1)` checked exactly) and all seven are in the image.

### 2.2  The error in inequality (I)

> (I) is derived as `h(x(P)) ≤ 2 log max(|q|,|m|) + log S`, `S = 3744`, and then
> *"Add the CPS bound `ĥ ≤ h(x) + 2.4614`."*

**CPS gives the reverse inequality.**  Sage's docstring is explicit —
`CPS_height_bound` returns `B` with `h(P) ≤ ĥ(P) + B` — and the numerics confirm
that this is the sharp direction here: over all `P = Σn_iG_i` with `|n_i| ≤ 5`,
`min(ĥ − h) = −2.46130`, i.e. within `10⁻⁴` of `−CPS`, while
`max(ĥ − h) = +0.594`.  The direction needed for (I) is `ĥ ≤ h + B`; the
rigorous constant available for it is Silverman's, `|h − ĥ| ≤ 7.021496`.

So `C₁ = 12.4978` is **not** justified.  The honest constant on v_task44's own
(unreduced) map is `2log 2.4662 + log 3744 + 7.0215 = 17.06`.

### 2.3  The repair, and the re-run reduction

The audit also found that v_task44's `x`-map is **not reduced**: its numerator
and denominator share a linear factor.  The reduced map is

  `x = (6q − 144m − 6)/(−12q − m − 12)`,  1-norms `156` and `25`,

(the pencil's base point `(q:m:z) = (−287:−24:289)` lies on the cubic, so the
map has degree 2 on `C` as it must).  Consequently

  **(I′)  `ĥ(P) ≤ log|q| + C₁′`,  `C₁′ = log(156·2.46621) + 7.021496 = 12.9740`**

— *one* `log|q|`, not two — which is strictly stronger than v_task44's (I) for
every `|q| ≥ e^{4.6}`, and more than compensates for the larger height constant.
`α = 2.46621 = (2.5·6)^{1/3}` is proven from
`|m³−m| ≤ 1.875c|q|³` and `|m|³ − |m| ≥ 0.75|m|³` for `|m| ≥ 2`.

The reduction was then re-run with an **own** implementation: LLL on the
4-dimensional lattice `⟨e₁,e₂,e₃, (⌊Cz₁⌋,⌊Cz₂⌋,⌊Cz₃⌋,⌊Cω⌋)⟩`, `C = ⌈(4B)⁵⌉`, and
a **rigorous exact CVP** (Babai nearest plane for the radius, then a full
Fincke–Pohst enumeration in exact rational arithmetic — not the "largest
Gram–Schmidt norm" heuristic and not a Babai bound), with the error term
`|Cλ| ≥ √(d²−3N²) − (3N+3) − 1`.

```
own reduction, C_6, C1' = 12.9740 :
     start 1e60   d = 5.9115e39     -> 30 -> 6 -> 6        REDUCED BOUND  N <= 6
     start 1e100  d = 1.0164e382    -> 21 -> 6 -> 6        REDUCED BOUND  N <= 6
     start 1e200  d = 1.0420e882    -> 21 -> 6 -> 6        REDUCED BOUND  N <= 6
(II) applies (|q| >= Q0) as soon as N > 4.8604
enumeration |n_i| <= 8  ->  exactly
   (-8,-14), (-3,-5), (-1,-1), (-1,0), (-1,1), (0,2), (1,3)
|q| <= Q0 direct sweep  ->  the same seven
brute force |q| < 2*10^6 ->  the same seven, nothing else
```

So the audit's reduction gives **`N ≤ 6`**, i.e. it is *sharper* than
v_task44's `N ≤ 8` (the reduced `x`-map more than pays for Silverman's larger
height constant), it is stable from starting bounds `10^60`, `10^100`, `10^200`,
and the enumeration recovers **exactly v_task44's seven points and no others**.
`Theorem C₆` therefore **stands**, on a repaired footing.

### 2.3b  `C₁₂`, likewise re-derived

The same pipeline applied to `m³ − m = 12(q³+q²+q+1)` (v_task44 gives no model,
constants or maps for this curve, so everything here is new):

```
minimal model      y^2 + y = x^3 + 18x - 1294        disc -723450123 (<0)
conductor          80383347            torsion 1
rank(proof=True)   3    gens (12,25), (81/4,683/8), (36,214)   saturation index 1
lambda_min         1.28642010262086    omega = 0.747142024237850
x-map              x = (3q - 144m - 3)/(-24q - m - 24)         S = 150
q-map              (-8x^2 + x + 2302y - 81721)/(8x^2 + 1152x - 2306y - 83881)
real poles of q    exactly 1, at z(P_inf) = 0.297632717366745
                   P_inf ~ (12.4262002135355, -29.6317145446800)
own kappa 0.13692, own Q0 13.692, C1' = 12.6169
reduction          1e60 -> 21 -> 4 -> 4 ;  1e100 -> 4 ;  1e200 -> 4
enumeration |n_i| <= 6  ->  exactly (-2,-4), (-1,-1), (-1,0), (-1,1)
brute force |q| < 2e6   ->  the same four
```

`disc < 0` again, so again exactly one real pole and the same inhomogeneous
elliptic-log form.  **v_task44's `C₁₂` list is confirmed**, with a sharper bound
(`N ≤ 4` against the published `N ≤ 6`).

### 2.4  Status of v_task44 after the audit

| claim | verdict |
|---|---|
| Weierstrass model, conductor, disc sign, rank 3 (unconditional 2-descent), generators, saturation | **CONFIRMED** independently |
| the `q`-map and its pole structure; `P∞ = (12θ−θ², 12θ−72)`; exactly one real pole | **CONFIRMED** (numerically *and* exactly in `Z[6^{1/3}]`) |
| `λ_min`, `ω₁`, `z(P∞)`, `κ` | **CONFIRMED** to all printed digits |
| inequality (I), constant `C₁ = 12.4978` | **WRONG** — CPS used in the wrong direction; repaired above |
| the `x`-map with `S = 3744` | valid but **not reduced**; the reduced map gives a strictly better (I) |
| Theorem C₆ (the seven points) | **CONFIRMED** by an independent reduction (own bound `N ≤ 6`, sharper than the published 8) + brute force to `|q| < 2·10⁶` |
| `C₁₂` (the four points) | **CONFIRMED** likewise (own bound `N ≤ 4`, sharper than the published 6) |
| "only cited input: an effective David bound `< 10²⁰⁰`" | unchanged — the audit's reduction is likewise stable up to a `10²⁰⁰` starting bound, and likewise does not evaluate David's constant |

---

## 3.  v_task45 — the filters

All re-derived; **no errors of substance**.

* **Lemma Φ (F1)(F2)(F3)** — verified for `e ∈ {3,5}` and every `q` in
  `[−400, 4000]`: 0 failures.
* **Lemma BP** — trivially correct (`|Q| = ∏|S_O|^{ℓ_O}` divides `|T| = n!/2`).
* **Lemma NC** — re-derived step by step, including every side condition the
  brief flagged:
  * `p ∈ {n,n−1,n−2}` prime with `n ≥ 12` gives `p ≥ 10 > 5 ≥ e`, so `p ∤
    gcd(e,q−1)` and hence `v_p(|S*|) = 0 ⟹ p ∤ Φ_e(q)`;
  * the "`p = n−2 ≤ n/2`" edge the brief worried about **cannot occur**:
    `n−2 > n/2 ⟺ n > 4`.  `v_p(n!) = 1` for `n/2 < p ≤ n` verified exhaustively
    for `n ≤ 3000`;
  * `p² > n` from `(n−1)(n−4) > 0`;
  * `0 < c < 2(n−2) ≤ 2p` forces `c = p`, contradicted by `6 ∣ c`.
  **Correct.**
* **Lemma NC-gen** (`j ≤ 4`, `n ≥ 40`) — correct.
* **Lemma NC-gen⁺** — the constants are right: `0.2310 = ln2/3`,
  `2.7726 = 4ln2`, `2.164 = 6/(4ln2)`; row 3's `0.1386 = ln2/5` comes from the
  *weaker* gap `q² ≥ n−3` (so `f ≥ ½log₂(n−3)`), and `3.607 = 6/(12ln2/5)`.
  `p = 2` really is the minimiser of `f(p−1)` subject to `p^f ≥ X`.
  **One defect:** the proof needs `p² > n` to get `v_p(n!) = j`, i.e.
  `n > (J(n)+1)²`.  With `J(n)+1 ≤ 2.164 ln(n−3)` this **fails for
  `40 ≤ n ≤ 81`**; the hypothesis should read `n ≥ 82`, not `n ≥ 40`.
  Non-load-bearing (that range is inside every scan).
* **Theorem W** — immediate from (F2)/(F3).  Measured retention `W₃(M) < 2n`:
  21.5 % of `n < 3000` (write-up says ~20 %).
* **Theorem L3₂-gen** — proof re-derived and correct.  Closed form reproduced
  **exactly**: `286` of the `3333` admissible `c ≤ 20000` are dead (**8.58 %**),
  `c = 12` dead, `c = 6` alive.  Exhaustive search over the first 60 dead `c`
  and `n < 40000` found **no** counterexample to the theorem.

---

## 4.  v_task46 — MASTER, Q-LB, and the Theorem U defect

### 4.1  What is right

* **MASTER**, **SIZE-UP**: two-line derivations, re-derived, correct.  The
  `f = 1` consistency check (`q ≤ (n+5)/6` vs `q ≥ n−3` ⟹ `n ≥ 5`) is right.
* **Q-LB / Lemma Q**: the `f`-optimisation is exactly right —
  `max_{f≥2} f·ln(8.1/f) = 2.9798` at `f = 3`, so `n > e^{2.9798} = 19.68`,
  i.e. `n ≥ 20`.  Recomputed: `f=2: 2.7974`, `f=3: 2.9798`, `f=4: 2.8223`,
  `f=5: 2.4121`, negative from `f ≥ 9`.  ✓
  **But the range is overstated.**  The constant `8.1` needs
  `n(n−2) ≥ 0.999n²`, i.e. `n ≥ 2000` (at `n = 40` the ratio is 0.95), and
  `K ≤ 1.01` needs `q ≥ 102`, i.e. `n ≥ 105`.  With honest constants at
  `n ≥ 40` one gets `8.518` and crossover `n ≥ 23`, so **Lemma Q is true, for
  `n ≥ 105`**, not for `n ≥ 20`.  Immaterial (everything below `10¹¹` is scanned).
* **Lemma SM** and its corollary: correct (`6/3.19 = 1.8809 ≥ 1.88`).
* **Lemma F / Lemma DS**: classical / correct.
* **The `c ≤ 216` table**: independently reproduced by brute force over
  `|k| ≤ 3·10⁶` (`v_task84_ccscan.c`).  Every witness matches:
  `c=24 (13,9)`, `c=30 (1994,16256)`, `c=48 (7,2)`, `c=60 (20,11)`,
  `c=72 (37,26)`, `c=78 (38,26)`, `c=90 (134,163)`, `c=102 (662,1686)`,
  `c=120 (259,380)`, `c=168 (147,137)`, and exactly the **7** values of `c`
  violating THRESHOLD-1.  `c = 36` indeed has **no** point on `C₃₆` (its large
  `E₃₆`-point fails the divisibility) — the write-up's honesty on that point is
  confirmed.
* **The witness identity**: `1994³ − 1994 = 7928213790 = 30·(16256²+16256+1)`,
  `16256 = 2⁷·127`, `X = 4ck = 239280`, `Y = 4c²(2q+1) = 117046800`,
  `Y² = X³ − 16c²X − 48c⁴` exactly, `4c ∣ X`, `4c² ∣ Y`, `Y/4c²` odd.
  **All verified.**

### 4.2  The defect: the threshold is evaluated at the wrong `n`

v_task46 §3 states the criterion correctly —

> a uniform bound closes the row **for all `n ≥ N₀`** iff there is `B(c)` with
> (i) `log|X(P)| ≤ B(c)` for every integral point of `C_c`, and
> (ii) `B(c) < log(4c(n−1))` for every admissible `(c,n)`, `n ≥ N₀`

— and then evaluates (ii) at `n_min = c/2.26` only, i.e. **as if `N₀` were 0**.
The correct binding value is `n_min(c) = max(N₀, c/2.26)`.  And `N₀` is not free
to choose: the v_task45 scan is complete and empty for `n ≤ 10¹¹`, so the row
only ever needs closing above `N₀ = 10¹¹`.  Recomputed at `c = 30`:

| `N₀` | required `B(30) <` | witness forces `B(30) ≥` | verdict |
|---|---|---|---|
| 1995 | 12.3859 | 12.3854 | (break-even) |
| 10⁴ | 13.9978 | 12.3854 | no contradiction |
| 10⁷ | 20.9056 | 12.3854 | no contradiction |
| **10¹¹** | **30.1159** | **12.3854** | **no contradiction** |

**The witness bites only if `N₀ ≤ 1995`.**  So Theorem U, as stated and
"[PROVEN]", is **not proven**: it refutes a uniform bound that would close row 2
*from scratch*, not one that closes it *above the scan floor* — and the latter is
all that is ever needed.

What the data *does* support is weaker and heuristic.  For `c ≳ 2.26·10¹¹` the
binding threshold really is `≈ 2 log c + O(1)`, and the measured ratios
`log X / log c` on `c ≤ 216` run from 1.75 to **3.64**, with 8 of the 14 `c`
carrying a point above 2.  That makes "`B(c) ≤ 2 log c + O(1)` is false"
plausible — but it is an extrapolation from `c ≤ 216` to `c > 10¹¹`, not a proof,
and no witness at large `c` is exhibited.

Two smaller points in the same section:

* (n1) actually gives `c < 1.13n` (the `f₁³` in `ℓ* < M/(6f₁³(n−3)²)` was dropped
  when passing to `c = 6f₁ℓ*`), not `c < 2.26n`.  The sharper form *raises*
  THRESHOLD-1 to `2 log c + 1.264`; no verdict in the table changes.
* the "conservative" remark in §3 compares `2log c + 0.693` with
  `2log c + 0.571`; with the sharper (n1) the honest value is `2log c + 1.264`,
  i.e. the table was mildly *anti*-conservative, not conservative.

### 4.3  What this changes

**Nothing about Theorem AT.**  Rows 2 and 3 are OPEN before and after; Theorem U
is a statement about which *routes* are dead.  But the following claims should be
downgraded from "proven" to "strongly suggested by the data at small `c`":

* v_task46 §0(a) "the statement such a bound would have to prove is FALSE";
* v_task46 §5 "**Theorem U** … **[PROVEN]** … with no computational input at all";
* v_task46 §6 "§3 removes (i) **permanently**";
* NOTES §4az addendum 2's title "the uniform-Diophantine route is PERMANENTLY
  CLOSED, by counterexample" and its body.

The *practical* conclusion ("per-`ℓ*` elliptic-curve work is not competitive")
survives untouched — it follows from v_task44 §2.2's counting argument
(`ℓ* < n/6`, so closing `ℓ* ≤ L` buys only `n ≤ 6L`), which is independent of
Theorem U and which I checked and confirm.

---

## 5.  v_task41 and v_task43

### 5.1  Lemma CT  [CONFIRMED]

Re-derived from Dickson's list (Huppert II.8.27): the subgroups of `L₂(q)` are
elementary abelian `p`-groups, cyclic, dihedral, Frobenius `E_{p^m}:C`, `A₄`,
`S₄`, `A₅`, and `L₂(q₀)` / `PGL₂(q₀)` for subfields.  Of these only `A₅` and the
subfield `L₂(q₀)` are perfect and nontrivial (`PGL₂(q₀)` is not perfect for odd
`q₀`, and equals `L₂(q₀)` for even `q₀`).

* `q = 2^f`, `f` an odd prime: `f′ ∣ f ⟹ f′ ∈ {1,f}`, and `L₂(2) ≅ S₃` is not
  perfect; `A₅ ≤ L₂(2^f)` needs `5 ∣ 2^f(4^f−1)`, and `ord₅(4) = 2`, so
  `5 ∣ 4^f−1 ⟺ 2 ∣ f`.  The brief's cross-check via `ord₅(2) = 4` gives the same
  answer.  **`f = 2` is correctly not claimed.**
* `q = p ≡ ±3 (mod 10)`, `p ≥ 7`: no subfield, and `A₅ ≤ L₂(p)` needs
  `p ≡ ±1 (mod 10)` or `p = 5`.

GAP confirmation (proper nontrivial **perfect** subgroups):

```
L2(8)   order 504      : 0        L2(16)  order 4080    : 1  [60]    (A5; 5 | 4^4-1)
L2(32)  order 32736    : 0        L2(64)  order 262080  : 2  [60,504]
L2(128) order 2097024  : 0        L2(4)=A5 order 60     : 0  (f=2, not claimed)
```

### 5.2  Lemma CT-×, PSN-×, A-2, Criterion CT  [CONFIRMED]

`C_G(U) = ∏ C_{S_i}(π_i(U))` (the centralising condition is componentwise);
`C_G(U) ≤ N_G(U) = U` kills `U_i = 1`; Goursat then forces `U = G` when the
factors are pairwise non-isomorphic.  `A_{n−1}` is perfect for `n ≥ 6`, proper,
and maximal (point stabiliser of a primitive action) hence self-normalising, so
`mult₁(A_n) ≥ 2`.  All correct.  GAP re-computation reproduces every published
number:

```
mult1(L2(7)) = 1   mult1(L2(8)) = 1   mult1(L2(11)) = 3   mult1(L2(13)) = 1
mult1(L2(7) x L2(13)) = 1     <- Criterion CT
mult1(L2(7) x L2(7))  = 3     <- control: the non-isomorphism hypothesis is needed
mult1(L2(7) x L2(11)) = 3     <- control: = 1*3, Lemma PSN-x with equality
mult1(A6..A9) = 3, 5, 7, 6    <- Lemma A-2's data
L2(p), p = +-3 mod 10, p in {7,13,17,23,37,43,47,53,67,73}: 0 proper perfect
L2(p), p = +-1 mod 10, p in {11,19,29,31,41}: exactly 2 classes of A5
```

### 5.3  Lemma ORB  [CONFIRMED]

`h(ℓ) = ℓ·log max(60, C/(2ℓ))` is non-decreasing on `[1,∞)` (derivative
`log(C/2ℓ) − 1 > 0` while `C/2ℓ ≥ 60 > e`; `ℓ log 60` afterwards; the two pieces
agree at the crossover) and `h(1) ≥ log(C/2)`.  Hence `k ≤ log(n!/2)/log(C(n,3)/2)
≈ n/3`.  Correct — and the conclusion ("≥3 orbits is arithmetically free") is
the right reading.

### 5.4  v_task43  [CONFIRMED, with a cleaner proof of Lemma NU]

The four `ν_out` values were recomputed from CTblLib character tables:
`ν_out(HS) = 1100`, `ν_out(McL) = 113400`, `ν_out(Fi₂₄′) = 306936` — matching
the write-up exactly — and the window arithmetic reproduces
`n₀ = 195/1126/4636/8270` against `n_max = 73/164/279/52703`, so HS, McL, Co₃ are
empty for all `n` and only `Fi₂₄′` needs Lemma R6-Fi.  The `(K2)` ratio
`ν²/(4|Out|ι) = 2.4228474` and `ν³ = 2.8916·10¹⁶ > C(52703,3) = 2.4397·10¹³` both
check.

**Lemma NU's second bullet is muddled but the lemma is true**, with a cleaner
proof: if `A ∩ Inn(S) = 1` then for `g ∈ N_S(A)` and `x ∈ A`,
`x^g x^{-1} ∈ A ∩ Inn(S) = 1` (it lies in `A` because `g` normalises `A`, and in
`Inn(S)` because `Inn(S) ⊴ Aut(S)` and `g ∈ Inn(S)`), so
**`N_S(A) = C_S(A) ≤ C_S(x)`** for *every* `x ∈ A` — no "minimum over the
classes" hedge and no need for `⟨x⟩` to be characteristic.  The same computation
gives `N_S(⟨x⟩) = C_S(x)` for outer `x` of prime order, which is what makes
`ν_out` a class size.  R6-CERT's chain (`v₂(n!) − 1 ≤ n−2`, `C(n,3) ≥ (n−2)³/6`)
is correct.

---

## 6.  Complete defect list

| # | where | severity | statement |
|---|---|---|---|
| **D1** | v_task44 §1, inequality (I) | **substantive, repairable** | CPS height bound used in the wrong direction; `C₁ = 12.4978` unproven.  Correct constant: Silverman's `7.0215` in place of `2.4614`.  Repaired here, with a *better* (I) from the reduced `x`-map. |
| **D2** | v_task46 §3, Theorem U | **substantive, not repairable as stated** | threshold (ii) evaluated at `n_min = c/2.26` instead of `max(N₀, c/2.26)`; with the free `N₀ = 10¹¹` the witness gives no contradiction.  Theorem U is not proven; downgrade to a heuristic. |
| D3 | v_task44 §1 | cosmetic | the `x`-map is not in lowest terms (`S = 3744` instead of `156`); harmless but it made (I) weaker than it needed to be. |
| D4 | v_task45 §2.4, Lemma NC-gen⁺ | cosmetic | needs `n ≥ 82` (from `p² > n`), not `n ≥ 40`. |
| D5 | v_task46 §2.3, Lemma Q | cosmetic | the constants `1.01` and `0.999` need `n ≥ 105` resp. `n ≥ 2000`; the lemma is true but not for `n ≥ 20`. |
| D6 | v_task46 §3 | cosmetic | (n1) gives `c < 1.13n`, not `c < 2.26n`; the "conservative" remark is backwards. |
| D7 | v_task49 §3, §5 | cosmetic | last failure of `2^{s/2} > s⁶` is `s = 74`, not 75; last failure of `d!/2 > s⁶` in the sharpened split is `812`, not 840.  Neither is binding. |
| D8 | NOTES §4ba addendum 2 / v_task49 §6, §8 | cosmetic inconsistency | the sharpened `s₀ = 15876` is announced, then `n₀ = 178089` (the *crude* `s₀ + 5`) is used in the same paragraph; likewise the (AB) residue is quoted with both `178084` and `71824`.  With the sharpened threshold, `n₀ = 15881`.  All far below `10¹¹`, so nothing downstream moves. |
| D9 | v_task43 §1, Lemma NU | cosmetic | the `A₀ = 1` branch is argued loosely; see §5.4 for a two-line correct proof. |

---

## 7.  Does the Theorem AT chain stand?

**Yes.**

* The **(H2′) discharge** (v_task49) is correct in every step I could test, and
  its one classical citation (Bochert) turns out to carry no weight, since the
  elementary imprimitive bound dominates it at every degree.  `s₀ = 178084` and
  the sharpened `s₀ = 15876` are both confirmed in exact integer arithmetic, and
  the overlap with the `10¹¹` scan is real.  Theorem GAP is hypothesis-free where
  it is used.
* The **row-1 closure** (`S₄(q)` odd non-prime, `ℓ* = 1`) rests on a genuine but
  repairable error in one constant.  The curve, its rank, its generators, the
  `q`-map, the pole structure and `z(P∞)`, `κ` and `λ_min` are all independently
  confirmed; the repaired inequality (I′) is *stronger* than the published one.
  The independent reduction gives `N ≤ 6`
  (v_task44: 8), stable from `10^60/10^100/10^200`, and the enumeration returns
  exactly v_task44's seven points; a brute-force sweep `|q| < 2·10⁶` finds
  nothing else.  The same pipeline on `C₁₂` gives `N ≤ 4` (v_task44: 6) and
  exactly its four points.  **Row 1 is closed.**
* The two **open rows** are unaffected: they were open before this audit and are
  open after.  The only change is that v_task46's claim to have *permanently*
  closed the uniform-Diophantine route must be withdrawn — which enlarges, not
  shrinks, the set of things that might still work.

Theorem AT therefore continues to hold for all `n ≥ 9` modulo **(H1)** alone
(cited classical facts, including the David-type effective constant for C₆/C₁₂
that v_task44 already flags), with `9 ≤ n ≤ 10¹¹` unconditional-modulo-(H1) by
exact scan.
