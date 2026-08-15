# v_task62 — the degree-7 spinor-norm square classes: four of the five rational columns are ZERO, and (T-BC-RES) then holds in every residue class

Date 2026-08-08.  Scripts `v_task62_spinor.g` (spinor-norm machinery,
validation, orthogonal degree-7 columns), `v_task62_lib.g` (shared library),
`v_task62_sp.g` + the residue scans (symplectic degree-4/6 columns),
`v_task62_spinor.py` (the Δ evaluation).  Outputs:
`v_task62_spinor_out.txt`, `v_task62_spinor_cols_out.txt`,
`v_task62_sp_out.txt`, `v_task62_sp_scan_out.txt`,
`v_task62_sp_scan6_out.txt`, `v_task62_frame_out.txt`,
`v_task62_spinor_py_out.txt`.  GAP 4.16dev + CTblLib.  **NOTES.md not
edited** (per brief).

---

## 0. Headline

1. **The load-bearing computation named in §4bj is done**, and four of the
   five rational degree-7 columns contribute **nothing**.  Three of the four
   zeroes have short *uniform* proofs (§2), not just a finite check.
2. **(T-BC-RES) holds.**  `Δ(q) ≠ 0` for **every** odd `q ≥ 5` — all 4680
   residue classes mod `M = 9360`, plus every defining-characteristic point.
   `min |Δ| = 1`.  So, modulo **(PAR)** and Lemma **GLUE**,
   **`D(B₃(q)) ≇ D(C₃(q))` for all odd `q`.**
3. But the margin is one class in ~1000 residue classes, so the result is
   **fragile**: shifting the orthogonal side by ±1 in the wrong class would
   produce `Δ = 0` in 832 resp. 260 residue classes (§6).  Three specific
   inputs are still owed (§7).
4. **Corrections to recorded data** (§5): `p^C₄(q) ≥ 3` is FALSE
   (`p^C₄(9) = 1`, `p^C₄(11) = p^C₄(13) = 2`); the degree-6 `SL₂(7)` column
   has character field `ℚ(√2)`, not `ℚ(√−2)` (so its presence congruence is
   `q ≡ ±1 mod 8`, not `q ≡ 1,3 mod 8`); and Rule-S gives the degree-7
   `L₂(13)` column **2** classes where the `q = 3` anchor records **1**
   (most likely `mult₁(Ω₇(3)) = 17`; `Δ` does not depend on it — §5.3).
5. **v_task61's two loose ends are closed**: the errored `DoPerfect2` block
   is replaced by a module-theoretic computation that re-derives the doubled
   `Sp₆(2)` tree at every `q ≤ 43`; and `p^C₄` is now known at `q = 9, 11,
   13, 19, …` (the `IsomorphicSubgroups` route that stalled at `q = 11` is
   bypassed entirely).

---

## 1. The machinery, and what it is validated against

### 1.1 Why the answer is "1 or 2 or 0", never "does `U` land in `Ω₇`"

The brief asks whether each `U` "lands in `Ω₇(q)` or only in
`SO₇(q) ∖ Ω₇(q)`".  That question has a one-line answer: since
`det × θ : O₇(q) → C₂ × C₂` is a homomorphism onto an abelian group and every
`U` here is **perfect**, `U ≤ Ω₇(q)` **always**.  The real content is the
*normalizer*, and it is controlled by:

> **Lemma SPIN.**  Let `U ≤ Ω₇(q)` be perfect and absolutely irreducible on
> `V = 𝔽_q⁷`.  Then `C_{SO₇}(U) = 1` (the only orthogonal scalar of
> determinant `1` is `1`, because `det(−1) = (−1)⁷ = −1`), so
> `N_{SO₇}(U)/U ↪ Stab_{Out(U)}(χ)` and equality holds whenever the
> stabilising automorphism is realised — which it always is, because the
> intertwiner `T ∈ GL₇` satisfies `T B Tᵗ = λB` with `λ⁷ = det(T)²` a square,
> hence `λ` a square, hence `T` rescalable to an isometry.  Consequently,
> writing `S = Stab_{Out(U)}(χ)` and `θ` for the spinor norm:
>
> | | `#Ω₇(q)`-classes of psn subgroups `≅ U` with this module |
> |---|---|
> | `S = 1` | **2** (the `SO`-class splits; `N_Ω(U) = U`) |
> | `S = C₂`, `θ(outer) ∉ (𝔽_q^×)²` | **1** |
> | `S = C₂`, `θ(outer) ∈ (𝔽_q^×)²` | **0** (`N_Ω(U) = U.2 ≠ U`) |
> | `\|S\| > 2` | **0** (`θ` has image `C₂`, so it cannot be injective on `S`) |
>
> Here "outer" means the isometry `T` inducing the outer automorphism,
> renormalised to `det T = +1` (replace `T` by `−T` if necessary; note
> `θ(−1_V) = disc(V)`).

This is exactly Rule-S (§4ai) with the `GSp`-multiplier replaced by the
spinor norm, which is the correct `Ω` analogue in odd dimension.

### 1.2 The spinor-norm routine

`LoadPackage("forms")` is **not available** in this GAP install, so the
spinor norm is implemented from scratch by the **Wall form**:

```
theta(g) = (-2)^k * det( chi_g ),     k = rank(g-1),
chi_g(x,y) = B(x',y)  where  x = (g-1)x'  ranges over the residual space.
```

Validated (`v_task62_spinor_out.txt`, section 1) for `q ∈ {3,5,7,9,11,13,17,
19,23,25,27}`, all `true`:

* (a) `θ(r_v) = B(v,v)` mod squares, 40 random reflections per `q`;
* (b) multiplicativity on random products of two reflections, 40 per `q`;
* (c) multiplicativity on random 6-fold reflection words, 30 per `q`;
* (d) **anchor** — every generator of GAP's `Omega(0,7,q)` has *square*
  spinor norm w.r.t. that group's own invariant bilinear form;
* (e) an element built as a product of two reflections of different square
  class has `det = 1` and *non-square* `θ` (i.e. it is in `SO ∖ Ω`);
* (f) `θ` is **surjective** on `SO(0,7,q)`, i.e. it detects the index-2
  subgroup `Ω₇(q)` and nothing coarser.

### 1.3 Anchor validation of the *whole pipeline*

Two independent anchors, both passed:

* **The doubled `Sp₆(2)` tree (§4ai addendum).**  Running the pipeline on
  `PerfectGroup(1344,1)`, `(1344,2)`, `(10752,8)` gives, for **every** `q`
  in `{3,5,7,9,11,13,17,19,23,25,27,29,31,37,41,43}`: two 7-dimensional
  faithful orthogonal modules forming a single `Out`-orbit, `Stab_Out = 1`,
  hence **2 `Ω₇(q)`-classes each**.  That is §4ai's addendum re-derived by a
  completely different route (modules and intertwiners rather than character
  tables), and it **repairs the errored `DoPerfect2` block of v_task61**,
  which had crashed on `CharacterTableAutomorphismImage`.
* **`p^C₄(5) = 3` and `p^C₄(7) = 4`.**  The same method applied to the
  symplectic side (multiplier instead of spinor norm) reproduces v_task61's
  *exhaustive* `IsomorphicSubgroups` counts exactly (`v_task62_sp_out.txt`).

---

## 2. THE SPINOR TABLE — the five rational degree-7 columns

`U₃(3)`'s degree-7 orthogonal character is the unique rational one with
indicator `+1`; `A₈`'s and `L₃(2)`'s likewise; `L₂(8)` has **four** degree-7
characters with indicator `+1`, one rational and three forming a Galois orbit
with field `ℚ(ζ₉)⁺`; `2⁶:A₇` has one.  (`v_task62` re-read the character
tables; this corrects nothing in §4ai's degree-7 list.)

| column | `Stab_Out(χ)` | `det`-normalised outer isometry `T` | `θ(T)` | `Ω₇(q)`-classes | valid for |
|---|---|---|---|---|---|
| `A₈` | `C₂` | `−τ`, `τ` = transposition of the `S₈`-frame | `disc·2 = 8·2 = 16 ≡ □` | **0** | **every odd `q`** [PROVEN] |
| `L₃(2)` | `C₂` | `−σ`, `σ` = 8-cycle in `PGL₂(7)` on `P¹(𝔽₇)` | `disc·2⁷ = 2·2⁷ = 2⁸ ≡ □` | **0** | **every odd `q`** [PROVEN] |
| `U₃(3)` | `C₂` | the outer element of `G₂(2) = U₃(3).2` | `≡ □` (it lies in `G₂(q) ≤ Ω₇(q)`) | **0** | **every odd `q`** [PROVEN] |
| `L₂(8)`, `χ` rational | `C₃` | order-3, so `θ(T)³ = 1 ⇒ θ(T) = 1` | `≡ □` | **0** | **every odd `q`** [PROVEN] |
| `L₂(8)`, `χ ∈ ℚ(ζ₉)⁺` (3 of them) | `1` | — | — | **2** | iff `q ≡ ±1 (mod 9)`, `p ≠ 3` |
| `2⁶:A₇` | `C₂` | `diag(−1,1,…,1)·(1 2)` in the monomial group | `1·2 = 2` | **1** iff `2 ∉ (𝔽_q^×)²`, else **0** | i.e. iff `q ≡ ±3 (mod 8)` [PROVEN + 29/29 machine] |

**Machine confirmation** (`v_task62_spinor_cols_out.txt`,
`v_task62_spinor_out.txt`, `v_task62_frame_out.txt`): every entry above was
also computed with the validated pipeline, for
`q ∈ {3,5,7,9,11,13,17,19,23,25,27,29,31,37,41,43}` for `A₈`, `L₃(2)`,
`U₃(3)`, `L₂(8)`.  For `2⁶:A₇` the general pipeline is too slow (order
161280), so `v_task62_frame.g` builds the monomial model directly and checks
it for **all 29 odd prime powers `q ≤ 99`**: `|G| = 161280`, module
absolutely irreducible, `t` normalises `G`, `t ∉ G`, `det t = 1`, and
`θ(t) ∉ □ ⟺ q ≡ ±3 (mod 8)` — **29/29 agree with the prediction, 0
failures** (`v_task62_frame2_out.txt`).  The general pipeline independently
gives 1 class at `q = 3, 5` (`v_task62_frame_out.txt`).

### 2.1 The three uniform proofs

*`A₈`.*  The degree-7 rational character is the deleted permutation character
of the natural 8-point action, so `V = {x ∈ 𝔽_q⁸ : Σxᵢ = 0}` with
`B = Σxᵢyᵢ`; `disc V = det Gram(A₇) = 8 ≡ 2`.  The outer automorphism is
conjugation by a transposition `τ`, which acts on `V` as the reflection in
`e₁ − e₂` (norm 2), so `det τ = −1` and `θ(τ) = 2`.  The `SO`-representative
is `−τ`, and `θ(−τ) = θ(−1_V)·θ(τ) = disc(V)·2 = 2·2 = 4 ≡ 1`.  **Square for
every odd `q`**, so `N_{Ω₇(q)}(A₈) = S₈ ⊋ A₈`: `A₈` is never psn. ∎

*`L₃(2) ≅ L₂(7)`.*  Same shape, via the 2-transitive action on
`P¹(𝔽₇)` (8 points): the degree-7 character is `π − 1`.  The outer
automorphism is realised by an element of `PGL₂(7) ∖ PSL₂(7)`, whose action
on the 8 points is an **odd** permutation (e.g. an 8-cycle `σ`, or the
involution `x ↦ −x` with cycle type `1²2³`).  Taking `σ` = 8-cycle = product
of 7 transpositions, `θ(σ) = 2⁷ ≡ 2` and `det σ = −1`, so
`θ(−σ) = disc·2⁷ = 2·2⁷ = 2⁸ ≡ 1`.  **Square for every odd `q`.** ∎

*`U₃(3)`.*  `U₃(3) = G₂(2)′` and its 7-dimensional orthogonal module is the
restriction of the `G₂` module; `U₃(3)` determines the octonion
multiplication on `V`, so its normaliser in `SO₇(q)` preserves that
multiplication, i.e. `N_{SO₇(q)}(U₃(3)) ≤ G₂(q)`.  But `G₂(q)` is perfect,
so `G₂(q) ≤ Ω₇(q)`, whence the whole normaliser lies in `Ω₇(q)` and
`N_{Ω₇}(U₃(3)) = N_{SO₇}(U₃(3)) = G₂(2) ⊋ U₃(3)`. ∎
*(This also explains §4ai's remark that `U₃(3)` "should" be a rational column
and yet is absent from the `q = 3` anchor.)*

*`L₂(8)`, rational `χ`.*  `Out(L₂(8)) = C₃` fixes the rational degree-7
character, so `N_{SO₇}(L₂(8)) = L₂(8).3`.  Any `T` in the outer coset has
`θ(T)³ = θ(T³) = 1` and `θ(T) ∈ {±1}`, so `θ(T) = 1`: the whole `.3` sits in
`Ω₇(q)`.  Never psn. ∎  The other three degree-7 characters are permuted
freely by that `C₃`, so `Stab_Out = 1` and they give **2** classes — but only
when `ζ₉ + ζ₉⁻¹ ∈ 𝔽_q`, i.e. `q ≡ ±1 (mod 9)`. ∎

*`2⁶:A₇` (the frame column, E6).*  Realise it as the monomial group
`D:A₇ ≤ SO₇(q)` with `V = 𝔽_q⁷`, `B = I`, `D = {diag(ε) : ε ∈ {±1}⁷,
∏εᵢ = 1} ≅ 2⁶`, `A₇` permuting coordinates.  `D` determines the frame
`{±e_i}`, so `N_{O₇}(D:A₇)` is the full monomial group `2⁷:S₇`, and
`N_{SO₇}(D:A₇)/(D:A₇) = C₂`, generated by
`t = diag(−1,1,…,1)·(1\,2)` (`det t = (−1)(−1) = +1`).  Now
`θ(t) = θ(r_{e₁})·θ(r_{e₁−e₂}) = 1·2 = 2`.  So

> `2⁶:A₇` is psn in `Ω₇(q)` **iff `2` is a non-square in `𝔽_q`, i.e. iff
> `q ≡ ±3 (mod 8)`**, and then it contributes exactly **1** class.

This is **E6 re-proved from the spinor norm** (E6 was previously a
[LIT-CHECK] transcription), and it agrees with the anchor (`3 ≡ 3 mod 8`, one
class at `q = 3`) and with the machine at `q = 3, 5`. ∎

### 2.2 Net effect on `p^O₇(q)`

```
p^O7(q) = 1  (Omega_7(q) itself)
        + 2  (G_2(q), E1)
        + 2  (Sp_6(2))       + 2 (2^3:L3(2)) + 2 (2^3.L3(2)) + 2 (2^6:L3(2))
        + 0  (A_8) + 0 (L_3(2)) + 0 (U_3(3)) + 0 (L_2(8) rational)
        + 2*[q = ±1 mod 9]   (L_2(8), Q(zeta_9)^+ triple)
        + 2*[13 is a square] (L_2(13))
        + 1*[q = ±3 mod 8]   (2^6:A_7)
        =  11 .. 16
```
(plus, at `q = 3` only, the three `p = 3` parabolic artifacts).  The
verified `L₂(13)` column: 2 classes at `q ∈ {3,9,17,23,25,27,29,43}`, absent
at `q ∈ {5,7,11,19,31,37,41}` — exactly `[13 ∈ (𝔽_q^×)²]`.

---

## 3. The symplectic columns, recomputed by the same method

Because the method is cheap (modules + intertwiners, no subgroup search) it
also settles the symplectic side across a wide residue range, which
`IsomorphicSubgroups` could not.  Scans over all odd prime powers
`q ≤ 199` (degree 4) and `q ≤ 199 / 61` (degree 6):
`v_task62_sp_scan_out.txt`, `v_task62_sp_scan6_out.txt`.

| column | rule (verified over the scan range) |
|---|---|
| `p^C₂ = a(q)` | `1 + 2·[q ≡ ±1 mod 5]` (rank-1 law, §4af/§4ai) |
| deg 4, `2.A₅` | psn `⟺ 3` is a **non**-square `⟺ q ≡ ±5 (mod 12)`; absent for `p = 3` |
| deg 4, `2.A₆` | **identical rule** `q ≡ ±5 (mod 12)`; absent for `p = 3` |
| deg 4, `Sym³ SL₂(q)` | multiplier `= ν³` with `ν` a non-square, hence **always** psn: 1 class for every `q` with `p ≥ 5`, `q ≠ 5` (at `q = 5` it *is* the `2.A₅` column) [PROVEN] |
| deg 4, `C₆` (order 1920) | `0` — no embedding at all (v_task61, exhaustive) |
| deg 6, `2.A₅` | psn `⟺ 2` is a non-square `⟺ q ≡ ±3 (mod 8)`; absent for `p = 5` |
| deg 6, `SL₂(7)` | field `ℚ(√2)`, present `⟺ q ≡ ±1 (mod 8)`; **2** classes iff `q ≡ ±7 (mod 16)`, `0` if `q ≡ ±1 (mod 16)` |
| deg 6, `U₃(3)` | psn `⟺ q ≡ ±5 (mod 12)`; absent for `p = 3` |
| deg 6, `2.L₂(13)` | `Out`-unstable ⇒ **2** iff `13 ∈ (𝔽_q^×)²` (§4ai) |
| deg 6, `2.J₂` | `Out`-unstable ⇒ **2** iff `q ≡ ±1 (mod 5)` (§4ai) |
| deg 6, `2.(A₅×A₅)` | `0` (the `C₄` member, killed in §4ai) |

So `p^C₄(q) = 1 + 2·[q ≡ ±5 mod 12] + [p ≥ 5, q ≠ 5]`, and
`p^C₆(q) = 1 + [q ≡ ±3 mod 8] + 2·[q ≡ ±7 mod 16] + [q ≡ ±5 mod 12]
+ 2·[13 ∈ □] + 2·[5 ∈ □]`, and
`mult₁(PSp₆(q)) = p^C₆ + a·p^C₄ + C(a,3)` by PSN-GF (§4af).

---

## 4. `Δ(q)` per residue class — the evaluation

All the rules above are congruence conditions on `q`, so `Δ` is periodic with
modulus `M = lcm(16, 9, 5, 12, 13) = 9360`.  `v_task62_spinor.py` enumerates
all 4680 odd residue classes (`v_task62_spinor_py_out.txt`).

> **Result.  `Δ(q) ≠ 0` in every one of the 4680 residue classes**, and at
> every defining-characteristic prime power as well.  `Δ` takes the values
> `{−8, −6, −4, −1, +1, +3, +4, +5, +6, +7, +8, +10}` — in particular `Δ = 0`
> and `Δ = ±2` never occur.  `min |Δ| = 1`.

The 45 distinct profiles `(a, p^C₄, p^C₆, p^O₇)` are tabulated in the output.
Representative rows:

| `q` | `a` | `p^C₄` | `p^C₆` | symplectic | `p^O₇` | `Δ` |
|---|---|---|---|---|---|---|
| 3 | 1 | 1 | 4 | 5 (+3 artifacts) | 14 (+3 artifacts) | `+9` |
| 5 | 1 | 3 | 2 | 5 | 12 | `+7` |
| 7 | 1 | 4 | 2 | 6 | 11 | `+5` |
| 9 | 3 | 1 | 7 | 11 | 13 | `+2` |
| 11 | 3 | 2 | 4 | 11 | 12 | `+1` |
| 19 | 3 | 4 | 5 | 18 | 14 | `−4` |
| 29 | 3 | 4 | 7 | 20 | 14 | `−6` |
| 41 | 3 | 4 | 6 | 19 | 11 | `−8` |
| 121 | 3 | 2 | 7 | 14 | 13 | `−1` |
| 169 | 3 | 2 | 5 | 12 | 11 | `−1` |

Note that `Δ` **changes sign** — confirming v_task61's diagnosis that the
*directed* statement T-BC⁺ (`mult₁(Ω₇) > mult₁(PSp₆)`) is false for
`q ≡ ±1 mod 5`, while the *symmetric* statement `Δ ≠ 0` survives.  The
orthogonal side wins for `a = 1`, the symplectic side wins for `a = 3` with
large `p^C₄`; the two never tie.

---

## 5. Falsifications of recorded data

1. **`p^C₄(q) ≥ 3` is FALSE.**  v_task61 §5 asserted it ("computed at
   `q = 5, 7`; the columns `Sp₄(q)`, `2.A₅`, `2.A₆` are rational hence present
   at every odd `q`").  Rationality of the character is presence, but *not*
   psn-ness: `2.A₅` and `2.A₆` are psn only for `q ≡ ±5 mod 12`.  Exact
   values: `p^C₄(9) = 1`, `p^C₄(11) = p^C₄(13) = 2`, `p^C₄(5) = 3`,
   `p^C₄(7) = 4`.  (This *raises* `Δ` for `a = 3` and is the main reason the
   `a = 3` classes do not collapse to `0`.)
2. **`SL₂(7)`'s degree-6 character field is `ℚ(√2)`, not `ℚ(√−2)`.**
   `CharacterTable("2.L3(2)")` gives `NF(8,[1,7])` for the two faithful
   degree-6 (indicator `−1`) characters, i.e. the real subfield `ℚ(√2)`.  So
   the presence congruence is `q ≡ ±1 mod 8`, and §4ai's / §4ac's
   `q ≡ 1,3 mod 8` is wrong.  Machine-confirmed: present exactly at
   `q ∈ {7,9,17,23,25,31,41,47,49,71,73,79,81,89,97,103,113,121,127,137,151,
   167,169,191,193,199}`.
3. **`L₂(13)` degree-7 column: Rule-S says 2, the anchor says 1.**  The two
   degree-7 characters of `L₂(13)` (field `ℚ(√13)`, indicator `+1`) are
   swapped by `Out(L₂(13)) = C₂`, so `Stab_Out = 1` and the `SO₇`-class
   splits into **two** `Ω₇(q)`-classes, both psn.  §4ae/§4af's anchor
   decomposition of `mult₁(Ω₇(3)) = 16` allots it only **1** ("the two
   `G₂`-copies fusing/filtering to one").  The Rule-S value is not an
   assumption: at `q = 3` the pipeline finds two 7-dimensional faithful
   orthogonal `GF(3)`-modules forming a single `Out`-orbit, so
   `Stab_Out = 1`, `N_{SO₇(3)}(L₂(13)) = L₂(13) ≤ Ω₇(3)`, and the single
   `SO₇(3)`-class must split into **two** `Ω₇(3)`-classes.  The most likely
   explanation is that the v_task9/10 census counted subgroups up to
   `Aut(Ω₇(3))` (the diagonal automorphism fuses exactly this pair, which is
   also how the ATLAS prints it), i.e. `mult₁(Ω₇(3)) = 17` in Müller's
   convention.  **This must be re-audited** — see §7.  *Note that the `Δ`
   computation of §4 never uses census numbers: every column is a Rule-S
   value, so an anchor-convention error does not propagate into `Δ`; it only
   affects the anchor cross-check.*  (BC1 is unaffected either way: `17 ≠ 7`.)

---

## 6. How fragile is the conclusion?

`min |Δ| = 1`, so the answer is decided by a single class in the tightest
residues.  The sensitivity analysis in `v_task62_spinor_py_out.txt`:

| perturbation of `p^O₇` | residue classes that would get `Δ = 0` |
|---|---|
| `−2` | 0 |
| `−1` | **832** |
| `+1` | **260** |
| `+2` | 0 |

So the theorem is *not* robust to a one-class error in any column.  The three
columns whose values are least secure are named in §7.  On the other hand
`Δ = ±2` never occurring means an error of exactly `±2` (e.g. a whole
`Out`-unstable column being present/absent) would *not* create a tie.

---

## 7. Theorem BC3, and what is still owed

> **Theorem BC3 [PROVEN modulo (PAR), Lemma GLUE, and the three inputs
> below].**  For every odd `q`, `mult₁(Ω₇(q)) ≠ mult₁(PSp₆(q))`, hence
> `D(B₃(q)) ≇ D(C₃(q))`.

Status of each hypothesis:

1. **(PAR)** — still a hypothesis.  §4ah reduced it to `H¹(Ū, Q) = 0` plus
   the open case `1 < R < Q`.  *Unchanged by this task.*
2. **Lemma GLUE** — [ARGUED, anchor-confirmed] in v_task61, still not
   case-exhaustive.  It is what licenses "orthogonal `⊥`-layers = 0" in
   (T-BC-RES).  This task supplies a piece of the missing bookkeeping: the
   spinor-norm routine of §1.2 is exactly the tool GLUE's item (ii) needs,
   and it is now validated.  *Making GLUE exhaustive is a finite job with
   this routine in hand.*
3. **Three column values not yet nailed down:**
   * **`L₂(13)` degree-7**, `2` vs `1` (§5.3).  If the true value is `1`,
     `p^O₇` drops by `1` in the `13 ∈ □` classes and `Δ = 0` becomes possible
     there.  *Decide by re-auditing the `q = 3` census convention.*
   * ~~`2⁶:A₇`~~ — **CLOSED**: hand proof (§2.1) plus 29/29 machine
     confirmations for all odd prime powers `q ≤ 99`, both halves of the
     `mod 8` rule (`v_task62_frame.g`).
   * **`2.J₂`** and **`2.L₂(13)`** on the symplectic side are taken from
     §4ai's character-table reading, not recomputed here; both are `Out`-
     unstable and contribute `2`, and both are `±2`-sized, so by §6 an error
     there cannot create a tie — but their *presence* congruences were not
     re-verified.
4. **`Sp₆(2)` itself** contributes `2` by §4ai (Rule-S branch 1,
   `Out(Sp₆(2)) = 1`); not re-run here (it is the one member of the tree
   whose group is large).
5. **`n > 3` remains OPEN** and is not advanced.  Nothing in this task is
   `n`-uniform except the method; `G₂ ⊂ Ω₇` is still `n = 3`-special.

### Precise residue of the simple-groups theorem

> `D(B_n(q)) ≇ D(C_n(q))` is now **proven for `n = 3`, all odd `q`**, modulo
> (PAR) + GLUE + item 3 above; and **open for `n ≥ 4`**.  Everything else in
> CFSG is settled (§4bh addendum, §4bi).
