# v_task63 — ADVERSARIAL AUDIT of Theorem BC3 (v_task62): **BROKEN**

Date 2026-08-08.  Scripts `v_task63_delta.py`, `v_task63_subfield.g`,
`v_task63_sym.g`, `v_task63_sym6.g`; outputs `v_task63_delta_out.txt`,
`v_task63_subfield_out.txt`, `v_task63_sym_out.txt`, `v_task63_sym6_out.txt`.
GAP 4.16.0.  **NOTES.md not edited** (per brief).

---

## 0. Headline

The spinor table of v_task62 §2 is **correct** — I re-derived all five rows
independently and found no wrong entry.  The break is not in the table, it is
in the **column inventory**: `p^C₆(q)` is missing an entire Aschbacher-`S`
column that `p^C₄(q)` carries, namely the defining-characteristic member

> **`Sym⁵ SL₂(q) < Sp₆(q)`, `p ≥ 7`** — 6-dimensional, absolutely irreducible,
> symplectic, `Stab_Out = C₂` with **multiplier `ν⁵ = ν` a non-square**, hence
> by Rule-S branch 2 exactly **1 class, psn**, for every `q` with `p ≥ 7`.

Its degree-4 sibling `Sym³ SL₂(q) < Sp₄(q)` **is** in v_task62's `p^C₄` (as
"`Sym^3`, multiplier `ν³`, always psn"), and its degree-7 orthogonal
counterpart `Sym⁶ SL₂(q) < Ω₇(q)` **is** absent from `p^O₇` but genuinely
contributes `0` (machine-verified below), so there is **no compensation on
the orthogonal side**.

Net effect: `p^C₆(q) → p^C₆(q) + 1` for every `q` with `p ≥ 7`, i.e.

> **`Δ(q) → Δ(q) − 1` for all `q` with `p ≥ 7`.**

Since v_task62's own `min |Δ| = 1` and `Δ = +1` is attained, this produces
ties immediately.  The smallest is

> ### `q = 11`:  `mult₁(Ω₇(11)) = mult₁(PSp₆(11)) = 12`,  `Δ(11) = 0`.

**1638 prime powers `q < 10³⁰` tie** on this correction alone
(`v_task63_delta_out.txt`, STAGE 2, first model).  A *second*, independent
omission — the subfield (Aschbacher `C₅`) columns, absent from **both** sides
— compounds this and additionally destroys the *method*: `Δ` is **not** a
function of `q mod 9360`, so the 4680-class scan of v_task62 §4 is not an
exhaustive verification even in principle.

**Verdict: Theorem BC3 is BROKEN.**  Not "the theorem is false" — `Δ = 0`
only means `mult₁` fails to separate — but the claimed proof does not stand,
and `mult₁` demonstrably does **not** separate `B₃(11)` from `C₃(11)`.

---

## 1. Verdicts per audit item

| # | item | verdict |
|---|---|---|
| 1 | 0/1/2 normalizer framing, `C_{SO₇}(U) = 1`, class-fusion count | **CONFIRMED** |
| 2 | the five spinor-table rows | **CONFIRMED** (all five, independently) |
| 3 | `p^O₇` = 11 base classes + congruence columns | **ERRATUM** — missing `C₅` tower (`G₂(q₀)`, `Ω₇(q₀)`); the missing `Sym⁶` column is correctly `0` |
| 4 | symplectic side, `a(q)`, PSN-GF assembly | **BROKEN** — `Sym⁵` column missing from `p^C₆`; `C₅` columns missing from `p^C₆`, `p^C₄`, `a`; `a(3) = 1` should be `0` |
| 5 | the `Δ` enumeration | **BROKEN** — ties at `q = 11, 49, 59, 61, 71, 121, 131, …`; and `Δ` is not periodic mod 9360 |
| 6 | scope of (PAR)/GLUE | **CLARIFIED** — see §6; neither hypothesis rescues the count |

---

## 2. Item 1 — the normalizer framing: CONFIRMED

Re-derived, not re-read.

* `C_{SO₇}(U) = 1`.  Absolute irreducibility gives `C_{GL₇}(U) = 𝔽_q^×·1`;
  intersecting with `O₇` leaves `{±1}`; `det(−1_V) = (−1)⁷ = −1`, so
  `C_{SO₇}(U) = 1`. ✓  Absolute irreducibility per column is genuinely
  available: for `A₈` and `L₃(2)` the module is the deleted permutation
  module on 8 points, irreducible over any field of characteristic
  `p ∤ 8` — i.e. **every odd `p`, no exceptions**; for the `Sp₆(2)`-tree
  §4ai's addendum checked `p = 3, 5, 7` by Brauer table / MeatAxe.
* `N_{SO₇}(U)/U = Stab_{Out(U)}(χ)` **with equality**.  The intertwiner
  `T` satisfies `T B Tᵗ = λB`; taking determinants, `λ⁷ = det(T)²` is a
  square, and `7` is odd, so `λ` is a square and `T` rescales to an
  isometry. ✓ (This is exactly where oddness of the dimension is used; the
  argument would fail in even dimension.)
* Class-fusion count.  With `G = SO₇(q) = Ω₇(q).2` and `U ≤ Ω₇`, the
  `G`-class splits into two `Ω`-classes **iff** `N_G(U) ≤ Ω`, i.e. iff no
  element of `N_G(U)` has non-square spinor norm.  The four cases of Lemma
  SPIN follow, and each is right:
  `Stab = 1` → `N_G(U) = U ≤ Ω` → 2 classes, both psn;
  `Stab = C₂`, `θ(outer)` non-square → 1 class, psn;
  `Stab = C₂`, `θ(outer)` square → 2 classes, neither psn (`N_Ω(U) = U.2`);
  `|Stab| > 2` → some non-trivial element has square `θ` → 0.  ✓
* **The `θ`-convention worry is void.**  `θ(r_v) = B(v,v)` and
  `θ(r_v) = Q(v) = B(v,v)/2` differ by the homomorphism
  `g ↦ 2^{(1−det g)/2}`, which is **trivial on `SO₇`**.  Since every
  evaluation in the table is on a `det`-normalised element of `SO₇`, both
  conventions give the same answer.  I checked `A₈` both ways: `4 ≡ □`
  resp. `1 ≡ □`.  ✓

---

## 3. Item 2 — the five spinor rows: CONFIRMED, all five

| row | independent re-derivation | verdict |
|---|---|---|
| `A₈` | `V = {Σxᵢ = 0} ⊂ 𝔽_q⁸`, `disc V = det Gram(A₇) = 8 ≡ 2`; outer = transposition `τ` = reflection in `e₁−e₂` (norm 2), `det τ = −1`; `θ(−τ) = θ(−1_V)θ(τ) = disc·2 = 4 ≡ □` **for every odd `q`** | **0** ✓ |
| `L₃(2)` | 2-transitive on `P¹(𝔽₇)` (8 points), `χ = π − 1`; outer realised by an order-8 element of `PGL₂(7)` (no element of order 8 in `PSL₂(7)`), an **odd** permutation = product of 7 transpositions; `θ(σ) = 2⁷`, `det σ = −1`, `θ(−σ) = 8·2⁷ = 2¹⁰ ≡ □` | **0** ✓ |
| `U₃(3)` | `U₃(3) = G₂(2)′` determines the octonion product on `V`, so `N_{SO₇}(U₃(3)) ≤ G₂(q) ≤ Ω₇(q)` (`G₂(q)` perfect); normalizer `= G₂(2) ⊋ U₃(3)` | **0** ✓ [ARGUED, as in v_task62] |
| `L₂(8)` rational `χ` | `Out = C₃`; `θ(T)³ = θ(T³) = 1` in `𝔽_q^×/□ ≅ C₂`, and cubing is the identity on `C₂`, so `θ(T) = 1` | **0** ✓ |
| `L₂(8)`, `ℚ(ζ₉)⁺` | degrees of `L₂(8)`: `1, 8, 9×3, 7×4` (`Σd² = 504` ✓); the four `7`s are the discrete series indexed by `Ĉ₉/±`: one rational (order-3 characters, `ζ₃+ζ₃⁻¹ = −1`) and three with field `ℚ(ζ₉)⁺`, permuted freely by `Out = C₃` → `Stab = 1`, **one subgroup class** in `SO₇`, splitting into 2 | **2** iff `q ≡ ±1 (9)` ✓ |
| `2⁶:A₇` | monomial model, `B = I`; `t = diag(−1,1,…,1)·(1 2)`, `det t = +1`, `θ(t) = θ(r_{e₁})·θ(r_{e₁−e₂}) = 1·2 = 2` | **1** iff `2 ∉ □` iff `q ≡ ±3 (8)` ✓ |

Sign conventions checked: `2 ∈ (𝔽_p^×)² ⟺ p ≡ ±1 (mod 8)`, so non-square
`⟺ q ≡ ±3 (mod 8)` — v_task62 has this right.  The `L₂(8)`-`ζ₉` and
`L₂(13)` rows correctly give **2** (one subgroup class splitting), **not**
`2 ×` (number of Galois-conjugate characters) — a trap v_task62 avoided.

**No erratum found in the spinor table.**

---

## 4. Item 3+4 — the column inventory: TWO OMISSIONS

### 4.1 THE BREAK: `Sym⁵ SL₂(q) < Sp₆(q)` is missing from `p^C₆`

`v_task63_sym.g` / `v_task63_sym_out.txt`, computed directly over `𝔽_q` for
`q ∈ {7,9,11,13,17,19,23,25,27,29,31,37,41,43,49,121}`:

| `k` | `dim` | form | `absirr` | outer `diag(ν,1)` rescales form by | Rule-S verdict |
|---|---|---|---|---|---|
| 3 | 4 | **alternating** | ✓ | `ν³` = non-square | 1 class, **psn** — *in v_task62* |
| **5** | **6** | **alternating** | ✓ | **`ν⁵` = non-square** | **1 class, psn — MISSING** |
| 6 | 7 | symmetric | ✓ | `ν⁶` = square (renormalisable) | see 4.2 |

The verdict for `k` odd needs no spinor norm and no convention: the invariant
form is alternating, `Stab_{Out}(χ) = C₂` (the diagonal automorphism; field
automorphisms twist `L(k)` to a non-isomorphic module), and the intertwiner
has similitude multiplier `ν^k = ν` — a non-square for odd `k`.  So it lies
in `GSp₆(q) ∖ Sp₆(q)` and cannot be rescaled in (`ν^k·λ² = 1` is unsolvable).
Hence `N_{Sp₆(q)}(Sym⁵SL₂(q)) = Sym⁵SL₂(q)`: **psn, 1 class, for every `q`
with `p ≥ 7`** (`5 < p` is what makes `L(5)` restricted-irreducible of
dimension 6).  Faithful, since `−1 ↦ (−1)⁵ = −1`.

This is a standard BHR class-`S` maximal of `Sp₆(q)`; it is simply absent
from §4ai's degree-6 `S`-table because that table was harvested from
**CTblLib's perfect groups of order ≤ 10¹⁰** — a source that by construction
contains only *cross*-characteristic members.  The degree-4 table escaped
because v_task61/62 added `Sym³` by hand.  **The two tables were built by
inconsistent methods, and that is the error.**

### 4.2 The orthogonal counterpart contributes 0 — no compensation

`Sym⁶ SL₂(q) < Ω₇(q)` (`p ≥ 7`, 7-dimensional, symmetric form, the module
factors through `PGL₂`).  `v_task63_sym6.g` implements the Wall-form spinor
norm and **anchors it twice**:

* `Sym²`: `SO₃(q) = PGL₂(q) > Ω₃(q) = PSL₂(q)` — `θ(outer)` **must** be a
  non-square.  ✓ at every `q` tested.
* `Sym⁴`: `Ω₅(q) = PSp₄(q)`, same conclusion.  ✓ at every `q` tested.

(The routine in `v_task63_sym.g` failed the `Sym²` anchor at `q = 13, 17` —
a genuine bug in the residual-space preimage; `v_task63_sym6.g` fixes it and
passes both anchors uniformly.  **The lesson generalises: an anchored spinor
routine is mandatory, and v_task62's anchors (a)–(f) are the right ones.**)

With the anchored routine, for `Sym^{2m}` the `det`-normalised outer element
has eigenvalues `ν^{−m},…,ν^m`, i.e. `m` hyperbolic pairs with ratios
`ν,…,ν^m`, so

> `θ = ν^{1+2+⋯+m} = ν^{m(m+1)/2}`:  `m=1 → ν` (non-□), `m=2 → ν³` (non-□),
> **`m=3 → ν⁶` (□)**.

Machine-confirmed at all 17 tested `q`.  So `PGL₂(q) ≤ Ω₇(q)` and
`PSL₂(q)` is **never** psn in `Ω₇(q)`: **`p^O₇` column `= 0`**.  v_task62's
omission of this column is harmless; the *symplectic* omission is not.

### 4.3 The second omission: the subfield (`C₅`) columns, absent on both sides

§4ab's **(E3)** ("subfield columns die") is **unsound as written**.  Its
argument — "the defining character is rational so `ρ∘Frob ≅ ρ` with
intertwiner `g` normalising the subgroup and inducing its field
automorphism" — is vacuous: `Frob_{q₀}` acts trivially on `𝔽_{q₀}`, so the
twist is the identity and `g = 1`.  The automorphism that would have to be
realised is `Frob_p`, and it twists the natural module to a
non-isomorphic one, so it is **not** realised by any linear map.

What actually happens is a square-class condition, machine-verified:

`v_task63_subfield.g` PART B — `N_{SL(2,q)}(SL(2,q₀))` computed outright:

| `SL₂(q₀) < SL₂(q)` | `|N|/|H|` | psn |
|---|---|---|
| `3 < 9` (`r=2`) | 2 | no |
| `3 < 27` (`r=3`) | **1** | **yes** |
| `3 < 81` (`r=4`) | 2 | no |
| `3 < 243` (`r=5`) | **1** | **yes** |
| `5 < 25` (`r=2`) | 2 | no |
| `5 < 125` (`r=3`) | **1** | **yes** |
| `7 < 49`, `9 < 81`, `11 < 121` (`r=2`) | 2 | no |

Exactly the rule "**psn ⟺ the index `r = [𝔽_q : 𝔽_{q₀}]` is odd**", whose
mechanism (PART A, verified for `q₀ ∈ {3,5,7,9,11,13,25,27}`, `r ≤ 6`) is:
*a non-square of `𝔽_{q₀}` stays a non-square in `𝔽_q` iff `r` is odd*
(because `(q−1)/(q₀−1) = 1+q₀+⋯+q₀^{r−1} ≡ r mod 2`).  The same square-class
governs `Sp₄(q₀) < Sp₄(q)` (multiplier), `Sp₆(q₀) < Sp₆(q)` (multiplier) and
`Ω₇(q₀) < Ω₇(q)` (spinor norm of `SO₇(q₀) ∖ Ω₇(q₀)`), giving **1 class each,
psn, iff the index is odd**.

`G₂(q₀) < Ω₇(q)` is different and **always** psn: `G₂` has trivial centre and
no diagonal automorphisms, `C_{SO₇}(G₂(q₀)) = 1`, and field automorphisms are
not linearly realised, so `N_{SO₇(q)}(G₂(q₀)) = G₂(q₀) ⊆ Ω₇(q)` — Lemma
SPIN's first branch: **2 classes for every subfield `q₀`, proper or not**.

So the correct `C₅` bookkeeping (for `q = p^r`, `σ = #{d ∣ r}`,
`σ_odd = #{d ∣ r, d < r, r/d odd}`) is

```
p^O7 += 2(σ − 1)   [G2(q0) tower]  +  σ_odd  [Omega_7(q0)]
p^C6 += σ_odd      [Sp6(q0)]     ;  p^C4 += σ_odd  [Sp4(q0)]
a    += σ_odd      [SL2(q0), q0 > 3]
```
plus the `Sym³`/`Sym⁵` copies over every odd-index subfield.

**Consequence for the method, independent of any tie:** `Δ` depends on the
divisor lattice of `r`, hence is **not** a function of `q mod 9360`.  The
4680-class scan of v_task62 §4 therefore cannot be an exhaustive
verification, whatever the column values are.

### 4.4 Smaller errata

* `a(3) = 1` in `v_task62_spinor.py`, but `SL₂(3)` is **not perfect**, so
  `a(3) = 0`.  (Harmless — `q = 3` is settled by the anchor — but it makes
  the `q = 3` row of §4's table wrong: `symp = 4`, `Δ = +10`, not `+9`.)
* The `L₂(13)` degree-7 "2 vs 1" flagged in v_task62 §5.3: I agree with
  Rule-S (**2**).  Two degree-7 characters over `ℚ(√13)`, swapped by
  `Out = C₂` ⇒ one `SO₇`-class with `N_{SO₇} = L₂(13) ≤ Ω₇` ⇒ splits into 2.
  The `q = 3` anchor discrepancy is a census-convention issue
  (`Aut(Ω₇(3))`- vs `Ω₇(3)`-classes), as v_task62 suspects.  **Not** a source
  of the break, and `Δ` never uses census numbers here.
* `PSN-GF` assembly `p₆ + p₂p₄ + C(p₂,3)` is **right**: the `2+2+2` layer
  needs three *pairwise distinct* classes (else the block-swap enlarges the
  normalizer), so binomial and not multiset coefficient.  ✓
* `a(q) = 1 + 2[q ≡ ±1 (5), q ∉ 5^ℕ]`: the `5` is `2.A₅ = SL₂(5)`, present
  iff `√5 ∈ 𝔽_q`, degree-2 character field `ℚ(√5)`, `Out`-unstable ⇒ 2
  classes (Rule-S branch 1) ✓; the `+1` is `SL₂(q)` itself, perfect for
  `q > 3` ✓ (and at `q = 5` the two coincide, correctly handled by the
  `p ≠ 5` guard).  Correct **except** for the missing subfield term.

---

## 5. Item 5 — the corrected `Δ` enumeration

`v_task63_delta.py` re-enters every column from the mathematics (not from
v_task62's file) and scans.

**Control.**  With `r = 1` and no subfield/`Sym⁵` columns it reproduces
v_task62 exactly: values `{−8,−6,−4,−1,1,3,5,6,7,8,10}`, **0** zero classes,
`min|Δ| = 1`.  So my column re-entry agrees with v_task62 where they overlap;
the disagreement is purely about *which columns exist*.

**Results** (`v_task63_delta_out.txt`):

| model | `min|Δ|` | ties (`q < 10³⁰`) | smallest ties |
|---|---|---|---|
| v_task62 as published | 1 | 0 | — |
| **+ `Sym⁵` only** | **0** | **1638** | **11, 49, 59, 61, 71, 131, 191, 229, 239, 241, …** |
| + `C₅` subfields only | **0** | 64 | 729 = 3⁶, 59049 = 3¹⁰, 13841287201 = 7¹², … |
| + both | **0** | 319 | 11, 59, 61, 71, 121, 131, 169, 191, … |

### The decisive small case, by hand

`q = 11`.  `p^O₇(11) = 11 + 2·[11 ≡ ±1 (9)] + 2·[13 ∈ □] + [11 ≡ ±3 (8)]
= 11 + 0 + 0 + 1 = 12`  (unchanged from v_task62; the `Sym⁶` column is `0`,
`r = 1` so no subfields).

Symplectic: `a(11) = 1 + 2 = 3` (`11 ≡ 1 mod 5`);
`p^C₄(11) = Sp₄(11) + Sym³SL₂(11) = 2` (`11 ≡ 11 mod 12`, so `2.A₅`/`2.A₆`
absent);
`p^C₆(11) = Sp₆(11)·1 + 2.A₅·1 (11 ≡ 3 mod 8) + 2.J₂·2 (11 ≡ 1 mod 5)
+ SL₂(7)·0 (11 ≢ ±7 mod 16) + U₃(3)·0 + 2.L₂(13)·0 + `**`Sym⁵SL₂(11)·1`**` = 5`.

`mult₁(PSp₆(11)) = 5 + 3·2 + C(3,3) = 12 = mult₁(Ω₇(11))`.

> **`Δ(11) = 0`.**  `mult₁` does **not** separate `B₃(11)` from `C₃(11)`.

`q = 49 = 7²` ties as well (`Sym⁵SL₂(49)`, and `p = 7` kills the `SL₂(7)`
column), as does `q = 121 = 11²` and `q = 169 = 13²` once the `C₅` columns
are in.  v_task62's own table lists `Δ(121) = Δ(169) = −1` — the two most
fragile rows it printed — and both flip to `0`.

**The author's own fragility analysis predicted precisely this failure
mode** (§6: a `−1` shift of the orthogonal side ties 832 classes; a `+1`
shift of the symplectic side is the same thing).  The audit did not find a
new kind of risk; it found the risk realised.

---

## 6. Item 6 — what (PAR) and GLUE do and do not control

* **`mult₁` is a `D`-invariant unconditionally** (§4aj, Lean-certified): the
  conductor-1 multiplicity is read off the ring `D(G)` itself.  Neither
  (PAR) nor GLUE is needed for that.  So `Δ(q) ≠ 0 ⟹ D(B₃(q)) ≇ D(C₃(q))`
  is sound as an implication.
* **(PAR)** is what licenses identifying `mult₁(G)` with the count of
  `G`-classes of perfect self-normalizing subgroups.  If (PAR) fails, both
  sides of `Δ` are the wrong objects.
* **Lemma GLUE** licenses "orthogonal `⊥`-layers `= 0`", i.e. the absence of
  a `p^O₄·p^O₃`-type term on the `Ω₇` side matching the symplectic
  `a·p^C₄ + C(a,3)`.
* **Neither hypothesis can rescue `q = 11`.**  (PAR) does not change the
  columns.  GLUE is a *suppression* lemma: if GLUE were **false** the
  orthogonal side would gain layers and `Δ(11)` could become positive again —
  so the honest statement is that `Δ(11) = 0` **under GLUE**, and if GLUE
  fails the whole `(T-BC-RES)` computation must be redone with orthogonal
  `⊥`-layers included.  Either way the published proof does not stand.

Also worth stating: `Δ = 0` is **not** a proof that `D(B₃(11)) ≅ D(C₃(11))`.
It says only that this particular invariant does not separate them.

---

## 7. Corrected table and the standing of Theorem BC3

**Corrected column formulas** (`q = p^r`; `σ = #{d ∣ r}`,
`σ_odd = #{d ∣ r, d < r, r/d odd}`; `D_odd = {d ∣ r : r/d odd}`):

```
p^O7(q) = 1 + 2σ + 8                                  (Omega_7, G2 tower, Sp6(2) tree)
        + σ_odd                                       (Omega_7(q0), odd index)
        + 2·[q ≡ ±1 mod 9]  + 2·[13 ∈ (F_q^x)^2] + [q ≡ ±3 mod 8]
        + 0                                           (A8, L3(2), U3(3), L2(8)_Q, Sym^6 SL2)

a(q)    = [q > 3] + 2·[q ≡ ±1 mod 5, p ≠ 5] + #{d ∈ D_odd, d < r, p^d > 3}

p^C4(q) = 1 + σ_odd + 2·[q ≡ ±5 mod 12, p ≠ 3] + #{d ∈ D_odd : p ≥ 5, p^d ≠ 5}
p^C6(q) = 1 + σ_odd + [q ≡ ±3 mod 8, p≠5] + 2·[q ≡ ±7 mod 16, p≠7]
        + [q ≡ ±5 mod 12, p≠3] + 2·[13 ∈ □, p≠13] + 2·[q ≡ ±1 mod 5, p≠5]
        + #{d ∈ D_odd : p ≥ 7}                        (<-- Sym^5, the missing column)
```

The entries that **moved** relative to v_task62:
`p^C₆ += #{d ∈ D_odd : p ≥ 7}` (**≥ 1** whenever `p ≥ 7`) and
`p^C₄ += (extra Sym³ subfield copies) + σ_odd`, `a += σ_odd`,
`p^O₇ += 2(σ−1) + σ_odd`.

**Does `Δ ≠ 0` survive?  No.  New `min |Δ| = 0`**, attained at
`q = 11, 49, 59, 61, 71, 121, 131, 169, 191, 229, …` (319 prime powers below
`10³⁰` in the full model; 1638 on the `Sym⁵` correction alone).

> ### Overall verdict on Theorem BC3: **BROKEN**
>
> `D(B₃(q)) ≇ D(C₃(q))` is **not** proven for all odd `q`.  The `mult₁`
> separator provably fails at `q = 11` (and at infinitely many `q`).  What
> survives is: `mult₁` separates `B₃(q)` from `C₃(q)` for the `q` where the
> corrected `Δ(q) ≠ 0`, which is still most `q` — including `q = 3` (the
> BC1 anchor, `17 ≠ 7`), `q = 5, 7, 9, 13, 17, 19, 23, 25, 27, 29, 31, 37,
> 41, 43, 47, 53, …`.  `n = 3` is therefore **re-opened, but only on a thin
> residue**: a second invariant is needed exactly on the tie set.

### What I would do next

1. **Rebuild both `S`-tables from a single source** that covers defining
   characteristic — the BHR tables for `Sp₆(q)` and `Ω₇(q)` (Bray–Holt–
   Roney-Dougal Tables 8.28–8.29 and 8.39–8.40), not CTblLib.  CTblLib can
   only ever see cross-characteristic members; the whole `Sym^k SL₂(q₀)`
   family is invisible to it.  Re-audit `p^C₄` the same way (are there
   `p ≥ 5` defining-characteristic members beyond `Sym³` at `q` non-prime?).
2. **Add the `C₅` layer explicitly** to both sides, and restate the target
   as a statement about `(p, r)`, not about `q mod 9360`.
3. **`q = 11` is small enough to be settled by direct computation**:
   `|Ω₇(11)| ≈ 1.5·10¹⁵`, `|PSp₆(11)| ≈ 1.5·10¹⁵` — out of reach for a
   subgroup sweep, but the two censuses can be assembled column by column
   from the corrected tables and cross-checked against BHR maximality data.
   That is the single most valuable next computation.
4. **`κ` or `ι₂` as the tie-breaker on the tie set** (§4ar's ratio trick),
   exactly as in the alternating family: `mult₁` alone is now known to be
   insufficient for `B₃/C₃`, which is the same lesson `A₁₀` taught.
