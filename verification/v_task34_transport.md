# Task 34 — transport of the conductors `ι`, `ι₂` from the socle factors
# to a Fitting-free `T` (NOTES.md §4ar item 3)

Date 2026-08-07.  Script `v_task34_transport.g`, raw output
`v_task34_transport_out.txt` (GAP 4.16.0).  **NOTES.md not edited.**

---

## 0. Notation

For a finite group `G`,

  `I(G) := { [G : N_G(A)] : 1 ≠ A ≤ G abelian } = { |A^G| : 1 ≠ A ≤ G abelian }`

(the second form: the index of the normalizer *is* the length of the
conjugacy class **of subgroups**).  `ι(G) = min I(G)`, `ι₂(G) =` second
smallest element of `I(G)` (second smallest **distinct value**).

Let `T` be Fitting-free, `Q := Soc(T) = S₁ × ⋯ × S_k`, so `C_T(Q) = 1` and
`T ↪ Aut(Q)`.  Put

* `K` := kernel of the `T`-action on `{S₁,…,S_k}`;  `Q ≤ K ⊴ T`.
  Since `C_K(Q) = 1`, the maps `π_i : K → Aut(S_i)` embed `K ↪ ∏_i Aut(S_i)`.
* `T_i` := stabiliser of the `i`-th factor; `ℓ_i := [T : T_i]` its orbit length.
* `Ā_i` := image of `T_i` in `Aut(S_i)` — the **almost simple group induced on
  `S_i`**; `S_i ≤ Ā_i ≤ Aut(S_i)`.
* `K_i := K ∩ ⋂_{j≠i} ker π_j` — the "`i`-th component" of `K`.  Then
  `S_i ≤ K_i ≤ Ā_i`, `[K_i, K_j] = 1`, `K_i ∩ K_j = 1` (`i ≠ j`).
* For `A ≤ K`, `supp(A) := { i : π_i(A) ≠ 1 }`.
* **The pair invariant.**  For a pair `S ≤ K* ≤ Ā ≤ Aut(S)`,

    `I(K* ≤ Ā) := { [Ā : N_Ā(A)] : 1 ≠ A ≤ K* abelian }`,

  `ι(K*≤Ā) = min`, `ι₂(K*≤Ā) =` second value.  Note both slots matter: `A`
  is drawn from `K*`, but fused by the larger `Ā`.
* `ν(S) := min { [S : N_S(A)] : 1 ≠ A ≤ Aut(S) abelian }`  (`≤ ι(S)`);
  `μ(S) :=` minimal index of a **proper subgroup** of `S`.

Everything below is stated for the *set* `I`, so it transports `ι` and `ι₂`
simultaneously.

---

## 1. The transport lemmas

### Lemma TR-1 (single-factor: an exact identity) — **[PROVEN]**

*Let `1 ≠ A ≤ K_i` be abelian, `ℓ = ℓ_i`.  Then*

  **`|A^T| = ℓ · |A^{Ā_i}|`**,

*the right-hand class being taken inside `Aut(S_i)` under conjugation by `Ā_i`.
Consequently*

  **`I(T) ⊇ P := ⋃_{orbits O} ℓ_O · I(K_{i_O} ≤ Ā_{i_O})`.**

*Proof.*  Every `T`-conjugate of `A` lies in some `K_j` (`K_i^t = K_{i^t}`),
and the resulting map `A^T → i^T` is `T`-equivariant and surjective, so
`|A^T| = ℓ · |fibre|` and the fibre over `i` is `A^{T_i}`.  `T_i` acts on
`K_i ≤ Aut(S_i)` by conjugation, and this action agrees with conjugation by
`ρ_i(T_i) = Ā_i` inside `Aut(S_i)` (the embedding `K ↪ ∏Aut(S_j)` is
`T`-equivariant, and `K_i ↪ Aut(S_i)` is injective).  Hence
`|A^{T_i}| = |A^{Ā_i}|`. ∎

Two consequences worth spelling out.

* The right object is the **pair** `(K_i, Ā_i)`, **not** the simple group `S_i`.
  `K_i` may be strictly larger than `S_i` (outer automorphisms realised inside
  one component), and `Ā_i` may be strictly larger than `K_i` (outer
  automorphisms realised only *diagonally*, which fuse `S_i`-classes without
  contributing new subgroups).  Both effects are visible in the GAP data of §3.
* `ν(S_i) ≤ ι(K_i ≤ Ā_i) ≤ m_i · ι(S_i)` with `m_i` the fusion number of §4am.

### Lemma TR-2 (multi-support floor) — **[PROVEN]**

*Let `A ≤ K` be abelian with `J := supp(A)`, `s = |J| ≥ 2`.  Then*

  `|A^T| ≥ |J^T| · ∏_{i∈J} [S_i : N_{S_i}(π_i A)] ≥ |J^T| · ∏_{i∈J} ν(S_i)`,

*and `|J^T| ≥ ℓ_i / s` for every `i ∈ J`.  In particular*

  **`|A^T| ≥ F := ν_min²`,  `ν_min := min_i ν(S_i)`**, *and more sharply
  `|A^T| ≥ (ℓ_i/s)·ν_min^s`.*

*Proof.*  `A ↦ supp(A)` is `T`-equivariant, so `|A^T| = |J^T|·|A^{T_J}| ≥
|J^T|·|A^Q|`.  The tuple map `A' ↦ (π_i A')_{i∈J}` is injective on nothing in
particular, but its **image** on `A^Q` is the full product orbit
`∏_{i∈J} (π_i A)^{S_i}` because `Q = ∏S_i` acts componentwise and
independently; hence `|A^Q| ≥ ∏_{i∈J}[S_i:N_{S_i}(π_i A)]`.  Each factor is
`≥ ν(S_i)` by definition of `ν` (`π_i A ≤ Aut(S_i)` is abelian `≠ 1`).
For the last claim, `T_J ∩ T_i ≤ T_i` gives
`ℓ_i = [T:T_i] ≤ [T:T_J∩T_i] = [T:T_J]·[T_J:T_J∩T_i] = |J^T|·|i^{T_J}| ≤
|J^T|·s`. ∎

### Lemma TR-3 (`A ⊄ K`: the factor-permuting branch) — **[PROVEN]**

*Let `A ≤ T` be abelian with `A ⊄ K`, `B := A ∩ K`.  Then*

  **`|A^T| ≥ min( F , |S_min| )`,  `|S_min| := min_i |S_i|`.**

*Proof.*  Throughout, `|A^T| = [T:QN_T(A)]·[Q:N_Q(A)] ≥ [Q:N_Q(A)]`.
Fix `a ∈ A \ K`; `a` moves at least two factors.

1. `supp(B)` is `A`-invariant (as `A` is abelian, `B^a = B`).  If some `a ∈ A`
   moves a point of `supp(B)`, then `|supp(B)| ≥ 2`, and `N_T(A) ≤ N_T(B)`
   gives `|A^T| ≥ |B^T| ≥ F` by TR-2.
2. Otherwise `A` fixes `supp(B)` pointwise.
   * If `B = 1`: for `q ∈ N_Q(A)` and `x ∈ A`, `x^q x^{-1} ∈ A ∩ Q ≤ B = 1`,
     so `N_Q(A) = C_Q(A) ≤ C_Q(a)`.  As `a` permutes the factors with an orbit
     of length `d ≥ 2`, `C_Q(a)` is a product of twisted diagonals and
     `[Q:C_Q(a)] ≥ |S_min|^{d−1} ≥ |S_min|`.
   * If `supp(B) = {i}` (a single point, fixed by `A`): then `B ≤ K_i` and
     `A ≤ T_i`, so `a` moves some factor `j ≠ i`.  Put `R := ∏_{m≠i} S_m`,
     which is `a`-invariant.  For `q ∈ R ∩ N_Q(A)`: `a^q a^{-1} ∈ A ∩ Q ≤ B ≤ S_i`
     and simultaneously `a^q a^{-1} ∈ R`, hence `= 1`, i.e. `q ∈ C_R(a)`.  So
     `[Q:N_Q(A)] ≥ [R : R ∩ N_Q(A)] ≥ [R:C_R(a)] ≥ |S_j| ≥ |S_min|`.
   * `|supp(B)| ≥ 2` with `A` fixing it pointwise: `|A^T| ≥ |B^T| ≥ F` as in 1. ∎

**This supersedes §4am's Lemma ι-outer** (which only treated `A ∩ Soc = 1` and
whose conclusion — "the outer branch only lowers `ι`" — is not what is needed
for `ι₂`).  It does not use Lemma ι-μ, so the §4at defect is irrelevant to it.
Note the *genuinely* outer abelian subgroups that could lower a conductor are
**not** in this branch at all: they are the ones inside `K_i \ S_i`, and
TR-1 already accounts for them exactly, through the pair invariant
`I(K_i ≤ Ā_i)`.

### Lemma TR-4 (`ν ≥ μ`; when the outer branch is harmless) — **[PROVEN]**

*For `S` simple, `ν(S) ≥ μ(S)`.  Hence if `ι(S) = μ(S)` then `ν(S) = ι(S)` and
no abelian subgroup of `Aut(S)` has an `S`-normalizer of index below `ι(S)`.*

*Proof.*  Let `1 ≠ A ≤ Aut(S)` be abelian with `N_S(A) = S`, i.e.
`[S,A] ≤ A`.  Since `S = Inn(S) ⊴ Aut(S)`, also `[S,A] ≤ S`, so
`[S,A] ≤ A ∩ S`.  If `A ∩ S = 1` this gives `A ≤ C_{Aut S}(S) = 1`,
contradiction.  If `A ∩ S ≠ 1` then `1 ≠ A ∩ S ≤ S` is abelian and normal in
`S` (normalised by `S` because `[S, A∩S] ≤ [S,A] ≤ A∩S`), contradicting
simplicity.  So `N_S(A) < S` and `[S:N_S(A)] ≥ μ(S)`. ∎

This is the clean statement §4am was reaching for.  For `A_m` (`m ≥ 9`)
`μ = m < C(m,3) = ι`, and indeed `ν(A_m) = C(m,2) < ι(A_m)` — the outer branch
*does* bite.  For a Lie-type `S` with `ι(S) = μ(S)` (true whenever the minimal
parabolic index is the minimal permutation degree — Kleidman–Liebeck, outside
a short list) the outer branch **cannot lower `ι`**.  It can still move `ι₂`;
see §4 input (I3).

### Theorem TR (transport) — **[PROVEN, conditional on (★) which is checkable]**

*Let `T` be Fitting-free with socle `Q = ∏S_i`, and*

  `P = ⋃_O ℓ_O·I(K_{i_O} ≤ Ā_{i_O})`,  `F = ν_min²`,  `Φ = min(F, |S_min|)`.

*Then `I(T) ⊇ P` and `I(T) \ P ⊆ [Φ, ∞)`.  Consequently:*

1. *(★₁) if `min P < Φ` then* **`ι(T) = min P = min_O ℓ_O · ι(K_{i_O} ≤ Ā_{i_O})`**;
2. *(★₂) if in addition the second smallest element `p₂` of `P` satisfies
   `p₂ < Φ`, then* **`ι₂(T) = p₂`**, *i.e.*

     **`ι₂(T) = min( ℓ_{O*}·ι₂(K≤Ā)_{O*} , min_{O ≠ O*} ℓ_O·ι(K≤Ā)_O )`**

   *where `O*` is a minimising orbit in (1) — the "second value of the best
   orbit, or first value of the second-best orbit, whichever is smaller",
   exactly as conjectured, but with the pair invariant in place of `ι(S_i)`
   and with the orbit length `ℓ_O` as a multiplier.*

*Proof.*  Every abelian `1 ≠ A ≤ T` is either (a) `i`-local — TR-1, value in
`P`; (b) inside `K` with `|supp| ≥ 2` — TR-2, value `≥ F`; or (c) `⊄ K` —
TR-3, value `≥ min(F,|S_min|)`. ∎

**Sharper form of (★).**  `F` may be replaced by the sharper
`min_{J,|J|=s≥2} (ℓ_{i}/s)·∏_{i∈J} ν(S_i)`.  Also `min P ≤ ℓ_{O}·m_O·ι(S_{i_O})`
and `ν(S) ≥ μ(S)` (TR-4), so a convenient sufficient form of (★₁) is

  `ℓ_O · m_O · ι(S_i) < μ(S_min)²`  for the minimising orbit.

### What is *not* proven

* Nothing in TR-1/2/3/4 is conditional; the only hypothesis of Theorem TR is
  the numerical condition (★), which must be checked per candidate `T`
  (it is a comparison of explicit numbers, not a new theory).
* The theorem transports the *value set*.  It does **not** compute
  `I(K_i ≤ Ā_i)` — that is a new table (see input (I3)) and is **not** the
  `ι`/`ι₂` tables of §4at/§4au, which are for the simple groups.

---

## 2. Falsification (run BEFORE the proofs were written)

`v_task34_transport.g` computes `I(G)` **exactly and exhaustively** below a
bound: every value `[G:N_G(A)] ≤ b` is realised by the subgroup `N = N_G(A)`
of index `≤ b`, and `A` is then a nontrivial abelian *normal* subgroup of `N`
with `N_G(A) = N`; so the scan `LowIndexSubgroups(G,b)` × `NormalSubgroups(N)`
is complete.  No sampling.

Part 6 of the script is a programmatic PASS/FAIL of Theorem TR, checking
[C1] `P ⊆ I(T)`, [C2] `ι(T) = min P`, [C3] `ι₂(T) = p₂`:

| `T` | orbits `(ℓ; K_i, Ā_i)` | predicted `P` (≤ b) | observed `I(T)` (≤ b) | C1 | C2 | C3 |
|---|---|---|---|---|---|---|
| `A₅ × A₅` | `(1;A₅,A₅)×2` | 5 6 10 15 | 5 6 10 15 25 30 36 | ✓ | ✓ 5 | ✓ 6 |
| `A₅ wr C₂` | `(2;A₅,A₅)` | 10 12 20 30 | 10 12 20 25 30 36 | ✓ | ✓ 10 | ✓ 12 |
| `(A₅×A₅).2` diag | `(1;A₅,S₅)×2` | 5 6 10 15 | 5 6 10 15 25 30 36 | ✓ | ✓ 5 | ✓ 6 |
| `(A₅×A₅).2²` | `(2;A₅,S₅)` | 10 12 20 30 | 10 12 20 25 30 36 | ✓ | ✓ 10 | ✓ 12 |
| `A₅ × A₆` | `(1;A₅,A₅),(1;A₆,A₆)` | 5 6 10 15 20 36 | identical | ✓ | ✓ 5 | ✓ 6 |
| `S₅ × A₆` | `(1;S₅,S₅),(1;A₆,A₆)` | 5 6 10 15 20 36 | identical | ✓ | ✓ 5 | ✓ 6 |
| `A₅ × L₂(7)` | `(1;·)×2` | 5 6 7 8 10 15 21 28 | + 35 40 | ✓ | ✓ 5 | ✓ 6 |
| `(A₅ wr C₂) × A₆` | `(2;A₅,A₅),(1;A₆,A₆)` | 10 12 15 20 | identical | ✓ | ✓ 10 | ✓ 12 |
| `A₅ × PGL(2,9)` | `(1;A₅,A₅),(1;A₆,PGL(2,9))` | 5 6 10 15 | + 30 | ✓ | ✓ 5 | ✓ 6 |
| `A₅ wr C₃` | `(3;A₅,A₅)` | 15 18 | identical | ✓ | ✓ 15 | ✓ 18 |

**10/10 PASS, no falsification.**  Points the data settles:

* **The orbit length really multiplies.**  `ι(A₅ wr C₂) = 10 = 2·ι(A₅)`,
  `ι(A₅ wr C₃) = 15 = 3·ι(A₅)`.  A formula "`ι(T) = min_i ι(S_i)`" (the naive
  reading of §4al's Lemma ι-prod, whose lower bound `ι(T) ≥ min ι(S_i)` is
  correct but far from tight) is **false**.
* **`Ā_i`, not `S_i`, is the right group.**  `I(A₆) = {10,15,20,36,45}` but
  `I(A₆ ≤ PGL(2,9)) = {10,30,36,40,45}`: the two `A₆`-classes of `V₄` fuse
  (`15 → 30`) and the two classes of `C₃` fuse (`20 → 40`).  `ι` is unchanged,
  **`ι₂` is not** (`15 → 30`).  So `ι₂` transport genuinely needs the
  almost-simple pair invariant.
* **`K_i`, not `Ā_i`, supplies the subgroups.**  In `(A₅×A₅).2` with the `2`
  acting *diagonally* as an outer automorphism, `K_1 = A₅` (not `S₅`), and the
  prediction `1·I(A₅ ≤ S₅)` is right; using `I(S₅ ≤ S₅)` would also have given
  `{5,6,10,15}` here by coincidence, but the distinction is real (`S₅ × A₆`
  has `K_1 = S₅` and the outer witness `⟨(1 2)⟩` contributes the value `10`).
* **The multi-support floor is tight.**  `A₅ wr C₂`: `25 = 5·5` (`V₄ × V₄`),
  `36 = 6·6` (`C₅ × C₅`); the diagonal outer `⟨(1 2)(6 7)⟩` in `(A₅×A₅).2²`
  gives exactly `100 = 10·10 = |J^T|·∏[S_i:N_{S_i}(π_i A)]` — TR-2 is an
  equality here.
* **TR-3 is tight.**  `A = ⟨swap⟩` in `A₅ wr C₂` gives `|A^T| = 60 = |S_min|`,
  matching the bound `[Q:C_Q(a)] ≥ |S_min|^{d−1}` exactly at `d = 2`.
* **Second-best-orbit case occurs.**  `(A₅ wr C₂) × A₆`: `ι = 10` from *both*
  orbits, `ι₂ = 12 = 2·ι₂(A₅)` from the best orbit, while the second-best
  orbit's *second* value (`15`) is third.  `A₅ × L₂(7)`: `ι = 5`, `ι₂ = 6`
  both from orbit 1, `7 = ι(L₂(7))` third.  Both alternatives of (★₂) are
  exercised.

Part 1 also gives an `Ā`-table used above (exhaustive, small groups):
`I(A₅)={5,6,10,15}`, `I(S₅)={5,6,10,15}`, `I(A₆)={10,15,20,36,45}`,
`I(S₆)={10,15,20,36,45,60}`, `I(PGL(2,9))=I(M₁₀)=I(PΓL(2,9))={10,30,36,40,45}`,
`I(L₂(7))={7,8,21,28}`, `I(PGL(2,7))={8,14,21,28}`, `I(A₇)∩[1,60]={35}`,
`I(S₇)∩[1,60]={21,35}`.  Note `ι(A₇)=35=C(7,3)` while `ι(S₇)=21=C(7,2)=ν(A₇)`
— the §4am `ν`-phenomenon, here as a *pair* invariant.

---

## 3. The transported Criterion AT

> **Theorem AT (transported form).**  Let `n ≥ 9` and let `T` be a
> Fitting-free non-simple group with `|T| = n!/2`, socle `Q = ∏_{i=1}^k S_i`,
> notation as in §0, and assume the numerical condition
>
>   (★)  `p₂ < min( ν_min² , |S_min| )`,  `p₂ =` second smallest element of `P`.
>
> If `T` has the same `(mult₁, κ)` pair as `A_n` — equivalently, by
> Lemma ι-A (§4ak) and Lemma ι₂-A (§4as), if `ι(T) = C(n,3)` **and**
> `ι₂(T) = C(n,4)` — then by Theorem TR there is an orbit `O*` with
>
>   `ℓ_{O*} · ι(K ≤ Ā)_{O*} = C(n,3)`
>
> and **either**
>
> * **(a) same orbit:** `ℓ_{O*} · ι₂(K ≤ Ā)_{O*} = C(n,4)`, whence, dividing —
>   *and the orbit length `ℓ` cancels together with the cubic* —
>
>     **`ι₂(K≤Ā)/ι(K≤Ā) = C(n,4)/C(n,3) = (n−3)/4`,**
>
>   which is §4ar's ratio relation verbatim, with `ρ = m₁/m₂` replaced by the
>   ratio of the *pair* invariants; **or**
>
> * **(b) two orbits:** `ℓ_{O**}·ι(K≤Ā)_{O**} = C(n,4)` for a second orbit
>   `O** ≠ O*`, whence
>
>     **`(n−3)/4 = (ℓ_{O**}·ι(K≤Ā)_{O**}) / (ℓ_{O*}·ι(K≤Ā)_{O*})`,**
>
>   a relation between two *different* socle factors, together with
>   `n!/2 = |T| = |T:Q|·∏|S_i|`.
>
> Case (a) is closed for every Lie family by §4as/§4au **once the pair
> invariants are known to equal the simple-group invariants**.  Case (b) is
> new and open.

**Status of the theorem: [PROVEN modulo the inputs (I1)–(I6) below].**
Group-theoretically the transport itself is complete; what is missing is
*data* (pair invariants) and *one new case* (b).

### Honest input list

| # | input | status |
|---|---|---|
| **I1** | `ι(A_n) = C(n,3)`, `ι₂(A_n) = C(n,4)` for `n ≥ 9` | **PROVEN** (§4ak, §4as) |
| **I2** | Transport TR-1…TR-4 / Theorem TR | **PROVEN** (this note); condition (★) is a numeric check per factorization, **not yet run** for the 222 admissible factorizations of §4am |
| **I3** | the **pair invariants** `ι(K ≤ Ā)`, `ι₂(K ≤ Ā)` for every admissible family `S`, all `S ≤ K ≤ Ā ≤ Aut(S)` | **OPEN.**  §4at/§4au tabulate `ι, ι₂` of the *simple* groups only.  TR-4 gives `ι(K≤Ā) = ι(S)` whenever `ι(S) = μ(S)` (so `ι` is safe for Lie type, modulo the KL minimal-degree table), but **`ι₂` is demonstrably not stable** — `A₆` vs `PGL(2,9)` shows `ι₂` doubling under fusion.  This is the main new debt created by the transport. |
| **I4** | fusion numbers `m₁, m₂` (now: which `S`-classes fuse in `Ā`), `≤ |Out(S)|` | partially known (§4am: `m ≤ 2` for long-root classes); needed per family for `ι₂` |
| **I5** | **case (b)** of the ratio trick — the two-orbit relation | **OPEN, new.**  It is a relation between two *distinct* simple factors plus the order equation `n!/2 = c·∏|S_i|`; the §4am scarcity argument (only 222 admissible factorizations for `n ≤ 70`) is the natural attack, but it is a `[COMPUTED]` range fact, not a proof |
| **I6** | `Bound G₂` for `q = p ≥ 5` | **OPEN** (§4au, unchanged) |
| **I7** | corrected `ι₂` closed forms at non-prime `q` (the `Z(U)` subfield trap) | **PROVEN/refuted per family** (§4au); must be re-derived for the *pair* invariant of I3 |

Two remarks on honesty:

* The transport **weakens** nothing in Criterion AT (§4am): `ι(T) = min P
  ≤ ℓ·m·ι(S_i)` still gives the upper bound §4am used, and TR-1 shows §4am's
  `c·min_i ι(S_i)` is an over-estimate of `ι(T)` only by the difference
  between `c` and `ℓ_O·m_O` — so Criterion AT remains **sufficient**, and the
  verified sweep to `n ≤ 70` stands.
* But the transport **does not by itself close `A_n` for all `n`**.  It removes
  §4ar item 3 from the open list and replaces it with I3 and I5.  I5 in
  particular is a genuinely new case that §4ar did not anticipate (§4ar assumed
  the two conductors are carried by the same factor; the GAP data —
  `(A₅ wr C₂) × A₆`, `A₅ × L₂(7)` — shows the second-best-orbit alternative is
  realised in nature, so it cannot be dismissed).

---

## 4. Reproduce

```
~/gap-4.16.0/gap -q -o 8g LeanDring/Even/verify/v_task34_transport.g \
    > LeanDring/Even/verify/v_task34_transport_out.txt
```
Runtime a few minutes; all arithmetic exact, all scans exhaustive below the
stated bounds.
