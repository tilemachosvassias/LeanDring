# v_task36 — the PAIR invariants `ι(K ≤ Ā)`, `ι₂(K ≤ Ā)` for the residual
# families (§4av inputs **I3**, **I4**, **I7**)

Date 2026-08-07.  Script `v_task36_pair_invariants.g`, raw output
`v_task36_pair_invariants_out.txt` (GAP 4.16.0).  **NOTES.md not edited.**

Definition (v_task34_transport.md §0), for `S ≤ K ≤ Ā ≤ Aut(S)`:

  `I(K ≤ Ā) := { [Ā : N_Ā(A)] : 1 ≠ A ≤ K abelian }`,
  `ι(K≤Ā) = min`,  `ι₂(K≤Ā) =` second smallest **distinct** value.

Headline results:

1. **The task brief's expectation "`ι₁` never changes" is FALSE.**  For
   `L_d(q)` with a graph automorphism in `Ā` the *minimal* value doubles
   (`L₃(2) ≤ Aut`: `7 → 14`; `L₃(3).2`: `13 → 26`; `L₄(2) = A₈ ≤ S₈`:
   `15 → 30`; `L₃(4)`: `21 → 42`; `Sp₄(4).4`: `85 → 170`).  The two
   end-node parabolic classes have equal index and are swapped by the
   duality, so they *fuse*.
2. Consequently the pair ratio `R^p = ι₂(K≤Ā)/ι(K≤Ā)` is **halved** for
   `L₃` and `L₄` when the graph automorphism is present, **unchanged**
   for `L₅`, `Sp₄(q)` even, `U₄`, `U₅`, `Sp₆`, `Sp₄(q)` odd at prime `q`,
   and **doubled** in exactly one situation: the odd-`q`, non-prime
   subfield-trap classes of `S₄/Sp₆/U₅` when `Ā` contains a diagonal
   automorphism.
3. `A_m ≤ S_m` with `K = A_m`: **completely unchanged**, `ι = C(m,3)`,
   `ι₂ = C(m,4)` (verified `m = 7, 8, 9`).  With `K = S_m` the spectrum
   shifts down to `C(m,2), C(m,3), C(m,4)` — which only *strengthens*
   Theorem κ-A and Lemma TO-0.
4. **Lemma ι₂-pair-bound** (§6, requested by the monitor for v_task37
   residue R1): `ι₂(K≤Ā) ≤ 2(q²+1)·ι(K≤Ā)` for every residual family and
   every admissible `Ā`; per family the constant is `≤ q+1` except `L₅`
   (`2(q²+1)`) and `Sp₆/U₅` (`≈ q`).
5. **Direction verdict:** no ratio-trick bound of §4at/§4au changes
   *direction*.  Every divisibility kill is preserved or tightened; the
   one upward case (item 2, factor exactly 2) leaves every divisibility
   condition literally unchanged (`t(q)` and `2t(q)` are both integers)
   and weakens only the *size* kills, by a bounded factor.  Details and
   the one caveat in §7.

---

## 0.  The fusion identity — the whole subject in one line

> **Lemma F [PROVEN].**  Let `S ⊴ Ā`, `1 ≠ A ≤ Ā`.  Then
>
>   **`[Ā : N_Ā(A)] = f(A) · [S : N_S(A)]`,   `f(A) := [Ā : S·N_Ā(A)]`,**
>
> and `f(A)` divides `[Ā : S] ≤ |Out(S)|`.

*Proof.*  `S ⊴ Ā` acts on the `Ā`-class `A^Ā`; the `S`-orbits on `A^Ā`
are permuted transitively by `Ā`, hence all have the common size
`|A^S| = [S:N_S(A)]`, and their number is `[Ā : S N_Ā(A)]`. ∎

Two immediate consequences used throughout.

* **(C1)  Only `S`-classes of the same `S`-index can fuse.**  Fused
  classes are `Ā`-conjugate, hence have equal `|A^S|`.  So the entire
  question "does `Ā`-fusion merge the classes realising `ι₁` and `ι₂`?"
  has the answer **never** whenever `ι₁ ≠ ι₂` — the danger is *not*
  merging `ι₁` with `ι₂`, it is merging the `ι₁`-class with a *different*
  class of the *same* index, which multiplies the value.
* **(C2)** `I(S ≤ Ā) = { f(A)·[S:N_S(A)] }` is computable from
  `I(S)` **plus the class-multiplicity of each index value plus the
  action of `Out(S)` on the class list** — nothing else.  This is what
  the script computes exactly (Tool 1 below).

For `K > S` there are additional values coming from abelian `A ⊄ S`;
by Lemma TR-4 (`ν(S) ≥ μ(S)`) these are `≥ μ(S)`, and for Lie type with
`ι(S) = μ(S)` they cannot go below `ι(S)`.  They *can* land strictly
between `ι₁` and `ι₂` — this really happens (`U₄(2).2`, §5.4) — and that
direction is harmless (it lowers `ι₂`, see §7).

---

## 1.  Method (exact, exhaustive, falsification first)

**Tool 1 (fusion table).**  For `S` simple: enumerate all `S`-classes of
abelian `1 ≠ A ≤ S` with `[S:N_S(A)] ≤ b` (from `LowIndexSubgroups(S,b)`
× abelian normal subgroups of each, deduplicated by `RepresentativeAction`
— exhaustive below `b`, exactly the v_task34 scan).  Then compute

  `D(A) := { ω ∈ Out(S) : A^a ∼_S A for a lifting ω }`,

a subgroup of `Out(S)` (well defined because inner automorphisms act
trivially on `S`-classes), by looping over the **elements** of `Out(S)`.
By Lemma F, for `Ā` with image `Ū ≤ Out(S)`,

  `f(A) = [Ū : Ū ∩ D(A)]`,  and  `I(S ≤ Ā) = { [Ū:Ū∩D(A)]·ind(A) }`.

The script prints this for **every** subgroup `Ū ≤ Out(S)`, i.e. for
every admissible `Ā` at once.

**Tool 2 (direct, needed for `K > S`).**  `I(K ≤ Ā)` up to `b` from
`LowIndexSubgroups(Ā,b)`: every value `[Ā:N_Ā(A)] ≤ b` is realised by
`N = N_Ā(A)` of index `≤ b`, and `A` is then a nontrivial abelian normal
subgroup of `N` with `A ≤ K` and `N_Ā(A) = N`.  Exhaustive below `b`.

**The two tools are independent** and were run against each other:
`L₃(2) ≤ PGL(2,7)` gives `{8,14,21,28}` by Tool 2 and
`{8,14,21,28}` by Tool 1; `L₃(3).2` gives `{26,52,104,117}` by both;
`A₈ ≤ S₈` gives `{30,35,56}` (Tool 1, `K=S`) inside
`{28,30,35,56,70}` (Tool 2, `K=Ā`).  No disagreement.

---

## 2.  When can a parabolic class fuse? [I4]

Notation: `S` of Lie type over `F_q`, `Δ` the Dynkin diagram, `P_J` the
standard parabolic of type `J ⊆ Δ`, `Ω_J` the set of `S`-conjugates of
`P_J`.  `Aut(S) = Inndiag(S)⋊⟨φ, γ⟩` (field, graph), and the image of
`Ā` in the graph group is written `Γ_Ā` (`|Γ_Ā| ≤ 2` for every residual
family: `A_{d−1}` has diagram group `C₂` (`d ≥ 3`), `C_n` has trivial
diagram group, `²A_{d−1}` (unitary) has trivial *residual* diagram
group, `C₂` in characteristic 2 and `G₂` in characteristic 3 have the
exceptional `C₂`).

> **Lemma P1 [PROVEN].**  Every `α ∈ Aut(S)` permutes the parabolic
> subgroups of `S` and induces a permutation `σ(α)` of the types, with
> `P_J^α ∈ Ω_{σ(α)J}`; `σ` is the projection `Aut(S) → Γ`, so
> **`σ(α) = id` for every inner, diagonal and field automorphism `α`.**

*Proof.*  Parabolics are exactly the subgroups `N_S(O_p(H))` for
`H ⊇` a Sylow `p`-subgroup (Borel–Tits), a description invariant under
every automorphism, so `Aut(S)` permutes them and preserves the
containment order, i.e. acts on the diagram.  `Inndiag` normalises the
standard `B`, `T` and each standard `P_J` (in `PGL_d(q)` the diagonal
matrices stabilise every standard flag; in general `Inndiag = S·T̂` with
`T̂ ≤ N(B)`), and the standard field automorphism fixes each `P_J`
elementwise-as-a-set (the standard `P_J` is defined over `F_p`).  So
both project to `id`. ∎

> **Corollary P2 (the parabolic-witness fusion number) [PROVEN].**
> Let `A` be a **characteristic subgroup of `U_{P_J}`** (e.g.
> `A = U_{P_J}` or `A = Z(U_{P_J})`), so that `N_S(A) = P_J` (Tool 2 of
> v_task32) and `A^α = A_{P_J^α}` for every `α ∈ Aut(S)`.  Then
>
>   **`f(A) = |Γ_Ā · J|`**  (the size of the `Γ_Ā`-orbit of the type `J`),
>
> in particular `f(A) = 1` whenever `Γ_Ā` fixes `J` — and always
> `f(A) = 1` if `Ā ≤ Inndiag(S)⟨φ⟩`.

*Proof.*  `A^Ā = { A_{P'} : P' ∈ ⋃_{J' ∈ Γ_Ā J} Ω_{J'} }` because `S` is
already transitive on each `Ω_{J'}` (all parabolics of a fixed type are
`S`-conjugate — the Bruhat/`BN`-pair fact), and the assignment
`P ↦ A_P` is an `Aut(S)`-equivariant bijection.  Divide by `|A^S| = |Ω_J|`
(all `Ω_{J'}` in one `Γ`-orbit have the same size, since the graph
automorphism is an isomorphism). ∎

> **Remark (robustness of `ι₁`).**  `ι(K≤Ā) = ι(S)` as soon as **one**
> `ι₁`-realising `S`-class has `f = 1`; extra same-index classes with
> `f = 2` are then invisible.  This is why the several same-index classes
> found in the data (`Sp₆(2)`: two at 63 and two at 135; `S₄(5)`: two at
> 156; `S₄(4)`: **four** at 85; `U₄(2)`: two at 40) are harmless.
> `L_d(q)` with a graph automorphism is the opposite situation: there are
> exactly **two** `ι₁`-classes and the duality swaps them, so *no*
> `ι₁`-class survives with `f = 1` and `ι₁` really doubles.

This answers the brief's question in the exact opposite of the expected
direction:

* **`L_d(q)`, `d ≥ 3`:** the duality sends `J = {k}` to `{d−k}`.  These
  are *different* `S`-classes of *equal* index `[d,k]_q`.  Hence for
  every `Ā` containing a graph automorphism,
  **`f(U_{P_1}) = 2`** — the `ι₁`-class fuses and `ι₁` **doubles**.
  `f(U_{P_2}) = 2` for `d = 5` (types `{2},{3}` swapped) but
  **`f(U_{P_2}) = 1` for `d = 4`** (type `{2}` is the fixed node).
* **`Sp₄(q)`, `q` even:** the exceptional graph automorphism swaps the
  two node types, both of index `(q+1)(q²+1)`; both `ι₁`-classes fuse,
  `ι₁` doubles.  For `q` odd there is no graph automorphism and
  `f ≡ 1` on parabolic witnesses.
* **`Sp₆(q)`, `U₄(q)`, `U₅(q)`:** trivial graph group, so `f ≡ 1` on
  parabolic witnesses for **every** `Ā`.
> **Remark (an elementary proof of the `L_d` case, no BN-pair theory).**
> `U_{P_k} = { g ∈ SL_d(q) : g` acts trivially on `W` and on `V/W }` for
> the `k`-space `W`, and its **pointwise fixed space on `V` has dimension
> `k`**.  Conjugation preserves that dimension, whereas the duality
> `g ↦ (g^T)^{-1}` sends `U_{P_k}` to a group with fixed space of
> dimension `d−k`.  Hence for `k ≠ d−k` the two classes are distinct and
> swapped: `f = 2`.  This settles `L₄(3)`, `L₅(2)`, … without any
> computation.

* **Diagonal and field automorphisms never move a parabolic class**
  (Lemma P1) — this is the brief's "why", proved above and confirmed
  computationally at `L₃(4)` (`Out = D₁₂`; the index-2 subgroup
  `⟨diag, φ⟩ = D(U_{P₁})` of order 6 is exactly the non-graph part, and
  `ι₁ = 21` is preserved by it and doubled by everything outside it).

---

## 3.  The `ι₂`-realising classes, family by family [I4 + I7]

By (C1) the only question is: *does the `ι₂`-realising `S`-class have a
same-index partner class, and does `Out(S)` fuse them?*

### 3.1  Parabolic `ι₂` (`L₄`, `L₅`, `U₄`, `Sp₆`)

`ι₂ = [S:P_{J₂}]` for a second maximal parabolic; Corollary P2 applies
verbatim: `f₂ = |Γ_Ā·J₂|`.

* `L₄`: `J₂ = {2}`, graph-fixed ⟹ `f₂ = 1` always.  With graph,
  `f₁ = 2` ⟹ **`R^p = R/2`**.
* `L₅`: `J₂ = {2} ↔ {3}` ⟹ `f₂ = 2` exactly when `f₁ = 2` ⟹
  **`R^p = R`**.
* `U₄`, `Sp₆`: no graph group ⟹ `f₁ = f₂ = 1` ⟹ **`R^p = R`**.

### 3.2  Borel-type `ι₂` (`L₃`)

`ι₂(L₃(q)) = (q+1)μ` is realised by `A = Z(U_B) = X_{α+β}`, with
`N_S(A) = B = P_∅` (v_task32 §1a).  `∅` is a `Γ`-fixed type and `Z(U_B)`
is characteristic in `U_B`, so Corollary P2 gives `f₂ = 1` for **every**
`Ā`.  With a graph automorphism `f₁ = 2`:  **`R^p = (q+1)/2`.**

### 3.3  Involution-centraliser `ι₂` (`S₄(q)`, `q = p ≥ 5`)

`ι₂ = q²(q²+1)/2 = [S : C_S(t)]`, `A = ⟨t⟩`, `t` the image of
`diag(−1,−1,1,1)` (v_task32 §5.3).  There is only **one** `PSp₄(q)`-class
of involutions with that centraliser order (the other involution classes
have centralisers `GL₂(q)`/`GU₂(q)`-type, of *different* index), so by
(C1) no fusion is possible: `f₂ = 1`.  `q` odd ⟹ no graph ⟹ `f₁ = 1`.
**`R^p = R = q²/(2(q+1))`.**

### 3.4  Subfield-trap `ι₂` (`S₄`, `Sp₆`, `U₅` at non-prime `q`) — [I7]

Here `ι₂ = t(q)·ι₁`, realised by `A =` an `F_{q₀}`-line inside the long
root subgroup `X_θ = Z(U_{P₁}) ≅ (F_q,+)` (v_task32 Tool 5).  The Levi
torus of `S` acts on `X_θ ≅ F_q` through a character with image
`Λ ≤ F_q^×`, and

  `#{F_{q₀}-lines} = (q−1)/(q₀−1)`,  `|S`-orbit`| = t(q) = |Λ|/|Λ∩F_{q₀}^×|`,
  `#{S-classes of lines} = ((q−1)/(q₀−1))/t(q)`.

Two automorphism types matter, and here — unlike §2 — **the diagonal
automorphism is the dangerous one**:

* **Field automorphism `φ` (`x ↦ x^p`):**  the *standard* `F_{q₀}`-line
  `F_{q₀}·1 ≤ F_q` is `φ`-stable, and `φ` normalises `P₁` and `X_θ`.
  Hence `f = 1` on that class.  (`φ` may permute the *other* line
  classes, but the value `t(q)ι₁` is attained by the standard class, so
  `t(q)ι₁ ∈ I(S ≤ Ā)` for every `Ā`.)  **Field automorphisms never raise
  the trap value.**
* **Diagonal automorphism `δ`:**  `Inndiag` induces the *full* `F_q^×`
  on `X_θ`, which is transitive on the `F_{q₀}`-lines.  So if
  `Ā ⊄ S⟨φ⟩` (i.e. `Ā` contains a diagonal automorphism) the *whole* set
  of lines is one `Ā`-class and
  `f₂ = ((q−1)/(q₀−1))/t(q) = |Λ|^{-1}(q−1)/(q₀−1)·|Λ∩F_{q₀}^×|`.
  * `q` **even** (`S₄`, `Sp₆`): `gcd(2,q−1) = 1`, there is no diagonal
    automorphism at all, and moreover `Λ = F_q^×` already (squaring is
    bijective), so `t(q) = (q−1)/(q₀−1)` and `f₂ = 1`.  Nothing changes.
  * `q` **odd**: `Λ = (F_q^×)²` of index 2, so
    `f₂ = 2|Λ ∩ F_{q₀}^×|/(q₀−1) ∈ {1, 2}`.
    So **`f₂ ≤ 2`**, `= 2` exactly when `F_{q₀}^× ≤ (F_q^×)²`, i.e. when
    `(q−1)/(q₀−1)` is even.
  * `U₅(q)`: the Levi `GL₁(q²)` acts on `Z(U_{P₁}) ≅ F_q` through the
    **norm**, which is onto `F_q^×` (v_task32 §7), so `Λ = F_q^×`,
    `t(q) = (q−1)/(q₀−1)` and `f₂ = 1` for every `Ā`.

  And `f₁ = 1` throughout §3.4 (no graph group for `Sp₆`, `U₅`; for
  `Sp₄(q)` with `q` odd no graph either).  Hence
  **`R^p = f₂·t(q) ∈ {t(q), 2t(q)}`** — the single upward case in the
  whole analysis.

### 3.5  `Sp₄(q)`, `q` even, non-prime (graph present)

Both `ι₁`-classes (`Z(U_{P₁})`, `U_{P₂}`) fuse (`f₁ = 2`), and the
`ι₂`-class (`F_{q₀}`-lines in the long root group) is swapped by `γ`
with the corresponding *short*-root class of the same index, so
`f₂ = 2` as well.  **`R^p = R = t(q)`.**  Confirmed exactly at `q = 4`:
`I(S) = {85, 255}`, `I(S ≤ S.2_φ) = {85, 255}`,
`I(S ≤ S.4_γ) = {170, 510}` — ratio `3 = t(4)` in all three.

### 3.6  `A_m`, `Ā = S_m`

`ι₁ = C(m,3)` (witness `⟨(abc)⟩` ↔ 3-subsets) and `ι₂ = C(m,4)`
(witness the regular `V₄` on a 4-subset ↔ 4-subsets).  Both witness sets
are `S_m`-orbits, i.e. **single `S_m`-classes**, so `f₁ = f₂ = 1`:

  **`ι(A_m ≤ S_m) = C(m,3)`,  `ι₂(A_m ≤ S_m) = C(m,4)`  — unchanged.**

Verified exhaustively: `I(A₇ ≤ S₇) = {35}` (`C(7,3) = C(7,4) = 35`),
`I(A₈ ≤ S₈) = {30,35,56}`, `I(A₉ ≤ S₉) = {84,126,270}` with
`C(9,3) = 84`, `C(9,4) = 126` — and note `135 → 270` (the `A₉`
exceptional class of Lemma ι₃-A does fuse; `ι₁, ι₂` do not).

With `K = S_m` (an `S_m` realised *inside one component* of `K`) the
transposition class enters and

  `I(S_m ≤ S_m) ∩ [1, C(m,4)] = { C(m,2), C(m,3), C(m,4) }`

(verified `m = 7,8,9`: `{21,35}`, `{28,30,35,56,70}`, `{36,84,126}`).
This **lowers** `ι` from `C(m,3)` to `C(m,2)` and makes
`R^p = (m−2)/3`.  It strengthens Theorem κ-A and Lemma TO-0 (which need
`min P ≤ C(m,3)`); it never weakens them.

---

## 4.  The computed pair-invariant table

`e := |Out(S)|`; `Ā⁻` = any `Ā` **without** a graph automorphism,
`Ā⁺` = any `Ā` **with** one; `δ` = diagonal automorphism present.
`[C]` = exhaustively computed, `[P]` = proven by §§2–3,
`[P/c]` = proven modulo the cited BHR/Kleidman facts already used in
v_task32.

| family | `ι₁(S)` | `ι₂(S)` | `f₁` | `f₂` | `ι₁(K≤Ā)` | `ι₂(K≤Ā)` | `R^p` | tag |
|---|---|---|---|---|---|---|---|---|
| `L₃(q)`, `q≥3`, `Ā⁻` | `μ=q²+q+1` | `(q+1)μ` | 1 | 1 | `μ` | `(q+1)μ` | `q+1` | [P] |
| `L₃(q)`, `q≥3`, `Ā⁺` | `μ` | `(q+1)μ` | **2** | 1 | `2μ` | `(q+1)μ` | **`(q+1)/2`** | [P] |
| `L₄(q)`, `Ā⁻` | `[4,1]` | `[4,2]` | 1 | 1 | `[4,1]` | `[4,2]` | `(q²+q+1)/(q+1)` | [P/c] |
| `L₄(q)`, `Ā⁺` | `[4,1]` | `[4,2]` | **2** | 1 | `2[4,1]` | `[4,2]` | **`(q²+q+1)/(2(q+1))`** | [P/c] |
| `L₅(q)`, `Ā⁻` | `[5,1]` | `[5,2]` | 1 | 1 | `[5,1]` | `[5,2]` | `q²+1` | [P/c] |
| `L₅(q)`, `Ā⁺` | `[5,1]` | `[5,2]` | **2** | **2** | `2[5,1]` | `2[5,2]` | `q²+1` | [P/c] |
| `S₄(q)` odd, `q=p≥5` | `(q+1)(q²+1)` | `q²(q²+1)/2` | 1 | 1 | same | same | `q²/(2(q+1))` | [P/c] |
| `S₄(q)` odd, `q≠p`, `Ā` w/o `δ` | `(q+1)(q²+1)` | `t(q)ι₁` | 1 | 1 | `ι₁` | `t(q)ι₁` | `t(q)` | [P] |
| `S₄(q)` odd, `q≠p`, `Ā` with `δ` | `(q+1)(q²+1)` | `t(q)ι₁` | 1 | **≤2** | `ι₁` | `≤2t(q)ι₁` | `≤2t(q)` | [P] |
| `S₄(q)` even, `Ā⁻` | `(q+1)(q²+1)` | `t(q)ι₁` | 1 | 1 | `ι₁` | `t(q)ι₁` | `t(q)` | [P] |
| `S₄(q)` even, `Ā⁺` | `(q+1)(q²+1)` | `t(q)ι₁` | **2** | **2** | `2ι₁` | `2t(q)ι₁` | `t(q)` | [P],[C] `q=4` |
| `U₄(q)`, `q≥3` | `(q+1)(q³+1)` | `(q²+1)(q³+1)` | 1 | 1 | same | same | `(q²+1)/(q+1)` | [P/c],[C] `q=3` |
| `Sp₆(q)`, `q=p` | `(q⁶−1)/(q−1)` | `(q+1)(q²+1)(q³+1)` | 1 | 1 | same | same | `(q⁴−1)/(q³−1)` | [P/c],[C] `q=2` |
| `Sp₆(q)`, `q≠p` | `(q⁶−1)/(q−1)` | `t(q)ι₁` | 1 | `≤2` (`q` odd), 1 (`q` even) | `ι₁` | `≤2t(q)ι₁` | `≤2t(q)` | [P] |
| `U₅(q)`, `q=p` | `(q⁵+1)(q²+1)` | `q⁴(q⁵+1)/(q+1)` | 1 | 1 | same | same | `q⁴/((q+1)(q²+1))` | [P/c],[C] `q=2` |
| `U₅(q)`, `q≠p` | `(q⁵+1)(q²+1)` | `t(q)ι₁` | 1 | 1 | `ι₁` | `t(q)ι₁` | `t(q)` | [P] |
| `A_m`, `K=A_m` | `C(m,3)` | `C(m,4)` | 1 | 1 | same | same | `(m−3)/4` | [P],[C] `m≤9` |
| `A_m`, `K=S_m` | — | — | — | — | `C(m,2)` | `C(m,3)` | `(m−2)/3` | [C] `m=7,8,9` |
| `G₂(q)` | `(q⁶−1)/(q−1)` | (bound only) | ≤2 | ≤2 | `≥ι₁` | `≤2(q+1)ι₁` | `≤2(q+1)` | [P] |

`t(q) = |Λ|/|Λ ∩ F_{q₀}^×|` as in v_task32 Tool 5.
`G₂` is eliminated outright (§4au addendum, Lemma G₂-C) and needs only
the bound; `f ≤ 2` there because the graph group of `G₂` has order 2.

---

## 5.  Exhaustive GAP verification (falsification run first)

All exhaustive, no sampling.  `I(S)` reproduces §4at exactly in every
row, which is an independent re-derivation of that table.

| pair | `I(S)` | `I(S ≤ Ā)`, per `Ā` | verdict |
|---|---|---|---|
| `L₃(2) ≤ L₃(2).2` | `{7,8,21,28}` | `Ā=S`: `{7,8,21,28}`; `Ā=Aut`: **`{8,14,21,28}`** | `ι₁` class fuses (two `V₄`, index 7) — `ι₁ 7→8` (reorder!), `ι₂ 8→14` |
| `L₃(3) ≤ L₃(3).2` | `{13,52,104,117}` | `{13,…}` / **`{26,52,104,117}`** | `ι₁ 13→26`, `ι₂ = 52` fixed, `R: 4 → 2` |
| `L₃(4) ≤ L₃(4).·` | `{21,105}` | non-graph `Ā`: `{21,105,315}`; graph `Ā`: **`{42,105,315}`** | `ι₁ 21→42`, `ι₂ = 105` fixed, `R: 5 → 5/2 = (q+1)/2` |
| `L₄(2) = A₈ ≤ S₈` | `{15,35,56}` | **`{30,35,56}`** | `ι₁ 15→30`, `ι₂ = 35 = [4,2]₂` fixed, `R: 7/3 → 7/6` |
| `L₄(3)` | `{40,40,130}` — **two** classes at 40, one at 130 [C] | non-graph: `{40,130}`; graph: `{80,130}` [P, by the Remark] | `R: 13/4 → 13/8` |
| `L₅(2)` | `{31,31,155,155}` — **two** classes each [C] | non-graph: `{31,155}`; graph: `{62,310}` [P, by the Remark] | `R = 5 = q²+1` in both |
| `S₄(3) = U₄(2) ≤ .2` | `{27,40,45}` | `K=S`: `{27,40,45}` (no fusion at all); `K=Ā`: `{27,36,40,45}` | `ι₂ 40 → 36` for `K>S` (outer involution) |
| `Sp₆(2)` | `{63,63,135,135}` | `Out = 1` | pair = simple |
| `S₄(4) ≤ .2_φ / .4_γ` | `{85,85,85,85,255,255}` | `{85,255}` / **`{170,510}`** | `R = 3 = t(4)` in both |
| `S₄(5)` | `{156,156,325}` | `Out = C₂` diagonal only | pair = simple (Lemma P1) |
| `U₄(3)` | `{112,280}` (unique class each) | any `Ā` | pair = simple by (C1) |
| `U₅(2)` | `{165,176,297}` (unique class each) | any `Ā` | pair = simple by (C1) |
| `A₆ ≤ ·` (redo) | `{10,15,20,36,45}` | `Ā = S₆`: `{10,15,20,36,45}`; `Ā = PGL(2,9)`, `M₁₀`, `PΓL(2,9)`: `{10,30,36,40,45}` | reproduces v_task34 exactly; the fusing outer classes are identified as the two `C₂×C₂` classes (`D` of order 2) and the two `C₃` classes |
| `A₇/A₈/A₉ ≤ S_m` | `{35}` / `{15,35,56}` / `{84,126,135}` | `{35}` / `{30,35,56}` / `{84,126,270}` | `C(m,3), C(m,4)` never fuse |
| `S₇/S₈/S₉` (`K=Ā`) | — | `{21,35}` / `{28,30,35,56,70}` / `{36,84,126}` | `ι = C(m,2)` |

Two rows deserve comment.

* **`L₃(2)` is a genuine re-ordering,** not just a rescaling: the pair
  minimum `8` is the *old* `ι₂`, and the pair `ι₂ = 14` is the *old*
  `ι₁` doubled.  `q = 2` is outside the `L₃` family of §4at (`q ≥ 3`),
  but it shows the phenomenon is not merely multiplicative.
* **`U₄(2).2` with `K = Ā`** produces the new value `36 < 40`, from an
  outer involution.  This is the only place in the data where `K > S`
  changes anything; the effect is *downward*.

Cross-check with v_task37 PART D: it reports `A₆ ≤ PGL(2,9)` as the
unique ratio-3 pair and `L₃(3)` at ratio 4.  Both are reproduced here,
and this note adds the missing half of the second: `L₃(3)`'s ratio 4 is
the *simple-group* ratio; the **pair** ratio for `Ā = L₃(3).2` is **2**.
Anyone using "`b₂/b₁ = 4`" for `L₃(3)` must therefore use `Ā = S`.

---

## 6.  Lemma ι₂-pair-bound (the inequality form of I3, for v_task37 R1)

> **Lemma ι₂-pair-bound [PROVEN].**  Let `S` be simple with
> `ι(S) = μ(S)`, and suppose `w ∈ I(S)` satisfies `w > e·ι(S)` where
> `e := |Out(S)|`.  Then for **every** `S ≤ K ≤ Ā ≤ Aut(S)`,
>
>   **`ι(K≤Ā) ≥ ι(S)`  and  `ι₂(K≤Ā) ≤ e·w`,   hence
>    `ι₂(K≤Ā) ≤ (e·w/ι(S)) · ι(K≤Ā)`.**
>
> If moreover both the `ι(S)`-witness and the `w`-witness are
> characteristic subgroups of unipotent radicals of parabolics, `e` may
> be replaced by `2` in both places (Corollary P2 and `|Γ| ≤ 2`), giving
>
>   **`ι₂(K≤Ā) ≤ (2w/ι(S))·ι(K≤Ā)`  whenever `w > 2·ι(S)`.**

*Proof.*  Lower bound: for `1 ≠ A ≤ K` abelian, Lemma F gives
`[Ā:N_Ā(A)] ≥ [S:N_S(A)] ≥ ν(S) ≥ μ(S) = ι(S)` (Lemma TR-4).  Upper
bound: let `A₁` realise `ι(S)` and `A_w` realise `w`.  By Lemma F their
pair values are `f₁ι(S) ≤ e·ι(S) < w ≤ f_w·w ≤ e·w`.  They are therefore
**two distinct** elements of `I(K≤Ā)`, both `≤ e·w`, so the second
smallest element of `I(K≤Ā)` is `≤ e·w`. ∎

(The lemma is deliberately an inequality with no exact-table input: it
survives any additional values contributed by `A ⊄ S`, which can only
insert further elements *below* `e·w` and hence only lower `ι₂(K≤Ā)`.)

**Application to the residual families.**  Take for `w` the witness
named in the second column; `f ≤ 2` in every row by Corollary P2 / §3.

| family | `w` | `w/ι₁` | `c(q) := 2w/ι₁` (valid for) |
|---|---|---|---|
| `L₃(q)` | `Z(U_B)`, `(q+1)ι₁` | `q+1` | `2(q+1)`, `q ≥ 3` |
| `L₄(q)` | `U_{P₂}`, `[4,2]` | `(q²+q+1)/(q+1)` | `< 2(q+1)`, `q ≥ 2` |
| `L₅(q)` | `U_{P₂}`, `[5,2]` | `q²+1` | `2(q²+1)` |
| `U₄(q)` | `Z(U_{P_pt})` | `(q²+1)/(q+1)` | `< 2(q+1)`, `q ≥ 3` |
| `U₅(q)` | t.i.-line parabolic | `(q³+1)/(q²+1)` | `< 2q`, `q ≥ 2` |
| `Sp₆(q)` | Lagrangian parabolic `μ₃` | `(q⁴−1)/(q³−1)` | `< 2(q+1)` |
| `S₄(q)` | trap line / `⟨t⟩` | `≤ max(t(q), q²/(2(q+1)))` | `< 2q` |
| `G₂(q)` | Lemma G / Lemma G₂-C | `≤ q+1` | `2(q+1)` |
| `A_m` | `V₄` on a 4-set | `(m−3)/4` | `(m−3)/2` |

> **Corollary (the form v_task37 R1 asks for).**  For every residual
> family and every admissible `Ā`,
>
>   **`ι₂(K ≤ Ā) ≤ 2(q²+1)·ι(K ≤ Ā)`,**
>
> with `2(q²+1)` attained only by `L₅`; every other family satisfies the
> stronger `ι₂(K≤Ā) ≤ 2(q+1)·ι(K≤Ā)`.  In particular the R1 residue
> `ι₂(K≤Ā) > (n−3)·ι(K≤Ā)` forces `n − 3 < 2(q²+1)` on the `ι`-minimal
> factor, i.e. **`q > √((n−5)/2)`**, hence
> `|S*| ≥ |L₅(q)| > q^{24}` (or the corresponding lower bound in the
> other families, all `≥ q^8`), which is exactly the input the order
> squeeze (Lemma TO-2) needs.

*Verification that the hypothesis `w > e·ι₁` (or `w > 2ι₁`) is not
vacuous at small `q`:* the sharp form needs only `w > 2ι₁`, i.e.
`q + 1 > 2` (`L₃`), `q²+q+1 > 2(q+1)` (`L₄`, true `q ≥ 2`),
`t(q) ≥ 3` (`S₄` even non-prime — true since `q₀ ≤ q/2` forces
`t = (q−1)/(q₀−1) ≥ 3` for `q ≥ 4`), etc.  Each is checked in the table
above.

---

## 7.  Does any ratio-trick bound get WEAKER?  [the direction claim]

Write `R = ι₂(S)/ι(S)`, `R^p = ι₂(K≤Ā)/ι(K≤Ā) = (f₂/f₁)·R` (valid
whenever the same two classes win, which §3 establishes in every row).
From §§2–3, **`f₁, f₂ ∈ {1,2}` for every residual family**, so
`R^p/R ∈ {½, 1, 2}` and the three cases are:

**(i) `R^p = R/2` — `L₃`, `L₄` with a graph automorphism.**  The
ratio-trick equation `R^p = (n−3)/(4ρ)` becomes `R = (n−3)/(2ρ)`.
Writing `R = A/B` in lowest terms, the forced divisibility is
`B | 4ρ` before and `2B/gcd(2,A) | 4ρ` after — i.e. the modulus can only
**grow**.  Concretely `L₄`: `(q+1) | 4ρ ≤ 8 ⟹ q ≤ 7` becomes
`2(q+1) | 4ρ ≤ 8 ⟹ q ≤ 3`.  **Strictly tighter.**

**(ii) `R^p = R` — `L₅`, `S₄(q)` even, and every `Ā` without a graph
automorphism, and every `Ā` for `U₄`, `U₅`, `Sp₆`, `S₄(q)` odd prime,
and `A_m` with `K = A_m`.**  Nothing changes at all.

**(iii) `R^p = 2R` — and only here.**  `S₄(q)`/`Sp₆(q)` at odd
non-prime `q`, with a diagonal automorphism in `Ā`; `R = t(q)`,
`R^p = 2t(q) = (q−1)/(q₀−1)`.  Effects:

* **Divisibility kills: unaffected.**  `t(q)` and `2t(q)` are both
  integers, so `B = B^p = 1` and there was no divisibility condition to
  lose.  (This also corrects a slip worth recording: §4au's phrase
  "`t(q) ∣ 4ρ ≤ 8`" does **not** follow from `(n−3)/4 = ρ·t(q)` alone —
  that equation only *defines* `n`.  The non-prime kills of §4au are, on
  inspection, **size** kills, and should be stated as such.)
* **Size kills: weakened by a bounded factor.**  `n = 3 + 4ρ·R^p`
  doubles at most, so `C(n,3)` grows by at most `8`, against an
  unchanged `ι₁(K≤Ā) = ι₁`.  Worked out for `S₄(q)`, `q = q₀²` odd:
  `n ≤ 3 + 16t(q) ≈ 16√q`, `C(n,3) ≈ 683 q^{3/2}`, and
  `C(n,3) ≥ ι₁ ≈ q³` forces `q ≤ 77` (against `q ≤ 30` with `f₂ = 1`).
  **Still finite, still explicit; the constant roughly quadruples.**
* Also `f₂ ≤ 2` is *exact* here, not a crude `|Out|` bound (§3.4), so
  the loss cannot compound with the field-degree `f`.

**(iv) `K > S`.**  Outer abelian `A ≤ K \ S` add values to `I(K≤Ā)`,
never remove any.  Added values are `≥ ν(S) ≥ μ(S) = ι(S)` (Lemma TR-4),
so `ι` is unmoved and `ι₂` can only go **down** — the safe direction for
both the ratio trick (smaller `n`) and Lemma ι₂-pair-bound.  Observed
once, at `U₄(2).2` (`40 → 36`).  The one family where this is *not* a
minor effect is `A_m` with `K = S_m` (`ι` drops to `C(m,2)`), and there
it strengthens Theorem κ-A / Lemma TO-0.

> **Verdict.**  **No ratio-trick bound changes direction.**  Two families
> tighten, six are unchanged, one (odd non-prime `S₄`/`Sp₆` with a
> diagonal automorphism) loses a bounded constant in a size estimate and
> nothing in a divisibility estimate.  The brief's expectation
> "`ι₁` never changes" is wrong (§2), but the correction happens to push
> the ratio in the *favourable* direction in every case where it acts on
> `ι₁` alone.

---

## 8.  Caveats, honestly listed

* **(AB).**  Everything here, like §4as/§4ar/v_task37, computes over
  **abelian** `H` only.  v_task37 records that the true conductor uses
  `ind*(H) = [N_G(H):H']^{-1}|G|` over all `H`.  Which values of §4's
  table could be undercut by a non-abelian `H`?  The pair value
  `[Ā:N_Ā(H)]·|H′|` still satisfies Lemma F verbatim (`H′` is
  characteristic in `H`, and `f` is unchanged), so **§2, §3, §6 and the
  direction verdict of §7 are all insensitive to (AB)** — they are
  statements about the *fusion factor*, not about which `H` wins.  What
  (AB) can change is *which class realises `ι₂`*, hence the exact `R`
  column of §4 — and by §7(iv)-type reasoning any new smaller value only
  lowers `ι₂`.  Lemma ι₂-pair-bound is likewise safe (its upper bound is
  over a *sub*family of witnesses).
* `f₂ ≤ 2` in §3.4 uses `Λ = (F_q^×)²` for `Sp_{2n}`, an explicit
  root-datum computation, and the identification of the `ι₂`-realising
  class in v_task32 Tool 5; both are [PROVEN] there.
* The `[P/c]` rows inherit v_task32's dependence on the BHR
  maximal-subgroup tables — nothing new is added here.
* Rows marked with a `[C]` `q` are additionally confirmed by exhaustive
  GAP; the rest are proven uniformly in `q` by §§2–3 given `I(S)` from
  §4at/§4au.
* `L₃(2)` and `S₄(3) ≅ U₄(2)` are the two exceptional small members and
  behave differently from their families (re-ordering, resp. an outer
  value below `ι₂`); both `q` are outside the ranges §4at needs.

---

## 9.  Reproduce

```
~/gap-4.16.0/gap -q -o 12g LeanDring/Even/verify/v_task36_pair_invariants.g \
    > LeanDring/Even/verify/v_task36_pair_invariants_out.txt
```
The heavy rows were run as separate processes; the raw output file
concatenates them.  All arithmetic exact, all scans exhaustive below the
stated bounds.

**What did not finish.**  `FusionData` for `L₄(3)` and `L₅(2)` exceeded the
memory limit (the cost is `AutomorphismGroup` on a group of order
`6·10⁶`/`10⁷`, not the scan).  For those two rows the exhaustive
**class-multiplicity** computation *did* finish (`{40,40,130}`,
`{31,31,155,155}`) and the fusion pattern follows from the elementary
fixed-space Remark in §2 — no `AutomorphismGroup` is needed.  Likewise
`FusionData` for `U₄(3)`, `U₅(2)`, `S₄(5)` exceeded the memory limit;
there the class multiplicities settle the matter outright, since every
index value in `U₄(3)`, `U₅(2)` carries a **unique** class (so `f = 1` by
(C1) for every `Ā`) and `S₄(5)` has `Out = C₂` diagonal only (so `f = 1`
by Lemma P1).
