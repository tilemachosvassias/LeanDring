# v_task32: proofs of the `ι₂` closed forms of §4at, and three refutations

**Status of the task.**  §4at lists eight [CLAIMED] closed forms for `ι₂`, each
fitted to one or two values of `q`.  This note proves four of them for *all* `q`
in the stated range, proves three more for `q` **prime** only and **refutes**
them for every non-prime `q`, and refutes one outright except at the single `q`
where it was fitted.  A ninth section treats the `G₂(q)` upper bound requested
by the monitor.

All spot-checks are in `v_task32_iota2_proofs.g` / `..._out.txt`, each at a
value of `q` beyond the "verified at" column.

---

## 0.  Notation and the three tools

`S` is simple of Lie type over `F_q`, `q = p^f`, `Φ` its root system, `B = UT`
a Borel, `P_J` the parabolics, `U_P = O_p(P)`, `L_P = P/U_P` the Levi.  For
`1 ≠ A ≤ S` abelian, `ind(A) = [S : N_S(A)]`; equivalently `ind(A)` is the
size of the `S`-conjugacy **orbit** of the subgroup `A`.  Put
`I(S) = {ind(A)}`, `ι₁ = min I(S)`, `ι₂ = ` second smallest element of `I(S)`.

Throughout write `A = A_p × A_{p'}` (both characteristic in `A`, hence normal
in `N_S(A)`).

**Tool 1 (Borel–Tits).**  If `A_p ≠ 1` then `A_p ⊴ N_S(A)` is a nontrivial
normal `p`-subgroup, so `N_S(A)` lies in a proper parabolic `P` of `S`.  In
particular `[S:N_S(A)] = [S:P]·[P:N_S(A)]` for some maximal parabolic `P`.

**Tool 2 (every maximal parabolic index is in `I(S)`).**  `Z(U_P) ≠ 1` is
abelian and characteristic in `U_P ⊴ P`, hence normal in `P`; `P` is maximal
and self-normalising and `Z(U_P) ⋬ S`, so `N_S(Z(U_P)) = P`.  Hence
**`[S:P] ∈ I(S)` for every maximal parabolic `P`.**

**Tool 3 (Lemma R — the key index gap inside a parabolic).**
*Let `P` be a maximal parabolic with `U := U_P` **abelian** and
`C_P(U) = U`.  Let `1 ≠ A` be abelian with `N := N_S(A) ≤ P` and put
`L₀ := N U / U ≤ L_P`.  Then either*

* `A = U` *and* `N = P`; *or*
* `[P:N] ≥ c_P :=` *the minimal index in `L_P` of a subgroup that stabilises
  some nonzero proper `F_p`-subspace of `U`.*

*Proof.*  Two sub-cases.
(i) `A ≤ U`.  Since `U` is abelian, `U ≤ C_S(A) ≤ N`, so `N = U L₀` and `A` is
an `L₀`-invariant subgroup of `U`.  If `A = U` then `N = N_S(U) = P` (Tool 2).
Otherwise `A` is a nonzero proper `L₀`-invariant `F_p`-subspace, so
`[P:N] = [L_P : L₀] ≥ c_P`.
(ii) `A ⊄ U`.  Then `A ∩ U ⊴ N`, and `[A, A∩U] = 1`.  If `A ∩ U = 1` then
`[A,U∩N] ≤ A ∩ U = 1`; combined with `A U/U` abelian normal in `L₀` one gets
`A ≤ C_P(U) = U` as soon as `U ≤ N`, a contradiction; and if `U ⊄ N` then
`[P:N] ≥ [U : U∩N] ≥ p`, and `U ∩ N` is a proper `L₀`-invariant subspace, so
again `[P:N] = [L_P:L₀]·[U:U∩N] ≥ c_P`.  If `A ∩ U ≠ 1` it is a proper
`L₀`-invariant subspace of `U` (proper because `U` abelian and `A ⊄ U` would
force `A ≤ C_P(U) = U`), so `[P:N] ≥ c_P` as before.  ∎

**Corollary R′.**  If `L₀` acts irreducibly on `U` as an `F_p`-module then the
only possibility is `A = U`, `N = P`.  In particular a subgroup `N` of small
index in `P` containing `U` and inducing a group acting irreducibly on `U`
carries **no** `N_S(A)` at all.  (This is what kills the "index `d`
determinant subgroups" of `GL`-type Levis: `SL_n(q)` is irreducible on the
natural module.)

**Tool 4 (the maximal-subgroup filter).**  If `[S:N_S(A)] < X` then
`N_S(A) ≤ M` maximal with `[S:M] < X`.  For every family below `S` is a
classical group of dimension `≤ 6`, so the maximal subgroups are completely
known (Bray–Holt–Roney-Dougal, *The maximal subgroups of the low-dimensional
finite classical groups*, LMS Lecture Notes **407** (2013), Tables 8.3–8.29;
also Kantor, *J. Algebra* **60** (1979) 158–168 and Cooperstein, *Israel J.
Math* **30** (1978) 213–235 for the minimal-degree statements).  Every
non-parabolic maximal `M` in the relevant range turns out to be **almost
simple**, hence has *no* nontrivial abelian normal subgroup, hence
`M ≠ N_S(A)`; and any `N < M` proper satisfies
`[S:N] ≥ [S:M]·μ(M)` with `μ(M)` the minimal index of a proper subgroup of
`M`, which in each case exceeds the claimed `ι₂`.

**Tool 5 (the `Z(U)` subfield trap — the source of all three refutations).**
Suppose `P₁` is a maximal parabolic realising `ι₁ = [S:P₁]` whose unipotent
radical has `Z(U_{P₁}) = X_θ ≅ (F_q, +)` a **long root subgroup**, with the
Levi acting on it through a character with image `Λ ≤ F_q^×`.  For every
subfield `F_{q₀} < F_q` and every `F_{q₀}`-line `A ≤ X_θ` one has
`A ⊴ N := U_{P₁}·(Stab_{L}(A))`, and `N = N_S(A)` (see §5), whence

> **`((q−1)/e) / |Λ ∩ F_{q₀}^×| · ι₁ ∈ I(S)`,   `e = |F_q^× : Λ|`.**

If `q = p` is prime, `X_θ` has no proper nontrivial subgroup and the trap is
empty.  If `q` is **not** prime the trap always produces a value strictly
between `ι₁` and the value claimed in §4at.  This is exactly what happens for
`S₄(q)` (both parities), `Sp₆(q)` and `U₅(q)`; it does **not** happen for
`L₃, L₄, L₅, U₄` because there `N_S(X_θ)` is *not* of minimal index.

---

## 1.  `L₃(q)`, `q ≥ 3`:  `ι₂ = (q+1)(q²+q+1)`  — **PROVEN**

`S = L₃(q)`, `μ := q²+q+1 = [3,1]_q = [3,2]_q`, both maximal parabolics of
index `μ`; `[S:B] = (q+1)μ`.

*(a) `(q+1)μ ∈ I(S)`.*  `Z(U_B) = X_{α+β}` is abelian of order `q` and normal
in `B`.  A subgroup properly containing `B` is a parabolic, and neither `P_α`
nor `P_β` normalises `X_{α+β}` (`[X_{-α}, X_{α+β}] ≤ X_β ≠ 1`, likewise for
`β`).  Hence `N_S(Z(U_B)) = B` and `ind = (q+1)μ`.

*(b) Nothing lies strictly between `μ` and `(q+1)μ`.*  Let `1 ≠ A` be abelian,
`N = N_S(A)`, `[S:N] < (q+1)μ`.
* If `A_p ≠ 1`: Tool 1 gives `N ≤ P` a proper parabolic.  `P = B` is excluded
  (index already `(q+1)μ`).  So `N ≤ P₁` (or `P₂`, dual).  Here
  `U = U_{P₁} ≅ F_q²` is abelian, `C_{P₁}(U) = U`, `L = GL₂(q)`.  By Lemma R,
  either `A = U`, `N = P₁`, `ind = μ`; or `[P₁:N] ≥ c_{P₁}`.  Now `c_{P₁}` is
  the minimal index of a subgroup of `GL₂(q)` stabilising a nonzero proper
  `F_p`-subspace `W ≤ F_q²`.  If `W` is an `F_q`-line, the orbit is the
  projective line, of size `q+1`.  Otherwise, let `F_{q'}` be the largest
  subfield over which `W` is a subspace; `GL₂(q)` is transitive on nonzero
  vectors, so the orbit of `W` has size `(q²−1)/(|W|−1) ≥ (q²−1)/(q'−1) ≥ q+1`.
  Hence `c_{P₁} = q+1` and `[S:N] ≥ (q+1)μ`.  (Note this argument is *uniform
  in `q`*: it never needs the minimal index of a proper subgroup of `GL₂(q)`,
  so the exceptional small subgroups `A₅ ≤ PSL₂(5)`, `A₅ ≤ PSL₂(9), PSL₂(11)`,
  and the determinant subgroups of index dividing `q−1`, all act irreducibly
  and are killed by Corollary R′.)
* If `A_p = 1`: `N ≤ M` maximal.  By BHR Table 8.3 the non-parabolic maximal
  subgroups of `L₃(q)` are the torus normalisers `(q−1)²:S₃` and
  `((q²+q+1)/d):3`, `PGL₂(q) ≅ SO₃(q)` (order `q(q²−1)`), the subfield and
  unitary subgroups `L₃(q₀).[·]`, `U₃(q₀).[·]` (`q = q₀^r`, order `≤ q⁴·f`),
  and, for small `q`, `3²:Q₈`, `A₆`, `3.A₆`, `L₂(7)`.  We need
  `|M| > |S|/((q+1)μ) = q³(q−1)²/d`.  Every listed `M` has order `≤ c·q⁴`
  (`c` absolute) except the sporadic almost simple ones, and `q³(q−1)² > q⁴`
  for `q ≥ 3` when `d = 1` and for `q ≥ 5` when `d = 3`; the residual cases
  `q = 4` (`A₆`, index 56) and `q = 3` are almost simple, so `M ≠ N_S(A)` and
  `N < M` gives `[S:N] ≥ [S:M]·6 > (q+1)μ`.

**Verified** at the new value `q = 5`: GAP finds the maximal indices
`31, 31, 3100, 3875, 4000` and, exhaustively over all subgroups of index `≤ 6`
of a parabolic, `I(L₃(5)) ∩ [1,186] = {31, 186}` — i.e. `ι₁ = 31`,
`ι₂ = 186 = (q+1)(q²+q+1)`.  ✔

---

## 2.  `L₄(q)`:  `ι₂ = [4,2]_q = (q²+1)(q²+q+1)`  — **PROVEN**

Maximal parabolics `P_k` = stabilisers of `k`-subspaces, indices
`[4,1]_q = [4,3]_q = (q+1)(q²+1)` and `[4,2]_q = (q²+1)(q²+q+1)`; all
`U_{P_k}` are abelian (`U_{P_k} ≅ Hom(V/W, W)`).  Both indices are in `I(S)`
by Tool 2, and `[4,1] < [4,2]`.

*Nothing strictly between.*  With `A_p ≠ 1` Tool 1 puts `N` in `P₁`, `P₂` or
`P₃`.  From `P₂` every index is `≥ [4,2]`.  For `P₁` (`U ≅ F_q³`,
`L = GL₃(q)` natural), Lemma R gives `[P₁:N] = 1` (`A = U`, index `[4,1]`) or
`[P₁:N] ≥ c_{P₁}`.  As in §1, an `L`-orbit of a proper nonzero `F_p`-subspace
`W ≤ F_q³` has size `≥ [3,1]_q = q²+q+1` when the `F_q`-span of `W` is proper,
and size `≥ |GL₃(q)| / (|GL_{3f/f'}(q')|·f) ≫ q³` when `W` spans.  So
`[S:N] ≥ [4,1]·(q²+q+1) = (q+1)(q²+1)(q²+q+1) > [4,2]`.
With `A_p = 1`, Tool 4: the only non-parabolic maximal of `L₄(q)` of index
below `[4,2] ≈ q⁴` would need order `> |S|/[4,2] = q⁶(q²−1)²(q−1)/d ≈ q^{11}`;
by BHR Table 8.8 the largest non-parabolic maximals are `PSp₄(q)` (index
`q²(q³−1)·(·) ≈ q⁵ ≫ [4,2]`), `SO₄^±(q)`, `SU₄(q₀)`, `GL₂(q²)`-type and
subfield subgroups, all of index `> [4,2]`, and all almost simple or of index
already too large.

**Verified** at the new value `q = 4`: `P₁` has index `85`, a unique nontrivial
abelian normal subgroup (order `q³ = 64`, index `85`), and its only proper
subgroup of index `≤ 4` (the index-`3` determinant subgroup) carries no
`N_S(A)`, as Corollary R′ predicts; `P₂` has index `357 = [4,2]_4` and equals
`N_G(A)` for `A = U_{P₂}` of order `256`.  So `ι₁ = 85`, `ι₂ = 357`. ✔

---

## 3.  `L₅(q)`:  `ι₂ = [5,2]_q`  — **PROVEN**

Identical to §2.  `[5,1]_q < [5,2]_q < [5,3]_q = [5,2]_q` … precisely, the
maximal parabolic indices are `[5,1] = [5,4]` and `[5,2] = [5,3]`, with
`[5,2]/[5,1] = q²+1`.  Both are in `I(S)` (Tool 2, all `U_{P_k}` abelian).
For `P₁` (`U ≅ F_q⁴`, `L = GL₄(q)`) Lemma R gives `[P₁:N] ≥ c_{P₁} = [4,1]_q
= q³+q²+q+1 > q²+1`, so nothing from `P₁` lands in `([5,1],[5,2])`; from `P₂`
everything is `≥ [5,2]`.  The non-parabolic maximals (BHR Table 8.18:
`PSp₄`-free here — the relevant ones are `SO₅(q)`, imprimitive, subfield,
`SU₅(q₀)`, `5^{1+2}:Sp₂(5)`, `L₂(11)`, `M₁₁`, `U₄(2)`) all have index far
above `[5,2] ≈ q⁶`, and the almost simple ones are excluded by Tool 4.

*(Spot-check: the arithmetic identities `[5,2]/[5,1] = q²+1` and
`c_{P₁} = [4,1]_q` are exact; no new GAP run is needed beyond `q = 2` already
in §4at, since the proof is uniform.  `L₅(3)` is out of reach of an exhaustive
low-index enumeration — order `2.4·10^{11}` — and the argument above does not
depend on it.)*

---

## 4.  `U₄(q)`, `q ≥ 3`:  `ι₂ = (q²+1)(q³+1)`  — **PROVEN**

`H(3,q²)` is a GQ of order `(q², q)`: `(q+1)(q³+1)` totally isotropic **lines**
and `(q²+1)(q³+1)` isotropic **points**.  So the two maximal parabolics have
*different* indices — contrary to the remark in §4ar, `U₄` is **not** a
"duality-swapped" case — and

`ι₁ = μ₁ = (q+1)(q³+1)` (t.i.-line stabiliser),
`μ₂ = (q²+1)(q³+1)` (isotropic-point stabiliser), both in `I(S)` by Tool 2.

*Nothing strictly between.*  `P_line = U:L` with `U ≅ {A ∈ M₂(F_{q²}) :
A + Ā^T = 0}` elementary abelian of order `q⁴`, `L = GL₂(q²)` acting by
`A ↦ XAX̄^T`.  Over `F_{q²}` this module is the twisted tensor product
`V ⊗ V^{(q)}`, irreducible for `SL₂(q²)` by Steinberg; hence `U` is an
irreducible `F_q`-module for any `L₀ ≥ SL₂(q²)`, and by Corollary R′ such
`L₀` give no `N_S(A)` except `A = U`, `N = P_line`.  Any other `L₀` misses
`SL₂(q²)`, so
`[P_line : N] ≥ [SL₂(q²) : SL₂(q²) ∩ L₀] ≥ q²+1` (`≥ 6` when `q = 3`),
which already exceeds `μ₂/μ₁ = (q²+1)/(q+1)`.  From `P_point` all indices are
`≥ μ₂`.  For `A_p = 1`, Tool 4: the dangerous maximal is `PSp₄(q)`, of index
`q²(q³+1)/(·)`, which does lie in `(μ₁, μ₂)` — e.g. index `126` in `U₄(3)` —
but `PSp₄(q)` is simple for `q ≥ 3`, so it is not an `N_S(A)`, and proper
subgroups of it have index `≥ (q+1)(q²+1)` there, pushing `[S:N]` far above
`μ₂`.  The nondegenerate-point stabiliser has index `q³(q−1)(q²+1) > μ₂`.
The remaining maximals (`SO₄^±`, `(q+1)³:S₄`, subfield, `L₂(7)`, `A₇`,
`4·L₃(4)`) are of much larger index.

**Verified** at the new value `q = 4`: the line parabolic has index `325` and
`N_G(U_P) = P` with `|U_P| = 256`; the point parabolic has index `1105` and
`N_G(Z(U_P)) = P` with `|Z(U_P)| = 4`; the unique proper subgroup of the line
parabolic of index `≤ 3` (again the determinant subgroup, `abinv = [3]`)
carries no `N_S(A)`.  So `ι₁ = 325 = (q+1)(q³+1)`,
`ι₂ = 1105 = (q²+1)(q³+1)`. ✔

---

## 5.  `Sp₄(q)`:  the claimed forms are **WRONG** for `q ≠ p` (odd) and for
## `q ≠ 4` (even);  correct statements below

`W(q)` is a GQ of order `(q,q)`: both maximal parabolics have index
`μ₁ = (q+1)(q²+1)`, so `ι₂` is *not* a second parabolic index.  Write
`P₁` = isotropic-point stabiliser, `U₁ = U_{P₁} = q^{1+2}` with
`Z(U₁) = X_{2e₁} ≅ F_q` the long root subgroup, Levi `L₁ = GL₁(q) × Sp₂(q)`;
`P₂` = t.i.-line stabiliser, `U₂ ≅ Sym²(F_q²)` elementary abelian of order
`q³`, `L₂ = GL₂(q)`.

### 5.1  The trap subgroup and its normaliser

`X_{2e₁} = {x_{2e₁}(c) : c ∈ F_q}`; the Levi torus acts by
`h(λ) : c ↦ λ²c` and the `Sp₂` factor **centralises** `X_{2e₁}` (because
`2e₁ − 2e₂` is not a root).  So the group induced on `Z(U₁) ≅ F_q` is
`Λ = (F_q^×)²` (all of `F_q^×` when `q` is even).  Let `F_{q₀}` be the largest
proper subfield of `F_q` (so `q₀ = p^{f/r}`, `r` the least prime divisor of
`f`) and let `A ≤ Z(U₁)` be an `F_{q₀}`-line.  Then

* `N_{P₁}(A) = U₁ : (Stab_Λ(A) × Sp₂(q))`, of index
  `t(q) := |Λ| / |Λ ∩ F_{q₀}^×|` in `P₁`;
* `N_S(A) = N_{P₁}(A)`.  Indeed `A` is a `p`-group so `N_S(A)` lies in a
  parabolic (Tool 1); `N_{P₁}(A)` contains `X_{±2e₂}` and all of `U₁`, and the
  only proper parabolic containing that set is `P₁`.  (Note `N_{P₁}(A)`
  contains a full Sylow `p`-subgroup of `S` but **not** a Borel, so it is not
  itself parabolic — no contradiction with Tits' theorem.)

Hence **`t(q)·(q+1)(q²+1) ∈ I(S)`**, and `t(q) < q+1 ≤ (anything else)`.
Values: `q` even, `t(q) = (q−1)/(q₀−1)`; `q` odd, `t(q) = ((q−1)/2)/|(F_q^×)²
∩ F_{q₀}^×|`, which is `(q₀+1)/2` when `f = 2` and `(q−1)/(p−1)` when `f` is an
odd prime.  For `q = p` prime `Z(U₁)` has no proper nontrivial subgroup and
the trap is empty.

### 5.2  `q` even

*Claim in §4at:* `ι₂ = 3(q+1)(q²+1)`, fitted at `q = 4` only.
*Truth:* `ι₂ = ((q−1)/(q₀−1))·(q+1)(q²+1)`.  At `q = 4` the two agree
(`q₀ = 2`, `(q−1)/(q₀−1) = 3`) — the "3" is `q−1`, not a constant.  At `q = 8`
the correct value is `7·585 = 4095 = q⁴−1`, and the claimed `1755` is not even
in `I(S)`:
a subgroup of index `1755` has order `2¹²·3·7²`, i.e. contains a **full Sylow
2-subgroup**; if `A_2 ≠ 1` it lies in a parabolic at index `3`, impossible
because the parabolic has abelianisation `C₇` (GAP) and hence no quotient of
order `3` or `6`; and if `A_2 = 1` then `A` is odd abelian, `|Aut(A)|₂ ≤ 2⁵`
forces `|C_S(A)|₂ ≥ 2⁷`, while every semisimple-element centraliser in
`Sp₄(8)` (`SL₂(64)`, `SL₂(8)×SL₂(8)`, `GL₂(8)`, `GU₂(8)`, tori) has
2-part `≤ 2⁶`.  **Contradiction, so `1755 ∉ I(Sp₄(8))`.**
For `q = 16` the correct value is `5·(q+1)(q²+1)`, again `≠ 3(q+1)(q²+1)`.

### 5.3  `q` odd

*Claim in §4at:* `ι₂ = q²(q²+1)/2`, fitted at `q = 5` only.

That value is genuine and its origin is now identified: it is the index of
`C_S(t)` for the involution `t = diag(−1,−1,1,1)`, `C_S(t) = (SL₂(q) ∘
SL₂(q)).2 / {±I}`, whose centre is the image of `⟨diag(−1,−1,1,1)⟩ ≅ C₂` —
the abelian normal subgroup `A = ⟨t⟩`.  Its index is
`|Sp₄(q)| / (2·|Sp₂(q)|²) = q²(q²+1)/2`.  (The *smaller* index
`q²(q²−1)/2` of `SL₂(q²).2` is **not** in `I(S)`: the image of `SL₂(q²).2` in
`PSp₄(q)` is `PSL₂(q²).2`, almost simple, and its `.2` is a field
automorphism, not a central involution — which is exactly why `300 ∉
I(S₄(5))` in the §4at table.)

**But the claim is correct only for `q = p` prime.**  For `q = p^f`, `f ≥ 2`,
the trap of §5.1 gives `t(q)·(q+1)(q²+1) ∈ I(S)` with
`t(q) ≈ q/(2q₀) < q²/(2(q+1)) = (claimed ι₂)/ι₁`.  Explicitly the claim fails
at every non-prime odd `q`:

| `q` | `t(q)` | `t(q)·ι₁` | claimed `q²(q²+1)/2` |
|---|---|---|---|
| 9  | 2  | **1640** | 3321 |
| 25 | 3  | 48 828 | 195 625 |
| 27 | 13 | 265 720 | 266 085 |

**Verified** by GAP at the new value `q = 9`: `A = ⟨x_{2e₁}(1)⟩` of order `3`
inside `Z(U₁) ≅ F₉` has `S`-orbit of length exactly `1640 = 2·(q+1)(q²+1)`,
strictly between `ι₁ = 820` and the claimed `3321`. ✔ **REFUTED.**

**Corrected statement.**  For `q` odd,
`ι₂(S₄(q)) = min{ t(q)·(q+1)(q²+1),  q²(q²+1)/2 }`, the first term present
only for `f ≥ 2`; in particular `ι₂ = q²(q²+1)/2` **iff `q` is prime**
(`q ≥ 5`).  The proof that nothing else intervenes is the same three-case
analysis as §1: from `P₂` Lemma R gives `[P₂:N] ≥ c_{P₂} = q+1` (the Borel of
`GL₂(q)` is the smallest reducible subgroup on `Sym²`, irreducible for
`p` odd), hence `≥ (q+1)ι₁`; from `P₁`, either `A ≤ Z(U₁)` (the trap, or
`A = Z(U₁)` giving `ι₁`), or `A/Z(U₁)` is a totally isotropic subspace of
`U₁/Z(U₁)` for the commutator form, hence contained in an `F_q`-line, giving
index `≥ (q+1)ι₁`, or `A_{p'} ≠ 1` and then `N ≤ C_S(A_{p'})`, whose index is
`≥ q²(q²+1)/2` by the list of semisimple centralisers above.

---

## 6.  `Sp₆(q)`:  **PROVEN for `q = p` prime, WRONG for `q` non-prime**

Parabolic indices: `μ₁ = (q⁶−1)/(q−1)` (isotropic points),
`μ₃ = (q+1)(q²+1)(q³+1)` (Lagrangians, `U_{P₃} ≅ Sym³` abelian),
`μ₂ = (q⁴+q²+1)(q+1)(q²+1) ≈ q⁷` (t.i. planes).  So `μ₁ < μ₃ < μ₂` and the
claim `ι₂ = μ₃` needs `(μ₁, μ₃)` empty.  Note `μ₃/μ₁ = (q⁴−1)/(q³−1)`, only
just above `q`.

*`q = p` prime.*  `Z(U_{P₁}) = X_{2e₁} ≅ F_p` has no proper subgroup, so the
trap is empty.  If `A ≤ U_{P₁}` with `A ⊄ Z(U_{P₁})` then `N/U_{P₁}` acts
reducibly on the `Sp₄(q)`-module `U_{P₁}/Z`, so
`[P₁:N] ≥ ` (minimal index of a proper subgroup of `Sp₄(q)`) `≥ q³ ≫ q`.
If `A_{p'} ≠ 1` then `N ≤ C_S(a)` for `a` semisimple `≠ 1`; the largest such
centraliser is `Sp₂(q) × Sp₄(q)` of index `q⁴(q⁴+q²+1) ≈ q⁸ ≫ μ₃`.  From
`P₂`, `P₃` every index is `≥ μ₃`.  Non-parabolic maximals (BHR Table 8.28/8.29:
`Sp₂(q³).3`, `Sp₂(q) wr S₃`, `G₂(q)` and `O₆^±(q)` for `q` even, subfield
groups, `2·U₄(2)`, `L₂(13)`, …) are all almost simple or of index `≫ μ₃`.
Hence **`ι₂(Sp₆(p)) = (q+1)(q²+1)(q³+1)`**, as claimed.

*`q` non-prime.*  The trap of §5.1 applies verbatim (`Z(U_{P₁})` is again the
long root subgroup `≅ F_q`, the `Sp₄` Levi factor centralises it, the torus
acts by `λ ↦ λ²`), giving `t(q)·μ₁ ∈ I(S)` with `t(q) < (q⁴−1)/(q³−1)` for
every non-prime `q` (`q = 4 : 3 < 4.05`; `q = 8 : 7 < 8.01`;
`q = 9 : 2 < 9.01`; `q = 16 : 5 < 16`; `q = 27 : 13 < 27`).
**Verified** by GAP at the new value `q = 4`: `A` of order `2` inside
`Z(U_{P₁}) ≅ F₄` has orbit `4095 = 3·1365`, strictly between `ι₁ = 1365` and
the claimed `5525`. ✔ **REFUTED for `q` non-prime.**

---

## 7.  `U₅(q)`:  **PROVEN for `q = p` prime (`q ≠ 4` anyway), WRONG for `q`
## non-prime**

`ι₁ = (q⁵+1)(q²+1)` = number of isotropic points = index of `P₁`;
the other maximal parabolic (t.i.-line stabiliser) has index `(q⁵+1)(q³+1)`.

*Identification of the claimed value.*  `q⁴(q⁵+1)/(q+1)` is **exactly the
number of nondegenerate points** of the unitary space:
`(q^{10}−1)/(q²−1) − (q⁵+1)(q²+1) = q⁴(q⁵+1)/(q+1)` (verified in GAP for
`q = 2,3,4,5,8,9`).  The stabiliser is `GU₄(q)`-type, and its centre in
`PSU₅(q)` is cyclic of order `(q+1)/gcd(5,q+1)`, which is nontrivial for every
`q ≥ 2` **except `q = 4`** (where `q+1 = 5 = gcd`, the centre collapses into
`Z(SU₅)` and the stabiliser becomes almost simple).  So for `q ≠ 4` this index
is in `I(S)` with `A = ` that centre.

*`q = p` prime.*  `Z(U_{P₁}) ≅ F_p`: the trap is empty.  The remaining
candidates inside `P₁` are `A/Z(U_{P₁})` totally isotropic for the Hermitian
commutator form on `U_{P₁}/Z ≅ F_{q²}³`, whose Witt index is 1, so
`[P₁:N] ≥ q³+1` — index `≥ (q³+1)ι₁ ≫` the claim; and `A_{p'} ≠ 1` forces
`N ≤ C_S(a)`, whose minimal index over semisimple `a ≠ 1` is exactly the
nondegenerate-point index `q⁴(q⁵+1)/(q+1)` (the next one, the nondegenerate
2-space stabiliser `GU₃ × GU₂`, is larger).  So
**`ι₂(U₅(p)) = q⁴(q⁵+1)/(q+1)`**, and `< (q⁵+1)(q³+1)` for all `q`.

*`q` non-prime.*  Trap again: the Levi `GL₁(q²)` acts on
`Z(U_{P₁}) = {x ∈ F_{q²} : x + x̄ = 0} ≅ F_q` by the **norm**, which is onto
`F_q^×`; so `((q−1)/(q₀−1))·ι₁ ∈ I(S)`, and

| `q` | `((q−1)/(q₀−1))·ι₁` | claimed `q⁴(q⁵+1)/(q+1)` |
|---|---|---|
| 4 | 52 275 | 52 480 |
| 8 | 14 909 895 | 14 913 536 |
| 9 | 9 684 200 | 38 742 705 |

so the claim fails at every non-prime `q` (and at `q = 4` doubly: the claimed
subgroup is centreless there).  **REFUTED for `q` non-prime.**

---

## 8.  What this does to §4at's ratio table

The ratio trick uses `(n−3)/4 = ρ · ι₂/ι₁`, `ρ ∈ {½,1,2}`.  For the three
refuted families the corrected ratio for non-prime `q` is
`ι₂/ι₁ = t(q) = (q−1)/(q₀−1)` (up to the factor of 2 in the odd case).  The
forced condition becomes `t(q) ∣ 4ρ ≤ 8`, i.e.

* `q = q₀²`:  `t = q₀+1 ≤ 8` ⟹ `q₀ ≤ 7`, finitely many `q`;
* `f` an odd prime:  `t = (q−1)/(p−1) ≤ 8` ⟹ `q ≤ 8` for `p = 2`, tiny
  otherwise.

So **the finiteness conclusions of §4at survive** — indeed they get *easier*,
because the corrected `ι₂/ι₁` is a much smaller and more rigid function of
`q`.  What must be redone is the arithmetic of the `S₄`, `Sp₆`, `U₅` rows: the
prime-`q` sub-case uses the old (now proven) formula, and the non-prime
sub-case uses `t(q)`.

---

## 9.  `G₂(q)`:  the requested upper bound  `ι₂ ≤ (q+1)·ι₁`

Set `α` short, `β` long simple roots, `Φ⁺ = {α, β, α+β, 2α+β, 3α+β, 3α+2β}`
with long roots `β, 3α+β, θ := 3α+2β`.  Both maximal parabolics have index
`μ = (q⁶−1)/(q−1) = ι₁` (the split Cayley hexagon has equally many points and
lines), and `[S:B] = (q+1)μ`.

> **Lemma G.**  `(q+1)·ι₁ ∈ I(G₂(q))` whenever `p = 3`; and
> `ι₂(G₂(q)) ≤ ((q−1)/(q₀−1))·ι₁ < (q+1)·ι₁` whenever `q` is **not** prime.
> Hence `ι₂(G₂(q)) ≤ (q+1)·ι₁` for all `q` with `p = 3` or `q` non-prime —
> in particular for the computed anchors `q = 3` and `q = 4`.

*Proof.*  (i) `p = 3`.  Put `A = ⟨X_{α+β}, X_{2α+β}, X_{3α+β}, X_θ⟩`.  The set
of roots involved is an ideal of `Φ⁺` (adding any positive root to any of them
either leaves the set or leaves `Φ`), so `A ⊴ B`.  The only commutator that
could be nonzero is `[x_{α+β}(t), x_{2α+β}(u)] = x_θ(3tu)`, whose structure
constant is `3`; in characteristic `3` it vanishes, so `A` is **abelian**.
`A` is not normal in `P_α`: `X_{−α}` moves `X_{α+β}` into `X_β ⊄ A`
(`β, α+β, 2α+β, 3α+β` is an `α`-string).  `A` is not normal in `P_β`:
`X_{−β}` moves `X_{α+β}` into `X_α ⊄ A`.  Since the only subgroups properly
containing `B` are parabolic, `N_S(A) = B` and `ind(A) = (q+1)μ`.
(ii) `q` non-prime.  `Z(U_{P_α}) = X_θ ≅ F_q` is the long root subgroup and
`N_S(X_θ) = P_α`, the parabolic whose Levi is orthogonal to `θ`; the Levi acts
on `X_θ` through a character with image `F_q^×`.  A subgroup of order `p` in
`X_θ` lies in no other root subgroup, so `N_S(A) ≤ N_S(X_θ) = P_α`, and the
`F_{q₀}`-line `A` has `P_α`-orbit of length `(q−1)/(q₀−1)`.  ∎

**Caveat on the mechanism suggested in the task brief.**  The proposed witness
— "`A` an `F_q`-line in `Z(U_{P₂})`, the long-root subgroup" — does **not**
give `B`.  `Z(U_{P_β}) = ⟨X_{3α+β}, X_θ⟩` is the natural `SL₂`-module for the
Levi of `P_β`, so all `q+1` of its `F_q`-lines are conjugate under `P_β` and
each is a **long root subgroup**, whose normaliser is a conjugate of `P_α` —
index `μ = ι₁`, not `(q+1)ι₁`.  Likewise `Z(U_B) = X_θ` gives `P_α`, and the
abelian ideals `⟨X_{3α+β},X_θ⟩` and `⟨X_{2α+β},X_{3α+β},X_θ⟩` are both normal
in `P_β`, again giving `μ`.  For `q = p ≥ 5` (char `≠ 3`, `q` prime) **neither
branch of Lemma G applies**, and I could not produce any `A` with
`N_S(A) = B`: for `p ≥ 5` every abelian normal subgroup of `B` contained in
`U` is a `T`-invariant abelian ideal, and each of the four abelian ideals is
normal in a maximal parabolic.  So the bound `ι₂ ≤ (q+1)ι₁` is
**open for `q = p ≥ 5`** and should not be assumed there.  This is consistent
with v_task30's finding that `ι₂(G₂(q))` is a `q mod 3`-dependent minimum of
several candidates.  A further prediction worth checking against v_task30:
for `q` non-prime the trap value `((q−1)/(q₀−1))·ι₁` should appear — at
`q = 4` that is `3·1365 = 4095`, well below the reported realised `6825`.

---

## 10.  Summary of verdicts

| family | claimed `ι₂` | verdict |
|---|---|---|
| `L₃(q)`, `q ≥ 3` | `(q+1)(q²+q+1)` | **PROVEN** (all `q`); new check `q = 5` exhaustive |
| `L₄(q)` | `[4,2]_q` | **PROVEN-mod-cited-fact** (BHR max-subgroup tables); new check `q = 4` |
| `L₅(q)` | `[5,2]_q` | **PROVEN-mod-cited-fact** (BHR); proof uniform in `q` |
| `U₄(q)`, `q ≥ 3` | `(q²+1)(q³+1)` | **PROVEN-mod-cited-fact** (BHR); new check `q = 4` |
| `S₄(q)`, `q` odd | `q²(q²+1)/2` | **WRONG** for `q` non-prime; PROVEN for `q = p ≥ 5`.  Refuted at `q = 9` (`1640 < 3321`) |
| `S₄(q)`, `q` even | `3(q+1)(q²+1)` | **WRONG**; correct value `((q−1)/(q₀−1))(q+1)(q²+1)`.  The `3` is `q−1` at `q = 4`.  Refuted at `q = 8` (`ι₂ = 4095`, and `1755 ∉ I(S)`) |
| `Sp₆(q)` | `(q+1)(q²+1)(q³+1)` | **WRONG** for `q` non-prime; PROVEN for `q = p`.  Refuted at `q = 4` (`4095 < 5525`) |
| `U₅(q)` | `q⁴(q⁵+1)/(q+1)` | **WRONG** for `q` non-prime; PROVEN for `q = p`; also fails at `q = 4` for a second reason (centreless stabiliser) |
| `G₂(q)` | — (upper bound requested) | `ι₂ ≤ (q+1)ι₁` **PROVEN for `p = 3` and for `q` non-prime**; **open for `q = p ≥ 5`**; the suggested witness does not work (§9) |

**One structural takeaway.**  All three refutations have a single cause
(Tool 5): when the parabolic of *minimal* index is the normaliser of a long
root subgroup `X_θ ≅ F_q` — which happens exactly for `Sp₂ₙ` and for the
isotropic-point parabolic of `U₅` — the `F_p`-subspaces of `X_θ` produce
indices `t(q)·ι₁` with `t(q)` a subfield-index ratio.  These are invisible at
`q` prime, which is precisely where every §4at row was fitted (`q = 4` for
`S₄` even being the one non-prime fit, and there `t(4) = 3` coincided with
the guessed constant).  Any future `ι`-type closed form fitted only at prime
`q` should be re-tested at `q = p²` before being believed.
