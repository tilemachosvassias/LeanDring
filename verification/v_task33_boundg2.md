# v_task33: **Bound G₂** for `q = p ≥ 5` — proven, with constant `c(q) = (q+1)/2`

This closes the single open input of the G₂ elimination (§4au item 1,
`v_task32_iota2_proofs.md` §9).  Script/output: `v_task33_boundg2.g`,
`v_task33_boundg2_out.txt`.

Notation as in v_task32: `S = G₂(q)` simple, `q = p^f`, `ind(A) = [S:N_S(A)]`
for `1 ≠ A ≤ S` abelian, `I(S) = {ind(A)}`, `ι₁ = min I(S)`, `ι₂ =` second
smallest.  For `q ≥ 3`, `ι₁ = μ = (q⁶−1)/(q−1)` (both maximal parabolics,
Tool 2 of v_task32).

---

## 1.  The witness: the centre of a maximal-rank `A₂`-subsystem subgroup

`G₂` is both simply connected and adjoint, so `Z(S) = 1` and, by
Steinberg's theorem, **centralisers of semisimple elements in the algebraic
group `G = G₂` are connected**.

Let `p ≥ 5` and `q = p`.  Then `3 ∤ q`, so `q ≡ ±1 (mod 3)` and exactly one
of `3 ∣ q−1`, `3 ∣ q+1` holds.

**Definition.**  Let `Σ ⊆ Φ(G₂)` be the subsystem of **long** roots,
`Σ ≅ A₂` (Borel–de Siebenthal: `A₂` is the maximal-rank subsystem obtained
by deleting the short simple root from the extended diagram).  Let
`H := ⟨X_γ : γ ∈ Σ⟩ ≤ G`, so `H ≅ SL₃` (simply connected, since `G` is and
`Σ` is closed of maximal rank with `Z(H) ≤ Z(G)·(torus)`; concretely `H` is
the `A₂` Levi-type subsystem subgroup of `G₂`).  Twisting the Frobenius by
the graph automorphism of `Σ` (realised inside `G` by an element of
`N_W(Σ)`, since `N_W(Σ)/W(Σ) ≅ C₂`) gives the two `F`-forms

* `H^F = SL₃(q)`, `Z(H^F) ≅ C_{gcd(3,q−1)}`;
* `H^F = SU₃(q)`, `Z(H^F) ≅ C_{gcd(3,q+1)}`.

Both `SL₃(q).2` and `SU₃(q).2` occur in `G₂(q)` (Kleidman, *The maximal
subgroups of the Chevalley groups `G₂(q)` with `q` odd, …*, J. Algebra **117**
(1988) 30–71, Theorem A; also Cooperstein 1981).  Their orders:

```
|G₂(q)| = q⁶(q⁶−1)(q²−1),  |SL₃(q)| = q³(q³−1)(q²−1),  |SU₃(q)| = q³(q³+1)(q²−1)
```

hence

> `[S : SL₃(q).2] = q³(q³+1)/2`,   `[S : SU₃(q).2] = q³(q³−1)/2`.   (1)

**Choice of `A`.**  Pick the form for which the centre is nontrivial:
`ε := +1` if `3 ∣ q−1` (use `SL₃(q)`), `ε := −1` if `3 ∣ q+1` (use
`SU₃(q)`).  Put `K := SL₃^ε(q) ≤ S` and

> `A := Z(K) ≅ C₃`.

`A ≠ 1` and abelian, so `ind(A) ∈ I(S)`.

---

## 2.  `N_S(A) = K.2`, of index `q³(q³+ε)/2`

**Lemma G₂-C.**  *Let `p ≥ 5`, `z` a generator of `A` (so `z` is semisimple of
order 3).  Then `C_S(z) = K` and `N_S(A) = K.2 = N_S(K)`, so*

> `ind(A) = q³(q³+ε)/2`.

*Proof.*  `z ∈ Z(K)` so `K ≤ C_S(z)`.  Let `z̄` be `z` viewed in the algebraic
group `G`; `C_G(z̄)` is connected (Steinberg, `G` simply connected) and
reductive of maximal rank, with root system
`Φ_z = {γ ∈ Φ : γ(z̄) = 1}`, a closed subsystem containing `Σ ≅ A₂`.  The
closed subsystems of `Φ(G₂)` are `∅, A₁, Ã₁, A₁×Ã₁, A₂, Ã₂, G₂`; the only one
properly containing the long `A₂` is `G₂` itself.  If `Φ_z = Φ` then
`z̄ ∈ Z(G) = 1`, contradicting `|z| = 3`.  Hence `Φ_z = Σ` and
`C_G(z̄) = H`; taking `F`-fixed points (and `C_G(z̄)` connected, so
`C_S(z) = (C_G(z̄))^F`) gives `C_S(z) = H^F = K`.

Since `A = ⟨z⟩` is cyclic of order 3, `C_S(A) = C_S(z) = K` and
`N_S(A)/C_S(A) ↪ Aut(C₃) ≅ C₂`.  Conversely `N_W(Σ)/W(Σ) ≅ C₂` supplies an
element `n ∈ N_S(K)` inducing the graph automorphism of `K`, which inverts
`Z(K) = A`; so `n ∈ N_S(A) ∖ C_S(A)`.  Therefore `N_S(A) = K.2` and (1)
gives the index.  ∎

*(No maximal-subgroup list is needed: the argument is a centraliser
computation.  Kleidman is cited only for the ambient fact that `K` exists in
`S`, itself immediate from Borel–de Siebenthal.)*

**Spot-check, `q = 5`** (`3 ∣ q+1`, `ε = −1`; `v_task33_boundg2_out.txt`):
in the ATLAS permutation group `G₂(5)` of degree 3906, the maximal subgroup
`M` of index `7750` has `|M| = 756000`, `M' = 3.U₃(5)` of order `378000`,
`A := Z(M') ≅ C₃`, and GAP returns

```
|C_G(A)| = 378000 (index 15500) ;  |N_G(A)| = 756000 (index 7750) ;  N_G(A) = M
[N:C] = 2 ;  q³(q³−1)/2 = 7750
```

i.e. `C_S(A) = SU₃(5)` and `N_S(A) = SU₃(5).2` exactly, index
`7750 = ι₂(G₂(5))`. ✔  (Consistency at non-prime `q = 4`, where `3 ∣ q−1`:
`q³(q³+1)/2 = 2080`, matching the maximal subgroup `3.L₃(4).2₃` of index 2080
in v_task30's table. ✔)

---

## 3.  Bound G₂

**Theorem (Bound G₂, `q = p ≥ 5`).**

> `ι₂(G₂(q)) ≤ c(q)·ι₁`  with  `c(q) = (q+1)/2`,  `ι₁ = (q⁶−1)/(q−1)`.

More precisely `ι₂ ≤ q³(q³+ε)/2` with `ε = ±1` as in §1, i.e.
`ι₂/ι₁ ≤ q³(q−1)/(2(q³−ε))`.

*Proof.*  By Lemma G₂-C, `q³(q³+ε)/2 ∈ I(S)`.  It exceeds `ι₁`: for `q ≥ 5`,
`ι₁ = (q⁶−1)/(q−1) < q⁶/(q−1) ≤ q⁶/4`, while
`q³(q³+ε)/2 ≥ q³(q³−1)/2 > q⁶/4`.  A value of `I(S)` strictly above `ι₁` is
`≥ ι₂` only in the wrong direction — rather, since `ι₂` is the *second
smallest* element of `I(S)` and `q³(q³+ε)/2 ∈ I(S) ∖ {ι₁}`, we get
`ι₂ ≤ q³(q³+ε)/2`.

Dividing by `ι₁ = (q⁶−1)/(q−1)`:

```
      q³(q³+ε)/2 · (q−1)     q³(q³+ε)(q−1)     q³(q−1)
c₀ := ───────────────────  = ─────────────  = ─────────  ,
             q⁶ − 1            2(q⁶ − 1)       2(q³ − ε)
```
using `q⁶−1 = (q³+ε)(q³−ε)`; explicitly `c₀ = q³(q−1)/(2(q³−1))` when `ε = +1` and
`c₀ = q³(q−1)/(2(q³+1))` when `ε = −1`; the former is the larger, so
`c₀ ≤ q³(q−1)/(2(q³−1))` always.  Finally

```
q³(q−1)/(2(q³−1)) < (q+1)/2   ⟺   q³(q−1) < (q+1)(q³−1)
                              ⟺   q⁴ − q³ < q⁴ + q³ − q − 1
                              ⟺   0 < 2q³ − q − 1,
```
true for all `q ≥ 2`.  Hence `c(q) = (q+1)/2` works.  ∎

Sharpness at `q = 5`: `c₀ = 500/252 = 1.984`, `ι₂ = 7750 = c₀·3906`, against
the bound `c(5) = 3`. ✔

**Combined with v_task32 §9** (`p = 3`: `c = q+1`; `q` non-prime:
`c = (q−1)/(q₀−1) < q+1`), we now have **unconditionally**

> **`ι₂(G₂(q)) ≤ (q+1)·ι₁` for every `q ≥ 3`**, and `≤ ((q+1)/2)·ι₁` for
> `q = p ≥ 5`.

So the constant assumed by §4au's elimination is now proven, and the
elimination of v_task30 stands as written with **no re-run needed**.  The
tightened constant is used below anyway, as a second, independent pass.

---

## 4.  Re-run of the ratio-trick elimination for G₂

The ratio trick gives `n − 3 = 4ρ·(ι₂/ι₁)`, `ρ ∈ {½, 1, 2}`, hence
`n ≤ 3 + 8c(q)`.  With `c(q) = (q+1)/2` for prime `q ≥ 5` and `c(q) = q+1`
elsewhere (`v_task33_boundg2.g`, part 2):

| `q` | `c(q)` | `n_max` | verdict |
|---|---|---|---|
| 3 | 4 | 35 | `ι₁ = 364 ∣ C(n,3)` only for `n ∈ {14, 28}`; ratio-forced set is `n = 3+16ρ ∈ {11,19,35}` — **disjoint** |
| 4 | 5 | 43 | no `n ≤ 43` with `1365 ∣ C(n,3)` |
| 5 | 3 | 27 | `C(27,3) = 2925 < ι₁ = 3906` — **size-impossible** |
| 7 | 4 | 35 | `C(35,3) = 6545 < 19608` — size-impossible |
| 8 | 9 | 75 | no `n ≤ 75` with `37449 ∣ C(n,3)` |
| 9 | 10 | 83 | no `n ≤ 83` with `66430 ∣ C(n,3)` |
| 11 ≤ q ≤ 37 | — | — | all size-impossible (`C(n_max,3) < ι₁`), see output |
| `q > 37` | — | — | `ι₁ ~ q⁵` beats `C(8q+12,3) = O(q³)`; monotone, so size-impossible |

(The tail is uniform: `C(3+8(q+1),3) < (8q+11)³/6 < q⁵ − q⁴ < ι₁` for
`q ≥ 11`, using the crudest constant `c = q+1`.)

**Verdict: the `G₂(q)` family is eliminated outright for every `q ≥ 3`, now
unconditionally.**  (`q = 2` is excluded from the family — `G₂(2)′ ≅ U₃(3)`
is handled in the `U₃` row; cf. the `28 / C(8,3) = 56` coincidence noted in
§4au(1).)

---

## 5.  Gaps / caveats

1. **Existence of the subsystem subgroup.**  `SL₃(q) ≤ G₂(q)` and
   `SU₃(q) ≤ G₂(q)` are used as known (Borel–de Siebenthal + Kleidman 1988,
   Theorem A, which lists `SL₃(q).2` and `SU₃(q).2` as maximal for `q > 2`).
   This is standard, citable group theory; no number theory is involved.
2. **Steinberg connectedness** is applied to `G₂` simply connected — correct,
   and the subsystem classification of `Φ(G₂)` is finite and explicit.
3. The argument needs `3 ∤ q`, i.e. `p ≠ 3`; `p = 3` is covered by
   v_task32 §9(i) (char-3 abelian ideal, `c = q+1`).  So the two branches
   together cover all prime `q`, and v_task32 §9(ii) covers `q` non-prime.
   **No `q` is left open.**
4. Only `q = 5` was spot-checked structurally (that is the only prime `q ≥ 5`
   for which `G₂(q)` is computationally reachable); the `q = 4` consistency
   check corroborates the `ε = +1` branch.
5. The bound is an *upper* bound only.  Whether `ι₂(G₂(p)) = q³(q³+ε)/2`
   exactly for all `p ≥ 5` is not claimed (it is true at `q = 5`); the
   elimination does not need it.
