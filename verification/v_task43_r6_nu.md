# Task 43 — residue **R6** / input **I12**: exact `ν(S)` for `HS, McL, Co₃, Fi₂₄′`,
# and the closure of branch (0) of Theorem TO′

Date 2026-08-07.  **NOTES.md not edited.**
Answers the residue **R6** of `v_task42_to_prime.md` §3.2 (input **I12**).

| file | what it does |
|---|---|
| `v_task43_r6_nu.g` / `_out.txt` | exact `ν(S)` for the four R6 groups (Lemma NU + Lemma SP recursion over CTblLib `Maxes`), the branch-(0) window test with the exact `ν`, an all-`n` 2-part certificate per row, and Lemma R6-Fi for `Fi₂₄′` |

**Headline.**

> `ν(HS) = 1100`, `ν(McL) = 15400`, `ν(Co₃) = 128800`, `ν(Fi₂₄′) = 306936`.
> Every one of the four R6 windows is **empty**, and in fact each row is
> empty for **all** `n`, not merely on its window.  **R6 / I12 is
> discharged; branch (0) of Theorem TO′ is closed unconditionally.**

Two of the four values come from the **outer** branch of `ν` (`HS`, `Fi₂₄′`),
two from the inner branch (`McL`, `Co₃` — `Out(Co₃) = 1`).  Three rows die
purely on the numbers; `Fi₂₄′` needs one extra lemma (R6-Fi), because there
`ν = μ` and the v_task42 window is reproduced **exactly** by the true `ν`.

---

## 0. The definition actually used

`v_task34_transport.md` §0:

  **`ν(S) := min { [S : N_S(A)] : 1 ≠ A ≤ Aut(S) abelian }`  (`≤ ι(S)`)**,

i.e. `A` ranges over abelian subgroups of `Aut(S)` and the normalizer is taken
**inside `S`** (equivalently inside `Inn(S)`).  This is the quantity entering
`F = ν_min²` in Lemma TR-2 and `Φ = min(F, |S_min|)` in TR-3.  It is *not*
`ι(S) = min{[S:N_S(A)] : 1 ≠ A ≤ S}`; the difference is exactly the outer
branch, and for `HS` and `Fi₂₄′` the difference is real.

## 1. Lemma NU — the reduction that makes `ν` computable  **[PROVEN]**

> Let `S` be non-abelian simple, `S = Inn(S) ⊴ Aut(S)`, `1 ≠ A ≤ Aut(S)`
> abelian, `A₀ := A ∩ Inn(S)`.
>
> * If `A₀ ≠ 1`: `Inn(S) ⊴ Aut(S)`, so anything normalising `A` normalises
>   `A₀`; hence `N_S(A) ≤ N_S(A₀)` and `[S:N_S(A)] ≥ [S:N_S(A₀)] ≥ ι(S)`.
> * If `A₀ = 1`: `A ↪ Out(S)`.  Pick `x ∈ A` of prime order; then
>   `N_S(A) ≤ N_S(⟨x⟩) = C_S(x)` when `|x|` is prime (a `p`-element of
>   `Aut(S)` outside `Inn(S)` with `⟨x⟩ ∩ Inn(S) = 1`, so normalising `⟨x⟩`
>   means inducing an automorphism of `C_p`, hence centralising if we take the
>   minimum over the classes).
>
> Hence **`ν(S) = min( ι(S), ν_out(S) )`**,
> `ν_out(S) := min{ [S : C_S(x)] : x ∈ Aut(S)\Inn(S) of prime order }`.

For all four groups `|Out(S)| ∈ {1,2}`, so `ν_out` is the minimum **outer
involution** `S`-class size, and for `τ` outer `τ^{S.2} = τ^S` (as
`S.2 = S⟨τ⟩` and `τ` centralises itself), so

  **`[S : C_S(τ)] = |τ^{S.2}|` = the class size read off the character table
  of `S.2`.**

`ι(S)` is taken from Lemma SP of `v_task39_sporadic_iota.md`
(`ι(S) = ilow(S)`, recursion over CTblLib `Maxes` with
`ClassPositionsOfFittingSubgroup`); the script **recomputes** it and re-checks
`EXACT = true` for all four.

## 2. The four values

| `S` | `|Out|` | `ι(S)` (witness `M`) | `ν_out(S)` (outer class) | **`ν(S)`** | branch |
|---|---|---|---|---|---|
| `HS` | 2 | `3850` (`2⁴.S₆`) | **`1100`** (`2c` of `HS.2`, `C_{HS}(τ) = S₈`) | **`1100`** | outer |
| `McL` | 2 | **`15400`** (`3^{1+4}:2S₅`) | `113400` (`2b` of `McL.2`) | **`15400`** | inner |
| `Co₃` | 1 | **`128800`** (`3⁵:(2×M₁₁)`) | — (`Out = 1`) | **`128800`** | inner |
| `Fi₂₄′` | 2 | `4860485028` (`2.Fi₂₂.2`) | **`306936`** (`2c` of `Fi₂₄`, `C_{Fi₂₄′}(τ) = Fi₂₃`) | **`306936`** | outer |

All four are **exact** (`ι` exact by Lemma SP with matching recursive lower
bound; `ν_out` exact because it is a character-table class size).  Note
`ν(Fi₂₄′) = 306936 = μ(Fi₂₄′)` — TR-4's bound `ν ≥ μ` is **attained**, so the
v_task42 window for `Fi₂₄′` does *not* shrink at all (§3).  For `M₁₁`
(v_task42's proof of concept) the same lemma gives `ν = ι = 55` since
`Out(M₁₁) = 1`.

## 3. The window checks (branch (0) of Theorem TO′)

Test, per `v_task42_to_prime.md` §3, applied with the **exact** `ν` and the
**exact** `ι` (v_task42 used `ν ≥ μ` and `ι ≤ ι_ub`, both conservative):

* **(III.1) trigger** `Φ = min(ν(S)², |S|) ≤ C(n,3)` — gives `n ≥ n₀`;
* **(III.3)** `ℓ ≥ ℓ_min = ⌈C(n,3)/(|Out(S)|·ι(S))⌉` and `|S|^ℓ ∣ n!/2`
  (checked exactly prime by prime: `ℓ·v_p(|S|) ≤ v_p(n!) − [p=2]`; this
  contains both the ORDER cap and the `p`-part filter).

**Lemma R6-CERT (all-`n`, closed form).**  `ℓ_min ≥ C(n,3)/K ≥ (n−2)³/(6K)`
with `K := |Out(S)|·ι(S)`, while `v_2(n!) − 1 ≤ n − 2`.  So `|S|^{ℓ_min} ∣ n!/2`
forces `(n−2)² ≤ 6K/v_2(|S|)`, i.e. `n ≤ n_max := 2 + ⌊√(6K/v₂(|S|))⌋`.
The row is empty for **all** `n` as soon as `n_max < n₀`.

```
S       nu(S)      Phi=min(nu^2,|S|)    n0      n_max   verdict
HS      1100          1210000           195       73    EMPTY for ALL n
McL     15400       237160000          1126      164    EMPTY for ALL n
Co3     128800    16589440000          4636      279    EMPTY for ALL n
Fi24'   306936    94209708096          8270    52703    window survives
```

* `HS`: v_task42's window was `71 ≤ n ≤ 75`; with the exact `ν = 1100` the
  trigger does not even start until `n = 195`.  **Window empty; row empty for
  all `n`.**
* `McL`: window was `78 ≤ n ≤ 144`, trigger now starts at `n = 1126`.
  **Empty; row empty for all `n`.**
* `Co₃`: window was `79 ≤ n ≤ 210`, trigger now starts at `n = 4636`.
  **Empty; row empty for all `n`.**
* The brute-force enumeration in the script confirms this independently:
  `0` values of `n` in `[n₀, 2·10⁵]` pass the exact divisibility test for
  these three.

### `Fi₂₄′` — the one row that needs an argument

Because `ν(Fi₂₄′) = μ(Fi₂₄′) = 306936` exactly, `n₀ = 8270` is unchanged and
the enumeration reproduces v_task42's window verbatim: **34412 values of `n`,
`8270 ≤ n ≤ 42681`, `ℓ_min` from `10` to `1333`, all passing the exact
`|S|^ℓ ∣ n!/2` test.**  So exact `ν` alone does *not* close this row — the
task's expectation fails here, and the reason is instructive: the generic test
is conservative in **both** slots simultaneously, allowing the floor to be
realised by an **outer** abelian `A` (`ν = 306936`) while allowing the pair
value to be as large as `|Out|·ι = 2·4.86·10⁹`, i.e. as if only **inner** `A`
existed.  The same component `K_i ≤ Ā_i` governs both.

> **Lemma R6-Fi [PROVEN].**  Branch (0) is empty for every `n` when the
> `Φ`-owning socle factor is `S = Fi₂₄′`.
>
> *Proof.*  Write `ν = 306936`, `ι = 4860485028`, `|Out| = 2`,
> `ℓ ≥ ℓ_min = ⌈C(n,3)/(|Out|·ι)⌉` (Lemma TO′-0.1, (III.3)).
>
> **(K1)** If some component `K_i` of `K` contains an outer automorphism of
> `S`, then `K_i = Aut(S)` and `A = ⟨τ⟩ ≤ K_i` is abelian with
> `[Ā:N_Ā(A)] ≤ |Out|·[S:C_S(τ)] = 613872`; so `ℓ_min ≥ C(n,3)/613872` and
> Lemma R6-CERT gives `n ≤ 420`, against the trigger `n ≥ 8270`.  Empty.
>
> **(K2)** Otherwise every abelian `A ≤ K` whose `π_i`-image is outer has
> `s := |supp(A)| ≥ 2` (an `A` with `supp(A) = {i}` lies in `K_i ≤ Inn(S_i)`),
> and TR-2's *sharp* form applies:
> `|A^T| ≥ (ℓ_i/s)·∏_{j∈supp A} ν(S_j) ≥ (ℓ_i/s)·ν_min^s`.
> * `s ≥ 3`: `|A^T| ≥ ν³ = 2.89·10¹⁶ > C(52703,3) = 2.44·10¹³`, and
>   `n ≤ 52703` on the whole window by R6-CERT.  So `Φ > C(n,3)`: empty.
> * `s = 2` with `supp(A)` meeting the `Fi₂₄′` orbit:
>   `|A^T| ≥ (ℓ/2)·ν² ≥ C(n,3)·ν²/(4|Out|ι) = 2.4228…·C(n,3) > C(n,3)`,
>   so again `Φ > C(n,3)` and branch (0)'s condition (III.1) fails.  Empty.
> * `s = 2` with `supp(A)` disjoint from the `Fi₂₄′` orbit: then both
>   participating factors `S_j` satisfy `ν(S_j)² ≤ |A^T| ≤ C(n,3)`, so each
>   `S_j` triggers branch (0) **in its own row**, and every other row is
>   empty (v_task42 sweep 2: all Lie/Suzuki/Ree families and 22 sporadics;
>   this script: `HS`, `McL`, `Co₃`).  Same for the alternative TR-3 floor
>   `|S_min| ≤ C(n,3)`, which is the row of `S_min`. ∎

The three sub-cases of (K2) are numerically certified in the script output
(ratio `ν²/(4|Out|ι) = 94209708096/38883880224 = 2.4228…`, and
`ν³ = 2.89·10¹⁶` vs `C(52703,3) = 2.44·10¹³`).

## 4. Verdict

| row | v_task42 window | status now |
|---|---|---|
| `HS` | `71 ≤ n ≤ 75` | **empty for all `n`** (trigger starts at `195`, cert caps at `73`) |
| `McL` | `78 ≤ n ≤ 144` | **empty for all `n`** (`1126` vs `164`) |
| `Co₃` | `79 ≤ n ≤ 210` | **empty for all `n`** (`4636` vs `279`) |
| `Fi₂₄′` | `8270 ≤ n ≤ 42681` | window survives the naive test; **empty for all `n`** by Lemma R6-Fi |
| (`M₁₁`) | `n = 11` | already closed in v_task42 (`ν = 55`, `55² > 165`) |

> **R6 / input I12 is DISCHARGED.**  Branch (0) of Theorem TO′ is empty for
> every `n` and every admissible socle factor, so Theorem TO′'s trichotomy
> reduces to branches (a)/(b) — all of which were already re-swept empty in
> v_task42 §5.  No hypothesis is added to Theorem AT and **I12 is removed**
> from its input list; combined with v_task42 (which deleted `(H3) (★₃)`) and
> v_task39 (which deleted `(H4)`), the remaining inputs are (H1), (H2) (AB),
> and the R1 Lie equations.

**Provenance / tags.**  `ι` values: `[COMPUTED, exact]` via Lemma SP over
CTblLib 1.3.11 `Maxes` (= the complete ATLAS maximal-subgroup lists, `[LIT]`).
`ν_out` values: `[COMPUTED, exact]` — character-table class sizes of `HS.2`,
`McL.2`, `Fi₂₄` (CTblLib).  Lemma NU, Lemma R6-CERT, Lemma R6-Fi: `[PROVEN]`.
The window enumeration is exact integer arithmetic (GAP big integers,
Legendre's formula for `v_p(n!)`); no floating point is used in any test.
