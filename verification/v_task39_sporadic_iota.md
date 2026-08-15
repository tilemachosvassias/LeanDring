# v_task39 — Input **I8** discharged: exact `ι(S)` for every sporadic group,
# and the sporadic row of Theorem AT closed over its full reach

Date 2026-08-07.  **NOTES.md not edited.**
Answers Problem **P1 / input I8** of `v_task38_theorem_at_assembly.md`.

| file | what it does |
|---|---|
| `v_task39_sporadic_iota.g` / `_out.txt` | exact `ι(S)` (upper bound **and** matching Lemma-SP recursive lower bound: `EXACT=true` on all 27), witness, maximal-normalizer spectrum, `μ(S)` — 26 sporadics + the Tits group, from CTblLib `Maxes` |
| `v_task39_iota_window.g` / `_out.txt` | the full value window `I(S) ∩ [ι, 2ι]` (superset), which makes the scan's candidate set `V(S)` **complete** |
| `v_task39_sporadic_scan.c` / `v_task39_sporadic_scan_out.txt` | exact 128-bit scan of `ℓ·v = C(n,3)` over the **entire** reach (`n ≤ 1.004·10¹⁰`), plus the per-group reach |

**Headline.**  The sporadic row closes.  With the *exact* `ι` the complete
list of coincidences over the whole range `n ≤ 1.004·10¹⁰` is

> `M₁₂`/`n = 12`, `J₂`/`n = 16`, `Suz`/`n = 66` (twice) — plus
> `²F₄(2)′`/`n = 27`, which is outside the project's sporadic list.

All lie at `n ≤ 66`, i.e. **inside** §4aj's exhaustively swept region
(`n ≤ 150` residue sweep; `n ≤ 70` admissible-factorization census).
So no sporadic socle factor can produce an unseparated twin for `n > 70`.

**The task's stated expectation is refuted in both directions.**
`M₁₁`/`n = 11` **disappears** — it was an artefact of the class-size
*upper bound* `ι_ub(M₁₁) = 165`; the true value is `ι(M₁₁) = 55`
(witness `3² ⊴ 3²:Q₈.2`), and `ℓ·55 = 165` needs `ℓ = 3` while the order
squeeze allows only `ℓ = 1` at `n = 11`.  `M₁₁` in fact has **reach 0**:
it can never be a large-`ι` socle factor at any `n`.  Two new
coincidences (`M₁₂`/12, `J₂`/16) appear because the *exact* value
divides `C(n,3)` where the bound did not.

---

## 1. The reduction and how `ι` is actually computed

`ι(S) := min{ [S:N_S(A)] : 1 ≠ A ≤ S abelian }`.  For an arbitrary finite
group `X` put `ilow(X) := min{ [X:N] : N ≤ X, F(N) ≠ 1 }`.

> **Lemma SP.**
> **(a)** For `S` non-abelian simple, `ι(S) = ilow(S)`.
> **(b)** `ilow(X) = min` over maximal `M < X` of
> `[X:M]` if `F(M) ≠ 1`, and `[X:M]·ilow(M)` if `F(M) = 1`.
> **(c)** The minimum in (a) is attained at a **maximal** `M` with
> `F(M) ≠ 1`, and there `N_S(Z(F(M))) = M` exactly.

*Proof.*  (a) If `1 ≠ A ≤ S` is abelian then `A ≤ F(N_S(A))`, so
`F(N_S(A)) ≠ 1` and `ι(S) ≥ ilow(S)`.  Conversely if `F(N) ≠ 1` put
`A := Z(F(N)) ≠ 1`: abelian, characteristic in `N`, so `N ≤ N_S(A)` and
`[S:N_S(A)] ≤ [X:N]`; hence `ι(S) ≤ ilow(S)`.
(b) Let `N ≤ X` with `F(N) ≠ 1` and pick a maximal `M ⊇ N`.  If
`F(M) ≠ 1`, `[X:N] ≥ [X:M]`.  If `F(M) = 1` then `N ≠ M`, so
`[X:N] = [X:M]·[M:N] ≥ [X:M]·ilow(M)`.  Both branches are attained.
(c) `A := Z(F(M)) ≠ 1` is characteristic in `M`, so `M ≤ N_S(A)`;
`N_S(A) ≠ S` since `S` is simple and `A` is a proper nontrivial subgroup;
maximality gives `N_S(A) = M`. ∎

So `ι` is a **pure recursion over the ATLAS maximal-subgroup tables**,
with the predicate `F(M) ≠ 1` decided from the *character table* of `M`
by `ClassPositionsOfFittingSubgroup` (the Fitting subgroup is visible in
the character table).  No group is ever constructed; nothing is
enumerated.

`v_task39_sporadic_iota.g` runs (b) top-down with memoisation and the
pruning `[X:M]·2 ≥ current best ⇒ do not recurse`, and prints, per group,
**both** the recursive value `lowbound` and the best `F ≠ 1` maximal
index `iota`.  Output: `EXACT=true` for **all 27 groups** — the recursion
never descends below a maximal subgroup, i.e. every sporadic `ι` is
realised by a maximal subgroup.  (That is a result, not an assumption:
Lemma SP(b) is what makes it checkable.)

Where a table appearing in the recursion has no stored `Maxes`, a valid
**lower** bound is substituted, so the printed `lowbound` remains a
genuine lower bound: for `M` almost simple with `F(M) = 1` and socle `S₀`,
any `N ≤ M` with `F(N) ≠ 1` fails to contain `S₀` (otherwise `F(N)` would
centralise `S₀`, but `C_M(S₀) = 1`), hence
`[M:N] ≥ [S₀ : N ∩ S₀] ≥ μ(S₀)`.  Five such substitutions occur
(`A₆.2²`→6, `L₂(16).2`→17, `L₃(4).2₁`→21, `U₆(2).2`→672, `L₃(7).2`→57);
each is an ATLAS minimal degree.  The fallback `ilow ≥ 2` is never needed
in a place that affects a value.

**Provenance.**  Maximal-subgroup classifications: CTblLib 1.3.11
`Maxes` = the complete ATLAS lists; for the Monster this is the finished
46-class list (Dietrich–Lee–Popiel 2023, incl. `L₂(13).2` and `41:40`).
The script reports `tables missing: [ ]` for **all 27 groups** — every
maximal subgroup of every sporadic has its character table in the
library, so the `F(M)` test is exhaustive with no hand input.
Tag for the whole `ι` column: **[COMPUTED, complete and exact]**, resting
only on the cited maximal-subgroup classifications (**[LIT]**).

## 2. `ι₂`

Exact `ι₂(S)` would need the second value of `I(S)`, which Lemma SP does
not deliver (its (b)-recursion computes a minimum, not a spectrum).  The
table below therefore records `ι₂^ub` = the *second smallest* index of a
maximal subgroup with `F ≠ 1`, which is an **upper** bound
(`ι₂(S) ≤ ι₂^ub`); a matching lower bound would need the descent inside
the maximals of index `< ι₂^ub`.  `ι₂` is not used anywhere in §4, so
this is recorded, not closed.

## 3. The table

`Out` = `|Out(S)|`; `μ(S)` = minimal faithful permutation degree
(= smallest maximal index); `ι_ub` = §4aj/v_task24's bound (smallest
nontrivial class size).  `ι₂^ub` = second smallest `F ≠ 1` maximal
index — an **upper** bound for `ι₂(S)`, not a value.

| S | Out | **ι(S)** | witness maximal `M = N_S(Z(F(M)))` | ι₂^ub | μ(S) | old ι_ub |
|---|---|---|---|---|---|---|
| M₁₁ | 1 | **55** | `3²:Q₈.2` | 165 | 11 | 165 |
| M₁₂ | 2 | **220** | `3².2.S₄` | 220 | 12 | 396 |
| M₂₂ | 2 | **77** | `2⁴:A₆` | 231 | 22 | 1155 |
| M₂₃ | 1 | **253** | `2⁴:A₇` | 1771 | 23 | 3795 |
| M₂₄ | 1 | **759** | `2⁴:A₈` | 1771 | 24 | 11385 |
| J₁ | 1 | **1045** | `2³.7.3` | 1463 | 266 | 1463 |
| J₂ | 2 | **280** | `3.A₆.2₂` | 315 | 100 | 315 |
| J₃ | 2 | **17442** | `2⁴:(3×A₅)` | 23256 | 6156 | 26163 |
| HS | 2 | **3850** | `2⁴.S₆` | 4125 | 100 | 5775 |
| McL | 2 | **15400** | `3^{1+4}:2S₅` | 15400 | 275 | 22275 |
| He | 2 | **8330** | `2².L₃(4).S₃` | 29155 | 2058 | 24990 |
| Ru | 1 | **188500** | `2⁶:U₃(3):2` | 417600 | 4060 | 593775 |
| Suz | 2 | **22880** | `3₂.U₄(3).2₃′` | 135135 | 1782 | 45760 |
| Co₁ | 1 | **1545600** | `3.Suz.2` | 8292375 | 98280 | 3091200 |
| Co₂ | 1 | **46575** | `2¹⁰:M₂₂:2` | 56925 | 2300 | 56925 |
| Co₃ | 1 | **128800** | `3⁵:(2×M₁₁)` | 170775 | 276 | 170775 |
| Fi₂₂ | 2 | **3510** | `2.U₆(2)` | 142155 | 3510 | 3510 |
| Fi₂₃ | 1 | **31671** | `2.Fi₂₂` | 55582605 | 31671 | 31671 |
| Fi₂₄′ | 2 | **4860485028** | `2.Fi₂₂.2` | 14081405184 | 306936 | 4860485028 |
| HN | 2 | **1539000** | `2.HS.2` | 74064375 | 1140000 | 1539000 |
| Th | 1 | **283599225** | `2⁵.L₅(2)` | 976841775 | 143127000 | 976841775 |
| O′N | 2 | **2857239** | `4₂.L₃(4).2₁` | 17778376 | 122760 | 2857239 |
| Ly | 1 | **9606125** | `3.McL.2` | 1113229656 | 8835156 | 19212250 |
| J₄ | 1 | **173067389** | `2¹¹:M₂₄` | 3980549947 | 173067389 | 3980549947 |
| B | 1 | **13571955000** | `2.²E₆(2).2` | 11707448673375 | 13571955000 | 13571955000 |
| **M** | 1 | **97239461142009186000** | `2.B` | 5.79·10²⁷ | 97239461142009186000 | 97239461142009186000 |
| *²F₄(2)′* | 2 | **1755** | `2.2⁸.F₂₀` | 2925 | 1600 | — |

Notes.
* `ι(S) ≤ ι_ub` everywhere (sanity: `N_S(⟨x⟩) ⊇ C_S(x)`).  It is
  **strict** for 15 of 26; the biggest gaps are `M₂₂` (77 vs 1155, 15×),
  `J₄` (1.73·10⁸ vs 3.98·10⁹, 23×) and `Th` (2.84·10⁸ vs 9.77·10⁸).
* `ι(M) = 9.7239461142009186·10¹⁹` is **confirmed exact** (`2.B`, the
  2A-involution centralizer, is simultaneously the smallest-index
  maximal and has `F = Z = C₂`).  P1's reach figure therefore stands:
  the sporadic row genuinely had to be checked to `n ≈ 10¹⁰`.
* Exactly five groups have `ι(S) = μ(S)` — Fi₂₂, Fi₂₃, J₄, B, M — i.e.
  their minimal faithful permutation representation *is* an abelian
  normalizer (`2.U₆(2)`, `2.Fi₂₂`, `2¹¹:M₂₄`, `2.²E₆(2).2`, `2.B`,
  all involution centralizers or `2`-local).  Relevant to
  v_task36's Lemma ι₂-pair-bound hypothesis (P4).
* **Convention.**  §4aj / `v_task24_spor_iota.g` use the 26-group list;
  the Tits group `²F₄(2)′` is **not** counted.  It is tabulated and
  scanned here anyway; its only coincidence (`n = 27`) is likewise deep
  inside the swept region, so the convention does not matter.

## 4. The arithmetic: `ℓ·v = C(n,3)` over the full reach

**What has to be excluded.**  `κ` separates `T` from `A_n` as soon as
`ι(T) ≠ ι(A_n) = C(n,3)`.  By TR-1, `ι(T) ≤ min_O ℓ_O·ι(K_O ≤ Ā_O)`.
So a sporadic orbit obstructs separation only in the **equality** case
`ℓ·v = C(n,3)` with `v = ι(K ≤ Ā)`.  By Lemma F (v_task36)
`v = f(A)·[S:N_S(A)]`, `f | |Out S| ≤ 2`, hence

  `v ∈ V(S) := { m·w : w ∈ I(S), w ≤ 2ι(S), 1 ≤ m ≤ |Out S| }`,
  `ι(S) ≤ v ≤ 2ι(S)`.

`V(S)` is read off the exact maximal-normalizer spectrum (§1–§2).
Side conditions, both necessary for `|T| = n!/2`:
`(TO-2)` `ℓ·log|S| ≤ log(n!/2)`; `(pp)` `ℓ·v_p(|S|) ≤ v_p(n!)` ∀`p`.

**The scan** (`v_task39_sporadic_scan.c`, exact `__int128`, complete in
`ℓ`: every `ℓ ≥ 1` compatible with (TO-2), i.e. the whole `n`-range up
to each group's reach; 64 s):

```
  M12      v=220        l=1     n=12    *** LIVE ***
  J2       v=280        l=2     n=16    KILLED by p-part at p=5
  J2       v=560        l=1     n=16    *** LIVE ***
  McL      v=30800      l=29    n=176   KILLED by p-part at p=2
  Ru       v=188500     l=47    n=377   KILLED by p-part at p=2
  Suz      v=22880      l=2     n=66    *** LIVE ***
  Suz      v=45760      l=1     n=66    *** LIVE ***
  2F4(2)'  v=2925       l=1     n=27    *** LIVE ***
```
**8 solutions in total over `5 ≤ n ≤ 1.004·10¹⁰`; 3 die by the p-part
filter; the 5 survivors sit at `n ∈ {12, 16, 27, 66}`.**

**Reach** (largest `n` for which the *inequality* `ℓ·|Out S|·ι(S) ≥
C(n,3)` is compatible with (TO-2) — i.e. the largest `n` at which `S`
could be a socle factor that does **not** already separate):

| worst offenders | M | B | Fi₂₄′ | Th | J₄ | Ly | O′N | HN | Co₁ | rest |
|---|---|---|---|---|---|---|---|---|---|---|
| reach `n ≤` | 1.004·10¹⁰ | 104454 | 104454 | 19548 | 13890 | 3211 | 2969 | 1884 | 1135 | ≤ 473 |

`M₁₁` has reach **0**.  §4aj's "`n ≲ 3100`" was indeed wrong by six
orders of magnitude (P1 confirmed); the corrected figure `1.02·10¹⁰` of
P1 is confirmed at `1.004·10¹⁰` with exact `ι`.

## 5. Verdict on the sporadic row of Theorem AT

**The row closes.**  For every `n > 70`:

1. every sporadic `S` with reach `< n` cannot be a socle factor of an
   unseparated twin at all (its orbit already gives
   `ℓ·ι(K≤Ā) < C(n,3)`, hence `ι(T) < ι(A_n)`, hence `κ(T) ≠ κ(A_n)`);
2. for the remaining ones the equality `ℓ·v = C(n,3)` has **no**
   solution with `n > 70` — the scan is exhaustive in `ℓ` and exact.

Every one of the 5 surviving coincidences lies at `n ≤ 66`, inside
§4aj's exhaustive residue sweep (`n ≤ 150`) and inside the sharpened
Criterion-AT census (`n ≤ 70`), where the twins are excluded by the
*factorization* condition, not by `ι` (e.g. `M₁₂`/`n=12` needs
`|T| = |A₁₂| = 2520·|M₁₂|` with `c | |Out M₁₂| = 2` for a single socle
factor — impossible; the coincidences are per-factor conditions, not
twins).  **Input I8 is discharged; hypothesis (H4) of `v_task38`
Theorem AT may be removed.**  The honest floor `9 ≤ n ≤ 2·10⁷` of
§4ax is now limited only by (H1)–(H3) and the three R1 Lie equations.

**No residue.**  The one thing that could have been missed is a value of
`I(S)` strictly between `ι(S)` and `2ι(S)` coming from a *non-maximal*
normalizer, which would enlarge the candidate set `V(S)`.
`v_task39_iota_window.g` computes a **superset** of `I(S) ∩ [1, 2ι(S)]`
by the same Lemma SP recursion in set-collecting mode; the result agrees
with the `V(S)` fed to the scan for all 27 groups.  Every place where the
recursion hits a table without stored `Maxes` is "subgroups of index ≤ 2
inside the `ι`-witness itself", which can only produce the endpoint
`2ι(S)` — already in `V(S)`.  The single exception (Co₃, `U₄(3).2₃′` at
cap 3) is settled by hand: `U₄(3).2` has no subgroup of index 3, and its
index-2 subgroup `U₄(3)` is simple, so `F ≠ 1` cannot occur there (and
`Out(Co₃) = 1` makes it moot anyway).  **`V(S)` is complete, so the scan
of §4 is complete.**
