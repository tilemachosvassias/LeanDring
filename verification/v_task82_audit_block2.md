# v_task82 — ADVERSARIAL AUDIT of the linear/unitary tower
# (`NOTES.md` §4be, §4bh + addendum; `v_task55`, `v_task56`, `v_task60`)

Date 2026-08-09.  **NOTES.md not edited.**
Independently re-derived, not re-read: the family table of
`v_task82_audit_block2.py` is written from the standard order /
parabolic-index formulas and only then cross-checked against `v_task52`'s
`FAM` (1156 rows, 0 mismatches) and against 19 known group orders.
Audited scripts are re-run only under **perturbed hypotheses** (pre-erratum
`μ`, restored slack, corrected `ppmax` cap) or to **fill computations that
were never run**.

| file | what it is |
|---|---|
| `v_task82_audit_block2.py` | PART 0 independent family table vs `FAM`; PART 1 `v_task55`; PART 2 `v_task56`; PART 3 `v_task60`; PART 4 cross-cutting; PART 5 what PART C's enumeration drops |
| `v_task82_audit_block2.g` / `_g_out.txt` | GAP: the `L₃` ι-witness at **two new `q`**; the unitary ι formulas vs CTblLib; `U₆(2)`'s exception; **Lemma X′ exactly at `d = 25`** — where the audit found the error |
| `v_task82_gapfill_d9d10_out.txt` | the equal-char almost-simple sweep at `d = 9, 10` — **never run before** |
| `v_task82_gapfill_d21_out.txt`, `v_task82_gapfill_d25_out.txt` | the equal-char censuses at `d = 21…24` and `d = 25…32` — **never run before** |
| `v_task82_E2_corrected.py` / `_out.txt` | `v_task60` PART E′ re-run with the **corrected** `ppmax_{2′}` cap (patches only that one line, execs `v_task60` otherwise unchanged) |

---

> ### Headline
>
> **One load-bearing FALSE lemma found**, plus **two unrun computations**
> and several documentation defects.  **No verdict moves**: after the
> repairs and the missing runs, **Theorem L3-T and Theorem LU-T (all `d`)
> both stand.**
>
> **(F1) `v_task60`'s `q = 2` sharpening of Lemma X′ is FALSE for the
> unitary tower**, and it is load-bearing in PART E′ / PART F(ii′) — the
> argument that closes (H3′).  GAP, exactly:
> `ppmax_{2′}(|U₂₅(2)|) = 3³⁴ = 1.67·10¹⁶` against the claimed cap
> `2^{3d/2−2} = 3.4·10¹⁰` — wrong by a factor `5·10⁵`, and wrong at
> **every** `d` tested (21, 23, 25, 30, 40, 46).  Cause: the step "no
> `r ≠ 2` has `ord_r(2) = 1`, so `k ≥ 2` and `m ≤ d/2`" is a **linear-tower
> count**.  In the unitary tower `3 | 2^i − (−1)^i` for **every** `i`, so
> `m = d − 1`, not `⌊d/2⌋` (GAP: `d = 25` gives `m_L = 12`, `m_U = 24`).
> **Repaired**: re-running PART E′ with the *proven* Lemma X′ bound
> `ppmax_{2′} ≤ 6^{d−1}` still gives **99 954 windows, all empty, 0
> survivors, `21 ≤ d ≤ 200`, both towers**.  The verdict is unchanged;
> the stated justification was not.
>
> **(F2) Two computations claimed but never run.**  `v_task56` PART C.2
> (equal-char almost-simple sweep) was run for `d = 4…8` only — its own
> ledger says `d ≤ 8` while its (H3) says `4 ≤ d ≤ 10`; and `v_task60`
> PART F(iii)'s "the PART E sweep covers every `d > 20` as well" is a
> **non-sequitur** (PART E swept the *targets* `d = 11…20`).  This audit
> ran `d = 9, 10` (49 298 targets each: 0 hits, 0 near-misses, control
> 49298/49298) and `d = 21…32` (C.4 census + C.2 sweep: 0 live, 0 hits),
> and supplies a **sweep-free repair** for the whole `d > 20` residue
> (§2.4 below, via `v_task60`'s own PACK-TOP).
>
> **(F3) `v_task60` PART C is not "uniform in `q`".**  Its shape
> enumeration silently drops both the `(Z2)` log-slack and Lemma ZM's
> `v_r(d!)` term.  Restoring them admits 100–600 extra candidate rows per
> target at small `q` (PART 5).  The branch is genuinely census-backed
> below the (uncomputed) threshold; the censuses exist for `d ≤ 20`, and
> this audit extends them to `d ≤ 32`.
>
> **Everything else checked out**, including the two items the brief
> flagged as most likely to break: the `μ(E₇)/μ(E₈)` erratum does **not**
> move `v_task55`'s violator list or tail bound, and the unitary ι
> correction is confirmed from independent data.

---

## 1. Item 1 — `v_task55` (`L₃`): **PASS**

### 1.1 Lemma Q, re-derived

`|S| = q³(q²−1)(q³−1)/e < q⁸` for every prime power `q` (checked, `q ≤ 3000`),
so `|G|² ≤ |S|` gives `|G| < q⁴`; the per-orbit floor gives
`q² < q²+q+1 ≤ 2ρ(G)`, hence `|G| < (2ρ)² = 4ρ²` — **strictly**.  The
script's non-strict test `|G| ≤ 4ρ²` is the conservative side. ✓

`D/μ ≥ 7/3 > 2` makes `α ≤ 2` finite: confirmed row by row (the tail
threshold is `None`/0 for every family with `D − 2μ` large). ✓

### 1.2 The erratum question — **the brief's suspicion is right about the
timing and wrong about the consequence**

`v_task55` (12:03/12:05) **does predate** `v_task58` (13:05–13:20), so its
stored output was produced with `μ(E₇) = 25`, `μ(E₈) = 51`.  But:

* re-running `v_task55` PART 2 against the **current** (corrected) `FAM`
  reproduces the PART-2 body **byte-identically** — same 56 violators,
  same 47 non-empty windows, same `q ≤ 23 815`;
* computed both ways, **no `q₁ ≥ 2` satisfies the surrogate Lemma-B
  condition for `E₇` or `E₈` at either `μ`** (`D − 2μ = 79` resp. `134`).

**Verdict: the violator list does not change and no new target window
appears.**  ✓

### 1.3 The tail bound `q₁ ≤ 2 709 504` — re-derived in closed form

The surrogate is `q₁^{D−2μ} ≤ 768 d³ f₁² g²` with `f₁ ≤ log₂ q₁`.  The
extremal row is `A₁ = L₂(q₁)` (`D = 3, μ = 1, d ≤ 2, g = 1`):
```
        q₁ ≤ 6144 f₁² ,   f₁ = log_p q₁ ≤ log₂ q₁ .
```
`f₁ = 21`: `6144·441 = 2 709 504 ≥ 2²¹` — holds.
`f₁ = 22`: `6144·484 = 2 973 696 < 2²²` — fails, and no `f₁ ≤ 39` reopens it.
So `2 709 504` is a **genuine** tail bound, not a scan artefact.  My
independent per-family scan reproduces `max = 2 709 504` exactly. ✓

`rank ≥ 25`: `v_task55` checks ranks 25–60 only.  Closed form: at rank 25
`D − 2μ ∈ {530, …, 1177}` against a cap `≤ 4.9·10⁸`, and `D − 2μ` is
increasing in `n`, so **all** ranks `≥ 25` are empty, not just `≤ 60`. ✓

The `2**D > 10**60: break` shortcut in `lie_rows()` skips high-rank rows
from the exact scan; **every skipped row has an empty tail**, so the scan
is complete. ✓

### 1.4 The four raw census survivors — orders and floor kills

| `q` | configuration | `c` | orders | `c \| ∏\|Out\|·2!` | floor |
|---|---|---|---|---|---|
| 4 | `A₅ × L₃(2)` | 2 | ✓ | ✓ | both factors fail (`10, 14 < 21`) |
| 9 | `A₆ × L₂(27)` | 12 | ✓ | ✓ | `A₆` fails (`40 < 91`); `L₂(27)` passes (`168 ≥ 91`) |
| 16 | `L₂(16) × Sz(8)` | 12 | ✓ | ✓ | both fail (`68, 195 < 273`) |
| 729 | `L₂(729) × L₂(19683)` | 108 | ✓ | ✓ | both fail (`8760, 354312 < 532171`) |

All four orders verified exactly (`|L₃(729)| = 79 766 292 776 346 468 190 080`).
Each configuration is killed because the floor must hold for **every**
orbit; `ῑ` is an upper bound, so a kill with `ῑ` is a fortiori a kill. ✓

### 1.5 The `O_p(maximal P)` ι-witness at **two new `q`** (GAP)

`q = 19` and `q = 23` are not among `v_task55`'s twelve values.

| `q` | `\|O_p(P)\|` | elem. ab. | `N_S(A) = P` | `ind*(O_p(P))` | `q²+q+1` | `ind*(Z(Syl_p))` | `(q+1)(q²+q+1)` |
|---|---|---|---|---|---|---|---|
| 19 | 361 = `q²` | ✓ | ✓ | **381** | 381 ✓ | **7620** | 7620 ✓ |
| 23 | 529 = `q²` | ✓ | ✓ | **553** | 553 ✓ | **13272** | 13272 ✓ |

Both the correct witness and the `Z(Syl_p)` trap reproduce exactly. ✓

### 1.6 Defect found (cosmetic)

`v_task55.md` §3.1 tabulates the `ℓ ≥ 3` thresholds as
`l=3:140, l=4:12, l=5:8, l≥6:4…3`.  Its own `_out.txt` prints
`135, 6, 3, 3, …`; my independent computation gives `131, 5, 3, 3, …`.
**The .md table matches neither.**  All three give the same downstream
conclusion (`q ≥ 141` is safe), so nothing moves.

> **Verdict, item 1: PASS.**  Theorem L3-T stands.

---

## 2. Item 2 — `v_task56` (LU, `d ≥ 4`): **PASS with two defects**

### 2.1 Lemma Z's `o(1)` — explicit, but **not** `o(1)` at small `q`

`(Z1) f₁k₁ ≤ Kf` and `(Z2) f₁μ₁ ≥ fb − Λ`, `Λ := log_p(4ℓd₁f₁g₁)`, give
```
      μ₁/k₁  ≥  b/K  −  Λ/(fK) .
```
The `o(1)` **is** explicit.  But it is `o(1)` only as `f → ∞` or `p → ∞`;
at `f = 1, p = 2` it is `Λ/K`, which is not small.  (`ι(S) > q^b` verified
for both towers, `4 ≤ d ≤ 20`, `q ≤ 200`.)

**Corollary Z-rank1 is therefore NOT valid "for every `d ≥ 4`, in one
line".**  A rank-1 factor has `μ₁ = k₁/2`, so `q₁^{μ₁} ≤ q^{K/2}` and the
floor is satisfiable whenever `4ℓd₁f₁g₁ ≥ q^{b−K/2}`.  Largest `q` at which
a rank-1 factor still survives Lemma Z:

| target | `L₄` | `L₅` | `L₆` | `L₇` | `L₈` | `L₁₀` | `U₄` | `U₅` | `U₆` | `U₈` |
|---|---|---|---|---|---|---|---|---|---|---|
| `q ≤` | 256 | 32 | 16 | 8 | 4 | 3 | 512 | 16 | 3 | 2 |

Zsygmondy's own exceptions (`q₁ = 2, k₁ = 6`; Mersenne `k₁ = 2`) are a
*second*, separate reason the lemma is inapplicable at small `q` — the
notes name that one ((H2)) but not this one.  **Harmless in the
almost-simple branch** (PART C.2 sweeps `q ≤ 2·10⁶` exactly); it matters in
the multi-factor branch, see §3.3.

### 2.2 The `j·d₁` window chain — steps 1–4 all check out

Every step re-derived and confirmed, including `ε ≥ (d−1)/(d+2)` in step 3.
**But the window itself is bounded wrongly.**  `v_task56` caps
`d₁ ≤ 2d` and `f₁ ≤ df` — neither is justified.  `(Z1)` gives `d₁f₁ ≤ df`
**directly**, so the window is simply

```
      q^{(d−1)/(d+2)} ≤ 8 d f ,       and d₁ ≥ d+1 forces f ≥ 2 .
```

(`f₁ ≤ df/(d+1) < f`, so the whole `f = 1` case is empty.)  Sharp windows
against the printed ones:

| `d` | sharp | `v_task56`'s table | swept? |
|---|---|---|---|
| 4 | 262 144 | 923 521 | ✓ C.2 `q ≤ 2·10⁶` |
| 6 | 32 768 | 531 441 | ✓ |
| 8 | 16 384 | 531 441 | ✓ |
| **9, 10** | 8 192 | 531 441 / 524 288 | **never swept → run here** |
| 11–20 | 4 096–8 192 | — | ✓ `v_task60` PART E |
| **≥ 21** | 4 096–8 192 | — | **never swept → §2.4** |

**Which `d` did C.2 actually cover?  `d = 4…8` only** (`main()` calls
`partC_sweep(qmax=2000000)` with the default `dlist=(4,5,6,7,8)`; the
output has exactly ten rows).  `v_task56` §8 (H3) claims `4 ≤ d ≤ 10` for
"PARTS C.2, C.4, E, F, G" — true for C.4/E/F/G, **false for C.2**.

**Gap filled here** (`v_task82_gapfill_d9d10_out.txt`):
```
 L_9   targets 49298  divisor pairs 1293941  control 49298/49298
       order-only NEAR-MISSES: NONE     HITS: NONE
 L_10 / U_9 / U_10 : likewise, 0 hits, 0 near-misses
```

### 2.3 `v_task60` PART F(iii) is a non-sequitur

> "The window is `≤ 524 288` and **decreasing in `d`**, so the PART E sweep
> covers every `d > 20` as well."

PART E swept the **targets** `d = 11…20`.  A target `L₂₅(q)` with `q`
inside `L₂₅`'s own window was never swept.  The window at `d ≥ 21` is
`q ≤ 8192` — small, but non-empty.

### 2.4 REPAIR (no sweep needed, every `d`, every `q ≥ 6`)

`v_task60`'s own **Corollary PACK-TOP** closes the `d₁ ≥ d+1` branch
outright.  `M_K = 1` in both towers, so some factor must cover `Φ_K`,
forcing `j₁k₁ ≥ K`; Lemma Z gives `≤`; hence `j₁k₁ = K` **exactly**.  For
`S₁ = L_{d₁}(q₁)` in `L_d(q)` this is `j d₁ = d`, and `(O)` becomes
```
   (d/d₁)(d₁²−1) = d²−1−δ   ⟺   d₁ = d − (1+δ)/d + 1/d₁ .
```
`δ = log_q(cκ) ≥ −log_q 6`, so for `q ≥ 6` we get `δ ≥ −1` and
`d₁ ≤ d + 1/d₁ < d+1` — **contradiction with `d₁ ≥ d+1`**.  `q ≤ 5` is
inside every census.  Checked numerically at `d = 4, 10, 21, 25, 60, 200`:
IMPOSSIBLE in every row.

The same DEG+PACK-TOP pair also disposes of **non-`L/U` socle families** in
the equal-characteristic almost-simple branch, which `v_task56` §3 never
treats analytically (it treats only `S₁ = L_{d₁}`) and leaves entirely to
the C.2 sweep: `(P=)`/`(R=)` force `σ₁ = N₁/n₁ = d/2`, and `j₁k₁ = K`
then fails for `C_n`, `B_n`, `D_n`, `G₂`, `F₄`, `³D₄`, `E₆`–`E₈`, `Sz`,
`R`, `²F₄`, leaving only `S₁ = L_d(q₁)` with `j = 1`, i.e. `c = 1`.

*(This is a **repair suggestion**, not a run; the runs above cover
`d ≤ 32` unconditionally.)*

### 2.5 The unitary ι correction — **CONFIRMED from independent data**

| `S` | exact | `(q+1)(q³+1)` (`P₂`) | `(q^d−…)/(q²−1)` (`P₁`) | matches |
|---|---|---|---|---|
| `U₄(2)` | 27 | **27** | 45 | `P₂` |
| `U₄(3)` | 112 | **112** | 280 | `P₂` |
| `U₅(2)` | 165 | — | **165** | `P₁` |
| `U₆(2)` | 693 (`m = 672`) | — | **693** | `P₁` |

`112 = (3+1)(27+1)` ✓ — and `280 = (3²+1)(3³+1)` is **exactly the second
element** of `v_task36`'s `I(U₄(3)) = {112, 280}`, so that pair is
`{[S:P₂], [S:P₁]}`.  GAP over the **whole subgroup lattice** of `U₄(2)`:
`I(S)` begins `27, 40, 45, …`, so `ι(U₄(2)) = 27 = (q+1)(q³+1)` exactly.
`U₆(2)`'s maximal indices are `[672, 693, 891, …]` — the named exception
`m = 672 < 693` confirmed.  ✓

`v_task50`'s `IOTA_UB` rows `U4(4)=1105`, `U4(5)=3276`, `U4(8)=33345` are
indeed the `P₁` values (true ι: 325, 756, 4617).  **Direction check**: `ῑ`
enters (i) the orbit floor for factors, (ii) `|G| ≤ 4ρ²`, (iii) the window
`ι(S) ≤ 2ρ` — larger `ῑ` is conservative in all three.  The stale rows are
**safe in every consumer**.  `IOTA_EXC[("U",6,2)] = 672` is consulted only
via `iota_LU`, which is used for **targets** only; as a *factor* `U₆(2)`
gets the formula value 693.  Correct. ✓

### 2.6 Stale `μ/k` table

`v_task56.md` §2.1 prints `E₇ = 25/18`, `E₈ = 17/10` — the **pre-erratum**
values.  Its own regenerated `_out.txt` gives `3/2` and `19/10`, and its
PART D.2(a) row `L₁₀` includes `E₇(1)`, which only the corrected `μ = 27`
admits.  So the **computation is post-erratum and the .md table is not**.
Direction: the stale values *understate* `μ/k`, i.e. they would wrongly
**exclude** `E₇/E₈` — the non-conservative direction for a reader who
reuses the table.  §4.2's family table likewise omits `E₇`.
Documentation defect; no verdict moves.

> **Verdict, item 2: PASS after the two missing sweeps (run here) and
> with the two documentation defects recorded.**

---

## 3. Item 3 — `v_task60` (residues)

### 3.1 The Φ-packing identity — **PASS, and valid for prime-power `u`**

`Φ_κ(u^s) = ∏_{κ′ : κ′/gcd(κ′,s) = κ} Φ_{κ′}(u)` verified at **1536**
instances (`u` prime, `u` a prime power `4,8,9,16,25,27,32,64,128,243`,
`u` composite `6,10`; `s ≤ 8`, `κ ≤ 12`): **0 mismatches**.
The `s`-free reduction `ms/gcd(ms,s_i) = mβ/gcd(mβ,α)` verified at
**56 472** instances: **0 mismatches**.  So "free of `s`, hence free of `q`"
is correct. ✓

**Integer level.**  The bridge is a Zsygmondy primitive prime `r` of
`u^{ms} − 1`: then `ord_r(q) = ord_r(u^s) = m` and
`ord_r(q_i) = ms/gcd(ms,s_i)`, so `r | |S_i|` **iff** PACK's condition
holds, and `r ≠ p` because `r ∤ u`.  Zsygmondy is a statement about an
arbitrary integer base, so **`u` being a prime power rather than a prime
costs nothing** — brute-force confirmed for `u ∈ {4,8,9,16,25,27,32,64}`,
`n ≤ 12`: a primitive prime exists in every case.
`pack_kill` iterates `for m in range(K, 2, -1)`, i.e. `m ≥ 3`, and
`ms ≥ m ≥ 3`, so the only exception that can bite is `(u, ms) = (2, 6)`. ✓

### 3.2 Lemma DEG — **PASS, with a terminology defect**

`n_i = D_i − 2N_i` recomputed for all 17 families at several ranks:
**0 mismatches** against `v_task60`'s list.  The identity behind it is
`dim G = 2|Φ⁺| + rank`.

**Defect:** `v_task60` calls `n_i` "the TWISTED RANK".  It is the
**ambient** rank for `²A_n`, `²D_n`, `²E₆` and `³D₄` (whose order
polynomials carry the untwisted degrees) and the twisted rank only for
`²B₂`, `²G₂`, `²F₄`.  In particular `³D₄` has twisted rank 2 while
`D − 2N = 4`, which is the value the note lists and the code uses.  The
code (`famrows`: `rk = D − 2*N`) is right; the **label** is wrong.

The two equations checked on three shapes:

| shape | `(P=)` | `(R=)` | `(O=)` |
|---|---|---|---|
| `L₆ ← S₆ × G₂` | proportional to `(R=)` — DEG cannot pin (the box does) | | |
| `L₁₂ ← O₁₄⁺ × F₄` | proportional — matches `v_task60` §2.2 exactly | | |
| `U₂₂ ← E₇ × E₈` | unique solution `j₁ = 2, j₂ = 7/8`; `231 = 231`, `21 = 21`, `(O=) 483 = a` ✓ | | |

So DEG is genuinely non-binding on the 21 residual shapes, exactly as
claimed, and PACK is what kills them. ✓

### 3.3 PART C is **not** "uniform in `q`"

`enumerate_configs` uses `lb = b/μ_i` — the floor **with the log-slack
dropped** — and `jbound_ZM` uses `need = ℓ_i·m` — Lemma ZM **with the
`v_r(d!)` term dropped**.  Both are valid only above a `q`-threshold that
PART D never computes (PART D's thresholds are for PACK-def's *size*
argument only).  Restoring both (a strict relaxation) admits this many
**extra candidate rows**:

| target | `q=2` | `q=3` | `q=8` | `q=64` | `q=10⁶` |
|---|---|---|---|---|---|
| `L₆` | +67 | +53 | +39 | +30 | +14 |
| `L₂₀` | +231 | +188 | +144 | +110 | +65 |
| `L₂₅` | +313 | +239 | +193 | +151 | +88 |
| `U₂₅` | +122 | +86 | +65 | +50 | +33 |

(and at `L₄`, `L₆`, `U₄` some rows have `lb = 0` outright, i.e. the floor
gives **no** lower bound at all and the enumeration is not even finite
without the separate `j_i ≥ 1/f`.)  So the headline

> "the equal-characteristic multi-factor branch has **zero** admissible
> socle shapes … No census enters the argument at all"

is **not literally true**.  Below the (uncomputed) threshold the branch
rests on the C.4 censuses: `q ≤ 10⁵` for `d ≤ 10`, `q ≤ 3000` for
`11 ≤ d ≤ 20`, and **nothing** for `d ≥ 21`.

**Gap filled here**: C.4 census + C.2 sweep at `d = 21…24` and `d = 25…32`,
both towers (`v_task82_gapfill_d21_out.txt`, `_d25_out.txt`):
```
 L_21 … L_32, U_21 … U_32 :  LIVE multi-factor configurations: NONE
 C.2 (q <= 20000)          :  0 hits, 0 near-misses, control 2328/2328
```
`d ≥ 33` at small `q` remains supported by PART C's incomplete enumeration
only — **named residual**, and the natural closure is the `σ = d/2`
argument of §2.4 (which is `q`-free).

### 3.4 `d = 25` with exact numbers — **and (F1), the one real error**

Lemma X′ `ppmax_{p′} ≤ 2^{d−1}(q+1)^{d−1}` — **holds**, exactly, in every
row tested (GAP, `d = 21, 24, 25, 26, 30`, `q = 2,3,4,5`, both towers).
The tail margins recompute correctly:

```
 (i)   cross char, almost simple, d = 25 : margin +423 (q=2), +758 (q=3)
       (v_task60 quotes +212 at d = 21;  I get +212.1 — MATCH)
 (ii)  q = 2 needs tau_1 = N_1/mu_1 <= log6/(2log2) = 1.2925 ; the
       families are L2, U3, R (tau = 1) and U4, G2 (tau = 6/5),
       plus Sz, 2F4 excluded by characteristic — MATCHES the note
```

**But the `q = 2` sharpening `ppmax_{2′} ≤ 2^{3d/2−2}` is FALSE for the
unitary tower.**  GAP, exact:

| | `ppmax_{2′}(\|S\|)` | `2^{3d/2−2}` | ok? |
|---|---|---|---|
| `L₂₁(2)` | 5 764 801 = `3¹⁴` | 536 870 912 | ✓ |
| `U₂₁(2)` | 22 876 792 454 961 = `3²⁸` | 536 870 912 | **✗** |
| `L₂₅(2)` | 129 140 163 = `3¹⁷` | 34 359 738 368 | ✓ |
| `U₂₅(2)` | 16 677 181 699 666 569 = `3³⁴` | 34 359 738 368 | **✗ by 5·10⁵** |
| `U₃₀(2)` | `3⁴²` | `2⁴³` | **✗** |
| `U₄₀(2)`, `U₄₆(2)` | `3⁵⁸`, `3⁶⁷` | — | **✗** |

**Cause.**  The note's derivation is: "no `r ≠ 2` has `ord_r(2) = 1`, so
`k ≥ 2`, `m ≤ d/2`".  The step `m ≤ ⌊d/k⌋` is the **linear-tower** count
(`r | q^i − 1` iff `k | i`).  In the unitary tower `m = #{i : r | q^i −
(−1)^i}`, and at `r = 3`, `q = 2` we have `3 | 2^i − 1` for `i` even **and**
`3 | 2^i + 1` for `i` odd, so `m = d − 1`.  GAP:

```
 d=21 : m_L(r=3) = 10 (= |d/2|)    m_U(r=3) = 20 (= d-1)
 d=25 : m_L(r=3) = 12              m_U(r=3) = 24
 d=46 : m_L(r=3) = 23              m_U(r=3) = 45
```
For `L` the sharpening survives (the `k = 2` term contributes
`3^{d/2}·2^{d/2−1} = 2^{1.29d−1} ≤ 2^{1.5d−2}`); for `U` it is off by
`2^{≈0.9d}`.

**Where it is load-bearing.**  `partE2_h3prime` sets
`cap = 2**((3*d)//2)` inside the loop over **both** `X ∈ {L, U}`, and that
cap is the `hi` end of every (H3′) window; and PART F(ii′) uses the same
sharpening to claim the unitary residue "dies from `d = 11`".  With the
correct bound the unitary residue is **not** killed analytically at all,
so (H3′) as stated is not closed for `U_d(2)`, `d > 200`.

**Repair, run here** (`v_task82_E2_corrected_out.txt`): PART E′ re-run with
the *proven* `ppmax_{2′} ≤ 6^{d−1}` for the unitary tower —
```
 PART E', q = 2, both towers, 21 <= d <= 200, cross char, l >= 2:
     windows killed EMPTY by (i)+(ii) alone : 99 954
     windows needing an exact sweep         : 0
     windows too large to sweep             : 0
     SURVIVORS                              : NONE
```
The unitary windows are empty by a wide margin anyway, because
`ι(U_d(q)) ≍ q^{2d−3}` makes the floor's lower end enormous — which is
precisely why the false cap never showed up as a survivor.  **The verdict
survives; the proof as written does not.**  `U_d(2)` for `d > 200` needs
either the corrected analytic statement or an extension of the (cheap)
window test.

> **Verdict, item 3: FAIL on the stated argument (one false lemma, one
> overstated uniformity claim), PASS on the conclusion after repair.**

---

## 4. Item 4 — cross-cutting: **PASS with a caveat**

### 4.1 `B_n/C_n` never meets an `L/U` order

`a/N = 2 + 1/n` for `B_n/C_n` and `2 + 2/d` for the towers; equality forces
`d = 2n`, and then `d²−1 = 4n²−1 = 2n²+n` gives `2n² − n − 1 = 0`, i.e.
`(2n+1)(n−1) = 0`, so `n = 1`.  Algebra confirmed; no solution for
`2 ≤ n ≤ 39`; exhaustive same-`q` search over `q ≤ 500`, `3 ≤ n ≤ 8`,
`4 ≤ d ≤ 16`: **0 coincidences**. ✓

**Caveat.**  "the `a/N` ratios must agree" is only valid when both orders
are read as polynomials in the **same** `q`.  For `|B_n(q₁)| = |L_d(q)|`
with `q₁ ≠ q` the step does not apply as written.  What actually rules that
out is the CFSG order theorem itself, cited independently one paragraph
earlier.  So §8.1's "one line" is a **consistency check, not an independent
proof**; the conclusion is correct because it is inherited from
[LIT: Artin; KLST].

### 4.2 The `a/N` table vs the erratum-corrected FAM

`D` and `N` are identical in my independent table and in `FAM` at every row
(1156 comparisons, 0 mismatches).  **The erratum touched only `μ`**, never
`D` or `N`, and Lemma EQ-EX compares `D₁/N₁` with `a/N`, so the EQ-EX ratio
table is erratum-free **by construction**.  All `μ`-consumers re-checked
with the corrected values:

```
 Lemma C  2D − 3μ :  E7 → 185 > 0 ,  E8 → 325 > 0        (intact)
 Lemma Z  μ/k     :  E7 → 3/2 ,      E8 → 19/10          (was 25/18, 17/10)
 Lemma Z2 μ/N     :  E7 → 3/7 ,      E8 → 19/40
```
The `μ/k` change is the one recorded in §2.6: the **code** uses the
corrected values, the **.md tables** do not.

> **Verdict, item 4: PASS.**

---

## 5. Ledger of findings

| # | finding | severity | status |
|---|---|---|---|
| F1 | `v_task60`'s `q=2` sharpening `ppmax_{2′} ≤ 2^{3d/2−2}` is **false for the unitary tower** (`m = d−1`, not `⌊d/2⌋`, at `r = 3`); load-bearing in PART E′ and PART F(ii′) | **error, load-bearing** | **repaired + re-run**: `6^{d−1}` gives 99 954 empty windows, 0 survivors, `21 ≤ d ≤ 200` |
| F2a | `v_task56` PART C.2 was run for `d = 4…8`, not `4…10` as (H3) claims | unrun computation | **run here**: `d = 9, 10`, 0 hits |
| F2b | `v_task60` PART F(iii) "the PART E sweep covers every `d > 20`" is a non-sequitur | unrun computation | **run here** `d = 21…32`; sweep-free repair in §2.4 |
| F3 | `v_task60` PART C drops the `(Z2)` slack and ZM's `v_r(d!)`; not "uniform in `q`" | overstated claim | quantified (PART 5); censuses now reach `d ≤ 32`; `d ≥ 33`, small `q` is a **named residual** |
| F4 | Corollary Z-rank1 not valid for every `q` (`q ≤ 256` at `L₄`, `q ≤ 512` at `U₄`) | overstated claim | harmless — covered by C.2 |
| F5 | `v_task56` §3's window bounds `d₁ ≤ 2d`, `f₁ ≤ df` are unjustified (`(Z1)` gives `d₁f₁ ≤ df`, a *sharper* window) | loose but safe | sharp windows tabulated |
| F6 | `v_task56.md` §2.1/§4.2 tables are pre-erratum (`E₇ 25/18`, `E₈ 17/10`) | doc defect, non-conservative direction | flagged |
| F7 | `v_task60` calls `D−2N` "the twisted rank"; it is the **ambient** rank for `²A`, `²D`, `²E₆`, `³D₄` | terminology | flagged (code correct) |
| F8 | `v_task55.md` §3.1's `ℓ≥3` threshold table matches neither its own output nor an independent recomputation | doc defect | flagged (conclusion unaffected) |
| F9 | `v_task56` §8.1's `B_n/C_n` "one line" needs same-`q`; it is a check, not a proof | rhetorical | inherited from KLST |

**Confirmed sound** (attacked, held): Lemma Q and its `α ≤ 2` finiteness;
the `2 709 504` tail bound (closed form) and its `rank ≥ 25` companion,
extended here to *all* ranks; the 56-violator list under the corrected `μ`;
the four census survivors' floor kills; the `O_p(P)` ι-witness at two new
`q`; the whole PACK cyclotomic identity including prime-power bases and the
Zsygmondy edge cases; Lemma DEG's bookkeeping; Lemma X′ itself; the unitary
ι correction against `v_task36`'s independent `I(U₄(3))` data; the a/N
table's erratum-independence.

---

## 6. Overall verdict

* **Theorem L3-T (`L₃(q)`, all `q ≥ 3`): STANDS.**  Nothing in item 1
  moved; the erratum is a non-event for it.
* **Theorem LU-T (`L_d(q)`, `U_d(q)`, all `d ≥ 4`, all `q`): STANDS**, but
  its published proof needs three amendments — the `q = 2` `ppmax`
  sharpening must be deleted for the unitary tower (F1), (H3) must be
  restated as `d ≤ 8` for C.2 with `d = 9, 10` supplied (F2a), and PART C's
  `q`-uniformity must be downgraded to "above an explicit threshold, with
  the C.4 censuses below it" (F3).  After the repairs and the four runs
  added here, **no counterexample and no live configuration appears
  anywhere**, and the two exact confirmations that were missing
  (`d = 9,10` and `d = 21…32`) are clean.
* **The one genuinely open item created by this audit**: the
  equal-characteristic multi-factor branch at `d ≥ 33` and small `q`, where
  PART C's enumeration is incomplete and no census exists.  §2.4's
  `σ = d/2` / PACK-TOP argument is `q`-free and looks sufficient; it should
  be written out.

---

## 7. Reproduce

```
python3 v_task82_audit_block2.py all        > v_task82_audit_block2_out.txt
~/gap-4.16.0/gap -q -o 8g v_task82_audit_block2.g > v_task82_audit_block2_g_out.txt
# the gap-fills (each imports the audited scripts unchanged):
python3 -c "import sys;sys.path.insert(0,'.');from v_task56_lu_twins import partC_sweep;partC_sweep(dlist=(9,10),qmax=600000)"
python3 -c "import sys;sys.path.insert(0,'.');from v_task56_lu_twins import partC_multi_full,partC_sweep;partC_multi_full(dlist=range(21,33),qmax=3000);partC_sweep(dlist=range(21,33),qmax=20000)"
# the corrected PART E' (patches the cap, then re-runs v_task60 unchanged):
python3 v_task82_E2_corrected.py 21 200     > v_task82_E2_corrected_out.txt
```
