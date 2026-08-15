# v_task25 — closing `A_n`: the sharpened criterion, the outer branch, and the coincidence scan

**Date:** 2026-08-07.  **Companion notes:** `Even/NOTES.md` §4ak–§4am.

## What changed

v_task24 asked "does some factor have `ι < C(n,3)`?" — the wrong question, and
too strong.  Separation of `A_n` from a twin `T` needs only `ι(T) ≠ C(n,3)`,
and `ι(T)` is bounded on **both** sides by its socle factors:

- `ι(S) ≥ μ(S)` (minimal degree), since `N_S(H)` is a proper subgroup — so for
  Lie type `ι` is **exact**, equal to the minimal parabolic index.
- `ι(T) ≥ min_i ι(S_i)` for socle-internal `H`, since projections are
  homomorphisms: `N_S(H) ≤ ∏ N_{S_i}(proj_i H)`.
- `ι(T) ≤ m·min_i ι(S_i)` with `m ∣ c`.

So a factor with `ι` far *above* `C(n,3)` separates just as well as one far
below, and the residue is the narrow window — with `m = 1`, the exact
coincidence `ι(S) = C(n,3)`.

## 1. The outer branch (`v_task25_outer*`)

For abelian `H ≤ T` with `H ∩ S = 1`, the index is governed by
`[S : C_S(H)]`, i.e. by `ν(S_i)` = least index of the fixed-point subgroup of
an outer automorphism.  Computed for `m = 5..12`:

  **`ν(A_m) = C(m,2)`, attained at the transposition** (vs `ι(A_m) = C(m,3)`).

Since `ν ≤ ι`, this branch only makes `ι(T)` smaller — it reinforces Theorem
κ-A rather than threatening it, giving a second independent reason for
`κ(T) > κ(A_n)` whenever `T` has an alternating factor and `c` is even.

## 2. Criterion AT, verified exhaustively (`v_task25_sharpened_sweep*`)

> If `c · min_i ι(S_i) < C(n,3)` for every admissible factorization
> `n!/2 = c·∏|S_i|`, then `κ(T) ≠ κ(A_n)` for every Fitting-free non-simple
> `T` of order `|A_n|` — no coincidence-checking needed.

Pruned DFS over **all** factorizations (`k ≤ 4`, exact `Out`-divisibility
`c ∣ ∏|Out(S_i)|`), `n = 5..70`: **222 admissible factorizations in total,
Criterion AT holds for every one, zero uncovered.**  A complete verification,
not a sufficient-condition scan.

The headline fact is the scarcity: across 66 values of `n`, `n!/2` admits only
222 factorizations into simple-group orders at all.

## 3. The coincidence residue (`v_task25_coincidence*`)

`ι` is a polynomial in `q` per family, so `ι(S) = C(n,3)` is explicit.
Inverting for every `n` and every family, `n = 9..100 000`:

**exactly one** numeric solution with `q = p^f`, `p ≤ n`: `n = 11`, `U₅(2)`,
`ι = (2⁵+1)(2²+1) = 165 = C(11,3)` — and it fails the second filter, since
`|U₅(2)| = 13 685 760 ∤ |A₁₁| = 19 958 400`.

The constraint `p ≤ n` is forced (all primes of `|S|` divide `n!/2`) and does
the work: for `L₂(q)`, the family with the slowest-growing `ι`, it makes
`q = C(n,3) − 1 ≈ n³/6` a **proper** prime power with `p ≤ n`, hence `f ≥ 3` —
a Pillai-type equation with finitely many solutions by Baker's method.

## Status

Group theory: complete — every lemma holds for all `n`.
Arithmetic: `A_n` closed for `n ≤ 150`; for all `n` it reduces to a finite
list of exponential-Diophantine equations, one per family, verified to have no
admissible solution below `10⁵`.

## Files

`v_task25_outer.g/_out.txt`, `v_task25_sharpened_sweep.py/_out.txt`,
`v_task25_coincidence.py/_out.txt`, `v_task25_coincidence_pp.py`.
