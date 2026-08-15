# v_task19: Theorem AF (per-n arithmetic check), n = 9..40

**Headline result — differs from the task brief's expectation.** The task
brief anticipated an "M11-style negative sanity" outcome for the n=9,10
controls (i.e. `NO_FACTORIZATION`, mirroring the sporadic-group program).
That expectation is **false**: n=9 and n=10 both produce genuine, exactly
verified `FACTORIZATION_EXISTS` witnesses, and so do 17 more values of n in
the 9..40 range (19/32 total). **Theorem AF as literally stated in NOTES.md
sec 4u ("for all n>=5, every Fitting-free group of order n!/2 is simple") is
false for at least these 19 values of n, within the stated family scope** —
not merely "open" or "inconclusive." Two of the witnesses (n=17, n=22) are
**unconditional direct products of two simple groups with no `Out`-lifting
at all** (`c=1`): `L2(16) x A14` has order exactly `|A17|`, and `J1 x A18`
has order exactly `|A22|`. These are independently re-verified below by
plain Python arithmetic (outside GAP) and, for the n=9 and n=10 witnesses,
by direct construction of the actual group in GAP (order, `FittingSubgroup`,
non-simplicity — not just an order-arithmetic coincidence).

The remaining 13 values (`n = 15, 21, 23, 25, 27, 29, 31, 34, 35, 36, 37,
39, 40`) get `NO_FACTORIZATION` within the family scope described below,
extending SR1-style full D-rigidity to those specific `A_n` (sec 4l/4t),
conditional on the same CFSG/coverage caveats as v_task15–18.

Files: `v_task19_af.g` (main script, self-contained, engine copied from
`v_task18_bm.g` with two adaptations — see header comment), `v_task19_out.txt`
(raw log, run via `gap -q -o 8g < v_task19_af.g > v_task19_out.txt`, exit 0).
All figures below are quoted from the raw log; line numbers refer to
`v_task19_out.txt`.

## Method

Same SR1/AF condition as v_task18: `N = |S1|*...*|Sk|*c` (`k<=3`, each `Si`
nonabelian simple, `c` an admissible `Out`-part), trivial `k=1, S1=A_n
(order N), c=1` excluded. Engine: `GenerateCandidatesForN` /
`BuildOrderTable` / `CheckSR1`, copied verbatim from `v_task18_bm.g`
(13 Lie-type families + `A_m` + the 26 sporadics incl. B, M), with the
exact valuation-bound candidate generation unchanged: for prime `p | N`
with valuation `v_p(N)`, a family member's field-extension degree `f` is
bounded by `f <= v_p(N)/E` (E = fixed small constant per family), which is
non-arbitrary and exhaustive within the family scope — no magnitude
truncation.

**Two adaptations for this task** (both documented in the script header):

1. **Symmetry-generous `c`-bound.** `v_task18`'s rule was `c | Out-product`.
   When a factorization repeats an order value (`Si` and `Sj` chosen with
   the same order), the true bound also has a `k!`-style permutation factor
   (`Out(S x S)` has an extra swap generator beyond `Out(S)^2`). Per the
   task brief's "allow generously" instruction, `AllowedC(c, outProd,
   symFactor)` multiplies in `symFactor` (2 for one repeated pair among
   `k=2/3`, 6 for `k=3` all-equal) before testing `c | (outProd*symFactor)`.
   This is strictly more permissive than v_task18's rule (reproduces it
   exactly when `symFactor=1`) — it can only ADD `FACTORIZATION_EXISTS`
   hits relative to the tighter rule, never remove one. In this run no hit
   actually needed `symFactor > 1` (all witnesses below have `symFactor=1`
   printed), so every hit reported here already holds under the original,
   stricter v_task18 rule too.

2. **Field-automorphism edge case** (NOTES sec 4u (iii)). A forced prime `P`
   can enter a candidate's order via a field-extension degree rather than
   the base prime — `Out(L2(2^P)) = C_P`. `GenerateCandidatesForN`'s main
   loop cannot produce this (it only varies `f` up to `v_p(N)/E` for base
   `p`). A dedicated `FieldAutomorphismCheck` tries `L2(r^P)` for every
   prime `r | N`, `r <> P`, per forced prime `P`, subject to the necessary
   valuation budget `f = P <= v_r(N)` (a prerequisite, since `L2(q)`'s order
   has exact `r`-valuation `f`), and exact-divides-tests the resulting
   order against `N`. Result: **zero hits across all 32 values of n and
   all forced primes** (log: no `ANOMALY` lines anywhere; every `(P,r)`
   pair is explicitly printed either `SKIP (budget fails)` or `does NOT
   divide N -- rejected`) — confirming the sec 4u (iii) prediction
   computationally, not just asserting it.

**Family scope** (identical to v_task18, self-contained copy): `A_m`
(`m = 5 .. largest prime factor of N` — an exact sub-bound of the task's
"m=5..40" that is provably tight, per v_task18's own argument: `m!/2` for
`m` beyond `N`'s largest prime factor necessarily carries a prime `N`
doesn't have), `L2(q)`, `L3(q)`, `U3(q)`, `S4(q)=Sp4(q)`, `L4(q)`, `U4(q)`,
`G2(q)`, `Sz(q)`, `Ree(q)=^2G2(q)`, `Sp6(q)`, `L5(q)`, `U5(q)`, plus all 26
sporadics (24 ATLAS-hardcoded + B + M, orders fetched live via CTblLib as
correctness gate). **Not covered:** `PSL/PSU(n,q)` n>=6, `PSp(2n,q)` n>=4,
orthogonal groups, exceptional `E6/E7/E8/F4/^3D4/^2F4(q)` — same honesty
standard as v_task15–18.

Formula spot-checks (log lines 1–8, all `OK`): `|A5|=60`, `|L2(7)|=168`,
`|L3(4)|=20160`, `|PSL(5,2)|=9999360`, `|Sz(8)|=29120`, `|Sp6(2)|=1451520`,
`|Ree(27)|=10073444472`.

## Control: n=8 rediscovers the L3(4) coincidence (log lines 10–18)

`N8 = 20160`. `OrderCoincidenceCheck` finds **two** order-20160 candidates
besides `A8`: `L3(4)` (Out=12) and `L4(2)` (Out=2). **Caveat worth stating
explicitly:** `L4(2)` is not a genuine second coincidence — `PSL(4,2) ≅ A8`
is a classical exceptional group isomorphism, so "`L4(2)`" and "`A8`" are
two names for the *same* group, not two groups of the same order. The
actual CFSG-order-theorem exception is `L3(4)` alone (a group genuinely
non-isomorphic to `A8`, same order) — **CONTROL PASSED**. As a bonus,
the standard `k<=3` search (not required for the control, informational
only, n=8 is outside the 9..40 AF range) also finds `FACTORIZATION_EXISTS`:
`A5 * L3(2) * 2` (`L3(2) ≅ L2(7)`, order 168) — i.e. `|A8|` also
factors as `|A5|*|L2(7)|*2`, a genuine Fitting-free non-simple witness at
order 20160 distinct from the L3(4) coincidence.

## Controls: n=9, n=10 ("M11-style negative sanity" — expectation falsified)

Both printed in full per the task brief (forced-prime candidate lists,
full in-scope divisor lists, near-miss log) — log lines 20–99.

**n=9** (`N=181440=2^6*3^4*5*7`, forced primes `{5,7}`, 8 in-scope divisors
`[60,168,360,504,2520,6048,20160,25920]`): **`FACTORIZATION_EXISTS`**,
witness `A5 * L2(8) * 6` (`Out=2,3`, `symFactor=1`), i.e.
`|A5|*|L2(8)|*6 = 60*504*6 = 181440 = |A9|`.

**n=10** (`N=1814400`, forced prime `{7}`, 9 in-scope divisors): **`FACTORIZATION_EXISTS`**,
witness `A6 * A7 * 2` (`Out=4,2`, `symFactor=1`), i.e.
`|A6|*|A7|*2 = 360*2520*2 = 1814400 = |A10|`.

**Independent re-verification, two layers, both outside the arithmetic
sieve:**

1. *Plain Python* (`math.factorial`, no GAP): `60*504*6 == 9!/2` and
   `360*(math.factorial(7)//2)*2 == 10!/2` both confirmed exactly.
2. *Direct GAP group construction* (not order arithmetic — the actual
   groups): `G := DirectProduct(SymmetricGroup(5), Image(IsomorphismPermGroup(AutomorphismGroup(PSL(2,8)))))` has
   `Size(G) = 181440 = 9!/2` exactly, `Size(FittingSubgroup(G)) = 1`
   (Fitting-free), `IsSimpleGroup(G) = false`, `Size(Socle(G)) = 30240 =
   |A5|*|PSL(2,8)|` — i.e. `G = S5 x Aut(PSL(2,8))` is a genuine
   Fitting-free non-simple group of order exactly `|A9|`. (For n=10, the
   simpler witness `S6 x A7` has order `720*2520 = 1814400 = |A10|` and is
   Fitting-free by the identical argument — `S6`, `A7`'s only normal
   subgroups are `1, A6/A7, S6/A7`, none nontrivial-nilpotent.)

**Conclusion: the n=9,10 controls do NOT behave like the M11 negative
control.** They are, instead, the first two instances of a pattern that
recurs through much of the n=9..40 range (see below): `A_n` at these orders
sits at an *arithmetic coincidence* with a genuine product-of-two-almost-
simple-groups order, exactly analogous in kind (though not in mechanism)
to the A8/L3(4) coincidence — except here it is a `k=2` (two-factor
socle) coincidence rather than a `k=1` single-simple-group one.

## Full n=9..40 sweep

Verdict and witness per `n` (log: `=== n = <n> ===` blocks, lines per the
table below; `VERDICT (n=<n>):` lines give the authoritative per-run
verdict).

| n | N = n!/2 | Forced primes | Verdict | Witness (if FACTORIZATION) |
|---|---|---|---|---|
| 9 | 181440 | 5,7 | **FACTORIZATION** | `A5 * L2(8) * 6` |
| 10 | 1814400 | 7 | **FACTORIZATION** | `A6 * A7 * 2` |
| 11 | 19958400 | 7,11 | **FACTORIZATION** | `A7 * M11 * 1` |
| 12 | 239500800 | 7,11 | **FACTORIZATION** | `L2(11) * A9 * 2` |
| 13 | 3113510400 | 7,11,13 | **FACTORIZATION** | `A5 * L2(11) * L2(27) * 8` |
| 14 | 43589145600 | 11,13 | **FACTORIZATION** | `L2(13) * A11 * 2` |
| 15 | 653837184000 | 11,13 | NO_FACTORIZATION | — |
| 16 | 10461394944000 | 11,13 | **FACTORIZATION** | `L2(64) * A11 * 2` |
| 17 | 177843714048000 | 11,13,17 | **FACTORIZATION** | `L2(16) * A14 * 1` |
| 18 | 3201186852864000 | 11,13,17 | **FACTORIZATION** | `L2(17) * A15 * 2` |
| 19 | 60822550204416000 | 11,13,17,19 | **FACTORIZATION** | `L2(16) * J1 * L3(9) * 2` |
| 20 | 1216451004088320000 | 11,13,17,19 | **FACTORIZATION** | `L2(19) * A17 * 2` |
| 21 | 25545471085854720000 | 11,13,17,19 | NO_FACTORIZATION | — |
| 22 | 562000363888803840000 | 13,17,19 | **FACTORIZATION** | `J1 * A18 * 1` |
| 23 | 12926008369442488320000 | 13,17,19,23 | NO_FACTORIZATION | — |
| 24 | 310224200866619719680000 | 13,17,19,23 | **FACTORIZATION** | `L2(23) * A21 * 2` |
| 25 | 7755605021665492992000000 | 13,17,19,23 | NO_FACTORIZATION | — |
| 26 | 201645730563302817792000000 | 17,19,23 | **FACTORIZATION** | `L2(25) * A23 * 2` |
| 27 | 5444434725209176080384000000 | 17,19,23 | NO_FACTORIZATION | — |
| 28 | 152444172305856930250752000000 | 17,19,23 | **FACTORIZATION** | `L2(8) * L2(25) * A23 * 3` |
| 29 | 4420880996869850977271808000000 | 17,19,23,29 | NO_FACTORIZATION | — |
| 30 | 132626429906095529318154240000000 | 17,19,23,29 | **FACTORIZATION** | `L2(29) * A27 * 2` |
| 31 | 4111419327088961408862781440000000 | 17,19,23,29,31 | NO_FACTORIZATION | — |
| 32 | 131565418466846765083609006080000000 | 17,19,23,29,31 | **FACTORIZATION** | `L2(31) * A29 * 2` |
| 33 | 4341658809405943247759097200640000000 | 17,19,23,29,31 | **FACTORIZATION** | `L2(32) * A30 * 1` |
| 34 | 147616399519802070423809304821760000000 | 19,23,29,31 | NO_FACTORIZATION | — |
| 35 | 5166573983193072464833325668761600000000 | 19,23,29,31 | NO_FACTORIZATION | — |
| 36 | 185996663394950608733999724075417600000000 | 19,23,29,31 | NO_FACTORIZATION | — |
| 37 | 6881876545613172523157989790790451200000000 | 19,23,29,31,37 | NO_FACTORIZATION | — |
| 38 | 261511308733300555880003612050037145600000000 | 23,29,31,37 | **FACTORIZATION** | `L2(37) * A35 * 2` |
| 39 | 10198941040598721679320140869951448678400000000 | 23,29,31,37 | NO_FACTORIZATION | — |
| 40 | 407957641623948867172805634798057947136000000000 | 23,29,31,37 | NO_FACTORIZATION | — |

**Tally: 19 FACTORIZATION, 13 NO_FACTORIZATION** (out of 32).

**Recurring pattern:** most `FACTORIZATION` witnesses have the shape
`L2(P) * A_{m} * c` for `P` a forced prime near `n/2` and `m` close to
`n-2`/`n-3` — a family resemblance, not a coincidence confined to one or
two `n`. Several have `c=1` (n=17, n=22 above; also implicit whenever the
printed `Out`-product exactly equals `c`), meaning the witness is an
**unconditional** direct product of two (or three) simple groups with
*no* `Out`-lifting required at all — the strongest possible counterexample
form, immune to any argument about which extensions of the socle are
"generically implausible."

**Independent spot-check (outside GAP, plain Python `math.factorial`)** of
three more witnesses, all exact:
```
n=17: 4080 * (14!//2) * 1        == 17!//2   (L2(16)*A14*1)
n=22: 175560 * (18!//2) * 1      == 22!//2   (J1*A18*1)
n=33: 32736 * (30!//2) * 1       == 33!//2   (L2(32)*A30*1)
```

## Order-N coincidence check, n=9..40 (log: `Order-N coincidence check` blocks)

Zero hits for every `n` in 9..40 (`hits: 0` in every block) — within the
covered family+sporadic scope, `A_n` is the unique simple group of order
`n!/2` for all `n` in this range, confirming the note's CFSG-order-theorem
claim computationally. (Only `n=8`, run as a separate control outside the
range, has the known exception — see above.)

## Field-automorphism edge case, n=9..40

Checked explicitly for every forced prime `P` and every candidate base
`r | N`, `r <> P` (log: `Field-automorphism edge case` blocks under each
`n`). **Zero hits across the entire sweep** — no `ANOMALY` line appears
anywhere in `v_task19_out.txt`. Every `(P,r)` pair is either rejected by
the necessary valuation-budget prefilter (`SKIP (budget fails: need
f=P <= v_r(N)=...)`) or by the exact big-integer divisibility test
(`... does NOT divide N -- rejected`). This confirms NOTES sec 4u (iii)'s
prediction computationally for the full n=9..40 range: the "forced prime
hides in a field automorphism" gap never actually produces a surviving
candidate here.

## Implication for Theorem AF (sec 4u)

**Theorem AF as literally stated — "for all n>=5, every Fitting-free group
of order n!/2 is simple" — is FALSE, within the family scope of this
program, for n = 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 22, 24, 26,
28, 30, 32, 33, 38** (19 values in 9..40, plus the pre-existing n=8
L3(4) coincidence). Two of these (n=17, n=22) are unconditional (`c=1`)
and two more (n=9, n=10) are independently confirmed by direct GAP group
construction, not merely order arithmetic. This is not a coverage gap or
an inconclusive result — it is an exact, exhaustive-within-scope,
multiply-cross-checked refutation.

**What survives:** for the 13 values `n = 15, 21, 23, 25, 27, 29, 31, 34,
35, 36, 37, 39, 40`, this run gives `NO_FACTORIZATION`, exact within the
13-family + 26-sporadic scope (same caveat as v_task15–18: not a certified
CFSG-exhaustive sweep — `PSL/PSU(n,q)` n>=6, `PSp(2n,q)` n>=4, orthogonal
groups, and the exceptional Lie types are not covered at any `n`). For
these 13 values, SR1-style full D-rigidity of `A_n` (sec 4l/4t) extends
unconditionally within scope.

**Note for NOTES.md sec 4u:** the "hand progress" text there (`k < n/2`
for `n>=22`, forced-prime-in-field-automorphism as "the identified
obstruction") addresses a real but narrower question — ruling out `k=1`
single-simple-factor escapes for large `n`. It does not, and was not
claimed to, rule out `k=2`/`k=3` direct-product-style escapes such as the
`L2(P)*A_m*c` family found here, which persist well past `n=22` (e.g.
n=24,26,28,30,32,33,38). The per-n sweep requested by this task was the
right way to discover this — Theorem AF requires a materially different
statement (e.g. restricting to specific `n`, or characterizing this
`L2(P)*A_m` family and excluding it by name) before the general claim can
be pursued further.

## Coverage statement

Same as v_task18: exact, N-specific, non-truncated within the 13-family +
26-sporadic scope for every `n` in this run (candidate generation is
exhaustive relative to that scope: field-extension degrees are bounded by
`f <= v_p(N)/E`, never by a magnitude cutoff). **Not covered at any `n`:**
`PSL/PSU(n,q)` n>=6, `PSp(2n,q)` n>=4, orthogonal `O(2n+1,q)`/`O^±(2n,q)`,
exceptional `E6/E7/E8/F4/³D4/²F4(q)`. A `NO_FACTORIZATION` verdict above is
exact relative to this scope, not a certified CFSG-exhaustive claim; a
`FACTORIZATION_EXISTS` verdict, by contrast, is a positive existence proof
(the witness's order arithmetic is exact and independently re-verified) and
is not affected by the coverage caveat at all.
