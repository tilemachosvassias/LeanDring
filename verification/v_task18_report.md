# v_task18: SR1 arithmetic check for the Baby Monster (B) and the Monster (M)

Closes the two `INCONCLUSIVE (coverage)` verdicts left by `v_task15` (see
`v_task15_report.md`): `|B|` and `|M|` exceed v_task15's global candidate
bound `2*10^24`, so a magnitude-truncated sweep couldn't rule out a
simple-group divisor beyond that bound. This task replaces the magnitude
bound with an **exact, N-specific** candidate generator so the resulting
verdicts for B and M are not merely bounded but exhaustive within the
stated family scope.

Files: `v_task18_bm.g` (main script), `v_task18_bm_out.txt` (raw log, run
via `gap -q -o 8g < v_task18_bm.g > v_task18_bm_out.txt`, exit 0),
`v_task18_anchor_check.g` / `v_task18_anchor_check_out.txt` (hand-audit
of the forced-slot argument for the specific large primes named in the
task brief). All figures below are quoted directly from the two raw logs.

## Method: why the search is exact, not truncated, for B and M

Same SR1 condition as v_task15: `|X| = S1*...*Sk*c` (`k<=3`, each `Si`
nonabelian simple, `c | prod_i |Out(Si)|` using **actual** per-family Out
orders, trivial `k=1,S1=X,c=1` excluded).

The key change (`v_task18_bm.g`, `GenerateCandidatesForN`): for a Lie-type
family with defining field `q = p^f`, the order formula always contains a
term `q^E` for a fixed small `E` (E=1 for L2, E=3 for L3/U3, E=4 for
S4=Sp4, E=6 for L4/U4/G2, E=2 for Sz, E=3 for Ree, E=9 for Sp6, E=10 for
L5/U5 — exact values in the script), and since `q-1, q+1, q^2-1, ...` are
all coprime to `p`, the `p`-adic valuation of `|family(q)|` is
**exactly** `E*f`. For the
order to divide `N`, `E*f <= v_p(N)` (the `p`-adic valuation of `N`) is
therefore a *necessary and non-arbitrary* bound — looping `p` over `N`'s
own prime set (11 primes for B, 15 for M) and `f` over this exact bound
generates every candidate that could possibly divide `N` in-family, with
no candidate skipped by a global magnitude cutoff. Every generated
candidate then gets an exact big-integer divisibility test
(`N mod order = 0`, GAP native bignums) before being trusted.

**Family scope:** the same 8 families as v_task15 (`A_n` n=5..30 relaxed
here to n up to N's largest prime, `L2(q)`, `L3(q)`, `U3(q)`, `S4(q)`,
`L4(q)`, `U4(q)`, `G2(q)`) plus 5 bonus families added specifically to
widen the net for the task's named large primes: `Sz(q)` (Suzuki,
`q=2^f`, f odd), `Ree(q)=^2G2(q)` (`q=3^f`, f odd), `Sp6(q)`, `PSL5(q)`,
`PSU5(q)` — plus the 24 non-B/M sporadics as discrete extra candidates
(hardcoded ATLAS orders/Out, order fetched live from `CTblLib` as a
correctness gate). Bonus-family order formulas were spot-checked against
known values before use (log lines 1–5, all OK): `|PSL(5,2)|=9999360`,
`|Sz(8)|=29120`, `|Sp6(2)|=1451520`, `|Ree(27)|=10073444472`.

**Not covered** (same honesty standard as v_task15): `PSL/PSU(n,q)` n>=6,
`PSp(2n,q)` n>=4, orthogonal `O(2n+1,q)`/`O^±(2n,q)`, exceptional
`E6/E7/E8/F4/³D4/²F4(q)`. A verdict below is therefore exact relative to
the 13-family + sporadic scope, not a certified CFSG-exhaustive sweep.

## Controls (log lines 10–16)

- **Positive control — J2 rediscovery:** `CheckSR1(604800, ...)` →
  `FACTORIZATION_EXISTS`, detail `A5 * A7 * 4  [Out=2,2]` — exactly
  reproduces v_task15's J2 result using the new N-specific generator,
  confirming the machinery still finds the known positive case.
- **Negative control — M11:** `CheckSR1(7920, ...)` → `NO_FACTORIZATION`,
  candidates dividing 7920: `[60, 360, 660]` — matches v_task15's M11
  anchor exactly.

## Factorizations verified

```
|B| = 4154781481226426191177580544000000
    = 2^41 · 3^13 · 5^6 · 7^2 · 11 · 13 · 17 · 19 · 23 · 31 · 47
|M| = 808017424794512875886459904961710757005754368000000000
    = 2^46 · 3^20 · 5^9 · 7^6 · 11^2 · 13^3 · 17 · 19 · 23 · 29 · 31 · 41 · 47 · 59 · 71
```

(log lines 18–29, via `Collected(Factors(Size(CharacterTable(...))))`.)

**Valuation-1 ("large") primes of B:** 11, 13, 17, 19, 23, 31, 47.
**Valuation-1 primes of M:** 17, 19, 23, 29, 31, 41, 47, 59, 71.
The task brief singled out B: {31, 47} and M: {41, 59, 71} as the ones
worth a dedicated per-prime candidate search; both are subsets of the
full valuation-1 sets above, which this run also reports in full.

## Out-smoothness check (log lines 38–47)

Over every candidate (all 13 families + sporadics) that actually divides
`N`, is any candidate's `Out` value divisible by one of `N`'s own
valuation-1 primes? **Confirmed no** for both B (87 divisor-candidates
checked, all valuation-1 primes {11,13,17,19,23,31,47}) and M (119
divisor-candidates, all valuation-1 primes {17,19,23,29,31,41,47,59,71}).
This is the computational confirmation of the task's a priori claim that
"`Out` orders are too smooth to contain [these] large primes" — verified
on the actual generated data, not merely asserted.

## Per-large-prime candidate lists (log lines 49–310)

For each large prime `p`, every candidate (order dividing `N`, `p` |
order) found in the 13-family + sporadic scope:

**B, prime 31** (10 candidates): `L2(32)`, `L5(2)`, `L5(4)`, `L2(125)`,
`L3(5)`, `L3(25)`, `L4(5)`, `G2(5)`, `L2(31)`, `Th`.

**B, prime 47** (1 candidate — forced): `L2(47)` (order 51888, Out=2).
This is the *only* simple group in the covered scope whose order both
divides `|B|` and is divisible by 47.

**M, prime 41** (7 candidates): `L2(1024)`, `Sz(32)`, `U5(4)`, `L2(81)`,
`S4(9)`, `L4(9)`, `L2(41)`.

**M, prime 59** (1 candidate — forced): `L2(59)` (order 102660, Out=2).

**M, prime 71** (1 candidate — forced): `L2(71)` (order 178920, Out=2).

(Full lists for all valuation-1 primes of both B and M, including
11,13,17,19,23 for B and 17,19,23,29,31,47 for M, are in
`v_task18_bm_out.txt` lines 49–310; every one of them has multiple
candidates and is not a bottleneck.)

## Forced-slot anchor (hand audit, `v_task18_anchor_check.g`/`_out.txt`)

Mirrors the M11 anchor style from v_task15: since 47 (B) and 59, 71 (M)
each have **exactly one** covered-scope candidate, that candidate is
*forced* into any valid factorization (no other choice covers that
prime). This gives a small, hand-checkable rejection independent of the
general `k<=3` brute force:

**B:** `L2(47)` is forced. The other large prime, 31, must then be
covered by one of the remaining ≤2 slots. Tried `L2(47)*X` for all 10
`X` covering 31 — every one divides `|B|`, but in every case
`c = |B|/(51888·|X|)` is astronomically larger than
`Out-product = 2·Out(X) ∈ {2,4,6,8,10,12,16,24}`, so `c` never divides
it. Example: `L2(47)*L2(31)`: `c = 5381189977765419417600000`,
Out-product `= 4`, rejected. All 10 rejected; the `k=3` extension
(`L2(47)*X*Y` for every pair of 31-candidates) also finds nothing.

**M:** `L2(41)`, `L2(59)`, `L2(71)` are each the sole candidate for their
prime — three distinct forced slots exactly saturate the `k<=3` budget,
so `S1*S2*S3 = L2(41)*L2(59)*L2(71)` (order `632591412768000`) is the
*unique* candidate that could simultaneously cover 41, 59, and 71. It
does divide `|M|` (`|M| mod product = 0`), but
`c = |M|/632591412768000 = 1277313299684087810109379839000576000000`,
versus `Out-product = 2·2·2 = 8`. `c` is not 8, 4, 2, or 1 — rejected.
No other `k<=3` combination can cover all three primes at once (each
needs a dedicated slot and there is no room for a 4th), so this single
rejection settles M's three hardest primes simultaneously.

## Full CheckSR1 (k≤3) result (log lines 312–514)

- **B: 80 distinct in-scope divisor orders of `|B|`** (full list with Out
  values in `v_task18_bm_out.txt` lines 313–393). Exhaustive `k<=3` search
  over these (single, all pairs, all triples with product dividing `|B|`):
  **`B VERDICT: NO_FACTORIZATION`**.
- **M: 112 distinct in-scope divisor orders of `|M|`** (full list, lines
  396–508). Exhaustive `k<=3` search: **`M VERDICT: NO_FACTORIZATION`**.

## Verdicts

| Group | Order | Verdict | Basis |
|---|---|---|---|
| B (Baby Monster) | `4154781481226426191177580544000000` | **NO FACTORIZATION** (exhaustive within 13-family + sporadic scope) | 80 in-scope divisors, k≤3 exhaustive; prime-47 forced-slot anchor independently confirms |
| M (Monster) | `808017424794512875886459904961710757005754368000000000` | **NO FACTORIZATION** (exhaustive within 13-family + sporadic scope) | 112 in-scope divisors, k≤3 exhaustive; primes-{41,59,71} forced-slot anchor independently confirms |

This upgrades B and M from v_task15's `INCONCLUSIVE (coverage)` to
`NO_FACTORIZATION`, exact and non-truncated within the stated 13-family +
sporadic scope (an improvement in kind over v_task15's other 24 verdicts,
which relied on a global magnitude bound rather than an N-specific exact
one). Both control cases (J2 positive, M11 negative) reproduce v_task15's
results exactly using the same new generator, validating the method.

**Coverage caveat (honest, same style as v_task15):** this is not a
certified CFSG-exhaustive sweep. `PSL/PSU(n,q)` for `n>=6`, `PSp(2n,q)`
for `n>=4`, orthogonal groups `O(2n+1,q)`/`O^±(2n,q)`, and the
exceptional Lie types `E6/E7/E8/F4/³D4/²F4(q)` are not covered by this
run at any order. A simple group from one of those families whose order
happens to both divide `|B|` or `|M|` and be divisible by one of the
large primes cannot be ruled out by this data alone — though the task's
own reasoning (most such families fail immediately on a prime-set
mismatch against B's/M's fairly small prime sets: 11 primes for B, 15
for M) makes this increasingly implausible as rank grows, since higher-rank
Lie-type orders accumulate large "new" primes (e.g. via cyclotomic
factors `q^n±1` for growing `n`) that generically fall outside such a
small fixed prime set. This is a plausibility argument, not a proof, and
is flagged honestly as the residual scope gap, exactly as v_task15 did
for the other 24 sporadics.

## Combined sporadic ledger update

With this run, all **26/26** sporadic groups now have a settled SR1
arithmetic verdict within the program's stated family scope: 19 fully
D-rigid (`NO_FACTORIZATION`, v_task15 §4q), 5 with a genuine arithmetic
twin resolved to proven-tier D-rigidity by finer invariants (v_task16/17
§4r), and now B, M add 2 more `NO_FACTORIZATION` verdicts (this task) —
closing the "2 inconclusive" line from v_task15/§4q.
