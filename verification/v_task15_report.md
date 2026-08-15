# v_task15: SR1 arithmetic check for the 26 sporadic simple groups (corrected redo)

Redo of the two invalidated runs recorded in `Even/NOTES.md`:

- **v_task12** — invalid: implemented the `Out`-allowance `c` as a *size bound*
  (`c <= 576`) instead of a *divisibility* condition. All 18 "YES" verdicts
  were spurious, including a false positive on the M11 anchor.
- **v_task13** — arithmetically correct (divisibility enforced) but against a
  single *global* constant `c | 2^8*3^4 = 20736`, which is not realizable —
  it let M11 pass with `c = 12` even though the actual `Out(L2(11)) = C2`
  cannot supply a multiple of 12.

**Fix in v_task15:** for every candidate factorization `|M| = S1*...*Sk*c`
(`k <= 3`, each `Si` nonabelian simple, `k=1,S1=M,c=1` excluded), `c` must
divide the **actual** `prod_i |Out(Si)|`, computed per-family from the
standard `d.f.g` decomposition (diagonal · field · graph automorphisms), not
a global bound.

Files: `v_task15_sporadic.g` (script), `v_task15_out.txt` (raw log, run via
`gap -q < v_task15_sporadic.g > v_task15_out.txt`, exit 0, ~1.2s).  All
figures below are quoted directly from `v_task15_out.txt`.

## Out(·) formulas used (q = p^f)

| Family | `Out` formula | Note |
|---|---|---|
| `A_n`, n>=5 | 2 (4 for `A6`) | standard |
| `L2(q)` | `gcd(2,q-1)*f` | A1 diagram: no graph automorphism |
| `L3(q)` | `gcd(3,q-1)*f*2` | A2 diagram symmetry |
| `U3(q)` | `gcd(3,q+1)*f*2` | |
| `S4(q)`, q>=3 | `2*f` | uniform for q odd (d=2,g=1) and q=2^f (d=1,g=2, exceptional char-2 graph aut) |
| `L4(q)` | `gcd(4,q-1)*f*2` | A3 diagram symmetry |
| `U4(q)` | `gcd(4,q+1)*f*2` | |
| `G2(q)`, q>=3 | `f` | simply-connected = adjoint, trivial diagonal part |

Before trusting these on the sporadics, the script cross-checks them against
four known group **isomorphisms** where two different formulas must agree on
the same real `Out` value, plus three ATLAS-documented values (log lines
1–14, all `OK`):

- `L3(2) ≅ L2(7)` (order 168): both formulas give `Out=2`.
- `L4(2) ≅ A8` (order 20160): both give `Out=2`.
- `U4(2) ≅ S4(3)` (order 25920): both give `Out=2`.
- `L2(9) ≅ A6` (order 360): both give `Out=4`.
- `L3(4)`: `Out=12` (the classical exceptional `D12`), `U3(3)`: `Out=2`,
  `U3(4)`: `Out=4`, `U3(5)`: `Out=6`, `S4(4)`: `Out=4` — all match ATLAS.

**Known accidental order-collision** inside the generated range (the CFSG
order theorem's classic exception): `|A8| = |L3(4)| = 20160`, but
`Out(A8)=2 ≠ Out(L3(4))=12`. Handled explicitly: the divisibility check
tries every real group sharing a colliding order (log line 29: order 20160
→ `A8(2)`, `L3(4)(12)`, `L4(2)=A8` restated) and takes whichever choice is
most generous, so a `NO_FACTORIZATION` verdict is not an artifact of picking
the wrong realization. Four other collisions were found among the generated
candidates, all between literally isomorphic groups with identical `Out`
(orders 60, 168, 360, 25920 — log lines 26–30), so they don't affect any
verdict either way.

## Search and candidate generation

Candidates: `A_n` (n=5..30), `L2(q)`, `L3(q)`, `U3(q)`, `S4(q)`, `L4(q)`,
`U4(q)`, `G2(q)` for prime-power `q`, generated up to order
`2*10^24` — a bound chosen to exceed `|Fi24'| = 1255205709190661721292800`,
the largest of the 24 sporadics other than `B` and `M` (log lines 21–23:
553 distinct order values). For each sporadic order `N`, candidates dividing
`N` (excluding `N` itself, so the trivial `k=1,S1=M,c=1` case never appears)
are searched in subsets of size `k<=3` (with repetition, e.g. `S x S`) for
`P | N` and `c = N/P` dividing some realizable `prod |Out(Si)|`.

## Per-sporadic verdicts (from `v_task15_out.txt`, RESULTS TABLE)

| Group | \|M\| | Verdict | Detail |
|---|---|---|---|
| M11 | 7920 | **NO FACTORIZATION** | 3 candidates checked (see anchor below) |
| M12 | 95040 | **NO FACTORIZATION** | 3 candidates |
| M22 | 443520 | **FACTORIZATION** | `L2(7)*L2(11)*4` [Out=2,2], c=4 \| 4 |
| M23 | 10200960 | **NO FACTORIZATION** | 8 candidates |
| M24 | 244823040 | **FACTORIZATION** | `L2(23)*A8*2` [Out=2,2], c=2 \| 4 |
| J1 | 175560 | **NO FACTORIZATION** | 3 candidates |
| J2 | 604800 | **FACTORIZATION** | `A5*A7*4` [Out=2,2], c=4 \| 4 |
| J3 | 50232960 | **NO FACTORIZATION** | 6 candidates |
| J4 | 86775571046077562880 | **NO FACTORIZATION** | 14 candidates |
| HS | 44352000 | **NO FACTORIZATION** | 8 candidates |
| McL | 898128000 | **NO FACTORIZATION** | 14 candidates |
| He | 4030387200 | **NO FACTORIZATION** | 11 candidates |
| Ru | 145926144000 | **NO FACTORIZATION** | 16 candidates |
| Suz | 448345497600 | **FACTORIZATION** | `L3(3)*A11*4` [Out=2,2], c=4 \| 4 |
| ON | 460815505920 | **NO FACTORIZATION** | 15 candidates |
| Co3 | 495766656000 | **NO FACTORIZATION** | 16 candidates |
| Co2 | 42305421312000 | **NO FACTORIZATION** | 16 candidates |
| Co1 | 4157776806543360000 | **NO FACTORIZATION** | 33 candidates |
| Fi22 | 64561751654400 | **NO FACTORIZATION** | 25 candidates |
| Fi23 | 4089470473293004800 | **NO FACTORIZATION** | 31 candidates |
| Fi24' | 1255205709190661721292800 | **NO FACTORIZATION** | 35 candidates |
| HN | 273030912000000 | **NO FACTORIZATION** | 17 candidates |
| Ly | 51765179004000000 | **NO FACTORIZATION** | 19 candidates |
| Th | 90745943887872000 | **FACTORIZATION** | `L3(3)*L2(125)*U3(8)*3` [Out=2,6,18], c=3 \| 216 |
| B | 4154781481226426191177580544000000 | **INCONCLUSIVE (coverage)** | \|B\| exceeds the 2·10^24 candidate bound |
| M | 808017424794512875886459904961710757005754368000000000 | **INCONCLUSIVE (coverage)** | \|M\| exceeds the 2·10^24 candidate bound |

**Summary counts (log lines 88–93):** NO FACTORIZATION (SR1 holds, fully
D-rigid): **19**. FACTORIZATION EXISTS (explicit witness, SR1 doesn't
immediately settle rigidity): **5** — M22, M24, J2, Suz, Th. INCONCLUSIVE
(coverage bound): **2** — B, M.

The 5 `FACTORIZATION` verdicts are *arithmetic* necessary-condition hits
(e.g. `168*660*4 = 443520 = |M22|` with `Out(L2(7))=Out(L2(11))=2`, so
`c=4 | 2*2=4`), independently re-verified in Python outside GAP. They mean
the simple arithmetic SR1 test does not by itself rule out a Fitting-free
non-simple partner of matching order — it does **not** mean D-rigidity
actually fails for these five, only that this particular necessary-condition
check is inconclusive for them and would need the deeper argument (does a
genuine group of that shape exist and is it D-separated) that was used by
hand for the A8/L3(4) pair elsewhere in the thread.

## M11 anchor (mandatory, log lines 70–86)

`|M11| = 7920`. Candidates dividing 7920 (excluding 7920 itself): `[60, 360,
660]`, realized by:

- order 60: `A5 (Out=2)`, `L2(4) (Out=2)`, `L2(5) (Out=2)`
- order 360: `A6 (Out=4)`, `L2(9) (Out=4)`
- order 660: `L2(11) (Out=2)`

No pair among `{60,360,660}` multiplies to a divisor of 7920 (all three
pairwise products exceed 7920), so only `k=1` near-misses exist; `k=2,3`
contribute nothing. All three `k=1` attempts are rejected:

- `S1` order 60 (`A5`/`L2(4)`/`L2(5)`, Out-options `[2,2,2]`): `c = 7920/60 =
  132`; **132 does not divide any of [2,2,2]** — rejected.
- `S1` order 360 (`A6`/`L2(9)`, Out-options `[4,4]`): `c = 7920/360 = 22`;
  **22 does not divide any of [4,4]** — rejected.
- `S1` order 660 (`L2(11)`, Out-options `[2]`): `c = 7920/660 = 12`; **12
  does not divide [2]** — rejected. (This is exactly the near-miss flagged
  as spuriously "YES" in the invalidated v_task12/v_task13 runs.)

**M11 verdict: NO_FACTORIZATION — SR1 holds, M11 is fully D-rigid**, matching
the hand-proof in `Even/NOTES.md` §4k addendum.

## Coverage statement

Family scope: `A_n` (n=5..30), `L2(q)`, `L3(q)`, `U3(q)`, `S4(q)`, `L4(q)`,
`U4(q)`, `G2(q)`, generated up to order `2*10^24`. **Not covered at any
order:** Suzuki `Sz(q)`, Ree `²G2(q)`/`²F4(q)`, `PSL/PSU(n,q)` for `n>=5`,
`PSp(2n,q)` for `n>=3`, orthogonal `O(2n+1,q)`/`O^±(2n,q)`, exceptional
`E6/E7/E8/F4/³D4`. A `NO FACTORIZATION` verdict therefore means: no
factorization exists using the covered families (candidate generation was
not truncated below `|M|` for any of the 24 non-`B`/`M` sporadics — the bound
`2*10^24` exceeds even `|Fi24'|`), *assuming* those 8 families are the
complete relevant source of simple-group divisors for that `|M|` — it is not
a certified sweep against the full CFSG family list. `B` and `M` are
reported `INCONCLUSIVE` rather than `NO`, honestly, because their orders
(`~4*10^33`, `~8*10^53`) vastly exceed the `2*10^24` candidate bound, so a
simple-group divisor in that gap cannot be ruled out by this run.
