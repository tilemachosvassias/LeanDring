# v_task24 — the κ-invariant: separating A_n from its order-twins

**Date:** 2026-08-07.  **Engine:** GAP 4.15.1 (`~/gap-4.15.1/gap`, macOS).
**Companion notes:** `Even/NOTES.md` §4aj.

## The invariant

Müller Satz 2.3.3: the pair `(H, hH')` has conductor `(N_G(H,hH') : H')`,
and `N_G(H,H') = N_G(H)`.  So the conductor multiset — intrinsic, by the
kernel-checked `conductorMultiplicity_eq_of_ringEquiv` — contains
`|N_G(H)|/|H'|` for every subgroup `H`.  Put

  `κ(G) = max{ |N_G(H)|/|H'| : 1 ≠ H ≤ G }`,   `ι(G) = |G|/κ(G)`.

For `G` Fitting-free, `κ(G)` is exactly the **second-largest conductor**
(the largest, `|G|`, occurs once, at the trivial pair, by Satz 2.3.6).
No species labels are involved, so this is not behind the Gap-1 wall.

## 1. `ι(A_n)`, exhaustive over the full subgroup lattice (`v_task24_kappa*`)

| n | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|
| `κ(A_n)` | 12 | 36 | 72 | 1344 | 2160 |
| `ι(A_n)` | 5 | 10 | 35 | **15** | 84 |
| `C(n,3)` | 10 | 20 | 35 | 56 | 84 |
| witness `H` | `V₄` | `C₃×C₃` | `C₃` | `2³` | `C₃` |

`ι(A_n) = C(n,3)` for `n ≥ 7` **except `n = 8`**, where the witness is the
regular `2³ ⊴ AGL(3,2) ≤ A₈` of index 15 — the `A₈ ≅ L₄(2)` coincidence.
Every witness is abelian, so `ι(A_n) = min{ [A_n : N(H)] : 1 ≠ H abelian }`
in this range.

`ι(A₁₀) = 120 = C(10,3)`, minimised over all cyclic subgroups and all abelian
subgroups of all Sylow subgroups (not the full lattice — the full lattice of
`A₁₀` was not attempted).  Hence `κ(A₁₀) = 15120`.

## 2. The `A₁₀` tie, broken (`v_task24_kappa_twin*`)

`A₁₀` vs its twin `S₆ × A₇` is the program's only recorded `mult₁`
coincidence (both 4, §4w), previously separated only by the full rank
`r` (1658 vs 34707).  With `κ`:

| H | `[T : N_T(H)]` | ⟹ |
|---|---|---|
| `Syl₃(A₆) = C₃×C₃` in the `A₆` factor | 10 | `κ(T) ≥ 181440` |
| 3-cycle in the `A₇` factor | 35 | `κ(T) ≥ 51840` |

against `κ(A₁₀) = 15120`.  **Separated by a factor of 12**, with two
normalizer computations and no census.

## 3. Theorem κ-A (NOTES §4aj)

For `n ≥ 9`, any Fitting-free `T` with `|T| = |A_n|` whose socle has an
alternating factor `A_m` (`5 ≤ m ≤ n−2`) satisfies `ι(T) ≤ ι(A_m) <
C(n,3) = ι(A_n)`, hence `κ(T) > κ(A_n)` and `D(A_n) ≇ D(T)`.  Uniform in
`n`, no computation per pair.

Every twin the v_task19/v_task20 sweeps produced has an alternating socle
factor — all seven `A₁₀`-twins (socle `A₆ × A₇`), the `A₁₁` twin `A₇ × M₁₁`,
the `A₁₂` twins, `S₅ × Aut(L₂(8))` at `n = 9`, `L₂(16) × A₁₄` at `n = 17`,
`J₁ × A₁₈` at `n = 22`, `A₅·L₂(11)·L₂(27)·8` at `n = 13` — so all are
separated by κ-A.

## 4. Bonus: BC1 without a census, and why κ stops there

`ι(PSp₆(q)) = (q⁶−1)/(q−1)` (point-parabolic = normalizer of the abelian
long root subgroup).  `ι(Ω₇(q)) = min{ (q⁶−1)/(q−1), q³(q³−1)/2 }`, the
second term being the non-singular point stabilizer = `C_G(t)` for an
involution `t`.  At `q = 3`: **351 vs 364** — different, so
`D(Ω₇(3)) ≇ D(PSp₆(3))` with no perfect-subgroup census at all.  (Both
numbers are the minimal permutation degrees already used by v_task10.)

The crossover is at `q = 4`: for `q ≥ 5` the two values coincide
(3906 both at `q = 5`), so **κ is blind to `B₃/C₃` for `q ≥ 5`** — the
duality gives the two groups identical parabolic index data.  That is why
T-BC needs the bottom of the multiset (`mult₁`) rather than the top.

## Honest limits

- `ι(A_n) = C(n,3)` for general `n ≥ 9` rests on the standard
  large-subgroup bound for `A_n` [LIT-CHECK]; it is verified exhaustively
  only for `n ≤ 9`, and for `n = 10` over cyclic + abelian-in-Sylow
  subgroups.
- Theorem κ-A covers only twins **with** an alternating socle factor.  The
  residue (all socle factors non-alternating) is swept in §5 below, for
  `n ≤ 150` and within the stated family scope.

## Files

`v_task24_kappa.g/_out.txt` (full-lattice `κ(A_n)`, n = 5..9),
`v_task24_kappa_twin.g/_out.txt` (`ι(A₁₀)`, and the `S₆ × A₇` twin),
`v_task24_spor_iota.g/_out.txt` (sporadic `ι` bounds from CTblLib),
`v_task24_residue.py/_out.txt` (the arithmetic sweep).

## 5. The residue, swept (`v_task24_spor_iota*`, `v_task24_residue*`)

Theorem κ-A covers twins with an alternating socle factor.  Any other twin is
separated as soon as **one** factor has `ι < C(n,3)`.  So the residue question
is purely arithmetic: *is there a factorization of `n!/2` all of whose factors
have `ι ≥ C(n,3)`?*

`ι` upper bounds used (each valid — the subgroup is `N(H)` for a nontrivial
abelian `H`): minimal parabolic / isotropic-point index for Lie type
(`P = N(Z(U_P))`); smallest nontrivial class size for sporadics
(`N(⟨x⟩) ⊇ C(x)`), computed from CTblLib for all 26; exact values for
alternating.

**Result: over `5 ≤ n ≤ 150`, with `k ≤ 5` socle factors and the exact
`Out`-divisibility condition `c ∣ ∏|Out(S_i)|`, there are ZERO such
factorizations.**  Candidate counts per `n` run from 15 (n=9) to 342 (n=150),
of which 0–18 are "large-ι" at any given `n`, and no product of those divides
`n!/2` with an admissible cofactor.

The one near-miss is `n = 10`: `J₂ · c = 3`, killed because `Out(J₂) = 2` does
not admit `c = 3`.  It survives only under a size bound instead of a
divisibility condition — the same error that invalidated v_task12.

**Theorem AT (NOTES §4aj addendum):** for `5 ≤ n ≤ 150`, every Fitting-free
non-simple `T` with `|T| = |A_n|` has `κ(T) ≠ κ(A_n)`, hence
`D(A_n) ≇ D(T)`.  With `simpleGroupTheorem`, **`A_n` is D-rigid among all
finite groups for `5 ≤ n ≤ 150`**.

Previous status: 17 of 32 values in `9..40`, each closed by a per-pair
`RepresentativesPerfectSubgroups` census.  The sweep replacing them runs in
seconds.

**Scope:** the candidate families are v_task18/19's 13 plus all 26 sporadics —
not a certified CFSG-exhaustive list; `k ≤ 5`; and `ι(A_n) = C(n,3)` for
`n ≥ 9` rests on the standard large-subgroup bound [LIT-CHECK], verified
exhaustively only for `n ≤ 9`.
