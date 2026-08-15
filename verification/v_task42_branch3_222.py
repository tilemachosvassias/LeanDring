#!/usr/bin/env python3
"""v_task42, sweep 1 -- branch (III) of Theorem TO' over the 222 admissible
factorizations (n = 5..70, k <= 4).

Branch (III) of Theorem TO' is the case  "iota(A_n) = C(n,3) is NOT in P",
i.e. the smallest conductor of T is realised by a multi-support or a
factor-permuting abelian subgroup rather than by a single socle component.
By Lemma TR-2 / TR-3 that forces

        C(n,3)  >=  Phi := min( nu_min^2 , |S_min| )                (III.1)

and, by Lemma TO-0 (I(T) contains P, hypothesis-free),

        min P   >=  C(n,3).                                          (III.2)

A factorization is EXCLUDED from branch (III) if either

  (E1)  Phi_lo > C(n,3)      where Phi_lo = min( mu_min^2, |S_min| )
        and mu(S) <= nu(S) (Lemma TR-4) -- so Phi >= Phi_lo and (III.1) fails;
        equivalently C(n,3) IS in P, and Theorem TO's branch structure applies;

  (E2)  minP_ub < C(n,3)     where minP_ub = min_O ell_O*|Out(S_O)|*iota1(S_O)
        >= min P, so (III.2) fails.  This is the Lemma TO-0 separation: such a
        T has iota(T) <= min P < C(n,3), hence kappa(T) != kappa(A_n).

Both bounds are conservative in the direction that makes exclusion HARDER,
exactly as in v_task35: mu <= nu lowers Phi_lo, and |Out|*iota1 >= the true
pair invariant raises minP_ub.

Data and the factorization enumeration are imported verbatim from
v_task35_star_check.py (same cands()/search()/orbits_of()).
"""
import sys
from math import factorial, comb
from v_task35_star_check import cands, search, orbits_of

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 70
KMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 4

tot = 0
e1 = e2 = both = live = 0
live_rows = []
onlyE2 = []

for n in range(5, NMAX + 1):
    N = factorial(n) // 2
    C3 = comb(n, 3)
    for chosen, c in search(N, cands(N, n), KMAX):
        tot += 1
        orb = orbits_of(chosen)
        mu_min = min(r["nu"] for _, r in orb)          # nu >= mu; r["nu"] is the mu-bound
        s_min = min(r["order"] for _, r in orb)
        Phi_lo = min(mu_min * mu_min, s_min)
        minP_ub = min(ell * r["out"] * r["iota1"] for ell, r in orb)
        ok1 = Phi_lo > C3
        ok2 = minP_ub < C3
        fac = " * ".join(f"{r['name']}^{ell}" if ell > 1 else r["name"] for ell, r in orb)
        if ok1 and ok2:
            both += 1
        elif ok1:
            e1 += 1
        elif ok2:
            e2 += 1
            onlyE2.append((n, c, fac, Phi_lo, C3, minP_ub))
        else:
            live += 1
            live_rows.append((n, c, fac, Phi_lo, C3, minP_ub))

print(f"# v_task42 sweep 1: branch (III) over admissible factorizations n=5..{NMAX}, k<={KMAX}")
print(f"total factorizations           : {tot}")
print(f"excluded by BOTH (E1) and (E2) : {both}")
print(f"excluded by (E1) only  [C(n,3) in P, Phi_lo > C(n,3)] : {e1}")
print(f"excluded by (E2) only  [Lemma TO-0 separation]        : {e2}")
print(f"LIVE in branch (III)           : {live}")
print()
print("--- (E2)-only rows (branch (III) not excludable by the floor; separated by TO-0) ---")
for n, c, fac, P, C3, m in onlyE2:
    print(f"  n={n:3d} c={c:<4d} {fac}\n        Phi_lo={P}  C(n,3)={C3}  minP_ub={m}")
if not onlyE2:
    print("  -- none --")
print()
print("--- LIVE rows (would need a genuine branch-(III) argument) ---")
for n, c, fac, P, C3, m in live_rows:
    print(f"  n={n:3d} c={c:<4d} {fac}\n        Phi_lo={P}  C(n,3)={C3}  minP_ub={m}")
if not live_rows:
    print("  -- none: branch (III) is empty on all 222 --")
