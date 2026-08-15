#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
v_task87_pos.py -- the hypothesis (POS) of Theorem MF, tested exactly.

(POS)  every socle factor of the equal-characteristic multi-factor branch is
       defined over a field at least as large as the target's:  q_i >= q,
       i.e. j_i = f_i/f >= 1.

(POS) is AUTOMATIC when f = 1, i.e. for every PRIME q.  For f >= 2 it is a
consequence of the orbit floor, and this script tests that consequence with
NO logarithms and NO slack, using only

  (F)  l * |Out(S_1)| * iotabar(S_1)  >=  iota(S)     [Lemma TO'-0 + F]
  (P)  l * f_1 * N_1  <=  f * N                       [p-part, exact]

so l <= fN/(f_1 N_1) and hence, for a SUBFIELD factor (f_1 < f) to exist at
all,
        (fN / (f_1 N_1)) * |Out(S_1)| * iotabar(S_1)  >=  iota(S).

Everything is an exact integer comparison.  The script reports, for each
target, every (family, rank, f_1 < f) that passes -- i.e. every way (POS)
could conceivably fail.

Usage: python3 v_task87_pos.py [dlo dhi qmax]     (default 33 200 4096)
"""

import sys

sys.path.insert(0, ".")
sys.path.insert(0, __file__.rsplit("/", 1)[0])

from v_task52_lemmaC import FAM
from v_task56_lu_twins import iota_LU

BAR = "=" * 76


def prime_powers_f2(qmax):
    """(q, p, f) for every prime power q <= qmax with f >= 2"""
    out = []
    for q in range(4, qmax + 1):
        p = next(r for r in range(2, q + 1) if q % r == 0)
        m, f = q, 0
        while m % p == 0:
            m //= p
            f += 1
        if m == 1 and f >= 2:
            out.append((q, p, f))
    return out


def subfield_atoms(X, d, q, p, f):
    """every (family, rank, f_1 < f) that survives (F) + (P)"""
    N = d * (d - 1) // 2
    budget = f * N
    iS = iota_LU(X, d, q)
    out = []
    for F in FAM:
        ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], 10 ** 9)
        for n in ns:
            N1 = F["N"](n)
            if N1 > budget:
                break
            for f1 in range(1, f):
                q1 = p ** f1
                if not F["qform"](p, f1) or F["skip"](n, q1):
                    continue
                lmax = budget // (f1 * N1)
                if lmax < 1:
                    continue
                ib = F["iota"](n, q1)
                ou = F["d"](n, q1) * f1 * F["g"]
                if lmax * ou * ib >= iS:
                    out.append((F["name"](n, q1), lmax))
    return out


def main():
    dlo = int(sys.argv[1]) if len(sys.argv) > 1 else 33
    dhi = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    qmax = int(sys.argv[3]) if len(sys.argv) > 3 else 4096
    QS = prime_powers_f2(qmax)
    print(BAR)
    print("v_task87_pos.py -- (POS) tested exactly")
    print("  targets : L_d(q), U_d(q), %d <= d <= %d" % (dlo, dhi))
    print("  fields  : every prime power 4 <= q <= %d with f >= 2 (%d values,"
          " f <= %d)" % (qmax, len(QS), max(f for _, _, f in QS)))
    print(BAR)
    tot = {"L": 0, "U": 0}
    ex = {"L": [], "U": []}
    for d in range(dlo, dhi + 1):
        for X in ("L", "U"):
            for (q, p, f) in QS:
                s = subfield_atoms(X, d, q, p, f)
                if s:
                    tot[X] += len(s)
                    if len(ex[X]) < 14:
                        ex[X].append((X, d, q, s[:6]))
        if d % 20 == 0 or d == dhi:
            print("  ... d = %d done   (subfield atoms so far: L %d, U %d)"
                  % (d, tot["L"], tot["U"]))
            sys.stdout.flush()
    print()
    for X in ("L", "U"):
        print("  %s tower : %d (family, rank, f_1<f) rows survive (F)+(P)"
              % (X, tot[X]))
        for e in ex[X]:
            print("      %s_%d(%d) : %s" % e)
    print()
    print("""  READING.  A row here is NOT a counterexample -- it is a single socle
  factor that the floor alone cannot exclude.  An EMPTY list for a tower is
  a proof of (POS) for that tower on the tested range; a non-empty list
  means (POS) must be imported as a hypothesis there (it still holds
  automatically for every prime q, where f = 1).""")
    print(BAR)


if __name__ == "__main__":
    main()
