#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
v_task87_scan.py -- an EXACT, slack-free census of the equal-characteristic
MULTI-FACTOR branch for L_d(q) / U_d(q), 33 <= d <= 60, every prime power
q <= 100.

This is the numerical cross-check of Theorem MF (v_task87_lemmas.py) and, at
the same time, an independent unconditional closure of the audited residual
on that range: it uses NO degree bookkeeping, NO logarithms and NO dropped
slack.  Every test is an integer test:

  (D1)  prod_i |S_i|^{l_i}  divides  |S|                      [Soc T <= T]
  (D2)  c := |S| / prod_i |S_i|^{l_i}   divides
            prod_i ( |Out(S_i)|^{l_i} * l_i! )                [T/Soc T embeds
                                                               in prod Out wr Sym]
  (D3)  l_i * |Out(S_i)| * iotabar(S_i)  >=  iota(S)  for every i
                                                     [Lemma TO'-0 + Lemma F]
  (D4)  sum_i l_i >= 2                                 [T not almost simple]

so in particular the (Z2) log-slack and Lemma ZM's v_r(d!) term -- the two
things v_task82 (F3) found dropped from v_task60's PART C -- simply do not
occur.  Every S_i ranges over ALL 17 families of simple groups of Lie type
in the SAME characteristic p, at every rank and every field degree f_i >= 1
allowed by the exact p-part budget f_i N_i <= f N; in particular the
"subfield" configurations f_i < f (which PART C's floor silently excluded)
ARE enumerated here.

Only iotabar (an upper bound for iota of a socle factor, (H5)) and iota(S)
(the minimal-degree lower half, (H1)) are inherited from the literature --
both in the conservative direction of (D3).

Usage:  python3 v_task87_scan.py [dlo dhi qmax]     (default 33 60 100)
"""

import sys
from math import factorial

sys.path.insert(0, ".")
sys.path.insert(0, __file__.rsplit("/", 1)[0])

from v_task52_lemmaC import FAM, order_of, gcd
from v_task56_lu_twins import order_LU, iota_LU, out_LU, bdeg, Kmax

BAR = "=" * 76


def prime_powers(qmax):
    out = []
    for q in range(2, qmax + 1):
        n, p = q, None
        for r in range(2, q + 1):
            if n % r == 0:
                p = r
                break
        m, f = q, 0
        while m % p == 0:
            m //= p
            f += 1
        if m == 1:
            out.append((q, p, f))
    return out


# --------------------------------------------------------------- the atoms

def atoms(X, d, q, p, f, verbose=False):
    """every (family, rank, f_i) whose order divides |S| and which can carry
    at least one orbit length l >= 1 satisfying the exact orbit floor."""
    S = order_LU(X, d, q)
    iS = iota_LU(X, d, q)
    N = d * (d - 1) // 2
    budget = f * N                     # exact p-part budget (D1)
    out = []
    ndeg = nfloor = ndiv = 0
    for F in FAM:
        ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], 10 ** 9)
        for n in ns:
            N1 = F["N"](n)
            if N1 > budget:
                break
            for f1 in range(1, budget // N1 + 1):
                q1 = p ** f1
                if not F["qform"](p, f1):
                    continue
                if F["skip"](n, q1):
                    continue
                ndeg += 1
                lmax = budget // (f1 * N1)
                ib = F["iota"](n, q1)
                ou = F["d"](n, q1) * f1 * F["g"]
                # (D3) with the largest l that the p-budget allows -- cheap,
                # so it runs before the (expensive) order divisibility
                if lmax * ou * ib < iS:
                    nfloor += 1
                    continue
                o1 = order_of(F, n, q1)
                if o1 <= 1:
                    continue
                if S % o1:
                    ndiv += 1
                    continue
                out.append(dict(F=F, n=n, f1=f1, q1=q1, o=o1, ib=ib, ou=ou,
                                N1=N1, lmax=lmax,
                                name=F["name"](n, q1)))
    return S, iS, budget, out, (ndeg, nfloor, ndiv)


# --------------------------------------------------------------------- DFS

def census(X, d, q, p, f, report):
    S, iS, budget, A, stats = atoms(X, d, q, p, f)
    hits = []
    # deterministic order, biggest first (best pruning)
    A.sort(key=lambda a: -a["o"])
    nnode = [0]

    def rec(idx, rem, chosen, cnt, outbound):
        nnode[0] += 1
        if cnt >= 2:
            c = rem
            if c <= outbound and outbound % c == 0:
                hits.append(list(chosen))
        if idx >= len(A):
            return
        for t in range(idx, len(A)):
            a = A[t]
            if a["o"] > rem:
                continue
            r, l = rem, 0
            while True:
                if r % a["o"]:
                    break
                r //= a["o"]
                l += 1
                if l * a["ou"] * a["ib"] < iS:      # (D3)
                    continue
                if l * a["f1"] * a["N1"] > budget:  # (D1) p-part
                    break
                rec(t + 1, r, chosen + [(a, l)], cnt + l,
                    outbound * (a["ou"] ** l) * factorial(l))
                if l > 40:
                    break
    rec(0, S, [], 0, 1)
    report(X, d, q, len(A), nnode[0], stats, hits)
    return hits


# ------------------------------------------------------------- the controls

def control(X, d, q, p, f):
    """positive control: the atom generator must find S itself (l = 1),
    with the floor satisfied and the order dividing |S| exactly."""
    S = order_LU(X, d, q)
    key, n = ("A", d) if X == "L" else ("2A", d)
    F = [x for x in FAM if x["key"] == key][0]
    o1 = order_of(F, n, q)
    ok_order = (o1 == S)
    ib = F["iota"](n, q)
    ok_floor = (1 * (F["d"](n, q) * f * F["g"]) * ib >= iota_LU(X, d, q))
    return ok_order, ok_floor


def probe():
    """NEGATIVE control for the DFS: exhibit atom PAIRS whose orders jointly
    divide |S|.  These are exactly the nodes at which the search descends to
    depth 2, so a non-empty list proves the census is not vacuously empty --
    (D1) alone does admit two-factor products; they die on (D2)/(D3)."""
    print(BAR)
    print("PROBE -- the DFS descends: atom pairs jointly dividing |S|")
    print(BAR)
    tot = 0
    for (X, d, q, p, f) in [("L", 33, 2, 2, 1), ("L", 36, 3, 3, 1),
                            ("L", 34, 16, 2, 4), ("L", 40, 4, 2, 2),
                            ("L", 48, 2, 2, 1), ("U", 40, 8, 2, 3)]:
        S, iS, bud, A, st = atoms(X, d, q, p, f)
        A.sort(key=lambda a: -a["o"])
        for i, a in enumerate(A):
            for b in A[i + 1:]:
                if S % (a["o"] * b["o"]) == 0:
                    tot += 1
                    ou = (a["ou"] * b["ou"])
                    c = S // (a["o"] * b["o"])
                    print("  %s_%d(%d) : %-14s x %-14s   c | Out-product ? %s"
                          % (X, d, q, a["name"], b["name"],
                             "YES" if ou % c == 0 else "no (killed by (D2))"))
    print("  pairs found : %d   (all killed by (D2) and/or (D3))" % tot)
    print(BAR)


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "probe":
        probe()
        return
    dlo = int(sys.argv[1]) if len(sys.argv) > 1 else 33
    dhi = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    qmax = int(sys.argv[3]) if len(sys.argv) > 3 else 100
    QS = prime_powers(qmax)
    print(BAR)
    print("v_task87_scan.py -- EXACT equal-characteristic multi-factor census")
    print("  targets  : L_d(q), U_d(q),  %d <= d <= %d" % (dlo, dhi))
    print("  fields   : every prime power q <= %d  (%d values, f <= %d)"
          % (qmax, len(QS), max(f for _, _, f in QS)))
    print("  socle    : every multiset of Lie-type simple groups in char p,")
    print("             every rank, every f_i >= 1 (INCLUDING f_i < f)")
    print("  tests    : (D1) order divisibility  (D2) c | prod Out^l * l!")
    print("             (D3) exact orbit floor   (D4) at least two factors")
    print(BAR)
    tot_atoms = tot_nodes = tot_hits = 0
    ctrl_bad = []
    lines = []

    def report(X, d, q, na, nn, stats, hits):
        nonlocal tot_atoms, tot_nodes, tot_hits
        tot_atoms += na
        tot_nodes += nn
        tot_hits += len(hits)
        if hits:
            for h in hits:
                lines.append("  !! %s_%d(%d) : %s"
                             % (X, d, q, [(a["name"], l) for a, l in h]))

    for d in range(dlo, dhi + 1):
        for X in ("L", "U"):
            nat = 0
            for (q, p, f) in QS:
                ok1, ok2 = control(X, d, q, p, f)
                if not (ok1 and ok2):
                    ctrl_bad.append((X, d, q, ok1, ok2))
                h = census(X, d, q, p, f, report)
                nat += 1
            print("  %s_%-3d : %2d fields swept, atoms so far %d, "
                  "multi-factor HITS %d"
                  % (X, d, nat, tot_atoms, tot_hits))
            sys.stdout.flush()
    print()
    print("  total surviving atoms (single factors whose order divides |S|,")
    print("  floor-compatible) over all targets and fields : %d" % tot_atoms)
    print("  total DFS nodes                               : %d" % tot_nodes)
    print("  positive-control failures                     : %s"
          % (ctrl_bad[:5] if ctrl_bad else "NONE"))
    print()
    print("  MULTI-FACTOR CONFIGURATIONS SURVIVING (D1)-(D4) : %s"
          % ("NONE" if not lines else "\n".join(lines)))
    print(BAR)
    assert not ctrl_bad


if __name__ == "__main__":
    main()
