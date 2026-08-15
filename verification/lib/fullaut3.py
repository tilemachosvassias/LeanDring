# fullaut3.py -- exact Aut(D(G)) for 2-groups via prefix-lattice pruning.
# L = ghost image of D(G) in Z^(n*m) (species-major, m = phi(N) coords each).
# A candidate automorphism assigns, species by species in a fixed order,
# an image pi(s) and a twist gamma_s.  After each assignment, every basis
# element's PARTIAL image vector must lie in the projection of L onto the
# assigned coordinates (HNFs precomputed once).  Sound and very sharp.

import argparse
import sys
from fractions import Fraction
from itertools import product
from latauto import CycField, solve_matrix
from swaprigid import (FastDRing, Val2, units, gamma_vec,
                       gamma_species_perm, fibre_order, GROUPS16)
from dring2 import cyclic, dihedral, dicyclic

def hnf(rows):
    rows = [r[:] for r in rows if any(r)]
    if not rows: return [], []
    ncol = len(rows[0]); piv = []; r0 = 0
    for c in range(ncol):
        while True:
            nz = [i for i in range(r0, len(rows)) if rows[i][c] != 0]
            if not nz: break
            i0 = min(nz, key=lambda i: abs(rows[i][c]))
            rows[r0], rows[i0] = rows[i0], rows[r0]
            done = True
            for i in range(r0 + 1, len(rows)):
                if rows[i][c]:
                    q = rows[i][c] // rows[r0][c]
                    rows[i] = [a - q * b for a, b in zip(rows[i], rows[r0])]
                    if rows[i][c]: done = False
            if done: break
        if r0 < len(rows) and rows[r0][c] != 0:
            if rows[r0][c] < 0: rows[r0] = [-a for a in rows[r0]]
            piv.append((r0, c)); r0 += 1
            if r0 == len(rows): break
    return rows[:r0], piv

def member(v, rows, piv):
    w = list(v)
    for (r, c) in piv:
        if w[c]:
            q, rem = divmod(w[c], rows[r][c])
            if rem: return False
            w = [a - q * b for a, b in zip(w, rows[r])]
    return not any(w)

def full_aut3(Gctor, node_cap=2 * 10**6, verbose=True):
    G = Gctor(); D = FastDRing(G); n = len(D.species); m = D.phiN
    F = CycField(D.N); U = units(D.N)
    gperm = {a: gamma_species_perm(D, a) for a in U}
    tw = {a: [[tuple(gamma_vec(D, a, v)) for v in row] for row in D.table]
          for a in U}
    # distinct twist actions per (target) species
    twist_reps = []
    for i in range(n):
        seen = set(); reps = []
        for a in U:
            key = tuple(tw[a][i][c] for c in range(n))
            if key not in seen: seen.add(key); reps.append(a)
        twist_reps.append(reps)
    # lattice vectors: x_b = concat_s table[s][b]  (species-major)
    Lrows = [[D.table[s][b][r] for s in range(n) for r in range(m)]
             for b in range(n)]
    # prefix HNFs
    H = []
    for k in range(1, n + 1):
        rows, piv = hnf([row[:k * m] for row in Lrows])
        H.append((rows, piv))
    # cheap node invariant for candidate filtering: valuation profile row
    V = Val2(D)
    INF = 10**6
    def rowprof(i):
        prof = []
        for a in U:
            vals = sorted((V.val(tw[a][i][c]) or 0) if V.val(tw[a][i][c])
                          is not None else INF for c in range(n))
            prof.append(tuple(vals))
        return tuple(sorted(prof))
    prof = [rowprof(i) for i in range(n)]
    # backtracking
    auts = []
    nodes = [0]
    capped = [False]
    partial = [[[] for _ in range(n)]]  # partial[0][b] grows by m coords/step
    def extend(s, pim, twv, partial):
        if capped[0]: return
        if s == n:
            auts.append((dict(pim), dict(twv))); return
        forced = pim.get(s, None)
        cands = [forced] if forced is not None else \
                [j for j in range(n) if j not in pim.values()]
        for j in cands:
            if forced is None and j in pim.values(): continue
            # Gamma-equivariance forcing
            add = {s: j}; good = True
            for a in U:
                ia, ja = gperm[a][s], gperm[a][j]
                cur = pim.get(ia, add.get(ia))
                if cur is not None and cur != ja: good = False; break
                add[ia] = ja
            if not good: continue
            vals = set(add.values()) | {v for k, v in pim.items()
                                        if k not in add}
            ok2 = True
            for k, v in add.items():
                for k2, v2 in pim.items():
                    if v2 == v and k2 != k: ok2 = False; break
                if not ok2: break
            if not ok2: continue
            for a in twist_reps[j]:
                if node_cap is not None and nodes[0] >= node_cap:
                    capped[0] = True
                    return
                nodes[0] += 1
                # extend partial vectors by coords of species s
                newp = []
                fail = False
                rows, piv = H[s]
                for b in range(n):
                    pv = partial[b] + list(tw[a][j][b])
                    if not member(pv, rows, piv): fail = True; break
                    newp.append(pv)
                if fail: continue
                pim2 = dict(pim); pim2.update(add)
                twv2 = dict(twv); twv2[s] = a
                extend(s + 1, pim2, twv2, newp)
                if capped[0]: return
    extend(0, {}, {}, [[] for _ in range(n)])
    if verbose:
        suffix = " (CAPPED; result is a lower bound)" if capped[0] else \
                 " (exhaustive)"
        print(f"  search nodes: {nodes[0]}{suffix}", flush=True)
    # exact verification + dedupe by U-matrix
    Bm = [[tuple(Fraction(v) for v in vec) for vec in row] for row in D.table]
    result = {}
    for pim, twv in auts:
        pi = [pim[i] for i in range(n)]
        FB = [[tuple(Fraction(x) for x in
                     gamma_vec(D, twv.get(i, 1), D.table[pi[i]][c]))
               for c in range(n)] for i in range(n)]
        Um = solve_matrix(F, Bm, FB)
        if Um is None: continue
        ok = all(e[0].denominator == 1 and all(x == 0 for x in e[1:])
                 for row in Um for e in row)
        if not ok: continue
        Ut = tuple(tuple(int(Um[r][c][0]) for c in range(n))
                   for r in range(n))
        U2 = solve_matrix(F, FB, Bm)
        if U2 is None or not all(e[0].denominator == 1 and
                                 all(x == 0 for x in e[1:])
                                 for row in U2 for e in row): continue
        result[Ut] = (pi, twv)
    fib = [fibre_order(D, i) for i in range(n)]
    lev = [len(D.species[i][3][0]) for i in range(n)]
    triv = [b for b, (K, lam) in enumerate(D.basis)
            if all(lam[x] == 0 for x in K)]
    A = list(result.items())
    nsw = sum(1 for Ut, (pi, _) in A
              if any((fib[i] == 1) != (fib[pi[i]] == 1) for i in range(n)))
    nlv = sum(1 for Ut, (pi, _) in A
              if any(lev[i] != lev[pi[i]] for i in range(n)))
    def eta_setwise(Ut):
        return all(all(Ut[r][c] == 0 for r in range(n) if r not in triv)
                   for c in triv)
    neta = sum(1 for Ut, _ in A if eta_setwise(Ut))
    bound = "≥" if capped[0] else ""
    if neta < len(A):
        eta_note = "  *** eta(B) moved ***"
    elif capped[0]:
        eta_note = "  no moving witness among found; characteristic UNDECIDED"
    else:
        eta_note = "  ALL preserve eta(B)"
    print(f"{G.name}: species={n} |Aut(D)|={bound}{len(A)} "
          f"fibre-swap={bound}{nsw} "
          f"level-mix={nlv} eta-setwise={neta}" + eta_note, flush=True)
    return A

if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Exact Aut(D(G)) search for supported small 2-groups")
    parser.add_argument("groups", nargs="+")
    parser.add_argument("--node-cap", type=int, default=2 * 10**6)
    args = parser.parse_args()
    ctors = {"C2": lambda: cyclic(2), "C4": lambda: cyclic(4),
             "V4": lambda: dihedral(2), "C8": lambda: cyclic(8),
             "D4": lambda: dihedral(4), "Q8": lambda: dicyclic(2),
             "C2xC4": lambda: Group([(i,j) for i in range(2) for j in range(4)],
                                    lambda a,b: ((a[0]+b[0])%2, (a[1]+b[1])%4),
                                    "C2xC4")}
    ctors.update(GROUPS16)
    for nm in args.groups:
        full_aut3(ctors[nm], node_cap=args.node_cap)
