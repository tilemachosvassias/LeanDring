# latauto.py -- exact computation of the ghost-permutation automorphisms of
# D(G): permutations-with-Galois-twists (pi, gamma) of the species such that
# the induced ghost-ring automorphism F: (y_s) -> (gamma_s(y_{pi(s)}))
# preserves the lattice L = image of D(G).  Every such F restricts to a ring
# automorphism of D(G), and every ring automorphism of D(G) arises this way.
# So this computes Aut(D(G)) exactly.
#
# Checks: does any element of Aut(D(G)) move the trivial-fibre species set
# (swap problem), or mix subgroup levels (B4')?

import sys
from fractions import Fraction
from itertools import permutations, product
from dring2 import cyclotomic
from swaprigid import (FastDRing, Val2, units, gamma_vec,
                       gamma_species_perm, fibre_order, GROUPS16)
from dring2 import cyclic, dihedral, dicyclic

# ---------- exact arithmetic in Q(zeta_N): vectors of Fractions mod Phi_N
class CycField:
    def __init__(self, N):
        self.N = N
        self.Phi = cyclotomic(N)
        self.m = len(self.Phi) - 1
    def red(self, poly):
        poly = list(poly)
        for i in range(len(poly) - 1, self.m - 1, -1):
            c = poly[i]
            if c:
                for j in range(self.m + 1):
                    poly[i - self.m + j] -= c * self.Phi[j]
        poly = poly[:self.m] + [Fraction(0)] * (self.m - len(poly))
        return tuple(poly[:self.m])
    def mul(self, A, B):
        r = [Fraction(0)] * (len(A) + len(B) - 1)
        for i, a in enumerate(A):
            if a:
                for j, b in enumerate(B):
                    r[i + j] += a * b
        return self.red(r)
    def add(self, A, B): return tuple(a + b for a, b in zip(A, B))
    def sub(self, A, B): return tuple(a - b for a, b in zip(A, B))
    def zero(self): return tuple([Fraction(0)] * self.m)
    def one(self):  return tuple([Fraction(1)] + [Fraction(0)] * (self.m - 1))
    def is_zero(self, A): return all(a == 0 for a in A)
    def inv(self, A):
        # extended euclid: gcd(A(x), Phi(x)) = 1 over Q[x]
        a = [Fraction(c) for c in self.Phi]
        b = list(A)
        while b and b[-1] == 0: b.pop()
        s0, s1 = [Fraction(0)], [Fraction(1)]     # coeffs on A-side
        r0, r1 = a, b
        while True:
            while r1 and r1[-1] == 0: r1.pop()
            if len(r1) == 1:
                c = r1[0]
                return self.red([x / c for x in s1])
            q, rem = self._divmod(r0, r1)
            r0, r1 = r1, rem
            qs = self._polymul(q, s1)
            s0, s1 = s1, [ (s0[i] if i < len(s0) else Fraction(0)) -
                           (qs[i] if i < len(qs) else Fraction(0))
                           for i in range(max(len(s0), len(qs))) ]
    def _polymul(self, A, B):
        r = [Fraction(0)] * (len(A) + len(B) - 1)
        for i, a in enumerate(A):
            if a:
                for j, b in enumerate(B):
                    r[i + j] += a * b
        return r
    def _divmod(self, A, B):
        A = list(A); q = [Fraction(0)] * max(1, len(A) - len(B) + 1)
        while len(A) >= len(B) and any(A):
            while A and A[-1] == 0: A.pop()
            if len(A) < len(B): break
            c = A[-1] / B[-1]; d = len(A) - len(B)
            q[d] = c
            for j in range(len(B)):
                A[d + j] -= c * B[j]
            A.pop()
        return q, A

def solve_matrix(F, Bm, Cm):
    """solve Bm * U = Cm over the field F; Bm, Cm lists of rows."""
    n = len(Bm)
    A = [ [Bm[r][c] for c in range(n)] + [Cm[r][c] for c in range(n)]
          for r in range(n) ]
    for c in range(n):
        pr = next((r for r in range(c, n) if not F.is_zero(A[r][c])), None)
        if pr is None: return None
        A[c], A[pr] = A[pr], A[c]
        iv = F.inv(A[c][c])
        A[c] = [F.mul(iv, v) for v in A[c]]
        for r in range(n):
            if r != c and not F.is_zero(A[r][c]):
                f = A[r][c]
                A[r] = [F.sub(A[r][k], F.mul(f, A[c][k]))
                        for k in range(2 * n)]
    return [[A[r][n + c] for c in range(n)] for r in range(n)]

def integral(U):
    return all(all(x.denominator == 1 for x in ent)
               for row in U for ent in row)

def aut_group(D, verbose=True, max_perms=10**7):
    """Compute all (pi, twists) preserving the lattice; return list of pi."""
    G = D.G; n = len(D.species); N = D.N
    F = CycField(N)
    U = units(N)
    gperm = {a: gamma_species_perm(D, a) for a in U}
    # species field data: values rational iff fixed by all gamma as maps
    # (class-fixed => map-fixed as shown in step-2 notes)
    orbit_of = {}
    for i in range(n):
        orb = frozenset(gperm[a][i] for a in U)
        orbit_of[i] = orb
    # ghost matrix over the field: B[i][b]
    Bm = [[tuple(Fraction(v) for v in vec) + tuple() for vec in row]
          for row in D.table]
    Bm = [[tuple(list(e) + [Fraction(0)] * (F.m - len(e)))[:F.m]
           for e in row] for row in Bm]
    # pairwise twist-safe metric for pruning
    V = Val2(D)
    tw = {a: [[gamma_vec(D, a, v) for v in row] for row in D.table]
          for a in U}
    INF = 10**6
    def dtup(i, j):
        ds = []
        for a in U:
            best = INF
            for c in range(n):
                diff = [D.table[i][c][r] - tw[a][j][c][r]
                        for r in range(D.phiN)]
                w = V.val(diff)
                if w is None: best = INF; break
                if w < best: best = w
            ds.append(best)
        return tuple(sorted(ds))
    E = {}
    for i in range(n):
        for j in range(n):
            E[(i, j)] = dtup(i, j)
    # candidate permutations: backtracking with E-compatibility and
    # Gamma-equivariance (pi o gamma_a = gamma_a o pi on classes)
    results = []
    order = sorted(range(n))
    def extend(pos, pim):
        if pos == n:
            results.append(dict(pim)); return
        i = order[pos]
        if i in pim:
            extend(pos + 1, pim); return
        for j in range(n):
            if j in pim.values(): continue
            if E[(i, i)] != E[(j, j)]: continue
            ok = True
            for i2, j2 in pim.items():
                if E[(i, i2)] != E[(j, j2)] or E[(i2, i)] != E[(j2, j)]:
                    ok = False; break
            if not ok: continue
            # tentatively add i->j plus Gamma-orbit consistency
            add = {i: j}
            good = True
            for a in U:
                ia, ja = gperm[a][i], gperm[a][j]
                if ia in pim and pim[ia] != ja: good = False; break
                if ia in add and add[ia] != ja: good = False; break
                add[ia] = ja
            if not good: continue
            conflict = any((k in pim and pim[k] != v) or
                           (v in pim.values() and all(pim.get(k2) != v or k2 == k for k2 in pim) is False)
                           for k, v in add.items())
            # simpler conflict check
            conflict = False
            for k, v in add.items():
                if k in pim and pim[k] != v: conflict = True; break
                for k2, v2 in pim.items():
                    if v2 == v and k2 != k: conflict = True; break
            if conflict: continue
            pim2 = dict(pim); pim2.update(add)
            extend(pos + 1, pim2)
    extend(0, {})
    if verbose:
        print(f"  metric-compatible Gamma-equivariant permutations: "
              f"{len(results)}")
    # lattice check with twist search
    auts = []
    for pim in results:
        pi = [pim[i] for i in range(n)]
        # twists: only matter on non-rational species; one representative
        # per Gamma-orbit; enumerate assignments per orbit
        orbs = []
        seen = set()
        for i in range(n):
            o = tuple(sorted(orbit_of[i]))
            if o not in seen:
                seen.add(o); orbs.append(o)
        # twist choice per orbit: gamma in U/stab acting; enumerate U for
        # each nontrivial orbit representative, propagate equivariantly
        nontriv = [o for o in orbs if len(o) > 1]
        choices = list(product(U, repeat=len(nontriv))) if nontriv else [()]
        found = False
        for ch in choices:
            twist = [1] * n
            for o, a0 in zip(nontriv, ch):
                # assign twist a0 to representative, extend by equivariance:
                # twist(gamma_a s) must equal a0 (relative twists within an
                # orbit are forced up to stabilizer; enumerate rep only)
                for i in o: twist[i] = a0
            # build F(B): row i = gamma_{twist[i]} applied to row pi[i]
            FB = []
            for i in range(n):
                a = twist[i]
                row = []
                for c in range(n):
                    vec = D.table[pi[i]][c]
                    g = gamma_vec(D, a, vec)
                    row.append(tuple(list(map(Fraction, g)) +
                               [Fraction(0)] * (F.m - len(g)))[:F.m])
                FB.append(row)
            Um = solve_matrix(F, Bm, FB)
            if Um is None: continue
            if not integral(Um): continue
            # inverse direction
            Um2 = solve_matrix(F, FB, Bm)
            if Um2 is None or not integral(Um2): continue
            auts.append((pi, tuple(twist)))
            found = True
            break
        if verbose and found and any(pi[i] != i for i in range(n)):
            pass
    return auts

def report(name, ctor):
    G = ctor()
    D = FastDRing(G)
    n = len(D.species)
    print(f"== {G.name}: {n} species")
    auts = aut_group(D)
    fib = [fibre_order(D, i) for i in range(n)]
    lev = [len(D.species[i][3][0]) for i in range(n)]
    print(f"  |Aut(D(G))| (ghost-permutation autos) = {len(auts)}")
    swaps = []
    levmix = []
    for pi, twv in auts:
        for i in range(n):
            if (fib[i] == 1) != (fib[pi[i]] == 1):
                swaps.append((pi, i)); break
        for i in range(n):
            if lev[i] != lev[pi[i]]:
                levmix.append((pi, i)); break
    print(f"  autos moving trivial-fibre set: {len(swaps)}; "
          f"autos mixing |H|-levels: {len(levmix)}")
    for pi, i in swaps[:3]:
        print(f"    SWAP: species {i} (|H|={lev[i]},f={fib[i]}) -> "
              f"{pi[i]} (|H|={lev[pi[i]]},f={fib[pi[i]]})")
        print(f"    full perm: {pi}")
    return auts, swaps, levmix

if __name__ == "__main__":
    small = {"C4": lambda: cyclic(4), "V4": lambda: dihedral(2),
             "C8": lambda: cyclic(8), "D4": lambda: dihedral(4),
             "Q8": lambda: dicyclic(2)}
    small.update(GROUPS16)
    for nm in sys.argv[1:]:
        report(nm, small[nm])
