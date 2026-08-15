# swaprigid.py -- B4'/swap-problem search for 2-groups of order 16.
#
# For a 2-group G the mod-p block structure is a single block (Cor. C2),
# so the swap question must be attacked with HIGHER congruences.
# Intrinsic, twist-safe invariants used here:
#   * unique prime over 2 in Z[zeta_{2^k}] (totally ramified), pi = 1-zeta;
#     v = pi-adic valuation.
#   * for species s,t and gamma in Gamma = Gal(Q(zeta)/Q):
#       d_gamma(s,t) = min_{x in D(G)} v( s(x) - gamma(t(x)) )
#     (min over a Z-basis attains the min over the lattice).
#     A ring automorphism Phi induces s -> gamma_s o pi(s); the MULTISET
#     {d_gamma(s,t) : gamma} is Phi-invariant (relative twists permute Gamma),
#     and the Gamma-action on species classes commutes with pi.
#   * Gamma-stabilizers and Gamma-edges.
# WL refinement on these; if every stable class is fibre-pure and level-pure,
# then NO ring automorphism of D(G) can swap trivial/nontrivial fibres or
# mix subgroup levels. Signatures are deterministic (sha1 of canonical
# strings) => comparable across groups/processes: differing multisets rule
# out shadow isomorphisms D(G) ~ D(G~) at this invariant level.

import sys, json, hashlib
from fractions import Fraction
from dring2 import (Group, DRing, cyclic, dihedral, dicyclic, exponent,
                    cyclotomic)

# ---------------- constructors: the 14 groups of order 16 ----------------
def direct_product(A, B, name):
    E = [(i, j) for i in range(A.n) for j in range(B.n)]
    return Group(E, lambda a, b: (A.M[a[0]][b[0]], B.M[a[1]][b[1]]), name)

def metacyclic(n, r, name):  # <a,b | a^n, b^2, b a b^-1 = a^r>
    E = [(i, j) for j in range(2) for i in range(n)]
    def mul(a, b):
        i, j = a; k, l = b
        return ((i + (k if j == 0 else (r * k))) % n, (j + l) % 2)
    return Group(E, mul, name)

def C4sC4():  # C4 : C4, b a b^-1 = a^-1
    E = [(i, j) for j in range(4) for i in range(4)]
    def mul(a, b):
        i, j = a; k, l = b
        return ((i + (k if j % 2 == 0 else -k)) % 4, (j + l) % 4)
    return Group(E, mul, "C4:C4")
def V4sC4():  # (C2xC2) : C4, generator of C4 swaps coordinates
    E = [((x, y), j) for j in range(4) for x in range(2) for y in range(2)]
    def mul(a, b):
        (x1, y1), j = a; (x2, y2), l = b
        if j % 2 == 1: x2, y2 = y2, x2
        return (((x1 + x2) % 2, (y1 + y2) % 2), (j + l) % 4)
    return Group(E, mul, "C2^2:C4")
def Pauli():  # C4 o D4 central product (Pauli group P1)
    E = [(s, x, z) for s in range(4) for x in range(2) for z in range(2)]
    def mul(a, b):
        s1, x1, z1 = a; s2, x2, z2 = b
        return ((s1 + s2 + 2 * z1 * x2) % 4, (x1 + x2) % 2, (z1 + z2) % 2)
    return Group(E, mul, "C4oD4(Pauli)")

GROUPS16 = {
    "C16":     lambda: cyclic(16),
    "C8xC2":   lambda: direct_product(cyclic(8), cyclic(2), "C8xC2"),
    "C4xC4":   lambda: direct_product(cyclic(4), cyclic(4), "C4xC4"),
    "C4xC2xC2":lambda: direct_product(cyclic(4),
                        direct_product(cyclic(2), cyclic(2), "V4"), "C4xC2^2"),
    "C2^4":    lambda: direct_product(
                        direct_product(cyclic(2), cyclic(2), "V4"),
                        direct_product(cyclic(2), cyclic(2), "V4"), "C2^4"),
    "D8_16":   lambda: dihedral(8),
    "Q16":     lambda: dicyclic(4),
    "SD16":    lambda: metacyclic(8, 3, "SD16"),
    "M4_2":    lambda: metacyclic(8, 5, "M4(2)"),
    "D4xC2":   lambda: direct_product(dihedral(4), cyclic(2), "D4xC2"),
    "Q8xC2":   lambda: direct_product(dicyclic(2), cyclic(2), "Q8xC2"),
    "C4sC4":   C4sC4,
    "V4sC4":   V4sC4,
    "Pauli":   Pauli,
}

# ---------------- fast species table via subgroup-lattice precompute -----
class FastDRing(DRing):
    def _species_table(self):
        G, N = self.G, self.N
        subs = self.subs
        sid = {S: i for i, S in enumerate(subs)}
        leq = [[S <= T for T in subs] for S in subs]
        # conj_of[g][i] = index of g^-1 * subs[i] * g
        conj_of = [[sid[frozenset(G.conjT[G.inv[g]][x] for x in subs[i])]
                    for i in range(len(subs))] for g in range(G.n)]
        T = []
        for (H, cs, Hp, _) in self.species:
            hi = sid[H]; h = min(cs); row = []
            for (K, lam) in self.basis:
                ki = sid[K]
                counts = [0] * N
                for g in range(G.n):
                    if leq[conj_of[g][hi]][ki]:
                        counts[lam[G.conjT[G.inv[g]][h]]] += 1
                vec = [0] * self.phiN
                for k, c in enumerate(counts):
                    if c:
                        zp = self.zpow[k]
                        for i in range(self.phiN): vec[i] += c * zp[i]
                kK = len(K)
                assert all(v % kK == 0 for v in vec)
                row.append(tuple(v // kK for v in vec))
            T.append(row)
        return T

# ---------------- pi-adic valuation in Z[zeta_{2^k}] ----------------
class Val2:
    def __init__(self, D):
        self.N, self.m = D.N, D.phiN
        m = self.m
        # matrix P of multiplication by (1 - zeta): columns (1-z)*z^i
        P = [[0] * m for _ in range(m)]
        for i in range(m):
            col = list(D.zpow[i])
            z1 = D.zpow[(i + 1) % D.N] if i + 1 < D.N else D.zpow[0]
            col = [col[r] - D.zpow[i + 1][r] for r in range(m)] if i + 1 < D.N \
                  else [col[r] - z1[r] for r in range(m)]
            for r in range(m): P[r][i] = col[r]
        # exact inverse via fractions; adj = det * P^{-1}
        A = [[Fraction(P[r][c]) for c in range(m)] + \
             [Fraction(1 if c == r else 0) for c in range(m)]
             for r in range(m)]
        det = Fraction(1)
        for c in range(m):
            pr = next(r for r in range(c, m) if A[r][c] != 0)
            A[c], A[pr] = A[pr], A[c]
            if pr != c: det = -det
            det *= A[c][c]
            inv = 1 / A[c][c]
            A[c] = [v * inv for v in A[c]]
            for r in range(m):
                if r != c and A[r][c] != 0:
                    f = A[r][c]
                    A[r] = [A[r][k] - f * A[c][k] for k in range(2 * m)]
        self.det = int(det)
        assert abs(self.det) == 2, self.det   # Norm(1-zeta_{2^k}) = 2
        self.adj = [[int(A[r][m + c] * det) for c in range(m)]
                    for r in range(m)]
    def val(self, vec, cap=200):
        v = list(vec)
        if all(x == 0 for x in v): return None       # +infinity
        c = 0
        while c < cap:
            if sum(v) % 2 != 0: return c             # residue != 0
            y = [sum(self.adj[r][k] * v[k] for k in range(self.m))
                 for r in range(self.m)]
            if any(x % self.det for x in y): return c
            v = [x // self.det for x in y]
            if all(x == 0 for x in v): return None
            c += 1
        return cap

# ---------------- Gamma action ----------------
def units(N): return [a for a in range(1, N) if __import__('math').gcd(a, N) == 1]
def gamma_vec(D, a, vec):
    out = [0] * D.phiN
    for i, v in enumerate(vec):
        if v:
            zp = D.zpow[(a * i) % D.N]
            for r in range(D.phiN): out[r] += v * zp[r]
    return tuple(out)
def gamma_species_perm(D, a):
    G = D.G
    key2i = {D.species[i][3]: i for i in range(len(D.species))}
    perm = []
    for (H, cs, Hp, _) in D.species:
        h = min(cs)
        ha = G.e
        for _ in range(a % G.ordv[h]): ha = G.M[ha][h]
        csa = frozenset(G.M[ha][x] for x in Hp)
        perm.append(key2i[D._pair_canon(H, csa)])
    return perm

def fibre_order(D, i):
    G = D.G
    (H, cs, Hp, _) = D.species[i]
    cosH = D._cosets(H, Hp); cmap = {}
    for k, c in enumerate(cosH):
        for x in c: cmap[x] = k
    e_i = cmap[G.e]; rep = [min(c) for c in cosH]; cur = cmap[min(cs)]
    o, z = 1, cur
    while z != e_i:
        z = cmap[G.M[rep[z]][rep[cur]]]; o += 1
    return o

# ---------------- the certificate ----------------
def certify(name, iters=8):
    G = GROUPS16[name]()
    D = FastDRing(G)
    n = len(D.species)
    V = Val2(D)
    U = units(D.N)
    perms = {a: gamma_species_perm(D, a) for a in U}
    # precompute gamma-twisted rows
    tw = {a: [[gamma_vec(D, a, v) for v in row] for row in D.table]
          for a in U}
    ncol = n
    INF = 10 ** 6
    def dtuple(i, j):
        ds = []
        for a in U:
            best = INF
            ri, rj = D.table[i], tw[a][j]
            for c in range(ncol):
                diff = [ri[c][r] - rj[c][r] for r in range(D.phiN)]
                if sum(diff) % 2 != 0: best = 0; break
                w = V.val(diff)
                if w is not None and w < best: best = w
            ds.append(best)
        return tuple(sorted(ds))
    E = [[None] * n for _ in range(n)]
    for i in range(n):
        for j in range(i, n):
            rel = tuple(sorted(a for a in U if perms[a][i] == j))
            relb = tuple(sorted(a for a in U if perms[a][j] == i))
            dt = dtuple(i, j)
            E[i][j] = (dt, rel, relb); E[j][i] = (dt, relb, rel)
    # WL refinement, deterministic hashing
    col = [hashlib.sha1(repr(E[i][i]).encode()).hexdigest()[:16]
           for i in range(n)]
    for _ in range(iters):
        new = []
        for i in range(n):
            sig = sorted((E[i][j], col[j]) for j in range(n) if j != i)
            new.append(hashlib.sha1(
                (col[i] + repr(sig)).encode()).hexdigest()[:16])
        col = new
    classes = {}
    for i in range(n): classes.setdefault(col[i], []).append(i)
    # purity checks
    fib = [fibre_order(D, i) for i in range(n)]
    lev = [D.species[i][3][0] for i in range(n)]
    fibre_impure, level_impure, swap_pairs = [], [], []
    for c, mem in classes.items():
        trivs = [i for i in mem if fib[i] == 1]
        if trivs and len(trivs) != len(mem):
            fibre_impure.append(sorted((fib[i], len(lev[i])) for i in mem))
            if any(fib[i] == 2 for i in mem):
                swap_pairs.append(sorted(mem))
        if len({lev[i] for i in mem}) > 1:
            level_impure.append(sorted((len(lev[i]), fib[i]) for i in mem))
    res = dict(name=G.name, n_species=n, n_classes=len(classes),
               fibre_pure=not fibre_impure, level_pure=not level_impure,
               fibre_impure=fibre_impure[:5], level_impure=level_impure[:5],
               swap_candidates=swap_pairs[:5],
               sigs=sorted(col))
    with open(f"rigid_{name}.json", "w") as f:
        json.dump(res, f)
    print(f"{G.name}: species={n} classes={len(classes)} "
          f"fibre_pure={res['fibre_pure']} level_pure={res['level_pure']}")
    if fibre_impure:
        print("  FIBRE-IMPURE (fib_ord,|H|) classes:", fibre_impure[:3])
    if level_impure:
        print("  LEVEL-IMPURE (|H|,fib_ord) classes:", level_impure[:3])
    return res

if __name__ == "__main__":
    for nm in sys.argv[1:]:
        certify(nm)
