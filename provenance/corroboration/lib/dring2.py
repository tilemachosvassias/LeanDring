# dring2.py -- exact verification of p-local block structure of D(G)
# (Satz 2.2.7 formula vs intrinsic congruence blocks) and Theorem B5*.
# Pure python, exact arithmetic in Z[zeta_N] via reduction mod Phi_N,
# residue fields F_{p^d} = F_p[x]/f, f | Phi_{N0} mod p.

from math import gcd
from itertools import product

# ---------------- generic finite group on indices ----------------
class Group:
    def __init__(self, elems, mult, name=""):
        self.name = name
        self.elems = list(elems)
        self.n = len(self.elems)
        idx = {e: i for i, e in enumerate(self.elems)}
        self.M = [[idx[mult(a, b)] for b in self.elems] for a in self.elems]
        self.e = next(i for i in range(self.n)
                      if all(self.M[i][j] == j for j in range(self.n)))
        self.inv = [next(j for j in range(self.n) if self.M[i][j] == self.e)
                    for i in range(self.n)]
        # conj[g][x] = g x g^-1
        self.conjT = [[self.M[self.M[g][x]][self.inv[g]] for x in range(self.n)]
                      for g in range(self.n)]
        self.ordv = [self._order(x) for x in range(self.n)]
    def _order(self, x):
        o, y = 1, x
        while y != self.e:
            y = self.M[y][x]; o += 1
        return o
    def closure(self, gens):
        S = {self.e}; frontier = set(gens) | {self.e}
        S |= frontier
        while True:
            new = set()
            for a in S:
                for b in gens:
                    c = self.M[a][b]
                    if c not in S: new.add(c)
            if not new: break
            S |= new
        return frozenset(S)
    def all_subgroups(self):
        subs = {frozenset([self.e])}
        subs |= {self.closure([g]) for g in range(self.n)}
        changed = True
        while changed:
            changed = False
            for H in list(subs):
                for g in range((self.n)):
                    if g not in H:
                        K = self.closure(list(H) + [g])
                        if K not in subs:
                            subs.add(K); changed = True
        return sorted(subs, key=lambda s: (len(s), tuple(sorted(s))))
    def conj_sub(self, g, H):
        return frozenset(self.conjT[g][x] for x in H)
    def derived(self, H):
        gens = set()
        Hl = list(H)
        for a in Hl:
            for b in Hl:
                gens.add(self.M[self.M[self.M[a][b]][self.inv[a]]][self.inv[b]])
        # closure inside H (it is inside H automatically)
        return self.closure(list(gens))
    def pprime_part(self, x, p):
        o = self.ordv[x]
        a = 1
        while o % p == 0: o //= p; a *= p
        if o == 1: return self.e
        # exponent e: e = a * (a^{-1} mod o)
        e = a * pow(a, -1, o)
        y = self.e
        for _ in range(e % (self.ordv[x]) if self.ordv[x] else 0):
            y = self.M[y][x]
        return y
    def Op(self, H, p):  # O^p(H) = <p'-elements of H>
        gens = [x for x in H if self.ordv[x] % p != 0]
        return self.closure(gens)

def exponent(G):
    N = 1
    for x in range(G.n): N = N * G.ordv[x] // gcd(N, G.ordv[x])
    return N

# ---------------- group constructors ----------------
def cyclic(n):    return Group(range(n), lambda a, b: (a + b) % n, f"C{n}")
def dihedral(n):  # order 2n
    E = [(i, j) for j in range(2) for i in range(n)]
    def mul(a, b):
        i, j = a; k, l = b
        return ((i + (k if j == 0 else -k)) % n, (j + l) % 2)
    return Group(E, mul, f"D{n}(order {2*n})")
def dicyclic(n):  # order 4n, b^2=a^n
    E = [(i, j) for j in range(2) for i in range(2 * n)]
    def mul(a, b):
        i, j = a; k, l = b
        if j == 0: return ((i + k) % (2 * n), l)
        if l == 0: return ((i - k) % (2 * n), 1)
        return ((i - k + n) % (2 * n), 0)
    return Group(E, mul, f"Dic{n}(order {4*n})")
def perm_group(gens, n, name):
    idp = tuple(range(n))
    def mul(a, b): return tuple(a[b[i]] for i in range(n))
    elems = {idp}; frontier = [idp]
    while frontier:
        new = []
        for a in frontier:
            for g in gens:
                c = mul(a, g)
                if c not in elems: elems.add(c); new.append(c)
        frontier = new
    return Group(sorted(elems), mul, name)
def A4(): return perm_group([(1, 2, 0, 3), (0, 2, 3, 1)], 4, "A4")
def SL23():
    def mul(A, B):
        a, b, c, d = A; e, f, g, h = B
        return ((a*e+b*g) % 3, (a*f+b*h) % 3, (c*e+d*g) % 3, (c*f+d*h) % 3)
    elems = [(a, b, c, d) for a in range(3) for b in range(3)
             for c in range(3) for d in range(3) if (a*d-b*c) % 3 == 1]
    return Group(elems, mul, "SL(2,3)")

# ---------------- integer polynomial helpers ----------------
def polydiv_int(num, den):  # exact division, both int coeff lists (low->high)
    num = num[:]; q = [0]*(len(num)-len(den)+1)
    for i in range(len(num)-len(den), -1, -1):
        c = num[i+len(den)-1]
        assert c % den[-1] == 0
        q[i] = c // den[-1]
        for j, d in enumerate(den):
            num[i+j] -= q[i]*d
    assert all(v == 0 for v in num)
    return q
def cyclotomic(N, cache={}):
    if N in cache: return cache[N]
    num = [-1] + [0]*(N-1) + [1]      # x^N - 1
    for d in range(1, N):
        if N % d == 0:
            num = polydiv_int(num, cyclotomic(d))
    cache[N] = num
    return num

# ---------------- residue field F_p[x]/f, f | Phi_{N0} mod p ----------------
class ResidueField:
    def __init__(self, N, p):
        self.p = p
        N0 = N
        while N0 % p == 0: N0 //= p
        self.N0 = N0
        if N0 == 1:
            self.d = 1; self.f = [0, 1]  # F_p, beta = 1
            self.beta = (1,)
        else:
            d = 1
            while pow(p, d, N0) != 1: d += 1
            self.d = d
            PhiN0 = [c % p for c in cyclotomic(N0)]
            self.f = self._find_factor(PhiN0, d, p)
            self.beta = tuple([0, 1][:d] + [0]*(d-2)) if d > 1 else \
                        ((-self.f[0]) % p,)
        # powers of beta up to needed length set later
    def _find_factor(self, F, d, p):
        # monic degree-d divisor of F over F_p (all irred factors have deg d)
        if len(F) - 1 == d:
            return F
        for coeffs in product(range(p), repeat=d):
            g = list(coeffs) + [1]
            if self._divides(g, F, p): return g
        raise RuntimeError("no factor found")
    def _divides(self, g, F, p):
        r = F[:]
        for i in range(len(r)-len(g), -1, -1):
            c = r[i+len(g)-1] % p
            if c:
                for j, gv in enumerate(g):
                    r[i+j] = (r[i+j] - c*gv) % p
        return all(v % p == 0 for v in r)
    def mulf(self, A, B):
        p, f, d = self.p, self.f, self.d
        r = [0]*(len(A)+len(B)-1)
        for i, a in enumerate(A):
            if a:
                for j, b in enumerate(B):
                    r[i+j] = (r[i+j] + a*b) % p
        for i in range(len(r)-1, d-1, -1):
            c = r[i]
            if c:
                for j in range(d+1):
                    r[i-d+j] = (r[i-d+j] - c*f[j]) % p
        r = r[:d] + [0]*(d-len(r))
        return tuple(v % p for v in r[:d])
    def beta_powers(self, k):
        one = tuple([1]+[0]*(self.d-1))
        out = [one]
        for _ in range(k-1):
            out.append(self.mulf(out[-1], self.beta))
        return out

# ---------------- D(G) machinery ----------------
class DRing:
    def __init__(self, G):
        self.G = G
        self.N = exponent(G)
        self.Phi = cyclotomic(self.N)
        self.phiN = len(self.Phi)-1
        # zeta^k reduced mod Phi_N as int vectors
        self.zpow = []
        cur = [1]+[0]*(self.phiN-1)
        for k in range(self.N):
            self.zpow.append(tuple(cur))
            cur = [0]+cur  # * x
            if len(cur) > self.phiN:
                c = cur[self.phiN]
                cur = [cur[i]-c*self.Phi[i] for i in range(self.phiN)]
        self.subs = G.all_subgroups()
        self.sub_classes = self._classes(self.subs)
        self.species = self._species_classes()
        self.basis = self._basis_classes()
        assert len(self.species) == len(self.basis), \
            (len(self.species), len(self.basis))
        self.table = self._species_table()
    # ---- classes of subgroups
    def _classes(self, subs):
        G = self.G; seen = set(); classes = []
        for H in subs:
            if H in seen: continue
            orb = {G.conj_sub(g, H) for g in range(G.n)}
            seen |= orb
            classes.append(min(orb, key=lambda s: tuple(sorted(s))))
        return classes
    # ---- species: (H, coset of H') up to G-conjugacy
    def _pair_canon(self, H, coset):
        G = self.G
        best = None
        for g in range(G.n):
            k = (tuple(sorted(G.conjT[g][x] for x in H)),
                 tuple(sorted(G.conjT[g][x] for x in coset)))
            if best is None or k < best: best = k
        return best
    def _cosets(self, H, K):  # cosets of K in H
        G = self.G; rem = set(H); out = []
        while rem:
            x = min(rem)
            cs = frozenset(G.M[x][k] for k in K)
            out.append(cs); rem -= cs
        return out
    def _species_classes(self):
        out, seen = [], set()
        for H in self.sub_classes:
            Hp = self.G.derived(H)
            for cs in self._cosets(H, Hp):
                key = self._pair_canon(H, cs)
                if key not in seen:
                    seen.add(key)
                    out.append((H, cs, Hp, key))
        return out
    # ---- linear characters of H, as exponent dicts (values in Z/N)
    def _characters(self, H, Hp):
        G, N = self.G, self.N
        cosets = self._cosets(H, Hp)
        cmap = {}
        for i, cs in enumerate(cosets):
            for x in cs: cmap[x] = i
        e_idx = cmap[G.e]
        # quotient mult on coset indices
        rep = [min(cs) for cs in cosets]
        qm = [[cmap[G.M[rep[i]][rep[j]]] for j in range(len(cosets))]
              for i in range(len(cosets))]
        # greedy generators of the quotient
        gens = []; span = {e_idx}
        for i in range(len(cosets)):
            if i not in span:
                gens.append(i)
                # regenerate span
                span = {e_idx}; frontier = [e_idx]
                while frontier:
                    new = []
                    for a in frontier:
                        for g in gens:
                            c = qm[a][g]
                            if c not in span: span.add(c); new.append(c)
                    frontier = new
        # order of each gen in quotient
        def qorder(i):
            o, y = 1, i
            while y != e_idx: y = qm[y][i]; o += 1
            return o
        gorders = [qorder(i) for i in gens]
        chars = []
        for vals in product(*[range(0, N, N//d) for d in gorders]):
            lam = {e_idx: 0}; frontier = [e_idx]; ok = True
            while frontier and ok:
                new = []
                for a in frontier:
                    for gi, g in enumerate(gens):
                        c = qm[a][g]; v = (lam[a]+vals[gi]) % N
                        if c in lam:
                            if lam[c] != v: ok = False; break
                        else:
                            lam[c] = v; new.append(c)
                    if not ok: break
                frontier = new
            if ok and len(lam) == len(cosets):
                chars.append(tuple(lam[cmap[x]] if x in cmap else None
                                   for x in range(G.n)))
        # chars[i][x] = exponent of lambda at x (None off H)
        assert len(set(chars)) == len(cosets), (len(chars), len(cosets))
        return sorted(set(chars))
    def _basis_classes(self):
        G = self.G; out, seen = [], set()
        for K in self.sub_classes:
            Kp = G.derived(K)
            for lam in self._characters(K, Kp):
                # canonical under G-conjugation
                best = None
                for g in range(G.n):
                    Kg = tuple(sorted(G.conjT[g][x] for x in K))
                    lg = tuple(lam[G.conjT[G.inv[g]][x]] if
                               G.conjT[G.inv[g]][x] in K else None
                               for x in range(G.n))
                    # restrict to sorted Kg for the key
                    key = (Kg, tuple(lg[x] for x in Kg))
                    if best is None or key < best:
                        best = key; bestKg = frozenset(Kg); bestlg = lg
                if best not in seen:
                    seen.add(best)
                    out.append((bestKg, bestlg))
        return out
    # ---- species table (int vectors in Z[zeta_N])
    def _species_table(self):
        G, N = self.G, self.N
        T = []
        for (H, cs, Hp, _) in self.species:
            h = min(cs); row = []
            Hl = list(H)
            for (K, lam) in self.basis:
                counts = [0]*N
                for g in range(G.n):
                    cg = G.conjT[G.inv[g]]
                    ok = True
                    for x in Hl:
                        if cg[x] not in K: ok = False; break
                    if ok:
                        counts[lam[cg[h]]] += 1
                vec = [0]*self.phiN
                for k, c in enumerate(counts):
                    if c:
                        zp = self.zpow[k]
                        for i in range(self.phiN): vec[i] += c*zp[i]
                kK = len(K)
                assert all(v % kK == 0 for v in vec), "non-integral value!"
                row.append(tuple(v//kK for v in vec))
            T.append(row)
        return T
    # ---- intrinsic congruence blocks mod a prime over p
    def congruence_blocks(self, p):
        F = ResidueField(self.N, p)
        bp = F.beta_powers(self.phiN)
        def ev(vec):
            acc = [0]*F.d
            for i, v in enumerate(vec):
                bi = bp[i]
                for j in range(F.d): acc[j] = (acc[j] + v*bi[j]) % p
            return tuple(acc)
        n = len(self.species)
        evt = [[ev(v) for v in row] for row in self.table]
        parent = list(range(n))
        def find(a):
            while parent[a] != a: parent[a] = parent[parent[a]]; a = parent[a]
            return a
        for i in range(n):
            for j in range(i+1, n):
                if find(i) != find(j) and evt[i] == evt[j]:
                    parent[find(i)] = find(j)
        blocks = {}
        for i in range(n): blocks.setdefault(find(i), []).append(i)
        return sorted(sorted(b) for b in blocks.values())
    # ---- Satz 2.2.7 formula blocks
    def formula_root(self, ispec, p):
        G = self.G
        (H, cs, Hp, _) = self.species[ispec]
        K = G.Op(H, p)
        Kp = G.derived(K)
        h = min(cs)
        hp = G.pprime_part(h, p)
        assert hp in K, "p'-part not in O^p(H)?!"
        # Kbar = K/Kp with H-action
        cosK = self._cosets(K, Kp)
        cm = {}
        for i, c in enumerate(cosK):
            for x in c: cm[x] = i
        e_i = cm[G.e]
        rep = [min(c) for c in cosK]
        qm = [[cm[G.M[rep[i]][rep[j]]] for j in range(len(cosK))]
              for i in range(len(cosK))]
        qinv = [next(j for j in range(len(cosK)) if qm[i][j] == e_i)
                for i in range(len(cosK))]
        Hl = list(H)
        # C = fixed cosets under conj by H
        C = [i for i in range(len(cosK))
             if all(cm[G.conjT[u][rep[i]]] == i for u in Hl)]
        # B = subgroup generated by x^{-1} (u x u^{-1}), x in K, u in H
        bg = set()
        for x in K:
            for u in Hl:
                bg.add(cm[G.M[G.inv[x]][G.conjT[u][x]]])
        B = {e_i}; frontier = list(bg | {e_i})
        while frontier:
            new = []
            cur = set(B) | set(frontier); frontier = []
            for a in list(cur):
                for b in bg:
                    c = qm[a][b]
                    if c not in cur: cur.add(c); frontier.append(c)
            B = cur
        hpi = cm[hp]
        comp = [c for c in C if qm[qinv[c]][hpi] in B]
        assert len(comp) == 1, ("decomposition not unique", len(comp))
        c = comp[0]
        return self._pair_canon(K, cosK[c])
    def formula_blocks(self, p):
        roots = {}
        for i in range(len(self.species)):
            roots.setdefault(self.formula_root(i, p), []).append(i)
        return sorted(sorted(b) for b in roots.values())
    # ---- reporting helpers
    def spec_name(self, i):
        (H, cs, Hp, _) = self.species[i]
        G = self.G
        fib_ord = 1; y = min(cs)
        # order of coset in H/H'
        cosH = self._cosets(H, Hp)
        cmap = {}
        for k, c in enumerate(cosH):
            for x in c: cmap[x] = k
        e_i = cmap[G.e]; cur = cmap[min(cs)]; rep = [min(c) for c in cosH]
        o = 1; z = cur
        while z != e_i:
            z = cmap[G.M[rep[z]][rep[cur]]]; o += 1
        return f"(|H|={len(H)},fib_ord={o})"

def primes(n):
    out, d = [], 2
    while d*d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0: n //= d
        d += 1
    if n > 1: out.append(n)
    return out

def analyze(G):
    D = DRing(G)
    ps = primes(G.n)
    print(f"== {G.name}: |G|={G.n}, exp={D.N}, "
          f"#species=#basis={len(D.species)}")
    all_ok = True
    for p in ps:
        cb = D.congruence_blocks(p)
        fb = D.formula_blocks(p)
        match = (cb == fb)
        all_ok &= match
        print(f"   p={p}: {len(cb)} blocks; congruence==Satz2.2.7formula: "
              f"{'OK' if match else '*** MISMATCH ***'}")
        if not match:
            print("     congruence:", cb)
            print("     formula:   ", fb)
    # B5* checks: involution pairs and general fibre-collapse law
    # index species by (subgroup-class key, fibre)
    n = len(D.species)
    viol = []
    checked_pairs = 0
    for p in [q for q in ps if q != 2]:
        cb = D.congruence_blocks(p)
        blk = {}
        for bi, b in enumerate(cb):
            for i in b: blk[i] = bi
        # group species by subgroup class
        bysub = {}
        for i, (H, cs, Hp, key) in enumerate(D.species):
            bysub.setdefault(key[0], []).append(i)
        for subkey, idxs in bysub.items():
            # find trivial-fibre species over this subgroup class
            triv = [i for i in idxs if D.G.e in D.species[i][1]]
            assert len(triv) == 1
            t0 = triv[0]
            for i in idxs:
                if i == t0: continue
                (H, cs, Hp, _) = D.species[i]
                # order of fibre & its p'-part triviality
                cosH = D._cosets(H, Hp)
                cmap = {}
                for k, c in enumerate(cosH):
                    for x in c: cmap[x] = k
                e_i = cmap[D.G.e]; rep = [min(c) for c in cosH]
                cur = cmap[min(cs)]
                o, z = 1, cur
                while z != e_i:
                    z_new = e_i
                    # multiply cur o times: iterate
                    break
                # compute order properly
                o = 1; z = cur
                while z != e_i:
                    z = cmap[D.G.M[rep[z]][rep[cur]]]; o += 1
                op = o
                while op % p == 0: op //= p
                ppart_trivial = (op == 1)
                same = (blk[i] == blk[t0])
                checked_pairs += 1
                if same != ppart_trivial:
                    viol.append((p, i, o))
                if o == 2:  # involution pair: theorem says separated
                    if same:
                        viol.append(("INVOLUTION-PAIR-FUSED", p, i))
    if any(q != 2 for q in ps):
        print(f"   B5* law checked on {checked_pairs} (species,prime) pairs "
              f"over fixed subgroups: "
              f"{'ALL CONFIRMED' if not viol else viol}")
    if ps == [2]:
        cb = D.congruence_blocks(2)
        print(f"   2-group: number of 2-blocks = {len(cb)} "
              f"(predicted 1: {'OK' if len(cb) == 1 else '*** FAIL ***'})")
    return all_ok and not viol

if __name__ == "__main__":
    import sys
    tests = {
        "V4": lambda: dihedral(2), "C4": lambda: cyclic(4),
        "D4": lambda: dihedral(4), "Q8": lambda: dicyclic(2),
        "S3": lambda: dihedral(3), "C6": lambda: cyclic(6),
        "C12": lambda: cyclic(12), "D6": lambda: dihedral(6),
        "Dic3": lambda: dicyclic(3), "A4": A4, "SL23": SL23,
    }
    names = sys.argv[1:] if len(sys.argv) > 1 else list(tests)
    ok = True
    for nm in names:
        ok &= analyze(tests[nm]())
    print("OVERALL:", "ALL CHECKS PASSED" if ok else "FAILURES PRESENT")
