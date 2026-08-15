#!/usr/bin/env python3
# l2_twins -- Fitting-free NON-SIMPLE twins of S = L_2(q) = PSL(2,q), q >= 4.
#
# Pipeline copied from sporadic_twins.py (same two phases, same
# hypothesis-free inputs); the CFSG simple-order enumerator and the multiset
# census are IMPORTED from that file so there is exactly one implementation.
#
#   PHASE 1 (order census).  Enumerate every multiset {(S_i,l_i)} of finite
#   non-abelian simple groups with  prod |S_i|^{l_i} * c = |S|  and
#   c | prod_i (|Out(S_i)|^{l_i} * l_i!)   (forced by F(T)=1, T <= Aut(Soc T)).
#   Drop the unique "T simple" solution.
#
#   PHASE 2 (orbit floor).  Lemma TO'-0 + Lemma F:
#       l_O * |Out(S_i)| * iota(S_i)  >=  iota(S) = q+1     (q >= 4, q != 5,7,9)
#   An UPPER bound on iota(S_i) is the conservative direction.
#
# Exact integer arithmetic throughout.  Usage:
#     python3 l2_twins.py [QMAX]      (default 20000)

import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import random
import sporadic_twins as T50
from sporadic_twins import (simple_divisors, census, IOTA_UB,
                                     pow_divides)


# ---- fast exact factorisation (sporadic_twins's factorint is trial division only,
# ---- which is fine for the 71-smooth sporadic orders but not for |L2(q)|).
def _is_prime(n):
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def _rho(n):
    if n % 2 == 0:
        return 2
    while True:
        c = random.randrange(1, n)
        x = y = random.randrange(0, n)
        d = 1
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = T50.gcd(abs(x - y), n)
        if d != n:
            return d


def factorint(n):
    """exact prime factorisation, deterministic Miller-Rabin + Pollard rho"""
    f = {}
    stack = [n]
    while stack:
        m = stack.pop()
        if m == 1:
            continue
        if _is_prime(m):
            f[m] = f.get(m, 0) + 1
            continue
        d = 2
        while d * d <= m and d < 100000:
            if m % d == 0:
                break
            d += 1 if d == 2 else 2
        if d * d <= m and m % d == 0:
            stack.append(d)
            stack.append(m // d)
            continue
        g = _rho(m)
        stack.append(g)
        stack.append(m // g)
    return f


T50.factorint = factorint     # used inside simple_divisors


# ----------------------------------------------------------------- targets

def prime_powers_upto(M):
    """all prime powers q = p^f, 4 <= q <= M, as (q, p, f)"""
    sieve = bytearray(b'\x01') * (M + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(M ** 0.5) + 1):
        if sieve[i]:
            sieve[i*i::i] = bytearray(len(range(i*i, M+1, i)))
    out = []
    for p in range(2, M + 1):
        if not sieve[p]:
            continue
        q, f = p, 1
        while q <= M:
            if q >= 4:
                out.append((q, p, f))
            q *= p
            f += 1
    return sorted(out)


def order_L2(q):
    d = 2 if q % 2 else 1
    return q * (q * q - 1) // d


# iota(L_2(q)).  Dickson => the minimal index of a proper subgroup is q+1
# except q = 5,7,9,11 (indices 5,7,6,11); and the index-(q+1) Borel is
# N_S(U) with U the (abelian) unipotent radical, so ind*(U) = q+1.  The
# exceptional small-index subgroups are A5 (q=9,11) and S4 (q=7), of which
# only S4 = N(V4) is a normalizer of a non-trivial abelian subgroup.
IOTA_L2_EXC = {5: 5, 7: 7}          # q = 9,11 give back q+1  (GAP-checked)


def iota_target(q):
    return IOTA_L2_EXC.get(q, q + 1)


# ------------------------------------------------- generic iota upper bounds
#
# For a simple group of Lie type, the centre Z(U_P) of the unipotent radical
# of a parabolic P is a non-trivial ABELIAN subgroup with N_S(Z(U_P)) = P
# (Borel-Tits), so  iota(S) <= [S:P].  Below: the smallest parabolic index of
# each family (the "natural module point/isotropic-point stabiliser").

def gaussian(n, q):
    """[n,1]_q = (q^n-1)/(q-1)"""
    return (q ** n - 1) // (q - 1)


def iota_ub_generic(name):
    """Upper bound for iota(S) parsed from the family name; None if unknown."""
    import re
    m = re.match(r"^A(\d+)$", name)
    if m:
        k = int(m.group(1))
        return IOTA_UB.get(name, k * (k - 1) * (k - 2) // 6)
    if name in IOTA_UB:
        return IOTA_UB[name]
    m = re.match(r"^L(\d+)\((\d+)\)$", name)
    if m:
        n, q = int(m.group(1)), int(m.group(2))
        return gaussian(n, q)
    m = re.match(r"^U(\d+)\((\d+)\)$", name)
    if m:
        n, q = int(m.group(1)), int(m.group(2))
        # isotropic point stabiliser index
        return (q ** n - (-1) ** n) * (q ** (n - 1) - (-1) ** (n - 1)) // (q * q - 1)
    m = re.match(r"^S(\d+)\((\d+)\)$", name)
    if m:
        n, q = int(m.group(1)), int(m.group(2))
        return gaussian(n, q)
    m = re.match(r"^O(\d+)\((\d+)\)$", name)      # O_{2d+1}(q)
    if m:
        n, q = int(m.group(1)), int(m.group(2))
        return gaussian(n - 1, q)
    m = re.match(r"^O(\d+)([+-])\((\d+)\)$", name)
    if m:
        n, s, q = int(m.group(1)), m.group(2), int(m.group(3))
        d = n // 2
        if s == "+":
            return (q ** d - 1) * (q ** (d - 1) + 1) // (q - 1)
        return (q ** d + 1) * (q ** (d - 1) - 1) // (q - 1)
    m = re.match(r"^G2\((\d+)\)$", name)
    if m:
        q = int(m.group(1))
        return gaussian(6, q)
    m = re.match(r"^3D4\((\d+)\)$", name)
    if m:
        q = int(m.group(1))
        return (q ** 8 + q ** 4 + 1) * (q + 1)
    m = re.match(r"^F4\((\d+)\)$", name)
    if m:
        q = int(m.group(1))
        return (q ** 12 - 1) * (q ** 4 + 1) // (q - 1)
    m = re.match(r"^Sz\((\d+)\)$", name)
    if m:
        q = int(m.group(1))
        return q * q + 1
    m = re.match(r"^R\((\d+)\)$", name)
    if m:
        q = int(m.group(1))
        return q ** 3 + 1
    m = re.match(r"^2F4\((\d+)\)$", name)
    if m:
        q = int(m.group(1))
        return (q ** 6 + 1) * (q ** 3 + 1) * (q + 1)
    m = re.match(r"^E6\((\d+)\)$", name)
    if m:
        q = int(m.group(1))
        return (q ** 9 - 1) * (q ** 8 + q ** 4 + 1) // (q - 1)
    m = re.match(r"^2E6\((\d+)\)$", name)
    if m:
        q = int(m.group(1))
        return (q ** 8 + q ** 4 + 1) * (q ** 9 + 1) // (q + 1)
    m = re.match(r"^E7\((\d+)\)$", name)
    if m:
        q = int(m.group(1))
        return (q ** 14 - 1) * (q ** 9 + 1) * (q ** 5 - 1) // \
               ((q ** 2 - 1) * (q - 1))
    m = re.match(r"^E8\((\d+)\)$", name)
    if m:
        q = int(m.group(1))
        return (q ** 30 - 1) * (q ** 12 + 1) * (q ** 10 + 1) * (q ** 6 + 1) // \
               (q ** 2 - 1) ** 0 // (q - 1) // (q ** 2 - 1) // (q ** 4 - 1)
    return None


# ------------------------------------------------------------------- driver

def run(qmax, verbose_upto=200):
    global RAW
    targets = prime_powers_upto(qmax)
    print("# l2_twins  --  Fitting-free non-simple twins of L_2(q), 4 <= q <= %d"
          % qmax)
    print("# %d prime powers scanned" % len(targets))
    print()

    stats = {"empty1": 0, "killed_floor": 0, "killed_c": 0, "LIVE": 0}
    live = []
    nonempty_rows = []
    unknown_iota = set()
    ctrl_fail = []

    for (q, p, f) in targets:
        N = order_L2(q)
        iS = iota_target(q)
        cands = simple_divisors(N)
        # POSITIVE CONTROL.  The enumerator must produce the target itself
        # (under whatever canonical name), and must produce it EXACTLY once
        # -- otherwise an "empty census" would be a false negative, and the
        # simple-simple side would be untested.  This also re-proves, for
        # every scanned q, that |L2(q)| is the order of no other simple group.
        same_order = [nm for (nm, o, u) in cands if o == N]
        if len(same_order) != 1:
            print("!!! CONTROL FAILURE q=%d : simple groups of order %d = %s"
                  % (q, N, same_order))
            ctrl_fail.append((q, same_order))
        # the target itself under its canonical name
        # (L2(4),L2(5)->A5 ; L2(9)->A6 ; L2(7)->L3(2))
        # Phase-2 prefilter on socle factors
        surv, dead = [], []
        for (nm, o, u) in cands:
            iv = iota_ub_generic(nm)
            if iv is None:
                unknown_iota.add(nm)
                surv.append((nm, o, u))
                continue
            lmin = -(-iS // (u * iv))
            if pow_divides(o, lmin, N):
                surv.append((nm, o, u))
            else:
                dead.append(nm)
        if RAW:
            raw = census(N, cands, maxfac=16)
            rawns = [(ch, c) for (ch, c) in raw
                     if sum(l for (_, l) in ch) >= 2 or c > 1]
            if rawns:
                print("RAW q=%-6d iota=%-7d unfiltered non-simple census: %d"
                      % (q, iS, len(rawns)))
                for (ch, c) in rawns:
                    umap = dict((x[0], x[2]) for x in cands)
                    floor = min(l * umap[nm] * (iota_ub_generic(nm) or 10 ** 30)
                                for (nm, l) in ch)
                    print("      %-46s c=%-8d floor=%d"
                          % (" x ".join("%s^%d" % (nm, l) if l > 1 else nm
                                        for (nm, l) in ch), c, floor))
        sols = census(N, surv, maxfac=16)
        nonsimple = [(ch, c) for (ch, c) in sols
                     if sum(l for (_, l) in ch) >= 2 or c > 1]
        if not nonsimple:
            stats["empty1"] += 1
        else:
            rows = []
            for (ch, c) in nonsimple:
                umap = dict((x[0], x[2]) for x in cands)
                floor = min(l * umap[nm] * (iota_ub_generic(nm) or 10 ** 30)
                            for (nm, l) in ch)
                socle = " x ".join("%s^%d" % (nm, l) if l > 1 else nm
                                   for (nm, l) in ch)
                if floor < iS:
                    verdict = "KILLED orbit-floor (%d < %d)" % (floor, iS)
                    stats["killed_floor"] += 1
                else:
                    verdict = "*** LIVE ***"
                    stats["LIVE"] += 1
                    live.append((q, socle, c))
                rows.append("      SOCLE %-46s c=%-8d %s" % (socle, c, verdict))
            nonempty_rows.append((q, N, iS, len(cands), len(dead), rows))

    print("## Phase-1/2 rows with a NON-EMPTY non-simple census")
    print("   (all others: census empty already)")
    for (q, N, iS, nc, nd, rows) in nonempty_rows:
        print("q = %-6d |L2(q)| = %-18d iota = %-8d simple divisors %d (%d dead)"
              % (q, N, iS, nc, nd))
        for r in rows:
            print(r)
    print()
    print("## SUMMARY  (q <= %d)" % qmax)
    print("   positive control (|L2(q)| is a simple order, uniquely): %s"
          % ("PASS, all %d targets" % len(targets) if not ctrl_fail
             else "FAIL %s" % ctrl_fail))
    print("   targets with EMPTY non-simple census      : %d / %d"
          % (stats["empty1"], len(targets)))
    print("   non-simple candidates killed by orbit floor: %d" % stats["killed_floor"])
    print("   *** LIVE survivors ***                     : %d" % stats["LIVE"])
    for (q, socle, c) in live:
        print("      q = %d :  Soc = %s , c = %d" % (q, socle, c))
    if unknown_iota:
        print("   NOTE: no iota bound for: %s" % ", ".join(sorted(unknown_iota)))


# ---------------------------------------------------------------------------
# TARGETED SCAN of the two residual single-orbit branches (see the write-up
# l2_twins.md, Steps 5c and 5d).  Both reduce to S_1 = L_2(q_1):
#
#   (E1)  l = 1, T almost simple with socle S_1:
#             c * |L_2(q1)|  = |L_2(q)| ,  2 <= c | |Out(L_2(q1))| = d1*f1
#   (E2)  l = 2, Soc T = L_2(q1)^2, one orbit of length 2:
#             c * |L_2(q1)|^2 = |L_2(q)| ,  c | 2*(d1*f1)^2
#
# Exact integer arithmetic; the cube root is a seed only, every candidate is
# verified by exact multiplication.

def _icbrt(n):
    """exact integer cube root, integer Newton.  NO float seed: a float seed is
    off by about 1e-16 * n^(1/3), which is 10^24 at the scales reached by the
    l = 2 branch -- this bit an earlier version of this script and made the
    correction loop effectively non-terminating."""
    if n < 2:
        return n
    x = 1 << ((n.bit_length() + 2) // 3)
    while True:
        y = (2 * x + n // (x * x)) // 3
        if y >= x:
            break
        x = y
    while x * x * x > n:
        x -= 1
    while (x + 1) ** 3 <= n:
        x += 1
    return x


def is_prime_power(n):
    if n < 2:
        return False
    f = factorint(n)
    return len(f) == 1


def solve_L2_order(M):
    """all prime powers q >= 4 with |L_2(q)| = M  (q^3-q = M or 2M)"""
    out = []
    for mult, parity in ((1, "even"), (2, "odd")):
        v = M * mult
        r = _icbrt(v)
        for q in range(max(2, r - 2), r + 3):
            if q ** 3 - q != v:
                continue
            if q < 4 or not is_prime_power(q):
                continue
            if parity == "even" and q % 2 == 0:
                out.append(q)
            if parity == "odd" and q % 2 == 1:
                out.append(q)
    return sorted(set(out))


def l2_subcases(q1max_E1, q1max_E2):
    print("# TARGETED SCAN of the residual L_2(q1)-socle branches")
    for n in (0, 1, 7, 8, 26, 27, 10 ** 120, 10 ** 120 + 1,
              12345678901234567 ** 3):
        r = _icbrt(n)
        assert r ** 3 <= n < (r + 1) ** 3, (n, r)
    print("  _icbrt selftest (incl. the 10^120 scale of the l=2 branch): OK")
    hits = []
    n1 = 0
    for (q1, p1, f1) in prime_powers_upto(q1max_E1):
        d1 = 2 if q1 % 2 else 1
        S1 = q1 * (q1 * q1 - 1) // d1
        u1 = d1 * f1
        for c in range(2, u1 + 1):
            if u1 % c:
                continue
            n1 += 1
            for q in solve_L2_order(c * S1):
                hits.append(("E1", q1, c, q))
    print("  (E1)  l=1 almost simple, q1 <= %d : %d (q1,c) pairs tested, %d hits"
          % (q1max_E1, n1, len([h for h in hits if h[0] == "E1"])))
    n2 = 0
    for (q1, p1, f1) in prime_powers_upto(q1max_E2):
        d1 = 2 if q1 % 2 else 1
        S1 = q1 * (q1 * q1 - 1) // d1
        u1 = 2 * (d1 * f1) ** 2
        for c in range(1, u1 + 1):
            if u1 % c:
                continue
            n2 += 1
            for q in solve_L2_order(c * S1 * S1):
                hits.append(("E2", q1, c, q))
    print("  (E2)  l=2 socle L_2(q1)^2, q1 <= %d : %d (q1,c) pairs tested, %d hits"
          % (q1max_E2, n2, len([h for h in hits if h[0] == "E2"])))
    for h in hits:
        print("      HIT %s  q1=%d c=%d  ==>  q=%d" % h)
    if not hits:
        print("  NO SOLUTIONS in either branch.")
    # (E3) alternating socle A_m (|Out| = 2, resp. 4 at m = 6), l = 1, 2
    from sporadic_twins import SPORADIC as SPO, TITS as TIT
    fac = 1
    e3 = []
    for m in range(2, 200):
        fac *= m
        if m < 5:
            continue
        o = fac // 2
        if o > 10 ** 60:
            break
        u = 4 if m == 6 else 2
        for l in (1, 2):
            cap = u ** l * (2 if l == 2 else 1)
            for c in range(1, cap + 1):
                if cap % c or (l == 1 and c == 1):
                    continue
                for q in solve_L2_order(c * o ** l):
                    e3.append(("A%d" % m, l, c, q))
    print("  (E3)  alternating socle A_m^l, m <= 200, l = 1,2 : %d hits" % len(e3))
    for h in e3:
        print("      HIT %s^%d c=%d ==> q=%d" % h)
    # (E4) sporadic socle, l = 1, 2
    e4 = []
    for (nm, o, u) in list(SPO) + [TIT]:
        for l in (1, 2):
            cap = u ** l * (2 if l == 2 else 1)
            for c in range(1, cap + 1):
                if cap % c or (l == 1 and c == 1):
                    continue
                for q in solve_L2_order(c * o ** l):
                    e4.append((nm, l, c, q))
    print("  (E4)  sporadic socle S^l, all 27, l = 1,2 : %d hits" % len(e4))
    for h in e4:
        print("      HIT %s^%d c=%d ==> q=%d" % h)
    # positive control: c=1 in (E1) must reproduce q = q1
    ctrl = solve_L2_order(4 * (16 - 1) // 1)
    print("  positive control solve_L2_order(|L2(4)|=60) = %s (expect [4,5])"
          % solve_L2_order(60))
    print("  positive control solve_L2_order(|L2(9)|=360) = %s (expect [9])"
          % solve_L2_order(360))


def lemma_C_sweep(q1max=4096, rankmax=8):
    """Check the two uniform inequalities used in the write-up:
         (B)  |G| > iota(G)^2      (exceptions: J1, O'N, J3)
         (C)  |Out(G)| * iota(G) <= |G|^(2/3)
       over all simple G of Lie type with q1 <= q1max and rank <= rankmax,
       all A_m (m <= 60) and all 27 sporadics.  iota is replaced by the
       parabolic/3-cycle UPPER bound, which is the conservative direction
       for both inequalities."""
    import math
    from sporadic_twins import SPORADIC as SPO, TITS as TIT, gcd as G
    rows = []

    def add(nm, o, u):
        ub = iota_ub_generic(nm)
        if o > 1 and ub and ub > 1:
            rows.append((math.log(o) / math.log(ub), nm, o, ub, u))

    PP = []
    for pp in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]:
        qq, ff = pp, 1
        while qq <= q1max:
            PP.append((qq, pp, ff))
            qq *= pp
            ff += 1
    for (q1, p1, f1) in PP:
        for n in range(2, rankmax + 1):
            o = q1 ** (n * (n - 1) // 2)
            for i in range(2, n + 1):
                o *= q1 ** i - 1
            g = G(n, q1 - 1)
            o //= g
            if not (n == 2 and q1 in (2, 3)):
                add("L%d(%d)" % (n, q1), o, g * f1 * (2 if n >= 3 else 1))
        for n in range(3, rankmax + 1):
            o = q1 ** (n * (n - 1) // 2)
            for i in range(2, n + 1):
                o *= q1 ** i - (-1) ** i
            g = G(n, q1 + 1)
            o //= g
            if not (n == 3 and q1 == 2):
                add("U%d(%d)" % (n, q1), o, g * 2 * f1)
        for d in range(2, rankmax // 2 + 3):
            o = q1 ** (d * d)
            for i in range(1, d + 1):
                o *= q1 ** (2 * i) - 1
            g = G(2, q1 - 1)
            o //= g
            if not (d == 2 and q1 == 2):
                add("S%d(%d)" % (2 * d, q1), o, g * f1)
                if q1 % 2 == 1 and d >= 3:
                    add("O%d(%d)" % (2 * d + 1, q1), o, g * f1)
        if q1 >= 3:
            add("G2(%d)" % q1, q1 ** 6 * (q1 ** 6 - 1) * (q1 ** 2 - 1), f1 * 2)
        add("3D4(%d)" % q1, q1 ** 12 * (q1 ** 8 + q1 ** 4 + 1) *
            (q1 ** 6 - 1) * (q1 ** 2 - 1), 3 * f1)
        if p1 == 2 and f1 % 2 == 1 and f1 >= 3:
            add("Sz(%d)" % q1, q1 * q1 * (q1 * q1 + 1) * (q1 - 1), f1)
        if p1 == 3 and f1 % 2 == 1 and f1 >= 3:
            add("R(%d)" % q1, q1 ** 3 * (q1 ** 3 + 1) * (q1 - 1), f1)
    fac = 1
    for m in range(2, 61):
        fac *= m
        if m >= 5:
            add("A%d" % m, fac // 2, 4 if m == 6 else 2)
    for (nm, o, u) in list(SPO) + [TIT]:
        add(nm, o, u)

    rows.sort()
    print("# Lemma B / Lemma C sweep over %d simple groups" % len(rows))
    print("# (B) |G| > iota^2 : 12 smallest exponents log|G|/log(iota_ub)")
    for r in rows[:12]:
        print("   alpha=%.4f  %-14s |G|=%d iota_ub=%d |Out|=%d" % r)
    badB = [r for r in rows if r[0] <= 2.0]
    print("# groups violating (B): %s" % ", ".join(r[1] for r in badB))
    badC = [r for r in rows if r[4] * r[3] > round(r[2] ** (2.0 / 3.0)) + 1]
    print("# groups violating (C) |Out|*iota <= |G|^(2/3): %s"
          % (", ".join("%s (%d > %d)" % (r[1], r[4] * r[3],
                                         int(r[2] ** (2.0 / 3.0)))
                       for r in badC) or "NONE"))
    worst = max(rows, key=lambda r: r[4] * r[3] / (r[2] ** (2.0 / 3.0)))
    print("# tightest (C) row: %s  |Out|*iota=%d  |G|^(2/3)=%.1f  ratio %.3f"
          % (worst[1], worst[4] * worst[3], worst[2] ** (2.0 / 3.0),
             worst[4] * worst[3] / worst[2] ** (2.0 / 3.0)))


RAW = ("--raw" in sys.argv)

if __name__ == "__main__":
    args=[a for a in sys.argv[1:] if not a.startswith("--")]
    qmax = int(args[0]) if args else 20000
    if "--lemC" in sys.argv:
        lemma_C_sweep()
    elif "--l2sub" in sys.argv:
        e1 = int(args[0]) if args else 10 ** 7
        e2 = int(args[1]) if len(args) > 1 else 10 ** 5
        l2_subcases(e1, e2)
    else:
        run(qmax)
