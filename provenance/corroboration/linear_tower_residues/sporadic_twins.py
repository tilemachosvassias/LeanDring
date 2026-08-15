#!/usr/bin/env python3
# sporadic_twins -- Fitting-free non-simple twins of the sporadic groups.
#
# PHASE 1 (order census).  For each sporadic S (+ the Tits group) enumerate
# every multiset {(S_i, l_i)} of finite non-abelian simple groups with
#
#        prod |S_i|^{l_i}  *  c  =  |S|,        c = [T : Soc T],
#
# subject to the Fitting-free constraint  T <= Aut(Soc T), i.e.
#
#        c  |  |Out(Soc T)| = prod_i ( |Out(S_i)|^{l_i} * l_i! ).
#
# Non-simple T means: (#factors counted with multiplicity >= 2)  OR
# (one factor and c > 1).
#
# PHASE 2 (kill survivors).  Lemma TO'-0 (spectrum inclusion, hypothesis-free,
# the development record) transported to a sporadic target:  P = U_O l_O*I(K<=A_O)
# is contained in I(T) = I(S), so in particular
#        min_O l_O * iota(K<=A_O)  >=  iota(S)      (the ORBIT FLOOR)
# and each such value must actually BE a value of ind* on S.  With Lemma F,
#        iota(K<=A) = f(A)*[S_i:N(A)],  f | |Out(S_i)|,
# hence   l_O * iota(K<=A)_O  <=  l_O * |Out(S_i)| * iota(S_i)   is an
# achievable upper bound and l_O*|Out|*iota(S_i) < iota(S) kills outright.
#
# Exact integer arithmetic throughout.

import sys

def factorint(n):
    """trial division; sporadic orders are 71-smooth so this is instant."""
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


# ---------------------------------------------------------------- utilities

def prime_powers(N, plist):
    """all prime powers q = p^f, p in plist, q <= N"""
    out = []
    for p in plist:
        q, f = p, 1
        while q <= N:
            out.append((q, p, f))
            q *= p
            f += 1
    return out

# ---------------------------------------------------------------- CFSG orders
# Each entry: (name, order, |Out|)

SPORADIC = [
    ("M11",              7920, 1),
    ("M12",             95040, 2),
    ("M22",            443520, 2),
    ("M23",          10200960, 1),
    ("M24",         244823040, 1),
    ("J1",             175560, 1),
    ("J2",             604800, 2),
    ("J3",           50232960, 2),
    ("J4",  86775571046077562880, 1),
    ("HS",           44352000, 2),
    ("McL",         898128000, 2),
    ("He",          4030387200, 2),
    ("Ru",        145926144000, 1),
    ("Suz",       448345497600, 2),
    ("ON",        460815505920, 2),
    ("Co1",  4157776806543360000, 1),
    ("Co2",     42305421312000, 1),
    ("Co3",    495766656000, 1),
    ("Fi22",    64561751654400, 2),
    ("Fi23", 4089470473293004800, 1),
    ("Fi24'", 1255205709190661721292800, 2),
    ("HN",      273030912000000, 2),
    ("Ly",    51765179004000000, 1),
    ("Th",    90745943887872000, 1),
    ("B",  4154781481226426191177580544000000, 1),
    ("M",  808017424794512875886459904961710757005754368000000000, 1),
]
TITS = ("2F4(2)'", 17971200, 2)


def gcd(a, b):
    while b:
        a, b = b, a % b
    return a


def lie_orders(N, plist):
    """All finite simple groups of Lie type with order dividing N.
    Returns list of (name, order, |Out|).  Complete: every family is
    iterated until the order exceeds N (orders are strictly increasing in
    q and in the rank)."""
    res = []
    PP = prime_powers(N, plist)

    def add(name, o, out):
        if o > 1 and N % o == 0:
            res.append((name, o, out))

    for (q, p, f) in PP:
        # ---- A_d(q) = L_{d+1}(q),  d >= 1 ; simple unless (d,q)=(1,2),(1,3)
        d = 1
        while True:
            n = d + 1
            o = q ** (d * (d + 1) // 2)
            for i in range(2, n + 1):
                o *= q ** i - 1
            g = gcd(n, q - 1)
            o //= g
            if o > N:
                break
            if not (n == 2 and q in (2, 3)):
                add("L%d(%d)" % (n, q), o, g * f * (2 if n >= 3 else 1))
            d += 1
        # ---- 2A_d(q) = U_{d+1}(q), d >= 2
        d = 2
        while True:
            n = d + 1
            o = q ** (d * (d + 1) // 2)
            for i in range(2, n + 1):
                o *= q ** i - (-1) ** i
            g = gcd(n, q + 1)
            o //= g
            if o > N:
                break
            if not (n == 3 and q == 2):
                add("U%d(%d)" % (n, q), o, g * 2 * f)
            d += 1
        # ---- B_d(q) = Omega_{2d+1}(q), d >= 2 ; C_d(q) = PSp_{2d}(q), d >= 2
        d = 2
        while True:
            o = q ** (d * d)
            for i in range(1, d + 1):
                o *= q ** (2 * i) - 1
            g = gcd(2, q - 1)
            o //= g
            if o > N:
                break
            if not (d == 2 and q == 2):
                # B_d and C_d have equal orders; B_d ~ C_d for q even (same
                # group), distinct groups for q odd, d>=3.
                add("S%d(%d)" % (2 * d, q), o,
                    g * f * (2 if (d == 2 and p == 2) else 1))
                if q % 2 == 1 and d >= 3:
                    add("O%d(%d)" % (2 * d + 1, q), o, g * f)
            d += 1
        # ---- D_d(q) = POmega+_{2d}(q), d >= 4
        d = 4
        while True:
            o = q ** (d * (d - 1)) * (q ** d - 1)
            for i in range(1, d):
                o *= q ** (2 * i) - 1
            g = gcd(4, q ** d - 1)
            o //= g
            if o > N:
                break
            add("O%d+(%d)" % (2 * d, q), o, g * f * (6 if d == 4 else 2))
            d += 1
        # ---- 2D_d(q) = POmega-_{2d}(q), d >= 4
        d = 4
        while True:
            o = q ** (d * (d - 1)) * (q ** d + 1)
            for i in range(1, d):
                o *= q ** (2 * i) - 1
            g = gcd(4, q ** d + 1)
            o //= g
            if o > N:
                break
            add("O%d-(%d)" % (2 * d, q), o, g * 2 * f)
            d += 1
        # ---- 3D_4(q)
        o = q ** 12 * (q ** 8 + q ** 4 + 1) * (q ** 6 - 1) * (q ** 2 - 1)
        if o <= N:
            add("3D4(%d)" % q, o, 3 * f)
        # ---- G_2(q), q >= 3
        o = q ** 6 * (q ** 6 - 1) * (q ** 2 - 1)
        if o <= N and q >= 3:
            add("G2(%d)" % q, o, f * (2 if p == 3 else 1))
        # ---- F_4(q)
        o = q ** 24 * (q ** 12 - 1) * (q ** 8 - 1) * (q ** 6 - 1) * (q ** 2 - 1)
        if o <= N:
            add("F4(%d)" % q, o, f * (2 if p == 2 else 1))
        # ---- E_6(q)
        o = q ** 36
        for k in (12, 9, 8, 6, 5, 2):
            o *= q ** k - 1
        g = gcd(3, q - 1)
        o //= g
        if o <= N:
            add("E6(%d)" % q, o, g * 2 * f)
        # ---- 2E_6(q)
        o = q ** 36
        for k, s in ((12, -1), (9, +1), (8, -1), (6, -1), (5, +1), (2, -1)):
            o *= q ** k + s
        g = gcd(3, q + 1)
        o //= g
        if o <= N:
            add("2E6(%d)" % q, o, g * 2 * f)
        # ---- E_7(q)
        o = q ** 63
        for k in (18, 14, 12, 10, 8, 6, 2):
            o *= q ** k - 1
        g = gcd(2, q - 1)
        o //= g
        if o <= N:
            add("E7(%d)" % q, o, g * f)
        # ---- E_8(q)
        o = q ** 120
        for k in (30, 24, 20, 18, 14, 12, 8, 2):
            o *= q ** k - 1
        if o <= N:
            add("E8(%d)" % q, o, f)
        # ---- 2B_2(q), q = 2^(2m+1) >= 8
        if p == 2 and f % 2 == 1 and f >= 3:
            o = q * q * (q * q + 1) * (q - 1)
            if o <= N:
                add("Sz(%d)" % q, o, f)
        # ---- 2G_2(q), q = 3^(2m+1) >= 27
        if p == 3 and f % 2 == 1 and f >= 3:
            o = q ** 3 * (q ** 3 + 1) * (q - 1)
            if o <= N:
                add("R(%d)" % q, o, f)
        # ---- 2F_4(q), q = 2^(2m+1) >= 8  (and the Tits group at q=2)
        if p == 2 and f % 2 == 1 and f >= 3:
            o = q ** 12 * (q ** 6 + 1) * (q ** 4 - 1) * (q ** 3 + 1) * (q - 1)
            if o <= N:
                add("2F4(%d)" % q, o, f)
    return res


# Exceptional isomorphisms: keep one representative name per group.
ISO_DROP = {
    # name -> canonical name it duplicates
    "L2(4)": "A5", "L2(5)": "A5", "L2(9)": "A6", "S4(2)": None,
    "L4(2)": "A8", "L2(7)": "L3(2)", "U4(2)": "S4(3)", "O5(3)": "S4(3)",
}
# NOTE: U3(3) = G2(2)' must NOT be dropped -- G2(q) is generated only for
# q >= 3 (G2(2) is not simple), so U3(3) is its unique representative.


def alt_orders(N):
    res = []
    o, m = 60, 5   # |A_5| = 60
    while o <= N:
        if N % o == 0:
            res.append(("A%d" % m, o, 4 if m == 6 else 2))
        m += 1
        o = o * m // 1
        o = 1
        f = 1
        for i in range(2, m + 1):
            f *= i
        o = f // 2
    return res


def alternating(N):
    res = []
    fac = 1
    for m in range(2, 200):
        fac *= m
        o = fac // 2
        if m < 5:
            continue
        if o > N:
            break
        if N % o == 0:
            res.append(("A%d" % m, o, 4 if m == 6 else 2))
    return res


def simple_divisors(N):
    """Complete list of non-abelian finite simple groups whose order divides N."""
    plist = sorted(factorint(N).keys())
    res = []
    res += alternating(N)
    res += [(n, o, u) for (n, o, u) in SPORADIC if N % o == 0]
    if N % TITS[1] == 0:
        res.append(TITS)
    res += lie_orders(N, plist)
    # deduplicate by (name); then remove duplicate names from exceptional isos
    seen = {}
    for (n, o, u) in res:
        if n in ISO_DROP:
            continue
        if n not in seen:
            seen[n] = (n, o, u)
    return sorted(seen.values(), key=lambda t: t[1])


# ---------------------------------------------------------------- census

def census(N, cands, maxfac=64):
    """All multisets with prod |S_i|^{l_i} | N and N/prod dividing
    prod |Out(S_i)|^{l_i} * l_i! ."""
    sols = []
    n = len(cands)

    def rec(i, rem, chosen, outbound, nfac):
        if rem == 1 or i == n:
            c = rem
            if c == 1 or outbound % c == 0:
                if chosen:
                    sols.append((list(chosen), c))
            return
        # prune: remaining candidates all have order > rem  -> only c=rem left
        (nm, o, u) = cands[i]
        # option: skip
        rec(i + 1, rem, chosen, outbound, nfac)
        # option: take l >= 1 copies
        l = 0
        acc = 1
        fact = 1
        while nfac + l + 1 <= maxfac:
            l += 1
            acc *= o
            fact *= l
            if rem % acc != 0:
                break
            chosen.append((nm, l))
            rec(i + 1, rem // acc, chosen, outbound * (u ** l) * fact, nfac + l)
            chosen.pop()
    rec(0, N, [], 1, 0)
    return sols


# ---------------------------------------------------------------- PHASE 2
#
# iota upper bounds for every simple group occurring in the Phase-1 censuses.
#   * "SP" : exact / upper bound from sporadic_twins.g (Lemma SP,
#            smallest index of a maximal subgroup with F <> 1) -- CTblLib.
#   * "par": smallest parabolic index, an upper bound because the centre of
#            the unipotent radical of a parabolic P is a nontrivial abelian
#            subgroup A with N_S(A) >= P.   [LIT: Borel-Tits]
IOTA_UB = {
    # --- from the GAP run (Lemma SP) ---
    "A5": 5, "A6": 10, "A7": 35, "A8": 15, "A9": 84, "A10": 120, "A11": 165,
    "A12": 220,
    "L2(8)": 9, "L2(11)": 12, "L2(13)": 14, "L2(17)": 18, "L2(19)": 20,
    "L2(23)": 24, "L2(25)": 26, "L2(27)": 28, "L2(29)": 30, "L2(31)": 32,
    "L2(125)": 126,
    "L3(2)": 7, "L3(3)": 13, "L3(4)": 21, "L3(5)": 31, "L4(3)": 40,
    "L5(2)": 31, "L6(2)": 63,
    "U3(3)": 28, "U3(4)": 65, "U3(5)": 126, "U3(8)": 513, "U4(3)": 112, "U5(2)": 165,
    "U6(2)": 693,
    "S4(3)": 27, "S4(4)": 85, "S4(5)": 156, "S6(2)": 63, "S6(3)": 364,
    "S8(2)": 255, "O7(3)": 351, "O8+(2)": 135, "O8-(2)": 119,
    "Sz(8)": 65, "3D4(2)": 819, "G2(4)": 1365, "F4(2)": 69615,
    "2F4(2)'": 1755,
    "M11": 55, "M12": 220, "M22": 77, "M23": 253, "M24": 759, "J1": 1045,
    "J2": 280, "J3": 17442, "HS": 3850, "McL": 15400, "He": 8330,
    "Ru": 188500, "Suz": 22880, "Co1": 1545600, "Co2": 46575, "Co3": 128800,
    "Fi22": 3510, "Fi23": 31671, "Fi24'": 4860485028, "HN": 1539000,
    "Th": 283599225, "ON": 2857239, "Ly": 9606125, "J4": 173067389,
    "B": 13571955000, "M": 97239461142009186000,
    # --- parabolic bounds (no CTblLib Maxes) ---
    "L2(16)": 17, "L2(32)": 33, "L2(47)": 48, "L2(49)": 50, "L2(64)": 65,
    "L3(16)": 273, "L4(4)": 85, "L5(4)": 341, "L6(4)": 1365,
    "U4(4)": 1105, "U4(8)": 33345,
    "S4(8)": 585, "S6(4)": 1365, "S10(2)": 1023,
    "O10+(2)": 527, "O10-(2)": 495, "O12+(2)": 2079,
    # further parabolic bounds [S:P] (Borel-Tits: N_S(Z(U_P)) = P, Z(U_P)
    # abelian nontrivial), for the factors that have no CTblLib Maxes:
    "L3(7)": 57, "L3(9)": 91, "L3(25)": 651, "L4(7)": 400, "L4(9)": 820,
    "L4(5)": 156, "L5(3)": 121, "L6(3)": 364,
    "U3(11)": 1332, "U4(5)": 3276, "U5(4)": 17425, "U6(4)": 279825,
    "S4(7)": 400, "S4(9)": 820, "S6(5)": 3906, "S8(3)": 3280, "S12(2)": 4095,
    "O7(5)": 3906, "O9(3)": 3240, "O8+(3)": 1120, "O8-(3)": 1066,
    "O10+(3)": 9922, "O12-(2)": 2015,
    "G2(3)": 364, "G2(5)": 3906, "Sz(32)": 1025, "2E6(2)": 3968,
}


def iota_ub(name, order):
    """upper bound for iota(S); generic parabolic/Sylow fallbacks."""
    if name in IOTA_UB:
        return IOTA_UB[name]
    if name.startswith("A") and name[1:].isdigit():
        m = int(name[1:])
        return m * (m - 1) * (m - 2) // 6      # C(m,3), 3-cycle normalizer
    if name.startswith("L2("):
        q = int(name[3:-1])
        return q + 1
    return None


def parse_lie(name):
    return None


def phase2(N, iotaS, cands):
    """Keep only socle factors S_i that can survive the orbit floor
    l * |Out(S_i)| * iota(S_i) >= iota(S)  with  |S_i|^l dividing |S|.
    Returns (survivors, dead, unknown)."""
    surv, dead, unk = [], [], []
    for (nm, o, u) in cands:
        iv = iota_ub(nm, o)
        if iv is None:
            unk.append((nm, o, u))
            surv.append((nm, o, u))
            continue
        lmin = -(-iotaS // (u * iv))           # ceil
        if pow_divides(o, lmin, N):
            surv.append((nm, o, u))
        else:
            dead.append((nm, o, u, lmin))
    return surv, dead, unk


def pow_divides(o, l, N):
    if l <= 0:
        return True
    acc = 1
    for _ in range(l):
        acc *= o
        if N % acc != 0:
            return False
        if acc > N:
            return False
    return True


def main():
    groups = SPORADIC + [TITS]
    only = sys.argv[1] if len(sys.argv) > 1 else None
    for (name, N, outS) in groups:
        if only and only != name:
            continue
        cands = simple_divisors(N)
        iotaS = IOTA_UB[name]
        surv, dead, unk = phase2(N, iotaS, cands)
        print("=" * 72)
        print("S = %s   |S| = %d   iota(S) = %d" % (name, N, iotaS))
        print("  simple divisors of |S|                : %d" % len(cands))
        print("   ", ", ".join(c[0] for c in cands))
        print("  PHASE 2 orbit-floor prefilter: %d of %d socle factors DEAD"
              % (len(dead), len(cands)))
        print("    surviving factors: %s" % ", ".join(c[0] for c in surv))
        if unk:
            print("    NO IOTA BOUND (kept): %s" % ", ".join(c[0] for c in unk))
        sols = census(N, surv)
        # split off the "T simple" solution (single factor, l=1, c=1, S_1 = S)
        nonsimple = []
        for (ch, c) in sols:
            tot = sum(l for (_, l) in ch)
            if tot >= 2 or c > 1:
                nonsimple.append((ch, c))
        print("  socle-multiset solutions (post-filter): %d" % len(sols))
        print("  NON-SIMPLE SURVIVORS                  : %d" % len(nonsimple))
        for (ch, c) in nonsimple:
            # final orbit-floor test with the actual multiplicities
            floor = min(l * dict((x[0], x[2]) for x in cands)[nm2]
                        * iota_ub(nm2, 0)
                        for (nm2, l) in ch)
            verdict = "KILLED (orbit floor %d < %d)" % (floor, iotaS) \
                if floor < iotaS else "*** LIVE ***"
            print("      SOCLE %-40s  c = %-6d %s" %
                  (" x ".join("%s^%d" % (nm, l) if l > 1 else nm
                              for (nm, l) in ch), c, verdict))
        sys.stdout.flush()


if __name__ == "__main__":
    main()
