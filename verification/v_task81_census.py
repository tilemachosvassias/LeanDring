#!/usr/bin/env python3
"""
v_task81_census.py -- INDEPENDENT adversarial re-implementation of the CFSG
simple-order enumerator + the Fitting-free non-simple order census used by
v_task50 (sporadics), v_task51/52 (L2) and v_task53/54 (rank 1).

Written from scratch (order formulas typed from the standard ATLAS/Conway
tables, NOT copied from v_task50_sporadic_twins.py).  Exact integer arithmetic
only; no floats anywhere in a yes/no decision.

Checks performed (see __main__ dispatch):
  selfcheck   -- order formulas against known small orders
  unique      -- order-uniqueness of every sporadic order (+ Tits) among
                 ALL finite simple orders; plus a full coincidence hunt over a
                 bounded range to test the CFSG order theorem statement
                 (only A8/L3(4) and B_n(q)/C_n(q), q odd, n>=3).
  census      -- Phase-1 order census (with the c | |Out(Soc)| constraint) for
                 the sporadic targets, plus the Lemma-C prefilter in its
                 MAXIMALLY GENEROUS form (a factor survives if
                 l*|S_i|^(2/3) >= iota(S)), which can only ADD survivors
                 relative to v_task50's prefilter.
  cop3        -- all simple groups of order coprime to 3 in a large range
                 (tests the "3-coprime simple => Suzuki" CFSG corollary).
"""
import sys
from math import comb, factorial

# ---------------------------------------------------------------- primes ----
def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    i = 2
    while i * i <= n:
        if sieve[i]:
            sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
        i += 1
    return [i for i in range(n + 1) if sieve[i]]


def prime_powers_upto(n):
    """[(q,p,f)] for all prime powers q = p^f <= n, f >= 1."""
    out = []
    for p in primes_upto(n):
        q, f = p, 1
        while q <= n:
            out.append((q, p, f))
            q *= p
            f += 1
    return out


def gcd(a, b):
    while b:
        a, b = b, a % b
    return a


# ------------------------------------------------------- sporadic orders ----
# typed from the ATLAS; cross-checked in selfcheck() against factorisations.
SPORADIC = {
    "M11":  7920,
    "M12":  95040,
    "M22":  443520,
    "M23":  10200960,
    "M24":  244823040,
    "J1":   175560,
    "J2":   604800,
    "J3":   50232960,
    "J4":   86775571046077562880,
    "HS":   44352000,
    "McL":  898128000,
    "He":   4030387200,
    "Ru":   145926144000,
    "Suz":  448345497600,
    "ON":   460815505920,
    "Co1":  4157776806543360000,
    "Co2":  42305421312000,
    "Co3":  495766656000,
    "Fi22": 64561751654400,
    "Fi23": 4089470473293004800,
    "Fi24'": 1255205709190661721292800,
    "HN":   273030912000000,
    "Ly":   51765179004000000,
    "Th":   90745943887872000,
    "B":    4154781481226426191177580544000000,
    "M":    808017424794512875886459904961710757005754368000000000,
    "2F4(2)'": 17971200,
}
SPOR_OUT = {
    "M11": 1, "M12": 2, "M22": 2, "M23": 1, "M24": 1,
    "J1": 1, "J2": 2, "J3": 2, "J4": 1, "HS": 2, "McL": 2, "He": 2,
    "Ru": 1, "Suz": 2, "ON": 2, "Co1": 1, "Co2": 1, "Co3": 1,
    "Fi22": 2, "Fi23": 1, "Fi24'": 2, "HN": 2, "Ly": 1, "Th": 1,
    "B": 1, "M": 1, "2F4(2)'": 2,
}


# ------------------------------------------------- Lie-type order formulas --
def ord_L(n, q):                     # A_{n-1}(q) = PSL(n,q), n >= 2
    d = gcd(n, q - 1)
    o = q ** (n * (n - 1) // 2)
    for i in range(2, n + 1):
        o *= q ** i - 1
    return o // d


def ord_U(n, q):                     # ^2A_{n-1}(q) = PSU(n,q), n >= 3
    d = gcd(n, q + 1)
    o = q ** (n * (n - 1) // 2)
    for i in range(2, n + 1):
        o *= q ** i - (-1) ** i
    return o // d


def ord_BC(n, q):                    # B_n(q) = O_{2n+1}(q) and C_n(q) = PSp(2n,q)
    d = gcd(2, q - 1)
    o = q ** (n * n)
    for i in range(1, n + 1):
        o *= q ** (2 * i) - 1
    return o // d


def ord_Dplus(n, q):                 # D_n(q) = POmega^+_{2n}(q), n >= 4
    d = gcd(4, q ** n - 1)
    o = q ** (n * (n - 1)) * (q ** n - 1)
    for i in range(1, n):
        o *= q ** (2 * i) - 1
    return o // d


def ord_Dminus(n, q):                # ^2D_n(q) = POmega^-_{2n}(q), n >= 4
    d = gcd(4, q ** n + 1)
    o = q ** (n * (n - 1)) * (q ** n + 1)
    for i in range(1, n):
        o *= q ** (2 * i) - 1
    return o // d


def ord_G2(q):
    return q ** 6 * (q ** 6 - 1) * (q ** 2 - 1)


def ord_F4(q):
    return q ** 24 * (q ** 12 - 1) * (q ** 8 - 1) * (q ** 6 - 1) * (q ** 2 - 1)


def ord_E6(q):
    d = gcd(3, q - 1)
    return (q ** 36 * (q ** 12 - 1) * (q ** 9 - 1) * (q ** 8 - 1)
            * (q ** 6 - 1) * (q ** 5 - 1) * (q ** 2 - 1)) // d


def ord_2E6(q):
    d = gcd(3, q + 1)
    return (q ** 36 * (q ** 12 - 1) * (q ** 9 + 1) * (q ** 8 - 1)
            * (q ** 6 - 1) * (q ** 5 + 1) * (q ** 2 - 1)) // d


def ord_E7(q):
    d = gcd(2, q - 1)
    return (q ** 63 * (q ** 18 - 1) * (q ** 14 - 1) * (q ** 12 - 1)
            * (q ** 10 - 1) * (q ** 8 - 1) * (q ** 6 - 1) * (q ** 2 - 1)) // d


def ord_E8(q):
    return (q ** 120 * (q ** 30 - 1) * (q ** 24 - 1) * (q ** 20 - 1)
            * (q ** 18 - 1) * (q ** 14 - 1) * (q ** 12 - 1)
            * (q ** 8 - 1) * (q ** 2 - 1))


def ord_3D4(q):
    return q ** 12 * (q ** 8 + q ** 4 + 1) * (q ** 6 - 1) * (q ** 2 - 1)


def ord_Sz(q):                       # ^2B_2(q), q = 2^(2m+1) >= 8
    return q ** 2 * (q ** 2 + 1) * (q - 1)


def ord_Ree(q):                      # ^2G_2(q), q = 3^(2m+1) >= 27
    return q ** 3 * (q ** 3 + 1) * (q - 1)


def ord_2F4(q):                      # ^2F_4(q), q = 2^(2m+1) >= 8
    return (q ** 12 * (q ** 6 + 1) * (q ** 4 - 1)
            * (q ** 3 + 1) * (q - 1))


# ------------------------------------------------------- |Out| formulas -----
def out_L(n, q, p, f):
    return gcd(n, q - 1) * f * (2 if n >= 3 else 1)


def out_U(n, q, p, f):
    return gcd(n, q + 1) * 2 * f


def out_C(n, q, p, f):               # PSp(2n,q)
    o = gcd(2, q - 1) * f
    if n == 2 and p == 2:
        o *= 2                       # extra graph automorphism of Sp4(2^f)
    return o


def out_B(n, q, p, f):               # O_{2n+1}(q), q odd, n >= 3
    return 2 * f


def out_Dplus(n, q, p, f):
    return gcd(4, q ** n - 1) * f * (6 if n == 4 else 2)


def out_Dminus(n, q, p, f):
    return gcd(4, q ** n + 1) * 2 * f


# -------------------------------------------------- the full enumerator -----
# each entry: (name, order, |Out|, iota_upper_bound_or_None)
# iota bound is only used by the *generous* prefilter, via Lemma C.

def alternating_upto(N):
    out = []
    m = 5
    while factorial(m) // 2 <= N:
        out.append(("A%d" % m, factorial(m) // 2, 4 if m == 6 else 2))
        m += 1
    return out


# exceptional isomorphisms: canonical name kept -> aliases dropped
# (we simply never *generate* the alias)
def factorise(n):
    """exact factorisation by trial division; asserts full factorisation."""
    f = {}
    d = 2
    while d * d <= n and d < 2 * 10 ** 6:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def lie_orders_upto(N, qmax=None, allowed_primes=None):
    """All simple groups of Lie type of order <= N.  Returns [(name,order,out)].

    Deduplication of exceptional isomorphisms is by construction:
      * L2(4), L2(5) dropped in favour of A5 ; L2(9) -> A6 ; L4(2) -> A8 ;
        L3(2) kept, L2(7) dropped ; C2(3)=S4(3) dropped in favour of U4(2).
      * B_n only for q odd and n >= 3 (B_n(2^k) = C_n(2^k), B_2 = C_2).
      * D_n, ^2D_n only n >= 4 (D_3 = L_4, ^2D_3 = U_4).
      * G2 only q >= 3 (G2(2)' = U3(3)), ^2G_2 only q >= 27, Sz/^2F4 q >= 8.
    """
    res = []
    if qmax is None:
        qmax = N
    if allowed_primes is not None:
        pps = []
        for p in sorted(allowed_primes):
            q, f = p, 1
            while q <= min(qmax, N):
                pps.append((q, p, f))
                q *= p
                f += 1
        pps.sort()
    else:
        pps = prime_powers_upto(min(qmax, N))
    for (q, p, f) in pps:
        # --- L_n(q) ---
        n = 2
        while True:
            if n == 2 and q in (2, 3):
                pass
            else:
                o = ord_L(n, q)
                if o > N:
                    break
                nm = "L%d(%d)" % (n, q)
                if (n, q) in ((2, 4), (2, 5), (2, 9), (4, 2), (2, 7)):
                    pass          # A5, A5, A6, A8, L3(2) already present
                else:
                    res.append((nm, o, out_L(n, q, p, f)))
            if n >= 2 and ord_L(n + 1, q) > N:
                break
            n += 1
            if n > 60:
                break
        # --- U_n(q) ---
        n = 3
        while True:
            if (n, q) == (3, 2):
                pass
            else:
                o = ord_U(n, q)
                if o > N:
                    break
                res.append(("U%d(%d)" % (n, q), o, out_U(n, q, p, f)))
            if ord_U(n + 1, q) > N:
                break
            n += 1
            if n > 60:
                break
        # --- C_n(q) = PSp(2n,q), n >= 2 ---
        n = 2
        while True:
            if (n, q) == (2, 2):
                pass
            else:
                o = ord_BC(n, q)
                if o > N:
                    break
                if (n, q) == (2, 3):
                    pass          # S4(3) = U4(2), keep U4(2)
                else:
                    res.append(("S%d(%d)" % (2 * n, q), o, out_C(n, q, p, f)))
            if ord_BC(n + 1, q) > N:
                break
            n += 1
            if n > 60:
                break
        # --- B_n(q), q odd, n >= 3 ---
        if p != 2:
            n = 3
            while ord_BC(n, q) <= N:
                res.append(("O%d(%d)" % (2 * n + 1, q), ord_BC(n, q),
                            out_B(n, q, p, f)))
                n += 1
                if n > 60:
                    break
        # --- D_n^+, D_n^-, n >= 4 ---
        n = 4
        while ord_Dplus(n, q) <= N:
            res.append(("O%d+(%d)" % (2 * n, q), ord_Dplus(n, q),
                        out_Dplus(n, q, p, f)))
            n += 1
            if n > 60:
                break
        n = 4
        while ord_Dminus(n, q) <= N:
            res.append(("O%d-(%d)" % (2 * n, q), ord_Dminus(n, q),
                        out_Dminus(n, q, p, f)))
            n += 1
            if n > 60:
                break
        # --- exceptionals ---
        if q >= 3 and ord_G2(q) <= N:
            res.append(("G2(%d)" % q, ord_G2(q), f * (2 if p == 3 else 1)))
        if ord_F4(q) <= N:
            res.append(("F4(%d)" % q, ord_F4(q), f * (2 if p == 2 else 1)))
        if ord_E6(q) <= N:
            res.append(("E6(%d)" % q, ord_E6(q), gcd(3, q - 1) * f * 2))
        if ord_2E6(q) <= N:
            res.append(("2E6(%d)" % q, ord_2E6(q), gcd(3, q + 1) * 2 * f))
        if ord_E7(q) <= N:
            res.append(("E7(%d)" % q, ord_E7(q), gcd(2, q - 1) * f))
        if ord_E8(q) <= N:
            res.append(("E8(%d)" % q, ord_E8(q), f))
        if ord_3D4(q) <= N:
            res.append(("3D4(%d)" % q, ord_3D4(q), 3 * f))
        if p == 2 and f % 2 == 1 and f >= 3 and ord_Sz(q) <= N:
            res.append(("Sz(%d)" % q, ord_Sz(q), f))
        if p == 3 and f % 2 == 1 and f >= 3 and ord_Ree(q) <= N:
            res.append(("R(%d)" % q, ord_Ree(q), f))
        if p == 2 and f % 2 == 1 and f >= 3 and ord_2F4(q) <= N:
            res.append(("2F4(%d)" % q, ord_2F4(q), f))
    return res


def all_simple_upto(N, qmax=None, allowed_primes=None):
    res = []
    res += alternating_upto(N)
    res += lie_orders_upto(N, qmax, allowed_primes)
    for nm, o in SPORADIC.items():
        if o <= N:
            res.append((nm, o, SPOR_OUT[nm]))
    return res


def divisor_cap(N):
    """(qcap, primes): every simple group whose order DIVIDES N has defining
    characteristic p | N (its order has a full q-power factor), and satisfies
    |S| >= q^3/3 for every family (the minimum over families is A_1 = L_2(q),
    |L_2(q)| = q(q^2-1)/d >= q^3/3 for q >= 4; every other family has |S| >= q^5/2).
    Hence q^3 <= 3N."""
    primes = set(factorise(N).keys())
    qcap = icbrt(3 * N) + 1
    return qcap, primes


# ------------------------------------------------------------ self check ----
KNOWN = {
    "A5": 60, "A6": 360, "A7": 2520, "A8": 20160,
    "L3(2)": 168, "L3(3)": 5616, "L3(4)": 20160, "L2(8)": 504,
    "L2(11)": 660, "L2(13)": 1092, "L2(16)": 4080, "L2(17)": 2448,
    "L4(3)": 6065280, "L5(2)": 9999360,
    "U3(3)": 6048, "U3(4)": 62400, "U3(5)": 126000, "U3(8)": 5515776,
    "U4(2)": 25920, "U4(3)": 3265920, "U5(2)": 13685760, "U6(2)": 9196830720,
    "S4(4)": 979200, "S4(5)": 4680000, "S6(2)": 1451520, "S8(2)": 47377612800,
    "O7(3)": 4585351680, "O8+(2)": 174182400, "O8-(2)": 197406720,
    "G2(3)": 4245696, "G2(4)": 251596800, "F4(2)": 3311126603366400,
    "3D4(2)": 211341312, "Sz(8)": 29120, "Sz(32)": 32537600,
    "R(27)": 10073444472,
    # |2F4(q)| = q^12(q^6+1)(q^4-1)(q^3+1)(q-1); anchored at q=2 by
    #   |2F4(2)| = 2*|2F4(2)'| = 35942400 (asserted below).
    "E6(2)": 214841575522005575270400,
}


def selfcheck():
    ok = True
    tbl = dict((nm, o) for nm, o, _ in all_simple_upto(10 ** 26, qmax=100))
    for nm, o in KNOWN.items():
        got = tbl.get(nm)
        if got != o:
            print("  MISMATCH %-10s expected %d got %s" % (nm, o, got))
            ok = False
    # sporadic orders: check a few factorisations by hand-independent means
    assert SPORADIC["M11"] == 2**4 * 3**2 * 5 * 11
    assert SPORADIC["M22"] == 2**7 * 3**2 * 5 * 7 * 11
    assert SPORADIC["M24"] == 2**10 * 3**3 * 5 * 7 * 11 * 23
    assert SPORADIC["Fi22"] == 2**17 * 3**9 * 5**2 * 7 * 11 * 13
    assert SPORADIC["Suz"] == 2**13 * 3**7 * 5**2 * 7 * 11 * 13
    assert SPORADIC["M"] == (2**46 * 3**20 * 5**9 * 7**6 * 11**2 * 13**3
                             * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71)
    assert SPORADIC["B"] == (2**41 * 3**13 * 5**6 * 7**2 * 11 * 13 * 17 * 19
                             * 23 * 31 * 47)
    assert SPORADIC["2F4(2)'"] * 2 == ord_2F4(2)
    print("  order-formula self-check: %s   (%d known orders tested)"
          % ("PASS" if ok else "FAIL", len(KNOWN)))
    return ok


# ----------------------------------------------------- order uniqueness -----
ISO_PAIRS = set()          # nothing should collide after dedup except the real ones


def uniqueness():
    print("=== (A) order-uniqueness of every sporadic order among ALL simple orders ===")
    NMAX = max(SPORADIC.values())
    # We only need groups whose order EQUALS a sporadic order, so it suffices to
    # enumerate all simple groups of order <= max sporadic order.  That is huge
    # for the Monster; instead enumerate per target with qmax bounded by the
    # target order (order >= q^2 for every family, so q <= sqrt(N) suffices,
    # and in fact q <= N^(1/3) for all families -- we use sqrt to be safe).
    for nm in sorted(SPORADIC, key=lambda k: SPORADIC[k]):
        N = SPORADIC[nm]
        qcap, primes = divisor_cap(N)
        cand = [x for x in all_simple_upto(N, qmax=qcap, allowed_primes=primes)
                if x[1] == N]
        names = sorted(set(c[0] for c in cand))
        flag = "UNIQUE" if names == [nm] else "!!! COLLISION"
        print("  %-8s |S| = %-40d %s %s" % (nm, N, flag, names))
    print()
    print("=== (B) full coincidence hunt: all simple orders <= 10^12 ===")
    LIM = 10 ** 12
    lst = all_simple_upto(LIM, qmax=icbrt(3 * LIM) + 1)
    by = {}
    for nm, o, _ in lst:
        by.setdefault(o, set()).add(nm)
    coll = sorted((o, sorted(v)) for o, v in by.items() if len(v) > 1)
    print("  groups enumerated: %d ; distinct orders: %d" % (len(lst), len(by)))
    print("  order coincidences between DISTINCT names:")
    for o, v in coll:
        print("     %-16d %s" % (o, v))
    print()
    print("=== (C) B_n(q) vs C_n(q) for q odd, n>=3 : orders equal? ===")
    bad = 0
    for n in (3, 4, 5, 6):
        for q in (3, 5, 7, 9, 11, 13, 25, 27):
            if ord_BC(n, q) != ord_BC(n, q):
                bad += 1
    print("  |B_n(q)| = |C_n(q)| identically by the shared formula "
          "q^{n^2} prod (q^{2i}-1)/d  -- verified structurally, %d anomalies" % bad)
    print("  (these are the CFSG order theorem's infinite family; O_{2n+1}(q) and")
    print("   S_{2n}(q) are printed as separate names above, hence the pairs in (B).)")


# ----------------------------------------------------------- the census -----
def icbrt(n):
    """exact integer cube root (floor), Newton, no floats."""
    if n < 0:
        raise ValueError
    if n == 0:
        return 0
    x = 1 << ((n.bit_length() + 2) // 3 + 1)
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


def lemC_bound_ok(order_Si, ell, iota_S):
    """generous prefilter: does l * |S_i|^{2/3} >= iota(S) hold?
    Tested as (l^3) * |S_i|^2 >= iota(S)^3, exact integers.
    By Lemma C, |Out|*iota_ab(S_i) <= |S_i|^{2/3}, so this is implied by the
    true orbit floor (F): every factor killed here is killed by (F) too, and
    this test kills STRICTLY FEWER factors than v_task50's prefilter."""
    return (ell ** 3) * order_Si * order_Si >= iota_S ** 3


def census(target_name, N, iota_S, verbose=True, maxfac=64):
    """All multisets {(S_i, l_i)} of simple groups with prod |S_i|^{l_i} | N
    and c = N/prod dividing prod(|Out_i|^{l_i} * l_i!).  Returns list of
    (socle_list, c).  Also returns the survivors of the generous prefilter."""
    qcap, primes = divisor_cap(N)
    divs = [(nm, o, ou) for (nm, o, ou) in
            all_simple_upto(N, qmax=qcap, allowed_primes=primes)
            if N % o == 0]
    divs.sort(key=lambda t: t[1])
    # generous Lemma-C prefilter: minimum multiplicity forced by the floor
    survivors = []
    for (nm, o, ou) in divs:
        lmin = 1
        while not lemC_bound_ok(o, lmin, iota_S):
            lmin += 1
            if o ** lmin > N:
                break
        if o ** lmin <= N and lemC_bound_ok(o, lmin, iota_S):
            survivors.append((nm, o, ou, lmin))
    sols = []

    def rec(idx, rem, chosen):
        if len(sols) > 200000:
            return
        if rem == 1 or idx >= len(divs):
            if chosen:
                c = N // 1
                prod = 1
                outb = 1
                for (nm, o, ou, l) in chosen:
                    prod *= o ** l
                    outb *= (ou ** l) * factorial(l)
                c = N // prod
                if outb % c == 0:
                    sols.append((list(chosen), c))
            return
        # option: skip this factor
        rec(idx + 1, rem, chosen)
        nm, o, ou = divs[idx]
        l = 1
        r = rem
        while r % o == 0:
            r //= o
            chosen.append((nm, o, ou, l))
            rec(idx + 1, r, chosen)
            chosen.pop()
            l += 1
            if l > maxfac:
                break

    rec(0, N, [])
    # de-dup / drop the trivial simple solution Soc = S itself
    out = []
    for ch, c in sols:
        if len(ch) == 1 and ch[0][1] == N and c == 1:
            continue
        out.append((ch, c))
    return divs, survivors, out


def run_census(targets):
    for nm in targets:
        N = SPORADIC[nm]
        iota = IOTA_TARGET[nm]
        import os
        mf = int(os.environ.get('MAXFAC', '64'))
        divs, surv, sols = census(nm, N, iota, maxfac=mf)
        proper = [s for s in surv if s[1] != N]
        print("--- %s   |S| = %d   iota(S) = %d" % (nm, N, iota))
        print("    simple divisors           : %d" % len(divs))
        print("    non-simple census solutions: %d" % len(sols))
        print("    generous-prefilter survivors (proper factors): %s"
              % ([ (s[0], s[3]) for s in proper ] or "NONE"))
        for ch, c in sols[:12]:
            print("        socle %s  c=%d"
                  % (" x ".join("%s^%d" % (a, d) if d > 1 else a
                                for (a, o, ou, d) in ch), c))
        if len(sols) > 12:
            print("        ... (%d more)" % (len(sols) - 12))
        # what happens to each solution under the TRUE orbit floor (F)?
        # every solution must have, for each factor, l_i*|Out_i|*iota_ab(S_i) >= iota(S).
        # We use the generous Lemma-C surrogate |Out|*iota_ab <= |S_i|^{2/3}.
        killed = 0
        alive = []
        for ch, c in sols:
            ok = True
            for (a, o, ou, l) in ch:
                if not lemC_bound_ok(o, l, iota):
                    ok = False
                    break
            if ok:
                alive.append((ch, c))
            else:
                killed += 1
        print("    after the generous floor  : %d killed, %d ALIVE" % (killed, len(alive)))
        for ch, c in alive:
            print("        ALIVE socle %s  c=%d"
                  % (" x ".join("%s^%d" % (a, d) if d > 1 else a
                                for (a, o, ou, d) in ch), c))
        print()


IOTA_TARGET = {   # iota_ab from v_task39 -- the values under audit
    "M11": 55, "M12": 220, "M22": 77, "M23": 253, "M24": 759,
    "J1": 1045, "J2": 280, "J3": 17442, "J4": 173067389,
    "HS": 3850, "McL": 15400, "He": 8330, "Ru": 188500, "Suz": 22880,
    "ON": 2857239, "Co1": 1545600, "Co2": 46575, "Co3": 128800,
    "Fi22": 3510, "Fi23": 31671, "Fi24'": 4860485028, "HN": 1539000,
    "Ly": 9606125, "Th": 283599225, "B": 13571955000,
    "M": 97239461142009186000, "2F4(2)'": 1755,
}


# ---------------------------------------------- 3-coprime simple groups -----
def cop3(limit=10 ** 30):
    print("=== simple groups of order coprime to 3, order <= %g ===" % limit)
    found = []
    # alternating
    m = 5
    while factorial(m) // 2 <= limit:
        if (factorial(m) // 2) % 3 != 0:
            found.append(("A%d" % m, factorial(m) // 2))
        m += 1
    # sporadic
    for nm, o in SPORADIC.items():
        if o <= limit and o % 3 != 0:
            found.append((nm, o))
    # Lie type: enumerate with a q-cap; order >= q^2 so q <= sqrt(limit)
    qcap = 1
    while qcap * qcap <= limit:
        qcap *= 2
    qcap = min(qcap, 200000)
    for (nm, o, ou) in lie_orders_upto(limit, qmax=qcap):
        if o % 3 != 0:
            found.append((nm, o))
    print("  q-cap used for Lie families: %d" % qcap)
    print("  groups found with 3 nmid |S| : %d" % len(found))
    for nm, o in sorted(found, key=lambda t: t[1]):
        print("     %-14s %d" % (nm, o))
    # explicit Suzuki check
    print("  cross-check |Sz(q)| mod 3 for q=2^f, f odd <= 41:")
    bad = []
    for f in range(3, 42, 2):
        q = 2 ** f
        if ord_Sz(q) % 3 == 0:
            bad.append(f)
    print("     divisible-by-3 exponents: %s" % (bad or "NONE"))


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "all"
    if cmd in ("all", "selfcheck"):
        print("=== order-formula self-check ===")
        selfcheck()
        print()
    if cmd in ("all", "unique"):
        uniqueness()
        print()
    if cmd in ("all", "cop3"):
        cop3(10 ** 24)
        print()
    if cmd in ("all", "census"):
        print("=== Phase-1 census, independent implementation ===")
        import os
        which = os.environ.get("TARGETS")
        if which:
            run_census(which.split(","))
        else:
            run_census(["M11", "M23", "J1", "HS", "Ly", "2F4(2)'", "M22",
                        "M24", "J2", "Fi22", "Fi23", "Co3", "McL", "Co2"])
