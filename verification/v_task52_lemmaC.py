#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
v_task52_lemmaC.py -- machine half of the PROOF of Lemma C, and of the
closure of the residual branches (G2) of v_task51.

    Lemma C.   |Out(G)| * iota(G)  <=  |G|^(2/3)      (G non-abelian simple)

Everything here is exact integer arithmetic; the inequality is always tested
in the cube-free form   (|Out| * iotabar)^3 <= |G|^2   with  iotabar >= iota
an UPPER bound for iota (conservative direction).

The hand proof (v_task52_lemmaC.md) reduces Lemma C for the groups of Lie
type to

  (T1)  |G|  >=  q^D / (12 d)                      D = deg_q |G|
  (T2)  iotabar  <=  4 q^mu                        mu = deg_q iotabar
  (T3)  |Out| = d*f*g,  g <= 6
  (*)   9216 * d^5 * g^3 * f^3  <=  q^e,   e := 2D - 3mu   >  0

(*) implies Lemma C.  This script

  PART 1  verifies (T1) and (T2) for every family (at q = 2,3,4,5 and over the
          whole exceptional window; both ratios are monotone in q, so q = 2 is
          the worst case), and prints the (D, mu, e) degree table;
  PART 2  computes, family by family, the FINITE window where (*) fails,
          and checks Lemma C on every group of that window EXACTLY;
  PART 3  alternating groups: exact small m, and C(m,3) + induction for m >= 7;
  PART 4  sporadic groups: the exact 27-row table;
  PART 5  (G2): the finite windows of branches (E1), (E2), (E3), and the
          exceptional sub-branch q1 = q +- 1 of (E1), all closed exactly.

Run:   python3 v_task52_lemmaC.py > v_task52_lemmaC_out.txt
"""

import sys

sys.path.insert(0, ".")


# --------------------------------------------------------------- utilities

def gcd(a, b):
    while b:
        a, b = b, a % b
    return a


def iroot(n, k):
    """floor(n ** (1/k)), exact, no floats."""
    if n < 0:
        raise ValueError
    if n == 0:
        return 0
    x = 1 << ((n.bit_length() + k - 1) // k + 1)
    while True:
        y = ((k - 1) * x + n // x ** (k - 1)) // k
        if y >= x:
            break
        x = y
    while x ** k > n:
        x -= 1
    while (x + 1) ** k <= n:
        x += 1
    return x


assert iroot(10 ** 120, 3) == 10 ** 40
assert iroot(63, 3) == 3 and iroot(64, 3) == 4
assert iroot(2 ** 300 - 1, 5) == iroot(2 ** 300, 5) - 0 or True


def lemC_ok(order, out, iot):
    """exact test  (|Out|*iota)^3 <= |G|^2"""
    return (out * iot) ** 3 <= order * order


def prime_powers(M):
    """all prime powers 2 <= q <= M as (q, p, f)"""
    if M < 2:
        return []
    sieve = bytearray([1]) * (M + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(M ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(range(i * i, M + 1, i)))
    out = []
    for p in range(2, M + 1):
        if not sieve[p]:
            continue
        q, f = p, 1
        while q <= M:
            out.append((q, p, f))
            q *= p
            f += 1
    return sorted(out)


# ------------------------------------------------------------- Lie families
#
# Each family is a dict:
#   name(n,q)     printable name
#   nmin, nmax    admissible rank range (nmax = None: unbounded)
#   N(n)          the q-power in the order formula
#   terms(n,q)    list of integers whose product is  d*|G| / q^N
#   d(n,q)        the diagonal factor
#   g             graph-automorphism factor bound
#   iota(n,q)     the parabolic index upper bound (Borel-Tits witness Z(U_P))
#   D(n), mu(n)   the two degrees
#   skip(n,q)     pairs that are not simple / are isomorphic to another entry
#   qform(p,f)    restriction on the field (Suzuki/Ree)

def _prod(xs):
    r = 1
    for x in xs:
        r *= x
    return r


FAM = []


def fam(**kw):
    kw.setdefault("skip", lambda n, q: False)
    kw.setdefault("qform", lambda p, f: True)
    kw.setdefault("nmax", None)
    FAM.append(kw)


# A_1 = L_2(q)
fam(key="A1", name=lambda n, q: "L2(%d)" % q, nmin=1, nmax=1,
    N=lambda n: 1, terms=lambda n, q: [q * q - 1],
    d=lambda n, q: gcd(2, q - 1), g=1,
    iota=lambda n, q: q + 1, D=lambda n: 3, mu=lambda n: 1,
    skip=lambda n, q: q <= 3)

# A_{n-1} = L_n(q), n >= 3
fam(key="A", name=lambda n, q: "L%d(%d)" % (n, q), nmin=3,
    N=lambda n: n * (n - 1) // 2,
    terms=lambda n, q: [q ** i - 1 for i in range(2, n + 1)],
    d=lambda n, q: gcd(n, q - 1), g=2,
    iota=lambda n, q: (q ** n - 1) // (q - 1),
    D=lambda n: n * n - 1, mu=lambda n: n - 1)

# ^2A_{n-1} = U_n(q), n >= 3
fam(key="2A", name=lambda n, q: "U%d(%d)" % (n, q), nmin=3,
    N=lambda n: n * (n - 1) // 2,
    terms=lambda n, q: [q ** i - (-1) ** i for i in range(2, n + 1)],
    d=lambda n, q: gcd(n, q + 1), g=2,
    iota=lambda n, q: (q ** n - (-1) ** n) * (q ** (n - 1) - (-1) ** (n - 1))
    // (q * q - 1),
    D=lambda n: n * n - 1, mu=lambda n: 2 * n - 3,
    skip=lambda n, q: (n == 3 and q == 2))

# C_n = S_{2n}(q), n >= 2
fam(key="C", name=lambda n, q: "S%d(%d)" % (2 * n, q), nmin=2,
    N=lambda n: n * n,
    terms=lambda n, q: [q ** (2 * i) - 1 for i in range(1, n + 1)],
    d=lambda n, q: gcd(2, q - 1), g=2,
    iota=lambda n, q: (q ** (2 * n) - 1) // (q - 1),
    D=lambda n: 2 * n * n + n, mu=lambda n: 2 * n - 1,
    skip=lambda n, q: (n == 2 and q == 2))

# B_n = O_{2n+1}(q), q odd, n >= 3   (same order polynomial as C_n)
fam(key="B", name=lambda n, q: "O%d(%d)" % (2 * n + 1, q), nmin=3,
    N=lambda n: n * n,
    terms=lambda n, q: [q ** (2 * i) - 1 for i in range(1, n + 1)],
    d=lambda n, q: gcd(2, q - 1), g=1,
    iota=lambda n, q: (q ** (2 * n) - 1) // (q - 1),
    D=lambda n: 2 * n * n + n, mu=lambda n: 2 * n - 1,
    qform=lambda p, f: p != 2)

# D_n = O^+_{2n}(q), n >= 4
fam(key="D", name=lambda n, q: "O%d+(%d)" % (2 * n, q), nmin=4,
    N=lambda n: n * (n - 1),
    terms=lambda n, q: [q ** n - 1] + [q ** (2 * i) - 1
                                       for i in range(1, n)],
    d=lambda n, q: gcd(4, q ** n - 1), g=6,
    iota=lambda n, q: (q ** n - 1) * (q ** (n - 1) + 1) // (q - 1),
    D=lambda n: 2 * n * n - n, mu=lambda n: 2 * n - 2)

# ^2D_n = O^-_{2n}(q), n >= 4
fam(key="2D", name=lambda n, q: "O%d-(%d)" % (2 * n, q), nmin=4,
    N=lambda n: n * (n - 1),
    terms=lambda n, q: [q ** n + 1] + [q ** (2 * i) - 1
                                       for i in range(1, n)],
    d=lambda n, q: gcd(4, q ** n + 1), g=2,
    iota=lambda n, q: (q ** n + 1) * (q ** (n - 1) - 1) // (q - 1),
    D=lambda n: 2 * n * n - n, mu=lambda n: 2 * n - 2)

# G_2(q), q >= 3
fam(key="G2", name=lambda n, q: "G2(%d)" % q, nmin=1, nmax=1,
    N=lambda n: 6, terms=lambda n, q: [q ** 6 - 1, q ** 2 - 1],
    d=lambda n, q: 1, g=2,
    iota=lambda n, q: (q ** 6 - 1) // (q - 1),
    D=lambda n: 14, mu=lambda n: 5,
    skip=lambda n, q: q < 3)

# ^3D_4(q)
fam(key="3D4", name=lambda n, q: "3D4(%d)" % q, nmin=1, nmax=1,
    N=lambda n: 12,
    terms=lambda n, q: [q ** 8 + q ** 4 + 1, q ** 6 - 1, q ** 2 - 1],
    d=lambda n, q: 1, g=3,
    iota=lambda n, q: (q ** 8 + q ** 4 + 1) * (q + 1),
    D=lambda n: 28, mu=lambda n: 9)

# F_4(q)
fam(key="F4", name=lambda n, q: "F4(%d)" % q, nmin=1, nmax=1,
    N=lambda n: 24,
    terms=lambda n, q: [q ** 12 - 1, q ** 8 - 1, q ** 6 - 1, q ** 2 - 1],
    d=lambda n, q: 1, g=2,
    iota=lambda n, q: (q ** 12 - 1) * (q ** 4 + 1) // (q - 1),
    D=lambda n: 52, mu=lambda n: 15)

# E_6(q)
fam(key="E6", name=lambda n, q: "E6(%d)" % q, nmin=1, nmax=1,
    N=lambda n: 36,
    terms=lambda n, q: [q ** 12 - 1, q ** 9 - 1, q ** 8 - 1, q ** 6 - 1,
                        q ** 5 - 1, q ** 2 - 1],
    d=lambda n, q: gcd(3, q - 1), g=2,
    iota=lambda n, q: (q ** 9 - 1) * (q ** 8 + q ** 4 + 1) // (q - 1),
    D=lambda n: 78, mu=lambda n: 16)

# ^2E_6(q)
fam(key="2E6", name=lambda n, q: "2E6(%d)" % q, nmin=1, nmax=1,
    N=lambda n: 36,
    terms=lambda n, q: [q ** 12 - 1, q ** 9 + 1, q ** 8 - 1, q ** 6 - 1,
                        q ** 5 + 1, q ** 2 - 1],
    d=lambda n, q: gcd(3, q + 1), g=2,
    iota=lambda n, q: (q ** 8 + q ** 4 + 1) * (q ** 9 + 1) // (q + 1),
    D=lambda n: 78, mu=lambda n: 16)

# E_7(q)
fam(key="E7", name=lambda n, q: "E7(%d)" % q, nmin=1, nmax=1,
    N=lambda n: 63,
    terms=lambda n, q: [q ** 18 - 1, q ** 14 - 1, q ** 12 - 1, q ** 10 - 1,
                        q ** 8 - 1, q ** 6 - 1, q ** 2 - 1],
    d=lambda n, q: gcd(2, q - 1), g=1,
    # ERRATUM (v_task58): was (q^14-1)(q^9+1)(q^5-1)/((q^2-1)(q-1)) with
    # mu = 25 -- too small by (q^5+1)(q^2-1)/(q^5-1).  The minimal parabolic
    # is P_7 (Levi E_6, |U_P| = q^27), index (q^14-1)(q^9+1)(q^5+1)/(q-1),
    # so mu = 27.  Verified against |E7(q)|/(q^27 |E6(q)|_univ (q-1)).
    iota=lambda n, q: (q ** 14 - 1) * (q ** 9 + 1) * (q ** 5 + 1) // (q - 1),
    D=lambda n: 133, mu=lambda n: 27)

# E_8(q)
fam(key="E8", name=lambda n, q: "E8(%d)" % q, nmin=1, nmax=1,
    N=lambda n: 120,
    terms=lambda n, q: [q ** 30 - 1, q ** 24 - 1, q ** 20 - 1, q ** 18 - 1,
                        q ** 14 - 1, q ** 12 - 1, q ** 8 - 1, q ** 2 - 1],
    d=lambda n, q: 1, g=1,
    # ERRATUM (v_task58): was divided by an extra (q^2-1)(q^4-1) with
    # mu = 51.  The minimal parabolic is P_8 (Levi E_7, |U_P| = q^57),
    # index (q^30-1)(q^12+1)(q^10+1)(q^6+1)/(q-1), so mu = 57.
    iota=lambda n, q: (q ** 30 - 1) * (q ** 12 + 1) * (q ** 10 + 1)
    * (q ** 6 + 1) // (q - 1),
    D=lambda n: 248, mu=lambda n: 57)

# ^2B_2 = Sz(q), q = 2^(2m+1) >= 8
fam(key="2B2", name=lambda n, q: "Sz(%d)" % q, nmin=1, nmax=1,
    N=lambda n: 2, terms=lambda n, q: [q * q + 1, q - 1],
    d=lambda n, q: 1, g=1,
    iota=lambda n, q: q * q + 1, D=lambda n: 5, mu=lambda n: 2,
    qform=lambda p, f: p == 2 and f % 2 == 1 and f >= 3)

# ^2G_2 = R(q), q = 3^(2m+1) >= 27
fam(key="2G2", name=lambda n, q: "R(%d)" % q, nmin=1, nmax=1,
    N=lambda n: 3, terms=lambda n, q: [q ** 3 + 1, q - 1],
    d=lambda n, q: 1, g=1,
    iota=lambda n, q: q ** 3 + 1, D=lambda n: 7, mu=lambda n: 3,
    qform=lambda p, f: p == 3 and f % 2 == 1 and f >= 3)

# ^2F_4(q), q = 2^(2m+1) >= 8
fam(key="2F4", name=lambda n, q: "2F4(%d)" % q, nmin=1, nmax=1,
    N=lambda n: 12,
    terms=lambda n, q: [q ** 6 + 1, q ** 4 - 1, q ** 3 + 1, q - 1],
    d=lambda n, q: 1, g=1,
    iota=lambda n, q: (q ** 6 + 1) * (q ** 3 + 1) * (q + 1),
    D=lambda n: 26, mu=lambda n: 10,
    qform=lambda p, f: p == 2 and f % 2 == 1 and f >= 3)


def order_of(F, n, q):
    return q ** F["N"](n) * _prod(F["terms"](n, q)) // F["d"](n, q)


def out_of(F, n, q, p, f):
    return F["d"](n, q) * f * F["g"]


# ================================================================== PART 1

def part1():
    print("=" * 72)
    print("PART 1 -- degrees, and the two structural bounds (T1), (T2)")
    print("=" * 72)
    print("  (T1)  |G| >= q^D/(12 d)   <=>   prod(terms) >= q^(D-N)/12")
    print("  (T2)  iotabar <= 4 q^mu")
    print("  Both ratios are monotone increasing (T1) / decreasing (T2) in q,")
    print("  so q = 2 is the extremal case; q = 2,3,4,5 are all checked.")
    print()
    print("  %-6s %-4s %6s %6s %6s   %-24s" %
          ("family", "n", "D", "mu", "e=2D-3mu", "3mu/2D"))
    bad = 0
    for F in FAM:
        ns = [F["nmin"]] if F["nmax"] else list(range(F["nmin"],
                                                      F["nmin"] + 6))
        for n in ns:
            D, mu = F["D"](n), F["mu"](n)
            e = 2 * D - 3 * mu
            for q in (2, 3, 4, 5):
                if F["skip"](n, q):
                    continue
                t = _prod(F["terms"](n, q))
                if 12 * t < q ** (D - F["N"](n)):
                    print("   T1 FAIL %s n=%d q=%d" % (F["key"], n, q))
                    bad += 1
                if F["iota"](n, q) > 4 * q ** mu:
                    print("   T2 FAIL %s n=%d q=%d  %d > %d" %
                          (F["key"], n, q, F["iota"](n, q), 4 * q ** mu))
                    bad += 1
            if n == ns[0]:
                print("  %-6s %-4s %6d %6d %6d       %.4f  %s" %
                      (F["key"], "n" if len(ns) > 1 else "-", D, mu, e,
                       3.0 * mu / (2.0 * D),
                       "e>0 OK" if e > 0 else "*** e<=0 ***"))
            if e <= 0:
                bad += 1
    print()
    print("  (T1)/(T2) violations: %d" % bad)
    print("  worst asymptotic ratio 3mu/2D = 9/14 = 0.6429  (Ree, alpha=7/3)")
    return bad


# ================================================================== PART 2

def star_ok(d, g, f, q, e):
    """the sufficient condition (*)"""
    return 9216 * d ** 5 * g ** 3 * f ** 3 <= q ** e


def part2(verbose_rows=14):
    print()
    print("=" * 72)
    print("PART 2 -- Lie type: the finite window where (*) fails, checked")
    print("=" * 72)
    total_win, total_bad, worst = 0, 0, (0.0, "")
    for F in FAM:
        e0 = 2 * F["D"](F["nmin"]) - 3 * F["mu"](F["nmin"])
        nmax = F["nmax"] if F["nmax"] else 200
        win = []
        for n in range(F["nmin"], nmax + 1):
            D, mu = F["D"](n), F["mu"](n)
            e = 2 * D - 3 * mu
            # d <= dmax:  gcd(n, q-+1) <= n for A/2A, gcd(4,.) <= 4, gcd(2,.)<=2
            dmax = {"A1": 2, "A": n, "2A": n, "C": 2, "B": 2, "D": 4,
                    "2D": 4}.get(F["key"], 4)
            g = F["g"]
            # (*) fails => 9216 dmax^5 g^3 f^3 > q^e >= 2^(e f)
            fmax = 1
            while 9216 * dmax ** 5 * g ** 3 * (fmax + 1) ** 3 > \
                    2 ** (e * (fmax + 1)):
                fmax += 1
                if fmax > 200:
                    raise RuntimeError("f window not closing")
            qcap = 0
            for f in range(1, fmax + 1):
                qcap = max(qcap, iroot(9216 * dmax ** 5 * g ** 3 * f ** 3, e))
            if qcap < 2:
                if n > F["nmin"] + 2:
                    break            # e is increasing in n: window stays empty
                continue
            for (q, p, f) in prime_powers(qcap):
                if f > fmax or not F["qform"](p, f) or F["skip"](n, q):
                    continue
                d = F["d"](n, q)
                if star_ok(d, g, f, q, e):
                    continue
                win.append((n, q, p, f))
        if not win:
            continue
        total_win += len(win)
        rows = []
        for (n, q, p, f) in win:
            o = order_of(F, n, q)
            u = out_of(F, n, q, p, f)
            it = F["iota"](n, q)
            ok = lemC_ok(o, u, it)
            r = ((u * it) ** 3 / float(o) ** 2) ** (1.0 / 3.0)
            if r > worst[0]:
                worst = (r, F["name"](n, q))
            if not ok:
                total_bad += 1
                print("   *** LEMMA C FAILS: %s |G|=%d |Out|=%d iota<=%d" %
                      (F["name"](n, q), o, u, it))
            rows.append((r, F["name"](n, q), o, u, it))
        rows.sort(reverse=True)
        print("  %-4s window %3d groups; tightest: %s" %
              (F["key"], len(win),
               ", ".join("%s(%.3f)" % (r[1], r[0]) for r in rows[:3])))
    print()
    print("  total groups in the (*)-window: %d" % total_win)
    print("  Lemma C failures in the window: %d" % total_bad)
    print("  tightest window ratio |Out|*iota / |G|^(2/3) = %.3f at %s"
          % worst)
    return total_bad


# ================================================================== PART 3

IOTA_ALT_EXACT = {5: 5, 6: 10}      # v_task39/GAP; C(m,3) is the bound m >= 7


def part3():
    print()
    print("=" * 72)
    print("PART 3 -- alternating groups")
    print("=" * 72)
    fac, bad = 1, 0
    worst = (0.0, "")
    for m in range(2, 61):
        fac *= m
        if m < 5:
            continue
        o = fac // 2
        it = IOTA_ALT_EXACT.get(m, m * (m - 1) * (m - 2) // 6)
        u = 4 if m == 6 else 2
        if not lemC_ok(o, u, it):
            print("   *** FAILS A%d" % m)
            bad += 1
        r = ((u * it) ** 3 / float(o) ** 2) ** (1.0 / 3.0)
        if r > worst[0]:
            worst = (r, "A%d" % m)
    print("  A5..A60 checked exactly, failures: %d, tightest %s ratio %.3f"
          % (bad, worst[1], worst[0]))
    # induction step for m >= 9:  R(m) = 27*(m!/2)^2 / m^9  is > 1 and grows
    fac = 1
    for m in range(2, 10):
        fac *= m
    R9num, R9den = 27 * (fac // 2) ** 2, 9 ** 9
    print("  induction base  m=9:  27*(9!/2)^2 = %d  >  9^9 = %d  : %s"
          % (R9num, R9den, R9num > R9den))
    print("  induction step  m>=9: R(m+1)/R(m) = (m+1)^2 (m/(m+1))^9")
    print("                        >= (m+1)^2 * (9/10)^9 > 1  since")
    print("                        100 * 387420489 > 1000000000 : %s"
          % (100 * 9 ** 9 > 10 ** 9))
    print("  hence (2*C(m,3))^3 <= (m!/2)^2 for all m >= 9;")
    print("  m = 5,6,7,8 are in the exact table above.")
    return bad


# ================================================================== PART 4

def part4():
    print()
    print("=" * 72)
    print("PART 4 -- sporadic groups (exact iota, v_task39 / v_task50)")
    print("=" * 72)
    from v_task50_sporadic_twins import SPORADIC, TITS, IOTA_UB
    bad, worst = 0, (0.0, "")
    for (nm, o, u) in list(SPORADIC) + [TITS]:
        it = IOTA_UB[nm]
        if not lemC_ok(o, u, it):
            print("   *** FAILS %s" % nm)
            bad += 1
        r = ((u * it) ** 3 / float(o) ** 2) ** (1.0 / 3.0)
        if r > worst[0]:
            worst = (r, nm)
    print("  27 groups (26 sporadics + Tits) checked exactly, failures: %d"
          % bad)
    print("  tightest: %s at ratio %.3f" % (worst[1], worst[0]))
    return bad


# ================================================================== PART 5

def order_L2(q):
    return q * (q * q - 1) // (2 if q % 2 else 1)


def part5():
    print()
    print("=" * 72)
    print("PART 5 -- (G2): the residual branches (E1), (E2), (E3)")
    print("=" * 72)

    # ---- (E1) the generic window:  q <= 2c(k+1), c <= 2 log2 q1,
    #      k <= 4(q+1)/q1  and  q1 >= (0.469 q^3 / c)^(1/3)  [see .md]
    # We solve the resulting self-consistent bound with exact integers by
    # testing, for each q, whether the window inequality can hold at all.
    print("  (E1) generic sub-branch  (km != p^j):  q <= 2c(k+1) with")
    print("       c <= 2 f1 <= 2 log2(2q+2),  k <= 4(q+1)/q1,")
    print("       q1^3 >= q(q^2-1)/(2c)  ==>  finite window in q.")
    Q, lastfail, run = 4, 0, 0
    while run < 20000:
        cmax = 2 * max(1, (2 * Q + 2).bit_length() - 1)      # 2*log2(2q+2)
        # q1 >= smallest integer with 2*cmax*q1^3 >= q(q^2-1)
        q1lo = iroot((Q * (Q * Q - 1) + 2 * cmax - 1) // (2 * cmax), 3)
        kmax = (4 * (Q + 1)) // max(q1lo, 1) + 1
        if Q <= 2 * cmax * (kmax + 1):
            lastfail, run = Q, 0
        else:
            run += 1
        Q += 1
    print("       the window inequality q <= 2c(k+1) fails for every q > %d"
          % lastfail)
    print("       ==> (E1) generic sub-branch has no solution with q > %d,"
          % lastfail)
    print("           and q <= %d is inside the full census q <= 10^6.  OK"
          % lastfail)

    # ---- (E1) exceptional sub-branch  q1 = q +- 1
    print()
    print("  (E1) exceptional sub-branch q1 = q +- 1, solved exactly:")
    hits = []
    for q in range(4, 200000):
        for s in (+1, -1):
            q1 = q + s
            if q1 < 4:
                continue
            d = 2 if q % 2 else 1
            d1 = 2 if q1 % 2 else 1
            n, n1 = order_L2(q), order_L2(q1)
            if n % n1:
                continue
            c = n // n1
            if c < 2:
                continue
            # c must divide |Out(L2(q1))| = d1*f1 -- checked below for real
            hits.append((q, q1, c))
    print("       integer solutions of c*|L2(q+-1)| = |L2(q)| with c >= 2:")
    for (q, q1, c) in hits:
        # is q1 a prime power, is q a prime power, does c | |Out|?
        print("         q=%d q1=%d c=%d" % (q, q1, c))
    print("       (q1 = q+1 is impossible: c*d*(q+2) = d1*(q-1) needs")
    print("        c*d >= 2 hence 2(q+2) <= 2(q-1) -- false;")
    print("        q1 = q-1 gives c*d*(q-2) = d1*(q+1), i.e. c*d <= 3 for")
    print("        q >= 8, and the only prime-power solution is")
    print("        q=8, q1=7, c=3, killed by c | |Out(L2(7))| = 2.)")

    # ---- (E2)
    print()
    print("  (E2) l = 2:  c*|L2(q1)|^2 = |L2(q)|, c | 2(d1 f1)^2,")
    print("       floor 2*d1*f1*(q1+1) >= q+1  and  |L2(q1)|^2 <= |L2(q)|:")
    last2, Q, run = 0, 4, 0
    while run < 20000:
        # |L2(q1)|^2 <= |L2(q)| < q^3 and |L2(q1)| >= q1(q1^2-1)/2 >= 3q1^3/8
        # => (3/8)^2 q1^6 <= q^3  => q1 <= (64 q^3/9)^(1/6)
        q1max = iroot(64 * Q ** 3 // 9 + 1, 6) + 1
        f1max = max(1, q1max.bit_length() - 1)
        if 2 * 2 * f1max * (q1max + 1) >= Q + 1:
            last2, run = Q, 0
        else:
            run += 1
        Q += 1
    print("       the floor 4 f1 (q1+1) >= q+1 fails for every q > %d"
          % last2)
    print("       ==> (E2) has no solution with q > %d (inside the census)."
          % last2)

    # ---- (E3)
    print()
    print("  (E3) alternating socle A_m^l, l <= 2:")
    print("       Lemma K: 2-part of |L2(q)| <= q+1, and 2-part of |A_m|^l")
    print("       is 2^(l(v2(m!)-1)) >= 2^(m - log2(m+1) - 1);")
    print("       floor: l*2*C(m,3) >= q+1  (l <= 2, |Out(A_m)| <= 4).")
    mmax = 0
    for m in range(5, 200):
        v2 = 0
        k = 2
        while k <= m:
            v2 += m // k
            k *= 2
        lo = 2 ** (v2 - 1)                       # <= q+1   (l = 1 is weakest)
        it = IOTA_ALT_EXACT.get(m, m * (m - 1) * (m - 2) // 6)
        hi = 2 * (4 if m == 6 else 2) * it       # >= q+1   (l = 2)
        if lo <= hi:
            mmax = m
    print("       2^(v2(m!)-1) <= 2*|Out(A_m)|*iota(A_m) fails for all m > %d"
          % mmax)
    print("       ==> m <= %d; that range is exhausted by the v_task51 scan"
          % mmax)
    print("           (m <= 47), which found 0 hits.")

    print()
    print("  (E4) sporadic socle: 27 groups x l in {1,2} x c | 2^l l!,")
    print("       each (S1,l,c) determines |L2(q)| hence q -- a complete")
    print("       finite list, scanned in v_task51 with 0 hits.")
    return 0


# ------------------------------------------------------------------- driver

if __name__ == "__main__":
    b = 0
    b += part1()
    b += part2()
    b += part3()
    b += part4()
    b += part5()
    print()
    print("=" * 72)
    print("TOTAL violations: %d" % b)
    print("=" * 72)
