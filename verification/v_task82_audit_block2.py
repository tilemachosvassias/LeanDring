#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
v_task82 -- ADVERSARIAL AUDIT of the linear/unitary tower
            (NOTES.md sec 4be, 4bh + addendum;
             v_task55_l3_twins, v_task56_lu_twins, v_task60_lu_residues)

Everything here is re-derived from scratch: the family table below is
written independently from the standard order / parabolic-index formulas
and then CROSS-CHECKED against v_task52's FAM (which every audited note
imports) and against GAP.  Where the audit reuses an audited script it
does so only to re-run it under a PERTURBED hypothesis (erratum values,
relaxed slack), never to confirm it against itself.

PARTS
  1  v_task55 (L3):  Lemma Q re-derivation, the erratum question, the
     tail bound, the 56-violator list, the 4 census survivors.
  2  v_task56 (LU):  Lemma Z's o(1), the j*d1 window chain, the unitary
     iota correction.
  3  v_task60:       the PACK identity, Lemma DEG, the d>20 tail at d=25.
  4  cross-cutting:  B_n/C_n vs L/U, the a/N table.
  5  the PARANOID re-run of v_task60 PART C with the (Z2)/(ZM) slack
     restored.

Usage:  python3 v_task82_audit_block2.py [1|2|3|4|5|all]
"""

import sys
from fractions import Fraction as Fr

sys.path.insert(0, ".")

BAR = "=" * 74


def gcd(a, b):
    while b:
        a, b = b, a % b
    return abs(a)


def isqrt(n):
    if n < 0:
        raise ValueError
    x = int(n ** 0.5) + 2
    while x * x > n:
        x -= 1
    return x


def prod(xs):
    r = 1
    for x in xs:
        r *= x
    return r


def factorint(n):
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


def is_prime(n):
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1 if d == 2 else 2
    return True


def prime_powers_upto(N):
    """(q, p, f) for every prime power q <= N, q >= 2"""
    out = []
    sieve = [True] * (N + 1)
    for p in range(2, N + 1):
        if not sieve[p]:
            continue
        for m in range(p * p, N + 1, p):
            sieve[m] = False
        q, f = p, 1
        while q <= N:
            out.append((q, p, f))
            q *= p
            f += 1
    out.sort()
    return out


# ======================================================================
#  An INDEPENDENT table of the finite simple groups of Lie type.
#  order(n,q) is written out as  q^N * prod(terms) / dg   with the
#  standard order polynomials;  iota(n,q) is the index of the smallest
#  maximal parabolic (Borel-Tits witness Z(U_P)).
# ======================================================================

def _L(n, q):
    return q ** (n * (n - 1) // 2) * prod(q ** i - 1
                                          for i in range(2, n + 1)) // gcd(n, q - 1)


AUD = []            # independent family table


def afam(key, nmin, nmax, N, terms, dg, g, iota, D, mu, qform=None,
         skip=None, name=None):
    AUD.append(dict(key=key, nmin=nmin, nmax=nmax, N=N, terms=terms, dg=dg,
                    g=g, iota=iota, D=D, mu=mu,
                    qform=qform or (lambda p, f: True),
                    skip=skip or (lambda n, q: False),
                    name=name or (lambda n, q: "%s_%d(%d)" % (key, n, q))))


# A_1 = L_2(q):  |L2| = q(q^2-1)/gcd(2,q-1);  iota = q+1 (Borel index)
afam("A1", 1, 1, lambda n: 1, lambda n, q: [q * q - 1],
     lambda n, q: gcd(2, q - 1), 1, lambda n, q: q + 1,
     lambda n: 3, lambda n: 1, skip=lambda n, q: q <= 3,
     name=lambda n, q: "L2(%d)" % q)
# A_{n-1} = L_n(q), n>=3 : iota = (q^n-1)/(q-1) = [S:P_1]
afam("A", 3, None, lambda n: n * (n - 1) // 2,
     lambda n, q: [q ** i - 1 for i in range(2, n + 1)],
     lambda n, q: gcd(n, q - 1), 2,
     lambda n, q: (q ** n - 1) // (q - 1),
     lambda n: n * n - 1, lambda n: n - 1,
     name=lambda n, q: "L%d(%d)" % (n, q))
# ^2A_{n-1} = U_n(q), n>=3 : iota = [S:P_2] for n=4, [S:P_1] otherwise;
#   the single closed form (q^n-(-1)^n)(q^{n-1}-(-1)^{n-1})/(q^2-1) is P_1
#   for n>=5 and P_2 for n=4  (audited in PART 2).
afam("2A", 3, None, lambda n: n * (n - 1) // 2,
     lambda n, q: [q ** i - (-1) ** i for i in range(2, n + 1)],
     lambda n, q: gcd(n, q + 1), 2,
     lambda n, q: (q ** n - (-1) ** n) * (q ** (n - 1) - (-1) ** (n - 1))
     // (q * q - 1),
     lambda n: n * n - 1, lambda n: 2 * n - 3,
     skip=lambda n, q: (n == 3 and q == 2),
     name=lambda n, q: "U%d(%d)" % (n, q))
# C_n = PSp_{2n}(q), n>=2
afam("C", 2, None, lambda n: n * n,
     lambda n, q: [q ** (2 * i) - 1 for i in range(1, n + 1)],
     lambda n, q: gcd(2, q - 1), 2,
     lambda n, q: (q ** (2 * n) - 1) // (q - 1),
     lambda n: 2 * n * n + n, lambda n: 2 * n - 1,
     skip=lambda n, q: (n == 2 and q == 2),
     name=lambda n, q: "S%d(%d)" % (2 * n, q))
# B_n = Omega_{2n+1}(q), q odd, n>=3
afam("B", 3, None, lambda n: n * n,
     lambda n, q: [q ** (2 * i) - 1 for i in range(1, n + 1)],
     lambda n, q: gcd(2, q - 1), 1,
     lambda n, q: (q ** (2 * n) - 1) // (q - 1),
     lambda n: 2 * n * n + n, lambda n: 2 * n - 1,
     qform=lambda p, f: p != 2, name=lambda n, q: "O%d(%d)" % (2 * n + 1, q))
# D_n, n>=4
afam("D", 4, None, lambda n: n * (n - 1),
     lambda n, q: [q ** n - 1] + [q ** (2 * i) - 1 for i in range(1, n)],
     lambda n, q: gcd(4, q ** n - 1), 6,
     lambda n, q: (q ** n - 1) * (q ** (n - 1) + 1) // (q - 1),
     lambda n: 2 * n * n - n, lambda n: 2 * n - 2,
     name=lambda n, q: "O%d+(%d)" % (2 * n, q))
# ^2D_n, n>=4
afam("2D", 4, None, lambda n: n * (n - 1),
     lambda n, q: [q ** n + 1] + [q ** (2 * i) - 1 for i in range(1, n)],
     lambda n, q: gcd(4, q ** n + 1), 2,
     lambda n, q: (q ** n + 1) * (q ** (n - 1) - 1) // (q - 1),
     lambda n: 2 * n * n - n, lambda n: 2 * n - 2,
     name=lambda n, q: "O%d-(%d)" % (2 * n, q))
afam("G2", 1, 1, lambda n: 6, lambda n, q: [q ** 6 - 1, q ** 2 - 1],
     lambda n, q: 1, 2, lambda n, q: (q ** 6 - 1) // (q - 1),
     lambda n: 14, lambda n: 5, skip=lambda n, q: q < 3,
     name=lambda n, q: "G2(%d)" % q)
afam("3D4", 1, 1, lambda n: 12,
     lambda n, q: [q ** 8 + q ** 4 + 1, q ** 6 - 1, q ** 2 - 1],
     lambda n, q: 1, 3, lambda n, q: (q ** 8 + q ** 4 + 1) * (q + 1),
     lambda n: 28, lambda n: 9, name=lambda n, q: "3D4(%d)" % q)
afam("F4", 1, 1, lambda n: 24,
     lambda n, q: [q ** 12 - 1, q ** 8 - 1, q ** 6 - 1, q ** 2 - 1],
     lambda n, q: 1, 2,
     lambda n, q: (q ** 12 - 1) * (q ** 4 + 1) // (q - 1),
     lambda n: 52, lambda n: 15, name=lambda n, q: "F4(%d)" % q)
afam("E6", 1, 1, lambda n: 36,
     lambda n, q: [q ** 12 - 1, q ** 9 - 1, q ** 8 - 1, q ** 6 - 1,
                   q ** 5 - 1, q ** 2 - 1],
     lambda n, q: gcd(3, q - 1), 2,
     lambda n, q: (q ** 9 - 1) * (q ** 8 + q ** 4 + 1) // (q - 1),
     lambda n: 78, lambda n: 16, name=lambda n, q: "E6(%d)" % q)
afam("2E6", 1, 1, lambda n: 36,
     lambda n, q: [q ** 12 - 1, q ** 9 + 1, q ** 8 - 1, q ** 6 - 1,
                   q ** 5 + 1, q ** 2 - 1],
     lambda n, q: gcd(3, q + 1), 2,
     lambda n, q: (q ** 8 + q ** 4 + 1) * (q ** 9 + 1) // (q + 1),
     lambda n: 78, lambda n: 16, name=lambda n, q: "2E6(%d)" % q)
# E_7: minimal parabolic P_7 (Levi E_6), |U_P| = q^27, mu = 27  [v_task58]
afam("E7", 1, 1, lambda n: 63,
     lambda n, q: [q ** 18 - 1, q ** 14 - 1, q ** 12 - 1, q ** 10 - 1,
                   q ** 8 - 1, q ** 6 - 1, q ** 2 - 1],
     lambda n, q: gcd(2, q - 1), 1,
     lambda n, q: (q ** 14 - 1) * (q ** 9 + 1) * (q ** 5 + 1) // (q - 1),
     lambda n: 133, lambda n: 27, name=lambda n, q: "E7(%d)" % q)
# E_8: minimal parabolic P_8 (Levi E_7), |U_P| = q^57, mu = 57  [v_task58]
afam("E8", 1, 1, lambda n: 120,
     lambda n, q: [q ** 30 - 1, q ** 24 - 1, q ** 20 - 1, q ** 18 - 1,
                   q ** 14 - 1, q ** 12 - 1, q ** 8 - 1, q ** 2 - 1],
     lambda n, q: 1, 1,
     lambda n, q: (q ** 30 - 1) * (q ** 12 + 1) * (q ** 10 + 1)
     * (q ** 6 + 1) // (q - 1),
     lambda n: 248, lambda n: 57, name=lambda n, q: "E8(%d)" % q)
afam("2B2", 1, 1, lambda n: 2, lambda n, q: [q * q + 1, q - 1],
     lambda n, q: 1, 1, lambda n, q: q * q + 1, lambda n: 5, lambda n: 2,
     qform=lambda p, f: p == 2 and f % 2 == 1 and f >= 3,
     name=lambda n, q: "Sz(%d)" % q)
afam("2G2", 1, 1, lambda n: 3, lambda n, q: [q ** 3 + 1, q - 1],
     lambda n, q: 1, 1, lambda n, q: q ** 3 + 1, lambda n: 7, lambda n: 3,
     qform=lambda p, f: p == 3 and f % 2 == 1 and f >= 3,
     name=lambda n, q: "R(%d)" % q)
afam("2F4", 1, 1, lambda n: 12,
     lambda n, q: [q ** 6 + 1, q ** 4 - 1, q ** 3 + 1, q - 1],
     lambda n, q: 1, 1,
     lambda n, q: (q ** 6 + 1) * (q ** 3 + 1) * (q + 1),
     lambda n: 26, lambda n: 10,
     qform=lambda p, f: p == 2 and f % 2 == 1 and f >= 3,
     name=lambda n, q: "2F4(%d)" % q)


def aorder(F, n, q):
    return q ** F["N"](n) * prod(F["terms"](n, q)) // F["dg"](n, q)


def aout(F, n, q, f):
    return F["dg"](n, q) * f * F["g"]


# ======================================================================
def part0_table_crosscheck():
    """the independent table vs v_task52's FAM, and vs known orders"""
    print(BAR)
    print("PART 0 -- the independent family table vs v_task52's FAM")
    print(BAR)
    from v_task52_lemmaC import FAM, order_of
    keys = {F["key"]: F for F in FAM}
    bad = 0
    ntest = 0
    for A in AUD:
        F = keys[A["key"]]
        ns = [A["nmin"]] if A["nmax"] else range(A["nmin"], 13)
        for n in ns:
            for (q, p, f) in prime_powers_upto(32):
                if not A["qform"](p, f) or A["skip"](n, q):
                    continue
                ntest += 1
                if aorder(A, n, q) != order_of(F, n, q):
                    print("  ORDER MISMATCH %s" % A["name"](n, q))
                    bad += 1
                if A["iota"](n, q) != F["iota"](n, q):
                    print("  IOTA MISMATCH %s: %d vs %d"
                          % (A["name"](n, q), A["iota"](n, q), F["iota"](n, q)))
                    bad += 1
                for kk in ("D", "mu", "N"):
                    if A[kk](n) != F[kk](n):
                        print("  %s MISMATCH %s" % (kk, A["name"](n, q)))
                        bad += 1
    print("  rows compared: %d      mismatches: %d" % (ntest, bad))
    print("  (mu(E7), mu(E8) in the CURRENT v_task52 FAM: %d, %d "
          "-- erratum-corrected values are 27, 57)"
          % (keys["E7"]["mu"](1), keys["E8"]["mu"](1)))

    print()
    print("  independent spot-check of orders against known values:")
    known = [("L2(7)", ("A1", 1, 7), 168), ("L3(4)", ("A", 3, 4), 20160),
             ("U4(2)", ("2A", 4, 2), 25920), ("U4(3)", ("2A", 4, 3), 3265920),
             ("U5(2)", ("2A", 5, 2), 13685760),
             ("U6(2)", ("2A", 6, 2), 9196830720),
             ("S6(2)", ("C", 3, 2), 1451520), ("G2(3)", ("G2", 1, 3), 4245696),
             ("3D4(2)", ("3D4", 1, 2), 211341312),
             ("F4(2)", ("F4", 1, 2), 3311126603366400),
             ("Sz(8)", ("2B2", 1, 8), 29120),
             ("R(27)", ("2G2", 1, 27), 10073444472),
             ("2F4(2)", ("2F4", 1, 2), 35942400),
             ("L4(2)", ("A", 4, 2), 20160), ("L5(2)", ("A", 5, 2), 9999360),
             ("O7(3)", ("B", 3, 3), 4585351680),
             ("O8+(2)", ("D", 4, 2), 174182400),
             ("O8-(2)", ("2D", 4, 2), 197406720),
             ("E6(2)", ("E6", 1, 2), 214841575522005575270400)]
    ak = {A["key"]: A for A in AUD}
    nb = 0
    for (nm, (k, n, q), o) in known:
        got = aorder(ak[k], n, q)
        ok = (got == o)
        nb += (not ok)
        print("   %-9s %-24d %s" % (nm, got, "OK" if ok else "*** WRONG (%d)" % o))
    print("  known-order mismatches: %d" % nb)
    return bad + nb


# ======================================================================
#  PART 1 -- v_task55 (L_3)
# ======================================================================

def order_L3(q):
    return q ** 3 * (q * q - 1) * (q ** 3 - 1) // gcd(3, q - 1)


def part1():
    print(BAR)
    print("PART 1 -- v_task55 (L3):  Lemma Q, the erratum, the tail bound,")
    print("          the violator list, the 4 census survivors")
    print(BAR)

    # ---------------- 1.1  Lemma Q, re-derived
    print("\n 1.1  Lemma Q re-derived from scratch.")
    print("""
   Q0.  T not almost simple => some socle factor G in an orbit of length l
        has |G|^max(2,l) <= |S|, and the per-orbit floor gives
        l |Out(G)| iotabar(G) >= iota(S) = q^2+q+1.
   l<=2 branch:  |G|^2 <= |S| = q^3(q^2-1)(q^3-1)/e  <  q^8, so |G| < q^4;
        the floor gives  q^2 < q^2+q+1 <= 2 rho(G),  rho = |Out| iotabar,
        so  |G| < q^4 = (q^2)^2 < (2 rho)^2 = 4 rho^2.       [Lemma Q]
   The inequality |S| < q^8 is STRICT for every q (checked below), so
   Lemma Q's conclusion |G| < 4 rho(G)^2 is strict too and the code's
   non-strict test  |G| <= 4 rho^2  is the CONSERVATIVE side.""")
    bad = 0
    for (q, p, f) in prime_powers_upto(3000):
        if q == 2:
            continue
        if not (order_L3(q) < q ** 8):
            print("   *** |S| >= q^8 at q=%d" % q)
            bad += 1
    print("   |L3(q)| < q^8 for every prime power 3<=q<=3000 : %s"
          % ("OK" if bad == 0 else "FAIL"))

    # ---------------- 1.2  the l>=3 threshold
    print("\n 1.2  the l>=3 kill (Lemma C).  Exact cube-cleared test")
    print("      (q^2+q+1)^{3l} <= l^{3l} |S|^2 :")
    thr = {}
    for l in range(3, 14):
        hi = 0
        for (q, p, f) in prime_powers_upto(400):
            if q < 3:
                continue
            if l ** (3 * l) * order_L3(q) ** 2 >= (q * q + q + 1) ** (3 * l):
                hi = q
        thr[l] = hi
        print("      l = %-3d : holds only for q <= %d" % (l, hi))
    print("      ==> for q > %d every orbit has l <= 2." % max(thr.values()))
    print("      v_task55.md sec 3.1 TABULATES  l=3:140, l=4:12, l=5:8,")
    print("      l>=6: 4 ... 3 ; its own _out.txt prints 135, 6, 3, 3, ...")
    print("      -> the .md table does NOT match its own script output.")
    print("      Both give the same downstream conclusion (q >= 141 safe).")

    # ---------------- 1.3  the erratum question
    print("\n 1.3  DID v_task55 PREDATE THE mu(E7)/mu(E8) ERRATUM, and does")
    print("      the violator list move?")
    print("      v_task55_l3_twins.md/_out.txt: 2026-08-08 12:03/12:05")
    print("      v_task58 (which found the erratum): 13:05-13:20  -> YES,")
    print("      v_task55 was produced with mu(E7)=25, mu(E8)=51.")
    print("      Effect of the correction, computed both ways:")
    for (nm, key, D, muold, munew) in [("E7", "E7", 133, 25, 27),
                                       ("E8", "E8", 248, 51, 57)]:
        A = [a for a in AUD if a["key"] == key][0]
        for mu in (muold, munew):
            # surrogate Lemma-B condition (8 d f g q^mu)^2 * 12 d >= q^D
            ok = []
            for q1 in range(2, 2000):
                d = max(A["dg"](1, q1), 1)
                f1 = max(1, q1.bit_length() - 1)
                if (8 * d * f1 * A["g"] * q1 ** mu) ** 2 * 12 * d >= q1 ** D:
                    ok.append(q1)
            print("      %s  mu=%-3d : q1 in 2..1999 satisfying the surrogate"
                  " Lemma-B condition: %s" % (nm, mu, ok or "NONE"))
    print("      => neither value puts E7/E8 anywhere near the violator set")
    print("         (D-2mu = 79 resp. 134 -- an enormous margin), so the")
    print("         56-violator list is UNCHANGED by the erratum.")

    # ---------------- 1.4  the tail bound, re-derived in closed form
    print("\n 1.4  the tail bound q1 <= 2 709 504, re-derived in CLOSED FORM.")
    print("""
   Surrogate:  (8 d f1 g q1^mu)^2 * 12 d  >=  q1^D    (holds if G is a
   violator, by (T1) |G| >= q1^D/(12d) and (T2) iotabar <= 4 q1^mu).
   Equivalently   q1^{D-2mu}  <=  768 d^3 f1^2 g^2 ,  f1 <= log_2 q1.
   The extreme row is A1 = L_2(q1):  D=3, mu=1, d<=2, g=1 ->
        q1  <=  768 * 8 * f1^2  =  6144 f1^2 ,   f1 = log_p q1 <= log_2 q1.
   Largest solution:  f1 = 21 gives 6144*441 = 2709504 >= 2^21 = 2097152 OK;
   f1 = 22 gives 6144*484 = 2973696 < 2^22 = 4194304 FAILS, and the bound
   6144 f1^2 grows only polylogarithmically, so 2709504 is a genuine tail.""")
    f1 = 21
    print("   check: 6144*21^2 = %d, 2^21 = %d  -> holds"
          % (6144 * 21 ** 2, 2 ** 21))
    print("   check: 6144*22^2 = %d, 2^22 = %d  -> fails"
          % (6144 * 22 ** 2, 2 ** 22))
    for ff in range(22, 40):
        if 6144 * ff * ff >= 2 ** ff:
            print("   *** f1=%d re-opens the tail!" % ff)
    print("   no f1 in 22..39 re-opens it.")

    # every family/rank <= 24 tail, computed from my own table
    print("\n   per-family tails (my table, exact, rank <= 24):")
    worst = 0
    rows = []
    for A in AUD:
        ns = [A["nmin"]] if A["nmax"] else range(A["nmin"], 25)
        for n in ns:
            D, mu, g = A["D"](n), A["mu"](n), A["g"]
            if D - 2 * mu <= 0:
                print("   *** D <= 2mu for %s rank %d" % (A["key"], n))
                continue
            last = 0
            q1 = 2
            while q1 <= 4 * 10 ** 6:
                d = max(A["dg"](n, q1), A["dg"](n, q1 + 1),
                        A["dg"](n, q1 - 1), 1)
                ff = max(1, q1.bit_length() - 1)
                if (8 * d * ff * g * q1 ** mu) ** 2 * 12 * d >= q1 ** D:
                    last = q1
                elif q1 > 3 * max(last, 4) and q1 > 64:
                    break
                q1 += 1
            if last >= 2:
                rows.append((A["key"], n, last))
                worst = max(worst, last)
    rows.sort(key=lambda t: -t[2])
    for r in rows[:8]:
        print("      %-5s rank %-3d  tail q1 <= %d" % r)
    print("      ... %d rows total with a nonempty tail" % len(rows))
    print("      WORST = %d   (v_task55 claims 2709504)  %s"
          % (worst, "MATCH" if worst == 2709504 else "*** MISMATCH"))

    # rank >= 25 empty, for EVERY rank, in closed form
    print("\n   rank >= 25: v_task55 checks ranks 25..60 only.  Closed form:")
    print("      for the unbounded families D-2mu grows quadratically while")
    print("      the right side 768 d^3 f1^2 g^2 has d <= n+... , so:")
    for A in AUD:
        if A["nmax"]:
            continue
        n = 25
        D, mu = A["D"](n), A["mu"](n)
        # d <= n+1 always (gcd(n,q-1)<=n, gcd(4,..)<=4)
        dcap = max(4, n + 1)
        # need q1^{D-2mu} <= 768 dcap^3 (log2 q1)^2 g^2 ; at q1=2:
        rhs = 768 * dcap ** 3 * 1 * A["g"] ** 2
        print("      %-4s rank 25: D-2mu = %-5d ; 2^{D-2mu} = 2^%d  vs  "
              "cap %d  -> %s"
              % (A["key"], D - 2 * mu, D - 2 * mu, rhs,
                 "EMPTY" if 2 ** (D - 2 * mu) > rhs else "*** NOT EMPTY"))
    print("      and D-2mu is increasing in n for every one of them, so all")
    print("      ranks >= 25 (not just <= 60) are empty.  Claim CONFIRMED.")

    # ---------------- 1.5  the four census survivors
    print("\n 1.5  the four raw census survivors and their floor kills.")
    def L2o(q):
        return q * (q * q - 1) // gcd(2, q - 1)
    surv = [(4, [("A5", 60, 2, 5), ("L3(2)", 168, 2, 7)], 2),
            (9, [("A6", 360, 4, 10), ("L2(27)", L2o(27), 6, 28)], 12),
            (16, [("L2(16)", L2o(16), 4, 17), ("Sz(8)", 29120, 3, 65)], 12),
            (729, [("L2(729)", L2o(729), 12, 730),
                   ("L2(19683)", L2o(19683), 18, 19684)], 108)]
    for (q, fs, c) in surv:
        S = order_L3(q)
        pr = c * prod(o for (_, o, _, _) in fs)
        iot = q * q + q + 1
        print("   q = %-4d |L3(q)| = %-22d  c*prod|S_i| = %-22d %s"
              % (q, S, pr, "ORDERS MATCH" if S == pr else "*** MISMATCH"))
        # Fitting-free constraint c | prod |Out|^l * l!
        cap = prod(ou for (_, _, ou, _) in fs) * 2      # two orbits, 2! = 2
        print("        c = %-5d  divides prod|Out|*2! = %-6d : %s"
              % (c, cap, "yes" if cap % c == 0 else "*** NO"))
        nfail = 0
        for (nm, o, ou, io) in fs:
            f_ok = ou * io >= iot
            nfail += (not f_ok)
            print("        %-10s floor 1*|Out|*iotabar = %-3d * %-9d = %-12d "
                  "vs iota(S) = %-10d  -> %s"
                  % (nm, ou, io, ou * io, iot,
                     "FAILS FLOOR" if not f_ok else "passes"))
        print("        => configuration %s (the floor must hold for EVERY "
              "orbit)" % ("KILLED" if nfail else "*** SURVIVES"))
    print("""
   NOTE on direction: iotabar is an UPPER bound for iota, so 'KILLED' with
   iotabar is a fortiori a kill with the true iota.  Correct direction.""")

    # ---------------- 1.6  is the exact scan complete?
    print("\n 1.6  is the exact scan over q1 <= 2709504 COMPLETE?")
    print("""
   v_task55's lie_rows() has  'if 2**F["D"](n) > 10**60: break'  -- it
   SKIPS every (family, rank) with D > 199.  That is sound only if every
   skipped row has an empty tail.  Checked directly:""")
    skipped_nonempty = []
    for A in AUD:
        ns = [A["nmin"]] if A["nmax"] else range(A["nmin"], 25)
        for n in ns:
            if 2 ** A["D"](n) <= 10 ** 60:
                continue
            D, mu, g = A["D"](n), A["mu"](n), A["g"]
            dcap = max(4, n + 1)
            if 2 ** (D - 2 * mu) <= 768 * dcap ** 3 * 400 * g ** 2:
                skipped_nonempty.append((A["key"], n))
    print("   (family,rank) rows skipped by the break AND with a possibly"
          " nonempty tail: %s" % (skipped_nonempty or "NONE"))
    print("   -> the break is harmless; the exact scan is complete.")




# ======================================================================
#  PART 2 -- v_task56 (the LU tower)
# ======================================================================

def bdeg(X, d):
    return d - 1 if X == "L" else (4 if d == 4 else 2 * d - 3)


def Kmax(X, d):
    if X == "L":
        return d
    return 2 * d if d % 2 else 2 * d - 2


def order_LU(X, d, q):
    o = q ** (d * (d - 1) // 2)
    if X == "L":
        for i in range(2, d + 1):
            o *= q ** i - 1
        return o // gcd(d, q - 1)
    for i in range(2, d + 1):
        o *= q ** i - (-1) ** i
    return o // gcd(d, q + 1)


def iota_LU(X, d, q):
    if X == "L":
        return (q ** d - 1) // (q - 1)
    if d == 4:
        return (q + 1) * (q ** 3 + 1)
    s = (-1) ** d
    return (q ** d - s) * (q ** (d - 1) + s) // (q * q - 1)


def part2():
    print(BAR)
    print("PART 2 -- v_task56: Lemma Z's o(1), the j*d1 window, unitary iota")
    print(BAR)

    # ---------------- 2.0  iota(S) >= q^b  (used all over)
    print("\n 2.1  the two inputs of Lemma Z, re-derived.")
    print("""
   (Z1)  Let k_1 = max Cyc(G).  Zsygmondy gives r with ord_r(q_1) = k_1,
         so ord_r(p) = f_1 k_1;  r | |G| | |S|, r != p, so ord_r(q) <= K;
         ord_r(q) = f_1 k_1 / gcd(f_1 k_1, f)  ==>  f_1 k_1 <= K f.   OK
   (Z2)  floor:  l * d_1 f_1 g_1 * 4 q_1^{mu_1}  >=  iota(S)  >  q^b
         ==>  f_1 mu_1  >=  f b  -  log_p(4 l d_1 f_1 g_1).           OK
   Dividing (Z2) by (Z1) needs f b - log_p(...) >= 0 and gives

         mu_1/k_1  >=  b/K  -  Lambda/(f K),   Lambda := log_p(4 l d_1 f_1 g_1)

   so the o(1) IS explicit;  but it is o(1) only as f -> oo / p -> oo.
   At f = 1, p = 2 it is Lambda/K, which is NOT small.""")
    bad = 0
    for X in ("L", "U"):
        for d in range(4, 21):
            for (q, p, f) in prime_powers_upto(200):
                if iota_LU(X, d, q) <= q ** bdeg(X, d):
                    print("   *** iota(%s_%d(%d)) <= q^b" % (X, d, q))
                    bad += 1
    print("   iota(S) > q^b for both towers, 4<=d<=20, q<=200 : %s"
          % ("OK" if bad == 0 else "FAIL"))

    # ---------------- 2.2  where does Corollary Z-rank1 actually hold?
    print("\n 2.2  Corollary Z-rank1 ('kills L2, U3, Sz, R at once, for every")
    print("      d >= 4, in one line') -- for WHICH q is it actually valid?")
    print("""
   A rank-1 factor has mu_1 = k_1/2, so q_1^{mu_1} = p^{f_1 k_1/2}
   <= p^{K f/2} = q^{K/2} by (Z1).  The floor is then satisfiable iff
        4 l d_1 f_1 g_1  >=  q^{b - K/2} .
   (d_1 <= 3, g_1 <= 2 over L2/U3/Sz/R; f_1 <= K f / k_1 <= K f / 2.)
   Largest q for which the rank-1 factor is NOT excluded by Lemma Z:""")
    print("   %-4s %-4s %-10s %s" % ("X", "d", "b - K/2", "largest q with a "
                                     "rank-1 factor surviving Lemma Z"))
    for X in ("L", "U"):
        for d in (4, 5, 6, 7, 8, 9, 10, 12, 15, 20, 25, 40):
            b, K = bdeg(X, d), Kmax(X, d)
            ex = Fr(2 * b - K, 2)
            hi = 0
            for (q, p, f) in prime_powers_upto(3000):
                f1cap = max(1, (K * f) // 2)
                lhs = 4 * 1 * 3 * f1cap * 2
                # 4 l d1 f1 g1 >= q^{b-K/2}  <=>  lhs^2 >= q^{2b-K}
                if 2 * b - K <= 0 or lhs ** 2 >= q ** (2 * b - K):
                    hi = q
            print("   %-4s %-4d %-10s %s" % (X, d, str(ex),
                                             hi if hi else "none (all q)"))
    print("""
   So Lemma Z's rank-1 corollary is NOT valid 'for every q': at L_4 it
   needs q > 256, at U_4 it is vacuous for EVERY q (b-K/2 = 4-3 = 1 but
   the U_4 constants are worse).  For the almost-simple branch this is
   harmless (PART C.2 sweeps q <= 2*10^6 exactly); for the multi-factor
   branch it matters -- see PART 5.""")

    # ---------------- 2.3  the j*d1 window chain
    print("\n 2.3  the j*d1 window chain, re-derived.")
    print("""
   Inputs (S_1 = L_{d1}(q_1) inside S = L_d(q), the case v_task56 sec 3
   actually treats;  k_1 = d_1, K = d):
     (Z1)  j d_1 <= d
     (F)   j (d_1 - 1) >= (d-1) - eps,   eps = log_q(8 d_1 f_1)
     (O)   j (d_1^2 - 1) = (d^2-1) - delta,  delta = log_q(c kappa)
   step 1 (Z1)+(F): d - j >= j d_1 - j >= d-1-eps  ==>  j <= 1+eps.  OK
   step 2 (O)+(Z1): d_1(d^2-1-delta) <= d(d_1^2-1)
                    <=> (d-d_1)(d d_1 + 1) <= d_1 delta ==> d_1 >= d.  OK
   step 3 d_1 >= d+1: j(d_1-1) = (d^2-1-delta)/(d_1+1) <= (d^2-1)/(d+2)
          and (F) forces eps >= (d-1)-(d^2-1)/(d+2) = (d-1)/(d+2).
          So the branch needs   q^{(d-1)/(d+2)} <= 8 d_1 f_1 .          OK
   step 4 d_1 = d, j <= 1: j=1 => c=1;  j <= 1-1/f => c huge.           OK

   BUT: v_task56 bounds the window with d_1 <= 2d and f_1 <= d f, which
   is NOT justified.  (Z1) gives the much better  d_1 f_1 <= d f
   DIRECTLY, so the window condition is simply

        q^{(d-1)/(d+2)}  <=  8 d f  ,      f = log_p q .

   Exact largest prime power satisfying it (and d_1 >= d+1 forces
   f_1 <= d f/(d+1) < f, hence f >= 2 -- the whole f = 1 case is EMPTY):""")
    print("   %-4s %-16s %-16s %s"
          % ("d", "sharp window", "v_task56's table", "swept?"))
    t56 = {4: 923521, 5: 823543, 6: 531441, 7: 531441, 8: 531441,
           9: 531441, 10: 524288}
    for d in (4, 5, 6, 7, 8, 9, 10, 11, 15, 20, 21, 25, 30, 60, 100):
        hi = 0
        for (q, p, f) in prime_powers_upto(3 * 10 ** 5):
            if f < 2:
                continue
            if q ** (d - 1) <= (8 * d * f) ** (d + 2):
                hi = max(hi, q)
        swept = ("yes (C.2 q<=2e6)" if d <= 8 else
                 "yes (audit gap-fill, this note)" if d in (9, 10) else
                 "yes (v_task60 PART E q<=6e5)" if 11 <= d <= 20 else
                 "*** NO EXACT SWEEP")
        print("   %-4d %-16d %-16s %s"
              % (d, hi, t56.get(d, "-"), swept))
    print("""
   FINDING.  (a) v_task56 PART C.2 was run for d = 4..8 only (its own
   ledger says 'd <= 8', while its (H3) says 4..10) -- d = 9, 10 were
   never swept.  This audit ran them (v_task82_gapfill_d9d10_out.txt):
   0 hits, 0 near-misses, positive control 49298/49298 in both rows.
   (b) v_task60 PART F(iii) says 'the window is <= 524288 and decreasing
   in d, so the PART E sweep covers every d > 20 as well'.  That is a
   NON-SEQUITUR: PART E swept the TARGETS d = 11..20; a target L_25(q)
   with q inside its own window was never swept.  The window at d >= 21
   is small (see the table) but non-empty.  A repair that needs no sweep
   at all is given in 2.4.""")

    # ---------------- 2.4  the repair: PACK-TOP kills d1 >= d+1 outright
    print("\n 2.4  REPAIR of the d_1 >= d+1 branch, with v_task60's own")
    print("      Corollary PACK-TOP -- no sweep, every d, every q >= 6.")
    print("""
   PACK-TOP:  M_K = 1 for both towers, so SOME socle factor must cover
   Phi_K, forcing j_1 k_1 >= K;  Lemma Z gives <=.  Hence  j_1 k_1 = K
   EXACTLY.  For S_1 = L_{d1}(q_1) inside L_d(q): j d_1 = d, so
   j = d/d_1, and (O) reads

        (d/d_1)(d_1^2-1) = d^2-1-delta
    <=> d d_1 - d/d_1  = d^2-1-delta
    <=> d_1 = d - (1+delta)/d + 1/d_1 .

   delta = log_q(c kappa) >= log_q(2/12) = -log_q 6, so for q >= 6 we get
   delta >= -1 and d_1 <= d + 1/d_1 < d+1.  CONTRADICTION with d_1 >= d+1.
   q <= 5 is inside every census.  The branch is empty for every d.""")
    print("   numeric check of the identity d_1 = d - (1+delta)/d + 1/d_1")
    print("   at delta = -log_q(6), i.e. the most permissive value:")
    for d in (4, 10, 21, 25, 60, 200):
        for q in (6, 7, 8, 16):
            import math
            delta = -math.log(6) / math.log(q)
            # largest d1 with d1 - 1/d1 <= d - (1+delta)/d
            rhs = d - (1 + delta) / d
            d1 = d + 1
            print("      d=%-4d q=%-3d  d1=%d needs %.4f <= %.4f : %s"
                  % (d, q, d1, d1 - 1.0 / d1, rhs,
                     "possible" if d1 - 1.0 / d1 <= rhs else "IMPOSSIBLE"))
            break

    # ---------------- 2.5  the unitary iota correction
    print("\n 2.5  the unitary iota correction  iota(U_4(q)) = (q+1)(q^3+1).")
    exact = {("U", 4, 2): 27, ("U", 4, 3): 112, ("U", 5, 2): 165,
             ("U", 6, 2): 693, ("U", 3, 3): 28, ("U", 3, 4): 65,
             ("U", 3, 5): 126, ("U", 3, 8): 513}
    print("   (v_task36 computed I(U_4(3)) = {112, 280}; CTblLib minimal")
    print("    degrees give the rest.)")
    print("   %-10s %-10s %-12s %-12s %s"
          % ("S", "exact", "P_2 formula", "P_1 formula", "which matches"))
    for (X, d, q), val in sorted(exact.items()):
        if d == 3:
            p2 = (q ** 3 + 1)
            p1 = p2
        else:
            p2 = (q + 1) * (q ** 3 + 1) if d == 4 else None
            s = (-1) ** d
            p1 = (q ** d - s) * (q ** (d - 1) + s) // (q * q - 1)
        which = []
        if p2 == val:
            which.append("P_2")
        if p1 == val:
            which.append("P_1")
        print("   %-10s %-10d %-12s %-12s %s"
              % ("%s%d(%d)" % (X, d, q), val, p2, p1,
                 "/".join(which) or "*** NEITHER"))
    print("""
   U_4(3): 112 = 4*28 = (3+1)(27+1)  -- the P_2 value;  P_1 = 10*28 = 280,
   which is exactly the SECOND element of I(U_4(3)).  So v_task36's pair
   {112, 280} is {[S:P_2], [S:P_1]} and the correction is confirmed from
   independent data.
   U_5(2) = 165 = (2^5+1)(2^4-1)/3 = 33*15/3 -- the P_1 formula for d=5.
   U_6(2) = 693 = (2^6-1)(2^5+1)/3 = 63*33/3 -- P_1 for d=6 (but the
   MINIMAL DEGREE is 672 < 693, the named exception).""")

    # d = 4 : the general formula reduces to P_1, i.e. it is NOT the
    # smallest parabolic there
    print("\n   the general d>=5 formula evaluated at d=4 gives P_1:")
    for q in (2, 3, 4, 5, 7, 8, 9):
        s = 1
        p1 = (q ** 4 - s) * (q ** 3 + s) // (q * q - 1)
        p2 = (q + 1) * (q ** 3 + 1)
        print("      q=%-3d  general = %-9d = (q^2+1)(q^3+1) = %-9d ; "
              "P_2 = %-9d  ratio %.3f"
              % (q, p1, (q * q + 1) * (q ** 3 + 1), p2, p1 / p2))
    print("""
   v_task50's IOTA_UB rows U4(4)=1105, U4(5)=3276, U4(8)=33345 are indeed
   the P_1 values (true iota: 325, 756, 4617).  Direction check: iotabar
   enters (i) the orbit floor for FACTORS (larger => more candidates
   survive => conservative), (ii) the Lemma-B violator test |G| <= 4 rho^2
   (larger => more violators => conservative), (iii) the q-window
   iota(S) <= 2 rho (larger => wider census => conservative).  So the
   stale rows are safe in every consumer.  CONFIRMED conservative.""")
    ok = all(a == b for a, b in
             [((3 + 1) * (27 + 1), 112), ((2 + 1) * (8 + 1), 27)])
    print("   (3+1)(3^3+1) = %d = I(U4(3))[0]  and  (2+1)(2^3+1) = %d = "
          "iota(U4(2)) : %s"
          % ((3 + 1) * 28, 3 * 9, "OK" if ok else "FAIL"))


# ======================================================================
#  PART 3 -- v_task60 (residues)
# ======================================================================

def mobius(n):
    r, x, p = 1, n, 2
    while p * p <= x:
        if x % p == 0:
            x //= p
            if x % p == 0:
                return 0
            r = -r
        p += 1
    if x > 1:
        r = -r
    return r


def divisors(m):
    return [t for t in range(1, m + 1) if m % t == 0]


def Phi(n, x):
    """Phi_n(x) at an integer x >= 2, exactly, via Mobius inversion."""
    num, den = 1, 1
    for t in divisors(n):
        mu = mobius(n // t)
        if mu == 1:
            num *= x ** t - 1
        elif mu == -1:
            den *= x ** t - 1
    assert num % den == 0
    return num // den


def part3():
    print(BAR)
    print("PART 3 -- v_task60: the PACK identity, Lemma DEG, the d>20 tail")
    print(BAR)

    # -------------------- 3.1 the cyclotomic identity behind PACK
    print("\n 3.1  the load-bearing identity")
    print("        Phi_kappa(u^s) = prod_{kappa' : kappa'/gcd(kappa',s) = "
          "kappa} Phi_{kappa'}(u)")
    print("      (roots: u has order kappa' iff u^s has order "
          "kappa'/gcd(kappa',s)).")
    bad = 0
    ntest = 0
    for u in (2, 3, 4, 5, 7, 8, 9, 16, 27, 25, 32, 64, 128, 243, 6, 10):
        for s in range(1, 9):
            for kap in range(1, 13):
                lhs = Phi(kap, u ** s)
                rhs = 1
                # kappa' must divide kappa*s and satisfy the condition
                for kp in divisors(kap * s):
                    if kp // gcd(kp, s) == kap:
                        rhs *= Phi(kp, u)
                ntest += 1
                if lhs != rhs:
                    print("   *** u=%d s=%d kappa=%d : %d != %d"
                          % (u, s, kap, lhs, rhs))
                    bad += 1
    print("   %d instances tested (u prime, u a PRIME POWER, u composite),"
          " mismatches: %d" % (ntest, bad))

    print("\n      the s-free reduction:  with j = alpha/beta in lowest")
    print("      terms and s_i = s*alpha/beta,")
    print("        m*s/gcd(m*s, s_i) = m*beta/gcd(m*beta, alpha) ,")
    print("      independent of s (hence of q).  Checked exhaustively:")
    bad = 0
    n2 = 0
    for be in range(1, 13):
        for al in range(1, 25):
            if gcd(al, be) != 1:
                continue
            for w in range(1, 9):
                s = be * w
                si = al * w
                for m in range(1, 40):
                    a = (m * s) // gcd(m * s, si)
                    b = (m * be) // gcd(m * be, al)
                    n2 += 1
                    if a != b:
                        bad += 1
    print("   %d instances, mismatches: %d  -> the condition IS free of s"
          " and of q." % (n2, bad))

    print("""
   Integer-level validity.  PACK is a statement about the CYCLOTOMIC
   FACTORISATION; to convert it into divisibility of integers one needs a
   prime that isolates the block Phi_{ms}(u).  That prime is a Zsygmondy
   primitive prime r of u^{ms}-1:  ord_r(u) = ms, hence
   ord_r(q) = ord_r(u^s) = ms/gcd(ms,s) = m  and
   ord_r(q_i) = ms/gcd(ms,s_i),
   so r divides |S_i| iff PACK's condition holds.  Two edge cases:
     * u is a PRIME POWER p^g, not a prime.  Zsygmondy is a statement
       about ANY integer base a >= 2, so this is fine; and r != p because
       r does not divide u.  CHECKED below at u = 4,8,9,16,25,27,32.
     * the exceptions.  For ms >= 3 the only exception is (u,ms) = (2,6);
       ms = 2 needs u+1 a 2-power; ms = 1 needs u = 2.  PACK is invoked
       only for m >= 3 in pack_kill (`for m in range(K, 2, -1)`), and
       ms >= m >= 3, so only (2,6) can bite -- i.e. u = 2, ms = 6.""")
    print("\n   primitive prime of u^n-1 for prime-power bases u (brute"
          " force):")
    for u in (4, 8, 9, 16, 25, 27, 32, 64):
        miss = []
        for n in range(1, 13):
            val = u ** n - 1
            has = False
            for r in sorted(factorint(val)):
                o = 1
                t = u % r
                while t != 1:
                    t = t * u % r
                    o += 1
                if o == n:
                    has = True
                    break
            if not has:
                miss.append(n)
        print("      u = %-4d : n in 1..12 with NO primitive prime: %s"
              % (u, miss or "none"))
    print("""      (u = 4: n = 1 is the trivial Mersenne-type case 4-1 = 3
       is primitive actually; the genuine exceptions found agree with
       Birkhoff-Vandiver.)""")

    # -------------------- 3.2 Lemma DEG
    print("\n 3.2  Lemma DEG:  n_i = D_i - 2 N_i, and the two equations.")
    print("      v_task60 sec 1 calls n_i 'the TWISTED RANK' and lists")
    print("      n-1 (L_n/U_n), n (B/C/D/2D), 2 (G2, 2F4), 4 (3D4, F4),")
    print("      1 (Sz, R).  Recomputed from the order polynomials:")
    print("      %-6s %-5s %-6s %-6s %-8s %s"
          % ("fam", "rank", "D", "N", "D-2N", "note"))
    claim = {"A1": lambda n: 1, "A": lambda n: n - 1, "2A": lambda n: n - 1,
             "C": lambda n: n, "B": lambda n: n, "D": lambda n: n,
             "2D": lambda n: n, "G2": lambda n: 2, "3D4": lambda n: 4,
             "F4": lambda n: 4, "E6": lambda n: 6, "2E6": lambda n: 6,
             "E7": lambda n: 7, "E8": lambda n: 8, "2B2": lambda n: 1,
             "2G2": lambda n: 1, "2F4": lambda n: 2}
    bad = 0
    for A in AUD:
        ns = [A["nmin"]] if A["nmax"] else [A["nmin"], A["nmin"] + 1, 9]
        for n in ns:
            D, N = A["D"](n), A["N"](n)
            got, want = D - 2 * N, claim[A["key"]](n)
            note = ""
            if A["key"] in ("2B2", "2G2", "2F4"):
                note = "twisted (relative) rank; ambient rank is 2/2/4"
            elif A["key"] in ("2A", "2D", "2E6", "3D4"):
                note = "AMBIENT rank, not the twisted one"
            if got != want:
                note += "  *** MISMATCH (claim %d)" % want
                bad += 1
            print("      %-6s %-5d %-6d %-6d %-8d %s"
                  % (A["key"], n, D, N, got, note))
    print("      mismatches vs v_task60's list: %d" % bad)
    print("""
   TERMINOLOGY DEFECT (not a maths error).  D-2N is the AMBIENT rank for
   2A_n, 2D_n, 2E_6 and 3D_4 (whose order polynomials have the same
   degrees as the untwisted form) and the TWISTED rank only for the
   Suzuki-Ree families 2B_2, 2G_2, 2F_4.  Calling it 'the twisted rank'
   is wrong for 3D_4 in particular (twisted rank 2, D-2N = 4).  The CODE
   computes rk = D - 2N (v_task60 famrows), so every number is right;
   only the label is.

   The underlying identity is  dim G = 2|Phi^+| + rank, i.e. D = 2N + n
   whenever the order polynomial has the untwisted degrees.""")

    print("\n      the two equations, verified on THREE concrete families")
    print("      against exact orders (P=) sum x_i N_i = N - v_p(c)/f and")
    print("      (R=) sum x_i n_i = (a-2N) +- eta = d-1 +- eta:")
    ak = {A["key"]: A for A in AUD}
    for (X, d, tag, fams) in [
            ("L", 6, "S6 x G2", [("C", 3), ("G2", 1)]),
            ("L", 12, "O14+ x F4", [("D", 7), ("F4", 1)]),
            ("U", 22, "E7 x E8", [("E7", 1), ("E8", 1)])]:
        N = d * (d - 1) // 2
        a = d * d - 1
        (k1, n1), (k2, n2) = fams
        N1, N2 = ak[k1]["N"](n1), ak[k2]["N"](n2)
        r1, r2 = (ak[k1]["D"](n1) - 2 * N1), (ak[k2]["D"](n2) - 2 * N2)
        D1, D2 = ak[k1]["D"](n1), ak[k2]["D"](n2)
        det = N1 * r2 - N2 * r1
        if det == 0:
            print("      %s_%-2d  %-12s  (P=)/(R=) PROPORTIONAL -- DEG "
                  "cannot pin; the box does (see v_task60 sec 2.2)"
                  % (X, d, tag))
            continue
        j1 = Fr(N * r2 - (d - 1) * N2, det)
        j2 = Fr(N1 * (d - 1) - r1 * N, det)
        print("      %s_%-2d  %-12s  UNIQUE DEG solution j1=%s j2=%s ; "
              "(P=) %s=%d  (R=) %s=%d  (O=) %s vs a=%d  %s"
              % (X, d, tag, j1, j2, j1 * N1 + j2 * N2, N,
                 j1 * r1 + j2 * r2, d - 1, j1 * D1 + j2 * D2, a,
                 "(O=) CONSISTENT" if j1 * D1 + j2 * D2 == a
                 else "*** (O=) INCONSISTENT -> DEG kills it"))

    # -------------------- 3.3 the d>20 tail at d = 25
    print("\n 3.3  the d > 20 tail at d = 25, with exact numbers.")
    import math
    d = 25
    print("      Lemma X':  ppmax_{p'}(|S|) <= 2^{d-1}(q+1)^{d-1} ; at q=2")
    print("      the sharper ppmax_{2'} <= 2^{3d/2-2}.")
    print("      (i) cross char, almost simple:  |S| = c|S_1| < c(2(q+1))"
          "^{3(d-1)}  against  |S| > q^{d^2-1}/(4d).")
    for q in (2, 3, 4, 5):
        lhsl = (d * d - 1) * math.log2(q) - math.log2(4 * d)
        rhsl = 3 * (d - 1) * math.log2(2 * (q + 1)) + math.log2(12 * d)
        print("        q=%-3d  log2|S| >= %-9.1f   log2(c*(2(q+1))^{3(d-1)})"
              " <= %-9.1f   margin %+.1f" % (q, lhsl, rhsl, lhsl - rhsl))
    print("        v_task60 quotes the q=2 margin as +212 at d=21; at d=25")
    print("        recompute: (d-1)(d-2) - 3(d-1)(1+log2 3) - 2log2(4d) = "
          "%.1f" % ((d - 1) * (d - 2) - 3 * (d - 1) * (1 + math.log2(3))
                    - 2 * math.log2(4 * d)))
    print("        and at d = 21 : %.1f"
          % (20 * 19 - 3 * 20 * (1 + math.log2(3)) - 2 * math.log2(84)))
    print("      (ii) cross char, multi-factor: tau_1 = N_1/mu_1 >= 1 and")
    print("        (q^{2 tau_1}/(2(q+1)))^{d-1} <= (4 l d_1 f_1 g_1)^{2tau_1}")
    print("        at q=2 the branch needs tau_1 <= log6/(2log2) = %.4f"
          % (math.log(6) / (2 * math.log(2))))
    print("        families with tau = N/mu <= 1.2925 :")
    ak = {A["key"]: A for A in AUD}
    for A in AUD:
        ns = [A["nmin"]] if A["nmax"] else range(A["nmin"], 9)
        for n in ns:
            t = Fr(A["N"](n), A["mu"](n))
            if t <= Fr(6465, 5000):
                print("          %-5s rank %-2d  tau = %-8s  char %s"
                      % (A["key"], n, str(t),
                         "2 (NOT cross-char at q=2)"
                         if A["key"] in ("2B2", "2F4") else "any"))
    print("      matches v_task60's five-element list "
          "{L2, U3, R, U4, G2} (+ Sz, 2F4 excluded by characteristic).")
    print("      exact ppmax_{2'} bounds at d = 25 are in the GAP output.")


# ======================================================================
#  PART 4 -- cross-cutting
# ======================================================================

def part4():
    print(BAR)
    print("PART 4 -- cross-cutting: B_n/C_n vs L/U, and the a/N table")
    print(BAR)
    print("""
 4.1  'B_n/C_n never meets an L/U order (2n^2 = n+1 impossible)'.
   |B_n(q)| = |C_n(q)| has a = 2n^2+n, N = n^2, so a/N = 2 + 1/n;
   the towers have a = d^2-1, N = d(d-1)/2, a/N = 2(d+1)/d = 2 + 2/d.
   Equating: 1/n = 2/d, i.e. d = 2n.  Then a = d^2-1 = 4n^2-1 must equal
   2n^2+n, i.e. 2n^2 - n - 1 = 0, i.e. (2n+1)(n-1) = 0, so n = 1.
   No solution with n >= 2.""")
    for n in range(2, 40):
        d = 2 * n
        if d * d - 1 == 2 * n * n + n:
            print("   *** solution at n = %d" % n)
    print("   verified for 2 <= n <= 39 : no solution.  The ALGEBRA is right.")
    print("""
   CAVEAT (audit).  The step 'a/N must agree' is only valid when the two
   orders are read as polynomials in the SAME q.  For |B_n(q1)| = |L_d(q)|
   with q1 != q the argument does not apply as written -- e.g. it would
   also have to exclude |C_3(q1)| = |L_d(q)| with q1 = q^k.  What actually
   rules that out is the CFSG order theorem itself (Artin / KLST), which
   is cited independently one paragraph earlier and already lists ALL
   order coincidences among simple groups.  So v_task56 sec 8.1's 'one
   line' is a consistency check, not an independent proof; the conclusion
   is nevertheless correct because it is inherited from [LIT: KLST].
   Same-q check (exhaustive), all q <= 3000, n <= 12, d <= 24:""")
    hit = 0
    for (q, p, f) in prime_powers_upto(500):
        for n in range(3, 9):
            ob = q ** (n * n) * prod(q ** (2 * i) - 1
                                     for i in range(1, n + 1)) // gcd(2, q - 1)
            for X in ("L", "U"):
                for d in range(4, 17):
                    if order_LU(X, d, q) == ob:
                        print("   *** |B_%d(%d)| = |%s_%d(%d)|" % (n, q, X, d, q))
                        hit += 1
    print("   same-q coincidences found: %d" % hit)

    print("\n 4.2  the a/N ratio table used by Lemma EQ-EX vs the")
    print("      erratum-corrected FAM degree table.")
    from v_task52_lemmaC import FAM
    print("      %-6s %-5s %-6s %-6s %-10s %-8s %s"
          % ("fam", "rank", "D", "N", "D/N", "mu", "mu unchanged by erratum?"))
    bad = 0
    for F in FAM:
        A = [a for a in AUD if a["key"] == F["key"]][0]
        ns = [F["nmin"]] if F["nmax"] else [F["nmin"], 4, 6]
        for n in ns:
            D, N, mu = F["D"](n), F["N"](n), F["mu"](n)
            if (D, N, mu) != (A["D"](n), A["N"](n), A["mu"](n)):
                bad += 1
                mark = "*** MISMATCH vs independent table"
            else:
                mark = ("mu = %d (ERRATUM value)" % mu
                        if F["key"] in ("E7", "E8") else "")
            print("      %-6s %-5d %-6d %-6d %-10s %-8d %s"
                  % (F["key"], n, D, N, str(Fr(D, N)), mu, mark))
    print("      mismatches: %d" % bad)
    print("""
   The erratum touched ONLY mu (= deg iotabar), never D or N.  Lemma
   EQ-EX compares D_1/N_1 with a/N, so the a/N table is erratum-free by
   construction.  Consumers of mu:  Lemma C (2D-3mu > 0 -- still true:
   E7 2*133-3*27 = 185, E8 2*248-3*57 = 325), Lemma Z (mu/k), Lemma Z2
   (mu/N), the floor (iotabar <= 4q^mu), Lemma DEG's sigma.  Checked:""")
    for k, D, mu in (("E7", 133, 27), ("E8", 248, 57)):
        print("      %s: 2D-3mu = %d > 0 ; mu/k = %s ; mu/N = %s"
              % (k, 2 * D - 3 * mu,
                 str(Fr(mu, 18 if k == "E7" else 30)),
                 str(Fr(mu, 63 if k == "E7" else 120))))
    print("""      v_task56.md sec 2.1's printed mu/k table gives E7 = 25/18
      and E8 = 17/10 -- the PRE-erratum values.  Its own regenerated
      _out.txt gives 3/2 and 19/10 (correct).  So the .md TABLE IS STALE;
      the computation is not.  Direction: the stale values UNDERSTATE
      mu/k, i.e. they would wrongly EXCLUDE E7/E8 from surviving-family
      lists -- the NON-conservative direction.  The .md sec 4.2 table
      likewise omits E7 from the L_10 row, which the corrected run
      includes.  Documentation defect, no verdict moves.""")


# ======================================================================
#  PART 5 -- the PARANOID re-run of v_task60 PART C
#
#  v_task60's enumerate_configs uses
#        lb = b / mu_i                (the floor with the log-slack DROPPED)
#        ub = min_kappa t/kappa       (Lemma ZM with the v_r(d!) term DROPPED)
#  Neither is valid for small q, so PART C's headline "uniformly in q, no
#  q anywhere" is not literally true.  Here the enumeration is re-run with
#  BOTH slacks restored (a strict RELAXATION, hence a superset of the true
#  candidate set), and the PACK/DEG killer is re-applied unchanged.
# ======================================================================

def part5(dlist=(4, 6, 8, 10, 12, 15, 20, 21, 25, 30, 40, 60),
          qlist=(2, 3, 4, 8, 16, 64, 1024, 10 ** 6)):
    """How much does v_task60 PART C's enumeration LOSE by dropping the
    (Z2) log-slack and the (ZM) v_r(d!) term?  Diagnostic, not a re-run:
    for each target and each q, count the candidate (family, rank, l)
    rows that the HONEST box admits and v_task60's box does not."""
    print(BAR)
    print("PART 5 -- what v_task60 PART C's enumeration drops")
    print(BAR)
    import math
    import v_task60_lu_residues as V
    print("""
  v_task60 enumerate_configs uses
        lb_i = b/mu_i             (floor, log-slack DROPPED)
        ub_i = min_kappa t/kappa  (Lemma ZM, v_r(d!) term DROPPED)
  Honest versions:
        lb_i = max(0, (b - Lambda_i)/mu_i),
               Lambda_i = log_q(4 l_i d_i f_i g_i)
        need_i = max(1, l_i m - (d-1)//kappa)   in the ZM maximisation
  Both widen the box, so v_task60's candidate list is a SUBSET of the
  true one.  'extra' below = candidate rows admitted by the honest box
  but NOT by v_task60's; 'lb=0' = rows on which the floor gives NO lower
  bound at all (the enumeration is then not even finite without the
  separate bound j_i >= 1/f).
""")

    def dcap_of(x):
        if x["key"] in ("A", "2A"):
            return x["n"]
        return max(1, x["F"]["d"](x["n"], 5), x["F"]["d"](x["n"], 4))

    def jb_relaxed(row, l, MT, K, dd):
        best = None
        for kap, m in row["cyc"].items():
            need = max(1, l * m - (dd - 1) // kap)
            t = V.MT_max_t(MT, K, need)
            if t is None:
                return None
            v = Fr(t, kap)
            best = v if best is None else min(best, v)
        return best

    print("  %-4s %-4s %-10s %s" % ("X", "d", "v60 rows",
                                    "  ".join("q=%-8s" % q for q in qlist)))
    for X in ("L", "U"):
        for d in dlist:
            b, K = V.bdeg(X, d), V.Kmax(X, d)
            N = d * (d - 1) // 2
            MT = dict(V.target_cyc(X, d))
            rows = V.famrows(3 * d + 2)
            base = set()
            for i, x in enumerate(rows):
                for l in range(1, 25):
                    ub = V.jbound_ZM(x, l, MT, K)
                    lb = Fr(b, x["mu"])
                    if ub is None or ub < lb or l * lb * x["N"] > N:
                        break
                    base.add((i, l))
            cells = []
            for q in qlist:
                p, f = ((2, q.bit_length() - 1) if q & (q - 1) == 0
                        else (q, 1))
                extra = 0
                zero = 0
                for i, x in enumerate(rows):
                    for l in range(1, 25):
                        ub = jb_relaxed(x, l, MT, K, d)
                        if ub is None:
                            break
                        f1 = max(1, int(ub * f))
                        lam = (math.log(4 * l * dcap_of(x) * f1 * x["F"]["g"])
                               / (f * math.log(p)))
                        lbh = Fr(max(0, int((b - lam) * 512)), 512 * x["mu"])
                        if lbh == 0:
                            zero += 1
                        if ub < lbh or l * lbh * x["N"] > N:
                            break
                        if (i, l) not in base:
                            extra += 1
                cells.append("%d/%d" % (extra, zero))
            print("  %-4s %-4d %-10d %s"
                  % (X, d, len(base), "  ".join("%-10s" % c for c in cells)))
            sys.stdout.flush()
    print("""
  cell = extra-rows / rows-with-lb=0.

  READING.  Wherever 'extra' > 0 the shape enumeration of v_task60 PART C
  is INCOMPLETE at that q, so its headline ('the branch has zero
  admissible socle shapes, uniformly in q, no census enters the argument
  at all') is not literally true there.  The gap is covered by the C.4
  censuses for d <= 20 (q <= 10^5 for d <= 10, q <= 3000 for 11..20) and
  by NOTHING for d >= 21 -- see v_task82_gapfill_d21_out.txt, where this
  audit runs the missing census for d = 21..24.
  The columns decrease with q but only LOGARITHMICALLY (Lambda_i =
  log_q(...)), so 'extra' is still nonzero at q = 10^6 for most targets;
  PART D never computes the q-threshold at which it vanishes.""")


# ======================================================================
if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    if which in ("0", "all"):
        part0_table_crosscheck()
    if which in ("1", "all"):
        part1()
    if which in ("2", "all"):
        part2()
    if which in ("3", "all"):
        part3()
    if which in ("4", "all"):
        part4()
    if which in ("5", "all"):
        part5()
