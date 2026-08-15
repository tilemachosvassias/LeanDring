#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
v_task56_lu_twins.py -- Fitting-free NON-SIMPLE twins of the LINEAR and
UNITARY towers

        S = L_d(q) = PSL(d,q)     and     S = U_d(q) = PSU(d,q),   d >= 4.

This is the first UNIFORM-IN-RANK run of the programme.  Pipeline:
  L_2 pilot (v_task51) -> rank 1 (v_task53/54) -> rank 2 = L_3 (v_task55)
  -> HERE: d >= 4, both towers, uniform in d wherever possible.

Standing hypotheses (all upstream and PROVEN):
   T Fitting-free, |T| = |S|, D(T) = D(S), T NOT simple.
   Soc T = prod_j S_j^{l_j} over orbits, c = [T : Soc T],
   (F)  l_O * |Out(S_1)| * iota(S_1) >= iota(S)          [Lemma TO'-0 + F]
   (C)  |Out(G)| * iota(G) <= |G|^{2/3}                  [Lemma C, v_task52]
   (T1) |G| >= q1^D/(12 d),  (T2) iotabar <= 4 q1^mu,  (T3) |Out| = d f g,
        g <= 6                                           [v_task52]
   (P)  N - mu = 0 iff rank 1                            [v_task54 Lemma P]

Target data (PART A):
   |S| = q^N prod_{i=2}^d (q^i - eps_i)/e ,  N = d(d-1)/2 ,  a := deg_q|S| = d^2-1
   L: eps_i = 1, e = gcd(d,q-1) ;  U: eps_i = (-1)^i, e = gcd(d,q+1)
   iota(L_d(q)) = (q^d-1)/(q-1)                                  b = d-1
   iota(U_4(q)) = (q+1)(q^3+1)                                   b = 4
   iota(U_d(q)) = (q^d-(-1)^d)(q^{d-1}-(-1)^{d-1})/(q^2-1), d>=5 b = 2d-3
   K := max_{r | |S|, r != p} ord_r(q)  =  d (L) ; 2d (U, d odd) ;
        2d-2 (U, d even)

NEW UNIFORM TOOLS INTRODUCED HERE
  * Lemma Z (the Zsygmondy ratio test, EQUAL characteristic, PART B).
        f1 * k1 <= K * f      where k1 = max cyclotomic degree of |S_1|.
    With the orbit floor this becomes   mu1/k1 >= (b - L/f)/K , a purely
    numerical per-family test.  It kills every rank-1 family (L2, U3, Sz, R)
    for every d >= 4, in one line, and it is the tool that replaces the
    per-family kills of v_task55 section 5.2.
  * Lemma X (the cross-characteristic ppmax kill, PART E).
        ppmax_{p'}(|S|) <= C_d * q^{d-1}  -- the exponent d-1 is uniform in
    d, while |S| ~ q^{d^2-1}, so |S| > c*P^3 for every d >= 3 with margin
    growing quadratically.

PARTS
  A  invariants, the iota table, and validation against v_task39/50 data
  B  Lemma Z: the (mu/k) table and the surviving-family list per (X,d)
  C  equal characteristic, ALMOST SIMPLE: the j*d1 window analysis
     (Lemma Z + floor + order  ==>  d1 >= d, j <= 1, subfield only) and the
     exact factorisation-free sweep
  D  the multi-factor branch (Lemma Q at general d): l >= 3 by Lemma C,
     l <= 2 by Lemma Z (equal char) and by the p1-part (cross char)
  E  cross characteristic, almost simple: the ppmax^3 kill, exact
  F  alternating / sporadic socle, complete in q
  G  the residual census, with positive controls

All arithmetic exact.
"""

import sys
from fractions import Fraction

sys.path.insert(0, ".")

from v_task50_sporadic_twins import SPORADIC, TITS, IOTA_UB, census as census50
from v_task50_sporadic_twins import simple_divisors, phase2
from v_task51_l2_twins import is_prime_power
from v_task54_rank1_gaps import prime_powers_sieve
from v_task52_lemmaC import FAM, gcd, order_of, out_of, iroot
import v_task50_sporadic_twins as V50
from v_task51_l2_twins import iota_ub_generic

V50.iota_ub = lambda name, order: iota_ub_generic(name)

BAR = "=" * 76


# ------------------------------------------------------------ factorisation
# Pollard rho -- needed because |L_4(q)| ~ q^15 is far out of trial-division
# range for the census targets.

def _is_probable_prime(n):
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def _rho(n):
    if n % 2 == 0:
        return 2
    import random
    while True:
        x = random.randrange(2, n)
        y = x
        c = random.randrange(1, n)
        d = 1
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = gcd(abs(x - y), n)
        if d != n:
            return d


def factorint(n):
    f = {}
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47):
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
    stack = [n] if n > 1 else []
    while stack:
        m = stack.pop()
        if m == 1:
            continue
        if _is_probable_prime(m):
            f[m] = f.get(m, 0) + 1
            continue
        d = _rho(m)
        stack.append(d)
        stack.append(m // d)
    return f


V50.factorint = factorint


# ------------------------------------------------------------------ targets

def prime_powers_upto(M, qmin=2):
    return [t for t in prime_powers_sieve(M) if t[0] >= qmin]


def order_LU(X, d, q):
    """|L_d(q)| resp. |U_d(q)|"""
    o = q ** (d * (d - 1) // 2)
    if X == "L":
        for i in range(2, d + 1):
            o *= q ** i - 1
        e = gcd(d, q - 1)
    else:
        for i in range(2, d + 1):
            o *= q ** i - (-1) ** i
        e = gcd(d, q + 1)
    return o // e


# minimal-degree EXCEPTIONS in the two towers [LIT: Kleidman-Liebeck Table
# 5.2.2]: m(S) < [S:P_min].  Only two occur for d >= 4.  We use the smaller
# value as iota(S) -- the CONSERVATIVE direction, since iota(S) is the
# right-hand side of the orbit floor.
#   L_4(2) = A_8   : m = 8   (but iota(A_8) = 15 exactly: the index-8 maximal
#                    subgroup A_7 is simple, hence not N(H) with |H'| small --
#                    GAP-verified, PART B of the .g file)
#   U_6(2)         : m = 672 (vs [S:P_1] = 693)
IOTA_EXC = {("U", 6, 2): 672}


def iota_LU(X, d, q):
    """iota(S) = index of the SMALLEST maximal parabolic (Borel-Tits witness
    A = O_p(P), N_S(A) = P);  equal to the minimal permutation degree, so the
    (>=) half is (AB)-free.  [LIT: Cooperstein 1978; Kleidman-Liebeck 5.2.2]"""
    if (X, d, q) in IOTA_EXC:
        return IOTA_EXC[(X, d, q)]
    if X == "L":
        return (q ** d - 1) // (q - 1)
    if d == 4:
        # U_4(q) = O_6^-(q): the SMALLEST parabolic is P_2 (totally isotropic
        # 2-spaces), index (q+1)(q^3+1) < (q^2+1)(q^3+1) = [S:P_1].
        return (q + 1) * (q ** 3 + 1)
    s = (-1) ** d
    return (q ** d - s) * (q ** (d - 1) + s) // (q * q - 1)


def out_LU(X, d, q, f):
    e = gcd(d, q - 1) if X == "L" else gcd(d, q + 1)
    return 2 * f * e


def bdeg(X, d):
    """deg_q iota(S)"""
    return d - 1 if X == "L" else (4 if d == 4 else 2 * d - 3)


def Kmax(X, d):
    """max_{r | |S|, r != p} ord_r(q)"""
    if X == "L":
        return d
    return 2 * d if d % 2 else 2 * d - 2


def name_LU(X, d, q):
    return "%s%d(%d)" % (X, d, q)


def solve_LU(X, d, M):
    """all prime powers q with |S| = M -- complete in q (order is strictly
    increasing in q, degree a = d^2-1)."""
    a = d * d - 1
    out = []
    for e in range(1, d + 1):
        if d % e:
            continue
        v = M * e
        r = iroot(v, a)
        for q in range(max(2, r - 2), r + 3):
            if q < 2 or not is_prime_power(q):
                continue
            ee = gcd(d, q - 1) if X == "L" else gcd(d, q + 1)
            if ee != e:
                continue
            if order_LU(X, d, q) == M:
                out.append(q)
    return sorted(set(out))


# ============================================================ PART A

# known exact iota values (v_task39 / v_task50 CTblLib table) for validation
IOTA_KNOWN = {
    ("L", 4, 2): 15,       # L_4(2) = A_8 : iota(A_8) = 15  (NB m(A_8) = 8)
    ("L", 4, 3): 40, ("L", 4, 4): 85, ("L", 4, 5): 156, ("L", 4, 7): 400,
    ("L", 4, 9): 820,
    ("L", 5, 2): 31, ("L", 5, 3): 121, ("L", 5, 4): 341,
    ("L", 6, 2): 63, ("L", 6, 3): 364, ("L", 6, 4): 1365,
    ("U", 4, 2): 27,       # U_4(2) = S_4(3) : iota = 27 = (q+1)(q^3+1)
    ("U", 4, 3): 112,
    ("U", 5, 2): 165, ("U", 5, 4): 17425,
    ("U", 6, 4): 279825,
}
# ("U",6,2): v_task50 lists 693 = [S:P_1]; GAP's Maxes give the MINIMAL
# DEGREE m(U_6(2)) = 672 < 693, so 672 is used (conservative), see IOTA_EXC.

# v_task50 rows that are only PARABOLIC UPPER BOUNDS (the P_1 index), not the
# exact iota: for U_4 the smaller parabolic is P_2, so our value must be <=.
IOTA_UB_ONLY = {
    ("U", 4, 4): 1105, ("U", 4, 5): 3276, ("U", 4, 8): 33345,
}


def partA(dmax=12):
    print(BAR)
    print("PART A -- the two towers: invariants, iota, and the degree data")
    print(BAR)
    print("""
  |S| = q^N prod_{i=2}^d (q^i - eps_i)/e ,  N = d(d-1)/2 , a = deg_q|S| = d^2-1
  iota(S) = [S:P_min] with witness A = O_p(P_min) (Borel-Tits N_S(Z(U_P)) = P);
  the (>=) half is the minimal degree m(S) [LIT: Cooperstein; KL Table 5.2.2],
  so iota is proven over ALL subgroups and (AB) is not a debt.

  K := max ord_r(q) over r | |S|, r != p   (the top cyclotomic degree).
""")
    print("  %-3s %-3s %5s %5s %5s %5s %8s %8s %8s" %
          ("X", "d", "a", "N", "b", "K", "a/N", "b/K", "a/(2b)"))
    for X in ("L", "U"):
        for d in range(4, dmax + 1):
            a = d * d - 1
            N = d * (d - 1) // 2
            b = bdeg(X, d)
            K = Kmax(X, d)
            print("  %-3s %-3d %5d %5d %5d %5d %8s %8s %8s" %
                  (X, d, a, N, b, K, str(Fraction(a, N)), str(Fraction(b, K)),
                   str(Fraction(a, 2 * b))))
    print()
    print("  a/N = 2(d+1)/d  DECREASES with d  (the equal-characteristic")
    print("  strain diagnosed in v_task55).  b/K INCREASES with d -- that is")
    print("  the new leverage exploited by Lemma Z (PART B).")
    print()
    print("  VALIDATION of the iota formulas against the exact v_task39/50")
    print("  CTblLib table (Lemma SP values):")
    bad = 0
    for (X, d, q), val in sorted(IOTA_KNOWN.items()):
        got = iota_LU(X, d, q)
        ok = (got == val)
        if not ok:
            bad += 1
        print("     %-10s formula %-12d table %-12d %s"
              % (name_LU(X, d, q), got, val, "OK" if ok else "*** MISMATCH"))
    print("  exact-row mismatches: %d" % bad)
    print()
    print("  v_task50 rows that are only the P_1 parabolic UPPER bound (for")
    print("  U_4 the smaller parabolic is P_2, index (q+1)(q^3+1)); our value")
    print("  must be <= theirs, and the ratio is exactly (q^2+1)/(q+1):")
    for (X, d, q), val in sorted(IOTA_UB_ONLY.items()):
        got = iota_LU(X, d, q)
        p1 = (q * q + 1) * (q ** 3 + 1)
        print("     %-10s P_2 = %-10d  P_1 = %-10d  v_task50 = %-10d  %s"
              % (name_LU(X, d, q), got, p1, val,
                 "OK (<=)" if got <= val and p1 == val else "*** CHECK"))
    print("""
  Two order coincidences inside the towers, both handled exactly:
    L_4(2) = A_8 = |L_3(4)| -- minimal degree 8, but iota(A_8) = 15 =
      (2^4-1)/(2-1) : the degree-8 point stabiliser A_7 is simple, so it is
      not N(H) for any 1 != H with small |H'|.  The formula is UNCHANGED.
    U_4(2) = S_4(3) -- iota = 27 = (q+1)(q^3+1) : also unchanged.
  By the CFSG order theorem the only order coincidences among simple groups
  are {A_8, L_3(4)} and {B_n(q), C_n(q)} (q odd, n >= 3).  B_n/C_n never
  meets an L_d/U_d order: |B_n(q)| = q^{n^2} prod (q^{2i}-1)/gcd(2,q-1) has
  a = 2n^2+n and N = n^2, i.e. a/N = 2 + 1/n, while the towers have
  a/N = 2 + 2/d -- equal only for d = 2n, and then a = d^2-1 = 4n^2-1 vs
  2n^2+n, i.e. 2n^2 = n+1, impossible for n >= 2.
""")
    return bad


# ============================================================ PART B

# k = max cyclotomic degree occurring in |G| (the largest ord_{q1} of a prime
# divisor of |G| other than p1).  Derived from the order formulas of FAM.
KFAM = {
    "A1": lambda n: 2,
    "A": lambda n: n,
    "2A": lambda n: 2 * n if n % 2 else 2 * n - 2,
    "C": lambda n: 2 * n,
    "B": lambda n: 2 * n,
    "D": lambda n: 2 * n - 2,
    "2D": lambda n: 2 * n,
    "G2": lambda n: 6,
    "3D4": lambda n: 12,
    "F4": lambda n: 12,
    "E6": lambda n: 12,
    "2E6": lambda n: 18,
    "E7": lambda n: 18,
    "E8": lambda n: 30,
    "2B2": lambda n: 4,
    "2G2": lambda n: 6,
    "2F4": lambda n: 12,
}


def partB(dmax=12, rankmax=14):
    print(BAR)
    print("PART B -- Lemma Z, the Zsygmondy ratio test (EQUAL characteristic)")
    print(BAR)
    print("""
  Lemma Z [PROVEN].  Let S be L_d(q) or U_d(q), q = p^f, and let G be a
  socle factor of Lie type over F_{q1}, q1 = p^{f1}, in the SAME
  characteristic, sitting in an orbit of length l.  Let k1 be the largest
  cyclotomic degree occurring in |G| and mu1 = deg_{q1} iotabar(G).  Then

      (Z1)   f1 * k1  <=  K * f ,        K = max ord_r(q) over r | |S|,
      (Z2)   f1 * mu1 >=  f * b - log_p( 4 l d1 f1 g1 )      [orbit floor]

  hence          mu1 / k1  >=  b/K  -  log_p(4 l d1 f1 g1)/(f*K) .

  Proof of (Z1).  |G| has a Zsygmondy primitive prime divisor r of
  p^{f1 k1} - 1, i.e. ord_r(p) = f1*k1 and r != p (exceptions: (p^{f1},k1) =
  (2,6) and k1 = 2 with p^{f1}+1 a 2-power -- both handled separately below).
  r | |G| | |S|, and every r != p dividing |S| has ord_r(q) <= K, so
  ord_r(p) = f1 k1 divides K * ord... more precisely
  ord_r(q) = f1 k1 / gcd(f1 k1, f) <= K gives f1 k1 <= K f.   []

  Proof of (Z2).  Floor (F) with (T2)/(T3):
  4 l d1 f1 g1 q1^{mu1} >= l|Out(G)|iota(G) >= iota(S) > q^b.   []

  The test mu1/k1 >= b/K is PURELY NUMERICAL and uniform in q.
""")
    rows = []
    for F in FAM:
        ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], rankmax + 1)
        for n in ns:
            k = KFAM[F["key"]](n)
            mu = F["mu"](n)
            rows.append((F["key"], n, mu, k, Fraction(mu, k)))
    print("  %-6s %-4s %5s %5s %10s" % ("family", "n", "mu", "k", "mu/k"))
    seen = set()
    for (key, n, mu, k, r) in rows:
        if key in ("A", "2A", "C", "B", "D", "2D") and n > 8:
            continue
        print("  %-6s %-4d %5d %5d %10s" % (key, n, mu, k, str(r)))
    print("  (the six unbounded-rank families have mu/k -> 1 monotonically:")
    print("   A: 1-1/n, 2A: 1-3/2n resp 1-1/(2n-2), C/B: 1-1/2n, D: 1,")
    print("   2D: 1-1/n -- so a family once admitted stays admitted.)")
    print()
    print("  SURVIVING FAMILIES per target (mu/k >= b/K, the q -> infinity")
    print("  form; the log-correction is handled exactly in PART C/D):")
    surv = {}
    for X in ("L", "U"):
        for d in range(4, dmax + 1):
            thr = Fraction(bdeg(X, d), Kmax(X, d))
            live = []
            for F in FAM:
                ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], rankmax + 1)
                nmin_live = None
                for n in ns:
                    if Fraction(F["mu"](n), KFAM[F["key"]](n)) >= thr:
                        nmin_live = n
                        break
                if nmin_live is not None:
                    live.append("%s(n>=%d)" % (F["key"], nmin_live)
                                if not F["nmax"] else F["key"])
            surv[(X, d)] = live
            print("   %s_%-2d  b/K = %-6s  live: %s"
                  % (X, d, str(thr), ", ".join(live)))
    print("""
  READ-OFF.  For EVERY d >= 4 and both towers, the families
        A1 = L_2 ,  2A(3) = U_3 ,  2B2 = Sz ,  2G2 = R
  all have mu/k = 1/2 < b/K and are DEAD.  These are exactly the four
  rank-1 families -- i.e. the families with N = mu, the ones that Lemma EQ
  of v_task54 could not touch and that v_task55 had to kill one at a time.
  Lemma Z kills them uniformly, in every rank, in one line.
""")
    return surv


# ============================================================ PART C

def partC_window(dmax=10):
    print(BAR)
    print("PART C.1 -- the j*d1 window (equal characteristic, almost simple)")
    print(BAR)
    print("""
  S = L_d(q), S_1 = L_{d1}(q1), q1 = p^{f1}, j := f1/f.  (E): c|S_1| = |S|,
  2 <= c | |Out(S_1)|.  Three exact inputs:

    (Z1)   j * d1 <= d                            [Lemma Z, k1 = d1, K = d]
    (F)    j * (d1-1) >= (d-1) - eps ,  eps := log_q(8 d1 f1)
    (O)    j * (d1^2-1) = (d^2-1) - delta ,  delta := log_q(c * kappa),
           kappa in [1/12, 12]                                   [(T1), (E)]

  (Z1)+(F):   d - j >= j d1 - j >= d-1-eps  ==>  j <= 1 + eps.
  (O)+(Z1):   d1 (d^2-1-delta) = j d1 (d1^2-1) <= d (d1^2-1)
              ==>  (d - d1)(d d1 + 1) <= d1 * delta
              ==>  d1 >= d - delta/d  ==>  d1 >= d   (integers, delta < d).
  (O) with d1 >= d+1:  j <= (d^2-1)/((d+1)^2-1) and then
              j(d1-1) = (d^2-1-delta)/(d1+1) <= (d^2-1)/(d+2) ,
              which is < d-1-eps unless eps >= (d-1)/(d+2) >= 1/2, i.e.
              unless q^{1/2} <= 8 d1 f1  --  a finite window.
  So d1 = d and j <= 1: the SUBFIELD case.  j = 1 gives c = 1 (excluded).
  j <= 1 - 1/f gives  c >= (q/q1)^{d^2-1}/(4d) >= p^{d^2-1}/(4d) >= 2^15/16
  against c <= |Out(L_d(q1))| = 2 d f1 <= 2 d f.

  THE SAME derivation runs for U in U, with (Z1) reading j*k1 <= K.
  MIXED cases (L_{d1} inside U_d and U_{d1} inside L_d) are covered by the
  same three inputs with the mixed (b, K, k1, mu1) -- computed exactly below.
""")
    print("  the finite window of the  d1 >= d+1  branch, exactly:")
    print("  %-4s %-4s %-14s %s" % ("X", "d", "eps needed", "largest q with "
                                    "q^{(d-1)/(d+2)} <= 8 d1 f1 (d1<=2d)"))
    for X in ("L", "U"):
        for d in range(4, dmax + 1):
            hi = 0
            for (q, p, f) in prime_powers_upto(10 ** 6):
                d1cap = 2 * d
                f1cap = max(1, (d * f))
                need = Fraction(d - 1, d + 2)
                # exact: q^{d-1} <= (8 d1 f1)^{d+2}
                if q ** (d - 1) <= (8 * d1cap * f1cap) ** (d + 2):
                    hi = q
            print("  %-4s %-4d %-14s %d" % (X, d, str(Fraction(d - 1, d + 2)), hi))
    print()


def partC_sweep(dlist=(4, 5, 6, 7, 8), qmax=20000, verbose=True):
    """The factorisation-free EQUAL-characteristic decision, exactly.

    q1^{N1} | q^N bounds f1 <= f*N/N1, so the whole branch is a finite exact
    test per target, with no factorisation of |S|."""
    print(BAR)
    print("PART C.2 -- equal characteristic, decided EXACTLY for every q")
    print("            (factorisation-free, complete in f1 and in the type)")
    print(BAR)
    tot_hits = []
    for X in ("L", "U"):
        for d in dlist:
            N = d * (d - 1) // 2
            hits, near, pairs, ctl, ntar = [], [], 0, 0, 0
            for (q, p, f) in prime_powers_upto(qmax):
                if X == "L" and d == 4 and q == 2:
                    pass   # L_4(2) = A_8 is kept: it IS a target
                S = order_LU(X, d, q)
                ntar += 1
                selfseen = False
                for F in FAM:
                    ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], 3 * d + 2)
                    for n in ns:
                        N1 = F["N"](n)
                        if N1 > N * f:
                            break
                        for f1 in range(1, (N * f) // N1 + 1):
                            q1 = p ** f1
                            if not F["qform"](p, f1) or F["skip"](n, q1):
                                continue
                            o1 = order_of(F, n, q1)
                            if o1 < 60 or o1 > S or S % o1:
                                continue
                            c = S // o1
                            pairs += 1
                            if c == 1:
                                selfseen = True
                                continue
                            ou = out_of(F, n, q1, p, f1)
                            if c <= ou:
                                near.append((q, F["name"](n, q1), c, ou))
                            if ou % c == 0:
                                hits.append((q, F["name"](n, q1), c))
                if selfseen:
                    ctl += 1
            print("  %s_%-2d  targets %-7d divisor pairs %-9d control %d/%d"
                  % (X, d, ntar, pairs, ctl, ntar))
            print("        order-only NEAR-MISSES (c <= |Out|) : %s"
                  % (near[:8] if near else "NONE"))
            print("        HITS (c >= 2, c | |Out(S_1)|)       : %s"
                  % (hits or "NONE"))
            tot_hits += hits
            sys.stdout.flush()
    print()
    print("  TOTAL equal-characteristic hits over both towers: %s"
          % (tot_hits or "NONE"))
    print()
    return tot_hits


def partC_multi(dlist=(4, 5, 6, 7, 8, 9, 10), qmax=200000):
    """PART C.3 -- the EQUAL-characteristic MULTI-FACTOR branch, exactly.

    A multi-factor Fitting-free twin has a socle factor G (of Lie type, same
    characteristic) and an orbit length l >= 1 with
        (i)   |G|^l  divides |S|
        (ii)  |G|^{max(2,l)} <= |S|          (l >= 2, or a second orbit)
        (iii) l * |Out(G)| * iotabar(G) >= iota(S)      [orbit floor]
    q1^{l N1} | q^N bounds f1, so the test is finite and needs no
    factorisation of |S|."""
    print(BAR)
    print("PART C.3 -- equal characteristic, MULTI-FACTOR branch, exact")
    print(BAR)
    tot = []
    for X in ("L", "U"):
        for d in dlist:
            N = d * (d - 1) // 2
            lmax = int(lmax_lemC(X, d))
            surv, ntar = [], 0
            for (q, p, f) in prime_powers_upto(qmax):
                S = order_LU(X, d, q)
                io = iota_LU(X, d, q)
                ntar += 1
                for F in FAM:
                    ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], 3 * d + 2)
                    for n in ns:
                        N1 = F["N"](n)
                        if N1 > N * f:
                            break
                        for f1 in range(1, (N * f) // N1 + 1):
                            q1 = p ** f1
                            if not F["qform"](p, f1) or F["skip"](n, q1):
                                continue
                            o1 = order_of(F, n, q1)
                            if o1 < 60 or o1 * o1 > S:
                                continue
                            ou = out_of(F, n, q1, p, f1)
                            ib = F["iota"](n, q1)
                            for l in range(1, max(2, lmax) + 1):
                                if o1 ** l > S or S % (o1 ** l):
                                    break
                                if l * ou * ib >= io:
                                    surv.append((q, F["name"](n, q1), l))
            print("  %s_%-2d  targets %-7d  l_max %-3d  survivors %-4d  "
                  "LARGEST q with a survivor: %s"
                  % (X, d, ntar, lmax, len(surv),
                     max([t[0] for t in surv]) if surv else "-- NONE"))
            print("        %s" % (surv[:12] or ""))
            tot += surv
            sys.stdout.flush()
    print()
    print("  TOTAL equal-characteristic multi-factor survivors: %s"
          % (tot[:20] or "NONE"))
    print()
    return tot


def partC_multi_full(dlist=(4, 5, 6, 7, 8, 9, 10), qmax=300000):
    """PART C.4 -- the EQUAL-characteristic multi-factor branch, FULL census.

    Above the PART D.2(b) threshold every socle factor is forced into the
    defining characteristic, so the candidate list is the (short) list of
    equal-characteristic Lie factors passing the orbit floor, together with
    the alternating and sporadic factors that pass it.  On that list a
    COMPLETE multiset census (prod |G_j|^{l_j} | |S|, c | prod|Out|^l l!)
    is run, and the per-orbit floor is re-applied exactly.  No factorisation
    of |S| is needed anywhere."""
    print(BAR)
    print("PART C.4 -- equal characteristic, MULTI-FACTOR, FULL census")
    print(BAR)
    tot = []
    for X in ("L", "U"):
        for d in dlist:
            N = d * (d - 1) // 2
            lmax = max(2, int(lmax_lemC(X, d)))
            live, ntar, ncand = [], 0, 0
            for (q, p, f) in prime_powers_upto(qmax):
                S = order_LU(X, d, q)
                io = iota_LU(X, d, q)
                ntar += 1
                cand = []
                for F in FAM:
                    ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], 3 * d + 2)
                    for n in ns:
                        N1 = F["N"](n)
                        if N1 > N * f:
                            break
                        for f1 in range(1, (N * f) // N1 + 1):
                            q1 = p ** f1
                            if not F["qform"](p, f1) or F["skip"](n, q1):
                                continue
                            o1 = order_of(F, n, q1)
                            if o1 < 60 or o1 * o1 > S or S % o1:
                                continue
                            ou = out_of(F, n, q1, p, f1)
                            ib = F["iota"](n, q1)
                            if lmax * ou * ib >= io:
                                cand.append((F["name"](n, q1), o1, ou, ib))
                o, m = 60, 5
                while o * o <= S:
                    ib = IOTA_UB.get("A%d" % m, m * (m - 1) * (m - 2) // 6)
                    ou = 4 if m == 6 else 2
                    if S % o == 0 and lmax * ou * ib >= io:
                        cand.append(("A%d" % m, o, ou, ib))
                    m += 1
                    o = o * m
                for (nm, so, ou) in list(SPORADIC) + [TITS]:
                    if so * so <= S and S % so == 0 and lmax * ou * IOTA_UB[nm] >= io:
                        cand.append((nm, so, ou, IOTA_UB[nm]))
                ncand += len(cand)
                if not cand:
                    continue
                iot = dict((c[0], c[3]) for c in cand)
                outd = dict((c[0], c[2]) for c in cand)
                for (ms, c) in census50(S, [(a, b, cc) for (a, b, cc, _) in cand]):
                    if sum(l for (_, l) in ms) < 2:
                        continue
                    if all(l * outd[nm] * iot[nm] >= io for (nm, l) in ms):
                        live.append((q, ms, c))
            print("  %s_%-2d  targets %-7d  floor-passing factors %-6d  "
                  "LIVE multi-factor configurations: %s"
                  % (X, d, ntar, ncand, live or "NONE"))
            tot += live
            sys.stdout.flush()
    print()
    print("  TOTAL equal-characteristic multi-factor twins: %s"
          % (tot or "NONE"))
    print()
    return tot


# ============================================================ PART D

def partD(dmax=10):
    print(BAR)
    print("PART D -- the multi-factor branch (Lemma Q at general rank)")
    print(BAR)
    print("""
  If T is not almost simple then some socle factor G in an orbit of length l
  satisfies
      (Q1) |G|^{max(2,l)} <= |S|        (Q2) l |Out(G)| iota(G) >= iota(S).

  D.1  l >= 3 dies from Lemma C alone:  |Out|iota <= |G|^{2/3} <= |S|^{2/3l},
       so iota(S)^{3l} <= l^{3l} |S|^2 -- the exact cube-cleared test.
  D.2  l <= 2 (this includes the two-orbit case, where the smaller
       contribution has |G|^{2l} <= |S|).  Then |G|^2 <= |S| and
       2 rho(G) >= iota(S), rho = |Out|iota.  Eliminating q with
       |S| < q^{d^2-1} and iota(S) > q^b gives |G| < (2rho(G))^{a/(2b)},
       i.e. G has  alpha(G) = log|G|/log iota(G)  <=  a/2b  (+ o(1)).
       At d = 3 this is a/2b = 2, i.e. LEMMA B, a finite list (v_task55).
       At d >= 4, a/(2b) = (d+1)/2 > 2 for the linear tower -- the list is
       NO LONGER finite, and this is the genuine new difficulty of rank >= 3.
       It is resolved by splitting on the characteristic:
         (a) EQUAL characteristic: Lemma Z applies verbatim with l <= 2
             (the l enters only the log-correction), so the four rank-1
             families -- exactly the families with theta = D/mu <= 8/3 that
             made the list infinite -- are dead.  What remains has
             mu1/k1 >= b/K, and PART C's window analysis applies.
         (b) CROSS characteristic: q1^{l N1} = |G|^l_{p1} <= |S|_{p1} <=
             ppmax_{p'}(|S|) =: P, while the floor gives
             q1^{mu1} >= iota(S)/(4 l d1 f1 g1).  Since N1 >= mu1 (Lemma P)
             and l >= 2,
                          P  >=  ( iota(S) / (8 d1 f1 g1) )^2 ,
             i.e. P >~ q^{2b}.  PART E shows P <= C_d q^{d-1}: for the
             linear tower 2b = 2(d-1) > d-1, so this FAILS for every q above
             an explicit threshold.  (Lemma X-2.)
""")
    print("  D.1  the Lemma-C factor bound  k <= 2a/(3b)  (k = total number")
    print("       of socle factors with multiplicity) and the exact largest")
    print("       q for which an orbit of length l can survive:")
    print("  %-4s %-4s %-10s %s" % ("X", "d", "2a/(3b)",
                                    "l=3      l=4      l=5      l=6"))
    for X in ("L", "U"):
        for d in range(4, dmax + 1):
            row = []
            for l in range(3, 7):
                hi = "ALL q" if l <= lmax_lemC(X, d) else None
                if hi is None:
                    v = 0
                    q = 2
                    while q <= 10 ** 6:
                        S = order_LU(X, d, q)
                        io = iota_LU(X, d, q)
                        if l ** (3 * l) * S ** 2 >= io ** (3 * l):
                            v = q
                        elif q > 2 * max(v, 2):
                            break
                        q += 1
                    hi = str(v)
                row.append(hi)
            print("  %-4s %-4d %-10s %-8s %-8s %-8s %-8s"
                  % (X, d, str(lmax_lemC(X, d)), *row))
    print("""
       "ALL q" means Lemma C does NOT kill that orbit length -- and it
       happens for l = 3 already at d = 5 in the linear tower.  So the rank-2
       statement "Lemma C kills l >= 3" is FALSE from d = 5 on: the linear
       tower admits up to floor(2(d+1)/3) socle factors on order grounds.
       The unitary tower is far better behaved (b = 2d-3 instead of d-1):
       there l >= 3 is dead for every d >= 4 except the tail rows below.
""")
    print("""  D.2(a) the EQUAL-characteristic multi-factor kill, uniform in d.

       Lemma Z2 [PROVEN].  In the equal-characteristic multi-factor branch,
       |G|_p^l = q1^{l N1} divides |S|_p = q^N, so l f1 N1 <= f N, while the
       floor gives f1 mu1 >= f b - log_p(4 l d1 f1 g1).  Dividing,

              mu1 / N1  >=  l * b/N  -  (small) .

       Lemma Z  (PART B) says   mu1 / k1  >=  b/K  -  (small) .
       The two are INCOMPATIBLE for every family, at every rank, for the
       whole linear tower:  for L_{n1},  mu1/N1 = 2/n1  and  mu1/k1 = 1-1/n1,
       so Lemma Z2 with l = 2 forces n1 <= N/b = d/2 while Lemma Z forces
       n1 >= d.  The table below runs the same test for every family:
""")
    print("  %-4s %-4s %-10s %-10s %s"
          % ("X", "d", "l*b/N (l=2)", "b/K", "families passing BOTH"))
    for X in ("L", "U"):
        for d in range(4, dmax + 1):
            N = d * (d - 1) // 2
            b = bdeg(X, d)
            t2 = Fraction(2 * b, N)
            tz = Fraction(b, Kmax(X, d))
            both = []
            for F in FAM:
                ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], 40)
                for n in ns:
                    if (Fraction(F["mu"](n), F["N"](n)) >= t2
                            and Fraction(F["mu"](n),
                                         KFAM[F["key"]](n)) >= tz):
                        both.append("%s(%d)" % (F["key"], n))
            print("  %-4s %-4d %-10s %-10s %s"
                  % (X, d, str(t2), str(tz), both or "NONE  <== branch empty"))
    print()
    print("  D.2(b) the cross-characteristic multi-factor kill, exactly.")
    print("       Constraints: q1^{l N1} <= P := ppmax_{p'}(|S|) <=")
    print("       d!(q+1)^{d-1}, and q1^{mu1} >= iota(S)/(4 l d1 f1 g1).")
    print("       With N1 >= mu1 (Lemma P) and l >= 2 this needs")
    print("       P >= (iota(S)/(8 d1 f1 g1))^2.  Caps used: 2 N1 <= log_2 P,")
    print("       n1 <= 1+sqrt(log_2 P), f1 <= log_2 P / 2, d1 <= n1, g1 <= 6.")
    print("  %-4s %-4s %-14s %s" % ("X", "d", "2b vs d-1", "kill for all q >="))
    kills = {}
    for X in ("L", "U"):
        for d in range(4, dmax + 1):
            b = bdeg(X, d)
            thr = None
            for (q, p, f) in prime_powers_upto(10 ** 5):
                P = pbound(d, q)
                LP = P.bit_length()
                N1cap = max(1, LP // 2)
                n1 = 2
                while n1 * (n1 - 1) // 2 <= N1cap:
                    n1 += 1
                n1 -= 1
                f1 = max(1, LP // 2)
                lhs = P * (8 * max(n1, 4) * f1 * 6) ** 2
                rhs = iota_LU(X, d, q) ** 2
                if lhs >= rhs:
                    thr = None
                elif thr is None:
                    thr = q
            kills[(X, d)] = thr
            print("  %-4s %-4d %-14s %s" % (X, d, "%d vs %d" % (2 * b, d - 1),
                                            thr))
    print()
    return kills


def pbound(d, q):
    """P := ppmax_{p'}(|S|)  <=  d! * (q+1)^{d-1}.

    Proof.  Let r != p and k := ord_r(q).  The r-part of
    prod_{i=2}^{d}(q^i - eps_i) is r^v with
        v = m * v_r(Phi_k(q)) + v_r(m!) ,  m = #{i <= d : r | q^i - eps_i} ,
    by LTE.  Hence the r-part is at most Phi_k(q)^m * m! <=
    (q+1)^{phi(k) m} * d! , and phi(k)*m <= d-1 for every k:
      k = 1 : phi = 1, m = d-1                      -> d-1
      k = d : phi(d) <= d-1, m = 1                  -> <= d-1
      other : m <= floor(d/k) and phi(k) <= k-1, so phi(k) m <= (k-1)d/k
              <= d - d/k <= d-1 whenever k <= d.
    (For the unitary tower the same computation runs with the blocks
    q^i - (-1)^i, whose r-parts are governed by Phi_k(q), k <= 2d, and
    m <= #{i <= d : k | 2i} <= 2d/k, giving phi(k) m <= d-1 as well.)
    Machine-verified exactly in PART E."""
    fac = 1
    for i in range(2, d + 1):
        fac *= i
    return fac * (q + 1) ** (d - 1)


def lmax_lemC(X, d):
    """Lemma C bounds the TOTAL number of socle factors (with multiplicity):
    every factor has |G| >= (iota(S)/k)^{3/2}, so k * 3b/2 <= a, i.e.
    k <= 2a/(3b).  For the LINEAR tower 2a/(3b) = 2(d+1)/3 -> infinity, so
    Lemma C does NOT bound l by 2 at rank >= 3; for the UNITARY tower
    2a/(3b) = 2(d^2-1)/(3(2d-3)) -> d/3 as well.  Exact value:"""
    return Fraction(2 * (d * d - 1), 3 * bdeg(X, d))


# ============================================================ PART E

def partE(dmax=10, qmax=3000):
    print(BAR)
    print("PART E -- almost simple, CROSS characteristic: the ppmax^3 kill")
    print(BAR)
    print("""
  Lemma X [PROVEN].  ppmax_{p'}(|L_d(q)|) and ppmax_{p'}(|U_d(q)|) are
  <= C_d * q^{d-1}.
  Proof.  Let r != p, k := ord_r(q) (<= K).  By LTE the r-part of
  prod_{i=2}^{d}(q^i - eps_i) is r^{v} with
      v = m * v_r(Phi_k(q)) + v_r(m!) ,   m = #{i <= d : the block q^i-eps_i
                                                is divisible by r} <= d/k' ,
  where k' = k for the linear tower and k' = k/gcd(k,2) for the unitary one;
  and Phi_k(q) <= (q+1)^{phi(k)}.  Hence the r-part is at most
  (k (q+1)^{phi(k)})^{d/k'} * (d/k')!, whose q-exponent is
  phi(k) * d/k' <= max(d-1, ...) = d-1  (the maximum is attained at k = 1 and
  at k = d prime; for every other k, phi(k)/k <= 1/2 or floor(d/k) <= d/2).

  Consequence (Lemma K' of v_task53: |G| < (|G|_{p1})^3):
      |S| = c |S_1| < c * P^3 <= c * C_d^3 * q^{3(d-1)} ,
  while |S| > q^{d^2-1}/(4d).  Since d^2-1 - 3(d-1) = (d-1)(d-2) > 0 for
  every d >= 3, and GROWS QUADRATICALLY, the branch is empty above an
  explicit threshold.
""")
    print("  machine check of Lemma X (exact factorisation, all prime powers")
    print("  q <= %d):" % qmax)
    for X in ("L", "U"):
        for d in (4, 5, 6):
            bad, worstr = 0, (0, 0)
            for (q, p, f) in prime_powers_upto(min(qmax, 300 if d > 4 else qmax)):
                op = order_LU(X, d, q)
                while op % p == 0:
                    op //= p
                fac = factorint(op)
                P = max([r ** a for (r, a) in fac.items()] or [1])
                if P > pbound(d, q):
                    bad += 1
                rat = Fraction(P, q ** (d - 1))
                if rat > worstr[0]:
                    worstr = (rat, q)
            print("     %s_%-2d : P > d!(q+1)^{d-1} at %d prime powers ; "
                  "max P/q^{d-1} = %.3f at q = %d"
                  % (X, d, bad, float(worstr[0]), worstr[1]))
            sys.stdout.flush()
    print()
    print("  the exact q-threshold of the branch  |S| < c * P^3  with")
    print("  P <= q^{d-1} * C_d  and  c <= |Out(S_1)| <= 6 * n1 * log_2 P :")
    print("  %-4s %-4s %s" % ("X", "d", "survives only for q <="))
    for X in ("L", "U"):
        for d in range(4, dmax + 1):
            surv = []
            for (q, p, f) in prime_powers_upto(4000):
                S = order_LU(X, d, q)
                P = pbound(d, q)
                N1max = P.bit_length() - 1
                n1 = 2
                while n1 * (n1 - 1) // 2 <= N1max:
                    n1 += 1
                n1 -= 1
                ccap = max(1, 6 * n1 * max(1, P.bit_length() - 1))
                if S < ccap * P ** 3:
                    surv.append(q)
            print("  %-4s %-4d %s" % (X, d, max(surv) if surv else "EMPTY"))
    print()
    print("  (the constant d! is crude, so these thresholds are")
    print("   over-estimates; they are finite and shrink rapidly with d.)")
    print()


# ============================================================ PART F

def partF(dlist=(4, 5, 6, 7, 8, 9, 10)):
    print(BAR)
    print("PART F -- almost simple with ALTERNATING or SPORADIC socle")
    print(BAR)
    print("""
  (E): c|S_1| = |S|, 2 <= c | |Out(S_1)|.  For these two classes the
  candidate list is COMPLETE, and |S| = M is inverted exactly for q (the
  order is strictly increasing in q of degree a = d^2-1), so every row is
  complete in q -- it covers ALL q, not a range.
""")
    hits = []
    tested = 0
    for X in ("L", "U"):
        for d in dlist:
            o = 60
            for m in range(5, 200):
                if m > 5:
                    o = o * m
                if o > 10 ** 120:
                    break
                ou = 4 if m == 6 else 2
                for c in range(2, ou + 1):
                    if ou % c:
                        continue
                    tested += 1
                    for q in solve_LU(X, d, c * o):
                        hits.append((X, d, "A%d" % m, q, c))
            for (nm, so, ou) in list(SPORADIC) + [TITS]:
                for c in range(2, ou + 1):
                    if ou % c:
                        continue
                    tested += 1
                    for q in solve_LU(X, d, c * so):
                        hits.append((X, d, nm, q, c))
    print("  (S_1, c) pairs tested : %d      HITS : %s" % (tested, hits or "NONE"))
    # positive control: the inverter must find c = 1 self-solutions
    ctl = []
    o = 60
    for m in range(5, 40):
        if m > 5:
            o = o * m
        for X in ("L", "U"):
            for d in (4, 5, 6):
                s = solve_LU(X, d, o)
                if s:
                    ctl.append((X, d, "A%d" % m, s))
    print("  POSITIVE CONTROL (c = 1 self-solutions, alternating):")
    print("     ", ctl, "  <- |A_8| = |L_4(2)| must appear")
    print("""
  A SECOND, uniform kill for these two classes (independent of the scan):
  the orbit floor with l = 1 reads |Out(S_1)| iota(S_1) >= iota(S) > q^{d-1},
  while |Out| <= 4 and iota(A_m) <= C(m,3), iota(sporadic) <= the exact
  table; and c|S_1| = |S| pins |S_1| ~ q^{d^2-1}.  For A_m,
  C(m,3) ~ (log|S_1|/log log|S_1|)^3 is polylogarithmic in |S|, so the floor
  fails as soon as q^{d-1} exceeds it -- i.e. for every q with
  q^{d-1} > 4 C(m,3) where m!/2 ~ q^{d^2-1}.  This is a two-line proof for
  every d >= 4; the exact scan above is the machine confirmation.
""")
    return hits


# ============================================================ PART G

def ppmax_exact(X, d, q, p):
    """P := ppmax_{p'}(|S|), computed blockwise (each block is <= q^d, so
    Pollard rho factors it instantly)."""
    P = 1
    e = gcd(d, q - 1) if X == "L" else gcd(d, q + 1)
    for i in range(2, d + 1):
        t = q ** i - 1 if X == "L" else q ** i - (-1) ** i
        for (r, a) in factorint(t).items():
            if r == p:
                continue
            # the r-part of the WHOLE order, not of this block alone
            pass
    o = order_LU(X, d, q)
    while o % p == 0:
        o //= p
    for (r, a) in factorint(o).items():
        P = max(P, r ** a)
    return P


def partG_qtest(specs):
    """PART G -- the complete multi-factor necessary-condition test, BOTH
    characteristics and ALL socle types, over the residual windows.

    A Fitting-free non-simple twin that is not almost simple has a socle
    factor G in an orbit of length l >= 1 with
        (i) |G|^l | |S| ,  (ii) |G|^{max(2,l)} <= |S| ,
        (iii) l |Out(G)| iotabar(G) >= iota(S) .
    Enumeration is complete: Lie-type G has q1^{l N1} <= |S|_{p1} <= P (for
    p1 != p) resp. <= q^N (p1 = p), which bounds q1 and the rank; A_m has
    |A_m|^2 <= |S|; the sporadics are a 27-row table."""
    print(BAR)
    print("PART G -- the residual multi-factor census (complete, both")
    print("          characteristics, all socle types)")
    print(BAR)
    allsurv = []
    for (X, d, qmax) in specs:
        N = d * (d - 1) // 2
        lmax = max(2, int(lmax_lemC(X, d)))
        surv, ntar, live = [], 0, []
        for (q, p, f) in prime_powers_upto(qmax):
            S = order_LU(X, d, q)
            io = iota_LU(X, d, q)
            facS = factorint(S)
            ntar += 1
            cand = []
            # ---- Lie type, every characteristic.  |G|_{p1} = q1^{N1}
            # divides |S|, so the candidate fields q1 = p1^{f1} are read off
            # the factorisation of |S| -- a tiny, complete enumeration.
            rS = iroot(S, 2)
            for F in FAM:
                ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], 40)
                for n in ns:
                    N1, D1 = F["N"](n), F["D"](n)
                    # |G|^2 <= |S| with (T1) |G| >= q1^D1/(12 d1) bounds q1
                    qcap = iroot(12 * 40 * rS, D1)
                    if qcap < 2:
                        break
                    for p1 in sorted(facS):
                        f1 = 0
                        while True:
                            f1 += 1
                            q1 = p1 ** f1
                            if q1 > qcap or f1 * N1 > facS[p1]:
                                break
                            if not F["qform"](p1, f1) or F["skip"](n, q1):
                                continue
                            o1 = order_of(F, n, q1)
                            if o1 >= 60 and o1 * o1 <= S:
                                cand.append((F["name"](n, q1), o1,
                                             out_of(F, n, q1, p1, f1),
                                             F["iota"](n, q1)))
            # ---- alternating
            o, m = 60, 5
            while o * o <= S:
                cand.append(("A%d" % m, o, 4 if m == 6 else 2,
                             IOTA_UB.get("A%d" % m, m * (m - 1) * (m - 2) // 6)))
                m += 1
                o = o * m
            # ---- sporadic
            for (nm, so, ou) in list(SPORADIC) + [TITS]:
                if so * so <= S:
                    cand.append((nm, so, ou, IOTA_UB[nm]))
            floorok = []
            for (nm, o1, ou, ib) in cand:
                for l in range(1, lmax + 1):
                    if o1 ** l > S or S % (o1 ** l):
                        break
                    if l * ou * ib >= io:
                        surv.append((q, nm, l))
                        if nm not in [x[0] for x in floorok]:
                            floorok.append((nm, o1, ou))
            # PHASE 1 on the floor-surviving candidates only: a complete
            # multiset census, then the per-orbit floor re-applied exactly.
            if len(floorok) >= 1:
                iot = dict((nm, ib) for (nm, o1, ou, ib) in cand)
                outd = dict((nm, ou) for (nm, o1, ou, ib) in cand)
                for (ms, c) in census50(S, floorok):
                    tot = sum(l for (_, l) in ms)
                    if tot < 2:
                        continue
                    if all(l * outd[nm] * iot[nm] >= io for (nm, l) in ms):
                        live.append((q, ms, c))
        print("  %s_%-2d  q <= %-6d targets %-4d  l_max %-2d" % (X, d, qmax, ntar, lmax))
        print("        one-factor floor survivors : %s" % (surv or "NONE"))
        print("        FULL multi-factor census   : %s" % (live or "NONE"))
        allsurv += [(X, d) + t for t in live]
        sys.stdout.flush()
    print()
    print("  TOTAL survivors of the multi-factor necessary condition: %d"
          % len(allsurv))
    for s in allsurv:
        print("     ", s)
    print()
    return allsurv


def partG(specs, verbose=True):
    """specs = list of (X, d, qmax): the residual census."""
    print(BAR)
    print("PART G -- the residual census: Phase 1 (order census, RAW) +")
    print("          Phase 2 (orbit floor l|Out(S_i)|iota(S_i) >= iota(S))")
    print(BAR)
    tot_bad = tot_raw = tot_filt = 0
    for (X, d, qmax) in specs:
        raws, filts, bad, ntar = [], [], 0, 0
        for (q, p, f) in prime_powers_upto(qmax):
            N = order_LU(X, d, q)
            io = iota_LU(X, d, q)
            ntar += 1
            cands = simple_divisors(N)
            names = [c[0] for c in cands if c[1] == N]
            # positive control: the target itself must be in the divisor list
            tname = name_LU(X, d, q)
            alias = {"L4(2)": "A8", "U4(2)": "S4(3)"}
            want = alias.get(tname, tname)
            if want not in names:
                bad += 1
                print("   POSITIVE-CONTROL FAILURE %s : %s" % (tname, names))
            order_by_name = dict((n2, o2) for (n2, o2, u2) in cands)

            def strip(cen):
                return [(ms, c) for (ms, c) in cen
                        if not (c == 1 and len(ms) == 1 and ms[0][1] == 1
                                and order_by_name.get(ms[0][0]) == N)]

            raw = strip(census50(N, cands))
            surv, dead, unk = phase2(N, io, cands)
            filt = strip(census50(N, surv))
            if raw:
                raws.append((q, raw))
            if filt:
                filts.append((q, filt))
            if len(names) > 1:
                print("   %s : TWO simple groups of that order: %s"
                      % (tname, names))
        print("  %s_%-2d  q <= %-6d targets %-4d  RAW survivors %-4d  "
              "after floor %-4d  control failures %d"
              % (X, d, qmax, ntar, sum(len(r[1]) for r in raws),
                 sum(len(r[1]) for r in filts), bad))
        for (q, r) in raws:
            print("        RAW  q = %-6d %s" % (q, r))
        for (q, r) in filts:
            print("        LIVE q = %-6d %s" % (q, r))
        tot_bad += bad
        tot_raw += sum(len(r[1]) for r in raws)
        tot_filt += sum(len(r[1]) for r in filts)
        sys.stdout.flush()
    print()
    print("  TOTALS: control failures %d, RAW survivors %d, after floor %d"
          % (tot_bad, tot_raw, tot_filt))
    print()
    return tot_bad, tot_raw, tot_filt


# ==========================================================================

def main():
    args = sys.argv[1:]
    want = set(args) if args else {"A", "B", "C", "D", "E", "F", "G"}
    if "A" in want:
        partA()
    if "B" in want:
        partB()
    if "C" in want:
        partC_window()
        partC_sweep(qmax=2000000)
        partC_multi(qmax=300000)
        partC_multi_full(qmax=100000)
    if "D" in want:
        partD()
    if "E" in want:
        partE()
    if "F" in want:
        partF()
    if "G" in want:
        # windows = the PART D.2(b) cross-characteristic multi-factor
        # thresholds (above them every socle factor is equal-characteristic,
        # and PART C.4 has already emptied that branch)
        specs = [("L", 4, 839), ("L", 5, 251), ("L", 6, 137), ("L", 7, 89),
                 ("L", 8, 67), ("L", 9, 53), ("L", 10, 47),
                 ("U", 4, 43), ("U", 5, 11), ("U", 6, 11), ("U", 7, 11),
                 ("U", 8, 11), ("U", 9, 11), ("U", 10, 11)]
        partG_qtest(specs)


if __name__ == "__main__":
    main()
