#!/usr/bin/env python3
# rank1_twins -- Fitting-free NON-SIMPLE twins of the remaining RANK-1 Lie
# targets:
#
#       S = U_3(q) = PSU(3,q),   q >= 3        (U_3(2) is not simple)
#       S = Sz(q)  = 2B_2(q),    q = 2^(2m+1) >= 8
#       S = R(q)   = 2G_2(q),    q = 3^(2m+1) >= 27
#
# Pipeline is the l2_twins (L_2) PILOT, applied per family:
#   Phase 1  order census   : every multiset {(S_i,l_i)} of non-abelian finite
#                             simple groups with prod|S_i|^{l_i} * c = |S| and
#                             c | prod_i(|Out(S_i)|^{l_i} * l_i!).
#   Phase 2  orbit floor    : l_O * |Out(S_i)| * iota(S_i) >= iota(S).
#   Uniform steps           : --uniform (one orbit, then l = 1),
#                             --lemK    (Lemma K analogues),
#                             --rank    (Lemma R: which Lie types can be S_1),
#                             --eqchar  (the equal-characteristic half of the
#                                        residual l = 1 branch, decided
#                                        EXACTLY and completely in q1),
#                             --sub     (the residual l = 1 equation
#                                        c*|S_1| = |S|, scanned past the
#                                        census range, + negative control).
#
# The CFSG simple-order enumerator and the multiset census are IMPORTED from
# sporadic_twins.py; the fast factoriser, the generic iota upper
# bounds and prime_powers_upto are IMPORTED from l2_twins.py.
# Exact integer arithmetic throughout.
#
# Usage:
#   python3 rank1_twins.py --uniform
#   python3 rank1_twins.py --lemK
#   python3 rank1_twins.py --rank
#   python3 rank1_twins.py --census U3 3000
#   python3 rank1_twins.py --census Sz 31
#   python3 rank1_twins.py --census Ree 21
#   python3 rank1_twins.py --eqchar 121
#   python3 rank1_twins.py --sub 100000

import sys
import os
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sporadic_twins as T50
from sporadic_twins import (simple_divisors, census, pow_divides,
                                     SPORADIC, TITS, gcd)
import l2_twins as T51
from l2_twins import (factorint, iota_ub_generic, prime_powers_upto,
                               is_prime_power)

T50.factorint = factorint


# --------------------------------------------------------------------------
# A factorisation cache seeded with the ALGEBRAIC splittings of the three
# target orders.  Without it, Pollard rho has to attack q^2+1 / q^2-q+1
# directly at q ~ 10^9, which is what limits the reachable range; with it the
# Sz and Ree families can be scanned to q ~ 10^9 in seconds.
#     q = 2^f, f odd :  q^2 + 1   = (q + 2^((f+1)/2) + 1)(q - 2^((f+1)/2) + 1)
#     q = 3^f, f odd :  q^2 - q+1 = (q + 3^((f+1)/2) + 1)(q - 3^((f+1)/2) + 1)
# (both are the standard factorisations of the Zsygmondy blocks of 2B_2, 2G_2)
# --------------------------------------------------------------------------

_FCACHE = {}


def _merge(dst, src):
    for p, e in src.items():
        dst[p] = dst.get(p, 0) + e
    return dst


def fact_of_parts(parts):
    """factorisation of prod(parts), factoring each part separately"""
    f = {}
    for x in parts:
        if x == 1:
            continue
        _merge(f, factorint(x))
    return f


def cached_factorint(n):
    if n in _FCACHE:
        return dict(_FCACHE[n])
    return factorint(n)


T50.factorint = cached_factorint


# --------------------------------------------------------------------------
# The three families.
#
# order, |Out|, iota, and the ALGEBRAIC part-decomposition of |S| used both
# for the fast factorisation and for the Lemma K proofs.
# --------------------------------------------------------------------------

def U3_order(q):
    e = gcd(3, q + 1)
    return q ** 3 * (q * q - 1) * (q ** 3 + 1) // e


def Sz_order(q):
    return q * q * (q - 1) * (q * q + 1)


def Ree_order(q):
    return q ** 3 * (q - 1) * (q ** 3 + 1)


def U3_out(q, p, f):
    return gcd(3, q + 1) * 2 * f


def Sz_out(q, p, f):
    return f


def Ree_out(q, p, f):
    return f


def U3_iota(q):
    return q ** 3 + 1


def Sz_iota(q):
    return q * q + 1


def Ree_iota(q):
    return q ** 3 + 1


def U3_name(q):
    return "U3(%d)" % q


def Sz_name(q):
    return "Sz(%d)" % q


def Ree_name(q):
    return "R(%d)" % q


def U3_targets(qmax):
    # prime_powers_upto starts at 4; U_3(3) is simple and must be included
    return [(3, 3, 1)] + [(q, p, f) for (q, p, f)
                          in prime_powers_upto(max(qmax, 4)) if q <= qmax]


def Sz_targets(fmax):
    return [(2 ** f, 2, f) for f in range(3, fmax + 1, 2)]


def Ree_targets(fmax):
    return [(3 ** f, 3, f) for f in range(3, fmax + 1, 2)]


def U3_split(q):
    e = gcd(3, q + 1)
    # q^3 * (q-1) * (q+1) * (q+1) * (q^2-q+1) / e ; e | (q+1) and e | 3 so
    # divide the *second* (q+1) by e when e = 3 -- exactness asserted below.
    parts = [q ** 3, q - 1, q + 1, (q + 1), (q * q - q + 1)]
    if e == 3:
        parts[3] = (q + 1) // 3 * 3  # keep integrality; divide after merging
    f = fact_of_parts(parts)
    if e == 3:
        f[3] -= 1
        if f[3] == 0:
            del f[3]
    prod = 1
    for pr, ex in f.items():
        prod *= pr ** ex
    assert prod == U3_order(q), (q, prod, U3_order(q))
    return f


def Sz_split(q, f_exp):
    s = 2 ** ((f_exp + 1) // 2)
    parts = [q * q, q - 1, q + s + 1, q - s + 1]
    assert (q + s + 1) * (q - s + 1) == q * q + 1
    f = fact_of_parts(parts)
    prod = 1
    for pr, ex in f.items():
        prod *= pr ** ex
    assert prod == Sz_order(q)
    return f


def Ree_split(q, f_exp):
    s = 3 ** ((f_exp + 1) // 2)
    assert (q + s + 1) * (q - s + 1) == q * q - q + 1
    parts = [q ** 3, q - 1, q + 1, q + s + 1, q - s + 1]
    f = fact_of_parts(parts)
    prod = 1
    for pr, ex in f.items():
        prod *= pr ** ex
    assert prod == Ree_order(q)
    return f


FAM = {
    "U3":  dict(order=U3_order, out=U3_out, iota=U3_iota, name=U3_name,
                targets=U3_targets,
                split=lambda q, p, f: U3_split(q),
                # log_q |S| and log_q iota, as exact rationals in the leading
                # term:  |S| ~ q^8,  iota ~ q^3
                a=8, b=3,
                label="U_3(q) = PSU(3,q), q >= 3"),
    "Sz":  dict(order=Sz_order, out=Sz_out, iota=Sz_iota, name=Sz_name,
                targets=Sz_targets,
                split=lambda q, p, f: Sz_split(q, f),
                a=5, b=2,
                label="Sz(q) = 2B_2(q), q = 2^(2m+1) >= 8"),
    "Ree": dict(order=Ree_order, out=Ree_out, iota=Ree_iota, name=Ree_name,
                targets=Ree_targets,
                split=lambda q, p, f: Ree_split(q, f),
                a=7, b=3,
                label="R(q) = 2G_2(q), q = 3^(2m+1) >= 27"),
}


def ppmax(fac, skip_prime=None):
    """largest prime power p^e in a factorisation dict (optionally skipping
    one prime -- used for the CROSS-characteristic bound)"""
    best = 1
    for p, e in fac.items():
        if p == skip_prime:
            continue
        v = p ** e
        if v > best:
            best = v
    return best


# ==========================================================================
# --uniform :  the two uniform structure steps, checked EXACTLY (integer
#              arithmetic, no logs) on every target in a wide range.
#
#   (STEP 2)  k >= 2 socle orbits is impossible:  iota(S)^3 > |S|.
#   (STEP 3)  an orbit of length l >= 2 is impossible:
#                 ceil(iota(S)/l)^(3l/2) > |S|   for every 2 <= l <= L,
#             where L = floor(log|S| / log 60) is the absolute cap coming
#             from |S_1|^l <= |S|, |S_1| >= 60.
#             (the exponent 3l/2 is halved-integer; we compare squares.)
# ==========================================================================

def step_checks(fam, qs):
    d = FAM[fam]
    bad2, bad3 = [], []
    worst2 = None
    for (q, p, f) in qs:
        N = d["order"](q)
        iS = d["iota"](q)
        # STEP 2 : two orbits each contribute >= iota^{3/2}, total >= iota^3
        if iS ** 3 <= N:
            bad2.append(q)
        r = Fraction(iS ** 3, N)
        if worst2 is None or r < worst2[1]:
            worst2 = (q, r)
        # STEP 3
        L = 1
        while 60 ** (L + 1) <= N:
            L += 1
        for l in range(2, L + 1):
            # ((iS/l)^{3l/2})^2 = (iS/l)^{3l} > N^2   <=>   iS^{3l} > N^2 l^{3l}
            if iS ** (3 * l) <= N * N * l ** (3 * l):
                bad3.append((q, l))
    return bad2, bad3, worst2


def cmd_uniform():
    print("# rank1_twins --uniform : STEP 2 (one socle orbit) and STEP 3 (l = 1)")
    print("# checked EXACTLY (integer arithmetic) on every target in range.")
    print("#")
    print("# STEP 2 needs   iota(S)^3 > |S|                     [k >= 2 dies]")
    print("# STEP 3 needs   (iota(S)/l)^{3l/2} > |S|, l >= 2    [l >= 2 dies]")
    print("# Both are consequences of the orbit floor (Lemma TO'-0 + Lemma F)")
    print("# together with Lemma C  (|Out(G)|*iota(G) <= |G|^{2/3}), which")
    print("# gives |S_1| >= (iota(S)/l_O)^{3/2} for every orbit.")
    print()
    ranges = {"U3": U3_targets(20000),
              "Sz": Sz_targets(61),
              "Ree": Ree_targets(41)}
    for fam in ("U3", "Sz", "Ree"):
        qs = ranges[fam]
        bad2, bad3, worst2 = step_checks(fam, qs)
        d = FAM[fam]
        print("=" * 74)
        print("FAMILY %s   (%s)" % (fam, d["label"]))
        print("  targets checked            : %d   (q from %d to %d)"
              % (len(qs), qs[0][0], qs[-1][0]))
        print("  STEP 2  iota^3 > |S| fails : %s"
              % (bad2 if bad2 else "NEVER  -> at most ONE socle orbit"))
        print("          tightest ratio iota^3/|S| = %s  at q = %d  (%.4f)"
              % (worst2[1], worst2[0], float(worst2[1])))
        print("  STEP 3  (iota/l)^{3l/2} > |S| fails at (q,l) : %s"
              % (bad3 if bad3 else "NEVER  -> the orbit has LENGTH 1"))
        if bad3:
            print("          -> those (q,l) must be closed by the census")
    print()
    print("## Asymptotic half (the proof that covers q beyond the ranges above)")
    print("##   write |S| = q^a(1+o(1)), iota(S) = q^b(1+o(1)):")
    print("##     U3 : a = 8, b = 3      Sz : a = 5, b = 2      Ree: a = 7, b = 3")
    print("##   STEP 2 needs 3b > a :  9>8 ok,  6>5 ok,  9>7 ok  (all strict)")
    print("##   STEP 3 needs (3l/2)(b - log_q l) > a for all l >= 2, and")
    print("##   l <= a*log q/log 60, so log_q l -> 0; the binding case is l = 2:")
    print("##     3b - 3log_q 2 > a  <=>  log_q 2 < (3b-a)/3")
    for fam, thr in (("U3", Fraction(1, 3)), ("Sz", Fraction(1, 3)),
                     ("Ree", Fraction(2, 3))):
        # smallest q with log_q 2 < thr, i.e. 2^den < q^num
        num, den = thr.numerator, thr.denominator
        q0 = 2
        while not (2 ** den < q0 ** num):
            q0 += 1
        print("##     %-4s : threshold log_q 2 < %s  <=>  q >= %d"
              % (fam, thr, q0))
    print("##   so l = 1 is PROVEN for all q in Sz (q>=8, exact check above),")
    print("##   all q in Ree (q>=27), and all q >= 9 in U3; the U3 residue")
    print("##   q in {3,4,5,7,8} is covered by the census.")


# ==========================================================================
# --lemK : the Lemma K analogues (largest prime power dividing |S|), and the
#          CROSS-characteristic refinement ppmax_{p'} which is what actually
#          kills things.
#
#   Lemma K-U3 :  ppmax(|U_3(q)|)   <= max(q^3, 2(q+1)^2)
#                 ppmax_{p'}(|U_3(q)|) <= 2(q+1)^2
#   Lemma K-Sz :  ppmax(|Sz(q)|)    <= q^2+1   ( = iota(S) )
#                 ppmax_{2'}(|Sz(q)|) <= q^2+1
#   Lemma K-Ree:  ppmax(|R(q)|)     <= q^3
#                 ppmax_{3'}(|R(q)|) <= q^2-q+1
# ==========================================================================

KBOUND = {
    "U3":  (lambda q: max(q ** 3, 2 * (q + 1) ** 2), lambda q: 2 * (q + 1) ** 2),
    "Sz":  (lambda q: q * q + 1, lambda q: q * q + 1),
    "Ree": (lambda q: q ** 3, lambda q: q * q - q + 1),
}


def cmd_lemK():
    print("# rank1_twins --lemK : Lemma K analogues, verified on every target")
    print("#   col 1 : ppmax(|S|)          vs the claimed bound")
    print("#   col 2 : ppmax_{p'}(|S|)     vs the claimed bound  (p = char S)")
    print()
    ranges = {"U3": U3_targets(3000),
              "Sz": Sz_targets(41),
              "Ree": Ree_targets(27)}
    for fam in ("U3", "Sz", "Ree"):
        d = FAM[fam]
        bnd, bndp = KBOUND[fam]
        bad, badp = [], []
        tight, tightp = None, None
        for (q, p, f) in ranges[fam]:
            fac = d["split"](q, p, f)
            m = ppmax(fac)
            mp = ppmax(fac, skip_prime=p)
            if m > bnd(q):
                bad.append((q, m, bnd(q)))
            if mp > bndp(q):
                badp.append((q, mp, bndp(q)))
            r = Fraction(m, bnd(q))
            if tight is None or r > tight[1]:
                tight = (q, r)
            rp = Fraction(mp, bndp(q))
            if tightp is None or rp > tightp[1]:
                tightp = (q, rp)
        print("=" * 74)
        print("FAMILY %s : %d targets, q up to %d"
              % (fam, len(ranges[fam]), ranges[fam][-1][0]))
        print("  ppmax  violations      : %s" % (bad if bad else "NONE"))
        print("     tightest ratio      : %.4f at q = %d"
              % (float(tight[1]), tight[0]))
        print("  ppmax_{p'} violations  : %s" % (badp if badp else "NONE"))
        print("     tightest ratio      : %.4f at q = %d"
              % (float(tightp[1]), tightp[0]))
    print()
    print("## PROOFS (uniform in q; the runs above are cross-checks)")
    print("## U3: |S| = q^3 (q-1)(q+1)^2 (q^2-q+1)/e, e = gcd(3,q+1).")
    print("##     gcd(q-1,q+1) | 2, gcd(q-1,q^2-q+1) = 1, gcd(q+1,q^2-q+1) | 3,")
    print("##     and the 3-part of q^2-q+1 is exactly 3 when 3 | q+1 (and is")
    print("##     cancelled by e).  So for r odd, r != p, r != 3 the r-part")
    print("##     lies in a single block and is <= (q+1)^2.  For r = 3 with")
    print("##     3 | q+1 it is |q+1|_3^2 <= (q+1)^2.  For r = 2 (q odd)")
    print("##     it is |q-1|_2 |q+1|_2^2 with min(|q-1|_2,|q+1|_2) = 2, hence")
    print("##     <= 2(q+1)^2.  The p-part is q^3.")
    print("## Sz: |S| = q^2 (q-1)(q^2+1), q = 2^f; q-1 and q^2+1 are odd and")
    print("##     gcd(q-1, q^2+1) = gcd(q-1,2) = 1, so the three blocks are")
    print("##     PAIRWISE COPRIME and ppmax <= max(q^2, q-1, q^2+1) = q^2+1.")
    print("## Ree:|S| = q^3 (q-1)(q+1)(q^2-q+1), q = 3^f.  q^2-q+1 is odd and")
    print("##     coprime to (q-1)(q+1) (it is 3 mod q+1 and 1 mod q-1, and")
    print("##     3 does not divide it since 3 | q).  min(|q-1|_2,|q+1|_2) = 2,")
    print("##     so the 2-part is <= 2(q+1); the p-part is q^3; every odd")
    print("##     r != 3 has r-part <= max(q+1, q^2-q+1) = q^2-q+1.")


# ==========================================================================
# --rank : Lemma R.  With l = 1 (Step 3) the socle is a single simple S_1 and
#          c = |S|/|S_1| divides |Out(S_1)|.  If S_1 is of Lie type over
#          F_{q1} in characteristic p1 write
#                |S_1| = q1^N * M,     M = prod_i (q1^{d_i} - eps_i)/g,
#          so   q1^N = |S_1|_{p1}   and   M < q1^D,  D = sum d_i.
#          Then
#             (R1)  q1^N  = |S_1|_{p1}  <=  ppmax_{(p1)}(|S|)
#             (R2)  q1^{N+D} > |S_1| = |S|/c
#          Dividing:  q1^D > (|S|/c) / q1^N >= (|S|/c)/ppmax, so
#             D/N > log(|S|/(c*ppmax)) / log(ppmax).
#          Every Lie type has a FIXED rational D/N, so this eliminates all
#          types with D/N below the threshold -- and D/N -> 1 as the rank
#          grows, so the surviving list is always FINITE.
#
#          In the CROSS-characteristic case ppmax must be replaced by the much
#          smaller ppmax_{p'}, which for U3 and Ree is decisive on its own:
#             |S|/c <= |S_1| < (|S_1|_{p1})^3 <= ppmax_{p'}^3
#          (using D <= 2N, valid for every Lie type -- see LIE_TYPES).
# ==========================================================================

# (name, N, D) for every family of simple groups of Lie type.
# N = number of positive roots of the ambient (twisted) system = exponent of
#     the p-part;  D = sum of the degrees appearing in the order formula.
def lie_types(rankmax=12):
    T = []
    for n in range(2, rankmax + 2):                     # A_{n-1} = L_n(q)
        T.append(("L%d" % n, n * (n - 1) // 2, n * (n + 1) // 2 - 1))
    for n in range(3, rankmax + 2):                     # 2A_{n-1} = U_n(q)
        T.append(("U%d" % n, n * (n - 1) // 2, n * (n + 1) // 2 - 1))
    for r in range(2, rankmax + 1):                     # B_r / C_r
        T.append(("S%d/O%d" % (2 * r, 2 * r + 1), r * r, r * (r + 1)))
    for r in range(4, rankmax + 1):                     # D_r
        T.append(("O%d+" % (2 * r), r * (r - 1), r * r))
    for r in range(4, rankmax + 1):                     # 2D_r
        T.append(("O%d-" % (2 * r), r * (r - 1), r * r))
    T += [("G2", 6, 8), ("F4", 24, 28), ("E6", 36, 42), ("2E6", 36, 42),
          ("E7", 63, 70), ("E8", 120, 128), ("3D4", 12, 16),
          ("Sz", 2, 3), ("R", 3, 4), ("2F4", 12, 14)]
    return T


def cmd_rank():
    print("# rank1_twins --rank : Lemma R.  Which Lie types can be the socle S_1")
    print("#                   of the (length-1) socle orbit?")
    print()
    LT = lie_types()
    # sanity: D <= 2N for every type (this is Lemma K', |G| < (|G|_p)^3)
    bad = [t for t in LT if t[2] > 2 * t[1]]
    print("Lemma K'  (D <= 2N, i.e. |G| < (|G|_p)^3 for every Lie type):")
    print("   violations: %s" % (bad if bad else "NONE (extremal: A_1, D=2N)"))
    print()
    ranges = {"U3": U3_targets(2000), "Sz": Sz_targets(41),
              "Ree": Ree_targets(27)}
    for fam in ("U3", "Sz", "Ree"):
        d = FAM[fam]
        print("=" * 74)
        print("FAMILY %s" % fam)
        # ---- cross-characteristic, Lie socle : |S|/c < ppmax_{p'}^3
        _, bndp = KBOUND[fam]
        killq = None
        rows = []
        for (q, p, f) in ranges[fam]:
            N = d["order"](q)
            # |Out(S_1)| = d1*f1*g1 for a Lie S_1: g1 <= 6 (D_4), and
            # d1 = gcd(n, q1 -+ 1) <= n <= 13 for rank <= 12, so
            # |Out(S_1)| <= 78*f1 <= 78*log2(q1) and q1 <= q1^N <= ppmax_{p'}.
            cap = 78 * max(1, bndp(q).bit_length())
            ok = (bndp(q) ** 3) * cap < N          # contradiction => killed
            rows.append((q, ok))
            if ok and killq is None:
                killq = q
            if not ok:
                killq = None
        allok = all(r[1] for r in rows)
        print("  CROSS-characteristic Lie socle  (|S|/c < ppmax_{p'}^3, ")
        print("   c <= |Out(S_1)| <= 78*log2(ppmax_{p'})):")
        if allok:
            print("     CONTRADICTION for EVERY q in range -> branch EMPTY,")
            print("     q from %d to %d" % (rows[0][0], rows[-1][0]))
        elif killq is not None:
            print("     CONTRADICTION for all q >= %d in range;" % killq)
            print("     survives for q < %d  (-> census)" % killq)
        else:
            print("     NO uniform contradiction in this range"
                  " (-> census + --sub)")
        # ---- rank forcing via D/N
        print("  Lemma R threshold  D/N > log(|S|/(c*ppmax))/log(ppmax):")
        for (q, p, f) in ranges[fam][:1] + ranges[fam][len(ranges[fam])//2:
                                                      len(ranges[fam])//2+1] \
                + ranges[fam][-1:]:
            N = d["order"](q)
            pm = KBOUND[fam][0](q)
            cap = 78 * max(1, pm.bit_length())
            # threshold as a real number, computed from exact integers
            import math
            thr = math.log(N / cap / pm) / math.log(pm)
            surv = [t[0] for t in LT if Fraction(t[2], t[1]) > thr]
            surv = surv + ["L2"]
            print("     q = %-14d threshold %.4f   surviving types: %s"
                  % (q, thr, ", ".join(sorted(set(surv)))))
    print()
    print("## NOTE.  L2 (= A_1) has (N,D) = (1,2), D/N = 2, the maximum, so it")
    print("## always survives Lemma R -- exactly as in the L_2 pilot, where the")
    print("## residual branch was also an L_2(q1) socle.  Lemma R is a RANK")
    print("## bound, not a kill; the kill is the exact equation in --sub.")


# ==========================================================================
# --eqchar : the EQUAL-characteristic half of the residual l = 1 branch,
#            uniform in q.
#
#   S_1 of Lie type over F_{q1}, char p1 = p = char S.  Then
#        q1^N = |S_1|_p = |S|_p / c_p,        c_p = |c|_p,
#   and, since |S_1| = q1^N * prod_i (q1^{d_i} - eps_i)/g with
#        0.288 < prod_i (1 - q1^{-d_i}) <= 1     and    1 <= g <= 16,
#        |S_1| in [ 0.288 * q1^{N+D}/16 , q1^{N+D} ].
#   With |S_1| = |S|/c this is an EXACT WINDOW on q1^{N+D}:
#        q1^{N+D} >= |S|/c        and       288 * q1^{N+D} * c <= 16000 * |S| .
#   Both q1 (a p-power, N-th root of |S|_p/c_p) and the window are exact
#   integer conditions, so this branch can be decided outright per (q, type, c).
# ==========================================================================

def cmd_eqchar(fmax=None):
    print("# rank1_twins --eqchar : the EQUAL-characteristic half of the")
    print("#   residual l = 1 branch  c*|S_1| = |S| ,  2 <= c | |Out(S_1)| ,")
    print("#   decided EXACTLY (S_1 of Lie type in the DEFINING characteristic")
    print("#   p of the target).  No factorisation of |S| is needed here --")
    print("#   only |S| itself -- so this branch runs FAR past the census.")
    print("#   Completeness in q1: q1 = p^f1 with f1 <= (p-exponent of |S|),")
    print("#   because |S_1|_p = q1^N divides |S|_p; all f1 in that range and")
    print("#   all Lie types of rank <= 6 over F_{q1} are enumerated.")
    print()
    ranges = {"U3": [(p ** f, p, f) for (p, f) in
                     [(pp, ff) for pp in (2, 3, 5, 7, 11, 13)
                      for ff in range(1, 61)]],
              "Sz": Sz_targets(fmax or 301),
              "Ree": Ree_targets(fmax or 201)}
    pexp = {"U3": 3, "Sz": 2, "Ree": 3}
    for fam in ("U3", "Sz", "Ree"):
        d = FAM[fam]
        qs = sorted(set(ranges[fam]))
        if fam == "U3":
            qs = [t for t in qs if t[0] >= 3]   # U_3(2) is not simple
        hits = []
        nq1 = 0
        ctrl = 0
        ctrlnm = set()
        for (q, p, f) in qs:
            if fam == "U3" and q < 3:
                continue
            NS = d["order"](q)
            for f1 in range(1, pexp[fam] * f + 1):
                q1 = p ** f1
                nq1 += 1
                for (nm, o, u) in lie_over(q1, p, f1, rankmax=6, cap=NS):
                    if o <= 1 or NS % o:
                        continue
                    c = NS // o
                    if c == 1:
                        ctrl += 1
                        ctrlnm.add(nm)
                    if c >= 2 and u % c == 0:
                        hits.append((q, nm, c))
        print("=" * 74)
        print("FAMILY %s : %d targets (q up to %d), %d (target, q1) pairs"
              % (fam, len(qs), qs[-1][0], nq1))
        print("  POSITIVE CONTROL: the c = 1 self-solution S_1 = S must be")
        print("    found for every target: %d found / %d targets, names %s : %s"
              % (ctrl, len(qs), sorted(ctrlnm)[:3],
                 "PASS" if ctrl == len(qs) else "*** FAIL ***"))
        print("  EQUAL-CHARACTERISTIC hits : %d %s"
              % (len(hits), hits if hits else "-> branch EMPTY, uniformly"))


# ==========================================================================
# --census : Phase 1 + Phase 2 for every target in the range.
# ==========================================================================

def cmd_census(fam, lim, raw=False):
    d = FAM[fam]
    qs = d["targets"](lim)
    print("# rank1_twins --census %s : Fitting-free NON-SIMPLE twins" % fam)
    print("# %s" % d["label"])
    print("# %d targets, q from %d to %d" % (len(qs), qs[0][0], qs[-1][0]))
    print()
    stats = dict(empty=0, killed=0, live=0)
    live, ctrl_fail, unknown = [], [], set()
    rows_out = []
    for (q, p, f) in qs:
        N = d["order"](q)
        iS = d["iota"](q)
        _FCACHE[N] = d["split"](q, p, f)
        cands = simple_divisors(N)
        # POSITIVE CONTROL: exactly one simple group of order |S| (this
        # re-verifies, per target, the CFSG order-uniqueness input).
        same = [nm for (nm, o, u) in cands if o == N]
        if len(same) != 1 or same[0] != d["name"](q):
            ctrl_fail.append((q, same))
        # Phase-2 prefilter
        surv, dead = [], []
        for (nm, o, u) in cands:
            iv = iota_ub_generic(nm)
            if iv is None:
                unknown.add(nm)
                surv.append((nm, o, u))
                continue
            lmin = -(-iS // (u * iv))
            if pow_divides(o, lmin, N):
                surv.append((nm, o, u))
            else:
                dead.append(nm)
        umap = dict((x[0], x[2]) for x in cands)
        if raw:
            rawc = census(N, cands, maxfac=64)
            rawns = [(ch, c) for (ch, c) in rawc
                     if sum(l for (_, l) in ch) >= 2 or c > 1]
            if rawns:
                print("RAW q=%-12d iota=%-14d unfiltered non-simple census: %d"
                      % (q, iS, len(rawns)))
                for (ch, c) in rawns:
                    fl = min(l * umap[nm] * (iota_ub_generic(nm) or 10 ** 60)
                             for (nm, l) in ch)
                    print("      %-52s c=%-10d floor=%d"
                          % (" x ".join("%s^%d" % (nm, l) if l > 1 else nm
                                        for (nm, l) in ch), c, fl))
        sols = census(N, surv, maxfac=64)
        nonsimple = [(ch, c) for (ch, c) in sols
                     if sum(l for (_, l) in ch) >= 2 or c > 1]
        if not nonsimple:
            stats["empty"] += 1
            continue
        rr = []
        for (ch, c) in nonsimple:
            fl = min(l * umap[nm] * (iota_ub_generic(nm) or 10 ** 60)
                     for (nm, l) in ch)
            socle = " x ".join("%s^%d" % (nm, l) if l > 1 else nm
                               for (nm, l) in ch)
            if fl < iS:
                stats["killed"] += 1
                v = "KILLED orbit-floor (%d < %d)" % (fl, iS)
            else:
                stats["live"] += 1
                live.append((q, socle, c))
                v = "*** LIVE ***"
            rr.append("      SOCLE %-52s c=%-10d %s" % (socle, c, v))
        rows_out.append((q, N, iS, len(cands), len(dead), rr))
        sys.stdout.flush()
    print("## rows with a NON-EMPTY non-simple census (all others: empty)")
    for (q, N, iS, nc, nd, rr) in rows_out:
        print("q = %-14d |S| = %-26d iota = %-14d simple divisors %d (%d dead)"
              % (q, N, iS, nc, nd))
        for r in rr:
            print(r)
    if not rows_out:
        print("   (none)")
    print()
    print("## SUMMARY  family %s" % fam)
    print("   positive control (|S| a simple order, uniquely, = %s) : %s"
          % (fam, "PASS, all %d targets" % len(qs) if not ctrl_fail
             else "FAIL %s" % ctrl_fail))
    print("   targets with EMPTY non-simple census : %d / %d"
          % (stats["empty"], len(qs)))
    print("   candidates killed by the orbit floor : %d" % stats["killed"])
    print("   *** LIVE survivors ***               : %d" % stats["live"])
    for (q, socle, c) in live:
        print("      q = %d :  Soc = %s , c = %d" % (q, socle, c))
    if unknown:
        print("   NOTE: no iota bound for: %s" % ", ".join(sorted(unknown)))


# ==========================================================================
# --sub : the residual l = 1 equation  c * |S_1| = |S|,  2 <= c | |Out(S_1)|,
#         scanned FAR past the census range by inverting the target order.
# ==========================================================================

def _iroot(n, k):
    """exact integer k-th root, integer Newton, NO float anywhere"""
    if n < 2:
        return n
    x = 1 << ((n.bit_length() + k - 1) // k)
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


def solve_U3(M):
    """all prime powers q >= 3 with |U_3(q)| = M"""
    out = []
    for e in (1, 3):
        v = M * e            # = q^3(q^2-1)(q^3+1) ~ q^8
        r = _iroot(v, 8)
        for q in range(max(3, r - 3), r + 4):
            if q ** 3 * (q * q - 1) * (q ** 3 + 1) != v:
                continue
            if gcd(3, q + 1) != e or not is_prime_power(q):
                continue
            if q == 2:
                continue
            out.append(q)
    return sorted(set(out))


def solve_Sz(M):
    r = _iroot(M, 5)
    for q in range(max(8, r - 3), r + 4):
        if q * q * (q - 1) * (q * q + 1) == M:
            f = q.bit_length() - 1
            if 2 ** f == q and f % 2 == 1 and f >= 3:
                return [q]
    return []


def solve_Ree(M):
    r = _iroot(M, 7)
    for q in range(max(27, r - 3), r + 4):
        if q ** 3 * (q - 1) * (q ** 3 + 1) == M:
            f, t = 0, q
            while t % 3 == 0:
                t //= 3
                f += 1
            if t == 1 and f % 2 == 1 and f >= 3:
                return [q]
    return []


SOLVE = {"U3": solve_U3, "Sz": solve_Sz, "Ree": solve_Ree}


def lie_over(q1, p1, f1, rankmax=6, cap=None):
    """(name, |S_1|, |Out(S_1)|) for every simple group of Lie type over the
    single field F_{q1}, rank <= rankmax; entries with order > cap dropped."""
    out = []
    for t in _lie_over_raw(q1, p1, f1, rankmax):
        if cap is None or t[1] <= cap:
            out.append(t)
    return out


def _lie_over_raw(q1, p1, f1, rankmax):
    return socle_candidates(None, rankmax=rankmax, single=(q1, p1, f1))


def socle_candidates(q1max, rankmax=6, single=None):
    """(name, |S_1|, |Out(S_1)|) for every simple group of Lie type over
    F_{q1}, q1 <= q1max, rank <= rankmax, plus all A_m with |A_m| <= 10^80
    and all 27 sporadics + Tits.  With `single = (q1,p1,f1)` only that one
    field is used and the alternating/sporadic tail is omitted."""
    out = []
    if single is not None:
        PP = [single]
    else:
        PP = sorted(set(prime_powers_upto(q1max) + [(2, 2, 1), (3, 3, 1)]))
    for (q1, p1, f1) in PP:
        for n in range(2, rankmax + 2):
            o = q1 ** (n * (n - 1) // 2)
            for i in range(2, n + 1):
                o *= q1 ** i - 1
            g = gcd(n, q1 - 1)
            o //= g
            if not (n == 2 and q1 in (2, 3)):
                out.append(("L%d(%d)" % (n, q1), o,
                            g * f1 * (2 if n >= 3 else 1)))
        for n in range(3, rankmax + 2):
            o = q1 ** (n * (n - 1) // 2)
            for i in range(2, n + 1):
                o *= q1 ** i - (-1) ** i
            g = gcd(n, q1 + 1)
            o //= g
            if not (n == 3 and q1 == 2):
                out.append(("U%d(%d)" % (n, q1), o, g * 2 * f1))
        for r in range(2, rankmax + 1):
            o = q1 ** (r * r)
            for i in range(1, r + 1):
                o *= q1 ** (2 * i) - 1
            g = gcd(2, q1 - 1)
            o //= g
            if not (r == 2 and q1 == 2):
                out.append(("S%d(%d)" % (2 * r, q1), o, g * f1 * 2))
                if q1 % 2 == 1 and r >= 3:
                    out.append(("O%d(%d)" % (2 * r + 1, q1), o, g * f1))
        for r in range(4, rankmax + 1):
            o = q1 ** (r * (r - 1)) * (q1 ** r - 1)
            for i in range(1, r):
                o *= q1 ** (2 * i) - 1
            g = gcd(4, q1 ** r - 1)
            out.append(("O%d+(%d)" % (2 * r, q1), o // g,
                        g * f1 * (6 if r == 4 else 2)))
            o = q1 ** (r * (r - 1)) * (q1 ** r + 1)
            for i in range(1, r):
                o *= q1 ** (2 * i) - 1
            g = gcd(4, q1 ** r + 1)
            out.append(("O%d-(%d)" % (2 * r, q1), o // g, g * 2 * f1))
        if q1 >= 3:
            out.append(("G2(%d)" % q1, q1 ** 6 * (q1 ** 6 - 1) * (q1 ** 2 - 1),
                        f1 * 2))
        out.append(("3D4(%d)" % q1, q1 ** 12 * (q1 ** 8 + q1 ** 4 + 1) *
                    (q1 ** 6 - 1) * (q1 ** 2 - 1), 3 * f1))
        out.append(("F4(%d)" % q1, q1 ** 24 * (q1 ** 12 - 1) * (q1 ** 8 - 1) *
                    (q1 ** 6 - 1) * (q1 ** 2 - 1), f1 * 2))
        if p1 == 2 and f1 % 2 == 1 and f1 >= 3:
            out.append(("Sz(%d)" % q1, q1 * q1 * (q1 - 1) * (q1 * q1 + 1), f1))
            out.append(("2F4(%d)" % q1, q1 ** 12 * (q1 ** 6 + 1) *
                        (q1 ** 4 - 1) * (q1 ** 3 + 1) * (q1 - 1), f1))
        if p1 == 3 and f1 % 2 == 1 and f1 >= 3:
            out.append(("R(%d)" % q1, q1 ** 3 * (q1 - 1) * (q1 ** 3 + 1), f1))
    if single is not None:
        return out
    fac = 1
    for m in range(2, 120):
        fac *= m
        if m < 5:
            continue
        o = fac // 2
        if o > 10 ** 80:
            break
        out.append(("A%d" % m, o, 4 if m == 6 else 2))
    out += [(nm, o, u) for (nm, o, u) in SPORADIC] + [TITS]
    return out


def cmd_sub(q1max=20000):
    print("# rank1_twins --sub : the residual  c*|S_1| = |S|,  2 <= c | |Out(S_1)|")
    print("#   (Step 3 has already reduced the socle to a SINGLE simple S_1,")
    print("#    so this equation is the WHOLE residual problem.)")
    print("#   The target q is SOLVED FOR from (S_1,c) -- so each row is")
    print("#   COMPLETE IN q, i.e. it covers ALL q, not a q-range.")
    print()
    for n, k in ((0, 3), (1, 3), (7, 3), (8, 3), (10 ** 120, 3),
                 (10 ** 200, 8), (10 ** 200, 5), (10 ** 200, 7)):
        r = _iroot(n, k)
        assert r ** k <= n < (r + 1) ** k, (n, k, r)
    print("  _iroot selftest (k = 3,5,7,8 up to the 10^200 scale): OK")
    print("  positive controls:")
    for fam, q in (("U3", 3), ("U3", 5), ("U3", 8), ("Sz", 8), ("Sz", 32),
                   ("Ree", 27), ("Ree", 243)):
        M = FAM[fam]["order"](q)
        got = SOLVE[fam](M)
        print("     solve_%-4s(|%s(%d)| = %d) = %s  %s"
              % (fam, fam, q, M, got, "OK" if got == [q] else "*** FAIL ***"))
    print()
    cands = socle_candidates(q1max)
    print("  socle candidates enumerated: %d  (Lie q1 <= %d rank <= 6,"
          % (len(cands), q1max))
    print("   all A_m with |A_m| <= 10^80, all 27 sporadics + Tits)")
    print()
    for fam in ("U3", "Sz", "Ree"):
        hits = []
        tested = 0
        for (nm, o, u) in cands:
            if o <= 1:
                continue
            for c in range(2, u + 1):
                if u % c:
                    continue
                tested += 1
                for q in SOLVE[fam](c * o):
                    if FAM[fam]["name"](q) == nm:
                        continue          # c > 1 excludes S_1 = S anyway
                    hits.append((nm, c, q))
        print("  %-4s : %d (S_1,c) pairs tested -> %d hits %s"
              % (fam, tested, len(hits), hits if hits else ""))
    print()
    print("## NEGATIVE CONTROL / robustness.  The same scan with the")
    print("## Fitting-free constraint  c | |Out(S_1)|  DROPPED and replaced by")
    print("## the weak bound c <= 10^4: these are the pairs that the ORDER")
    print("## arithmetic alone permits, i.e. what the c-constraint is buying.")
    print("## (It also shows the order-inverters do fire when a solution")
    print("##  exists -- an all-empty scan would otherwise be untestable.)")
    small = socle_candidates(2000, rankmax=5)
    print("## candidate set for the control: %d groups (Lie q1 <= 2000,"
          % len(small))
    print("## rank <= 5, all A_m, all sporadics), c <= 2000.")
    for fam in ("U3", "Sz", "Ree"):
        near = []
        for (nm, o, u) in small:
            if o <= 1 or o > 10 ** 30:
                continue
            for c in range(2, 2001):
                for q in SOLVE[fam](c * o):
                    if FAM[fam]["name"](q) == nm:
                        continue
                    near.append((nm, c, q, u))
        print("  %-4s : %d order-only near-misses" % (fam, len(near)))
        for (nm, c, q, u) in near[:40]:
            print("        %s(q=%d) = %d * |%s|   [c | |Out| ? %s , |Out| = %d]"
                  % (fam, q, c, nm, "YES" if u % c == 0 else "no", u))
    print()
    print("  NOTE on completeness: the equation determines q from (S_1,c), so")
    print("  the only incompleteness is the range of S_1 (Lie q1 <= %d,"
          % q1max)
    print("  rank <= 6).  Larger S_1 is excluded by |S_1| = |S|/c together")
    print("  with Lemma R (--rank) for U3 and Ree; for Sz it is a scanned")
    print("  bound only.  See the write-up, gap (G3).")


# ==========================================================================

if __name__ == "__main__":
    a = sys.argv[1:]
    if "--uniform" in a:
        cmd_uniform()
    elif "--lemK" in a:
        cmd_lemK()
    elif "--rank" in a:
        cmd_rank()
    elif "--eqchar" in a:
        rest = [x for x in a if not x.startswith("--")]
        cmd_eqchar(int(rest[0]) if rest else None)
    elif "--census" in a:
        i = a.index("--census")
        fam = a[i + 1]
        lim = int(a[i + 2])
        cmd_census(fam, lim, raw=("--raw" in a))
    elif "--sub" in a:
        rest = [x for x in a if not x.startswith("--")]
        cmd_sub(int(rest[0]) if rest else 20000)
    else:
        print(__doc__ or "see header")
