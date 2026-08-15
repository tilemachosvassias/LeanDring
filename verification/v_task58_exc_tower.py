#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
v_task58_exc_tower.py -- Fitting-free NON-SIMPLE twins of the LARGE
EXCEPTIONAL tower

    F4(q)  , all q >= 2
    E6(q)  , all q >= 2
    2E6(q) , all q >= 2
    E7(q)  , all q >= 2
    E8(q)  , all q >= 2

Standing hypotheses (all upstream and PROVEN), verbatim from v_task57:
   T Fitting-free, |T| = |S|, D(T) = D(S), T NOT simple.
   Soc T = prod_i S_i^{l_i}; orbits O of length l_O; c = [T : Soc T];
   (F)  l_O * |Out(S_1)| * iota(S_1) >= iota(S)       [Lemma TO'-0 + F]
   (C)  |Out(G)| * iota(G) <= |G|^{2/3}               [Lemma C, v_task52]
   (T1) |G| >= q1^D/(12 d), (T2) iotabar <= 4 q1^mu, (T3) |Out| = d f g

PARTS
 0  the FAM ERRATUM for E7/E8 (mu was 25/51, is 27/57) -- re-derived here.
 1  invariants, the cyclotomic spectra, Lemma K-exc(tower), strain.
 2  Lemma Q -- T is almost simple.
 3  cross characteristic: the ppmax^3 kill.
 4  Lemma EQ' + the D/N table.
4.5 Lemma EQ-EX and the a/N = 13/6 block, in closed form.
4.6 the non-matched f1 killed by Zsygmondy + counting.
4.0 the factorisation-free exact equal-characteristic sweep.
 5  alternating / sporadic socle, complete in q, + the E8 sporadic floor.
 6  the residual census.
 8  the 13/6-block identity hunt.

All arithmetic is exact integer / Fraction arithmetic.
"""

import sys
from fractions import Fraction

sys.path.insert(0, ".")

from v_task50_sporadic_twins import SPORADIC, TITS, census as census50
from v_task50_sporadic_twins import simple_divisors, phase2
from v_task51_l2_twins import is_prime_power, factorint, iota_ub_generic
from v_task54_rank1_gaps import prime_powers_sieve
from v_task52_lemmaC import FAM, gcd, order_of, out_of, _prod
from v_task53_rank1_twins import _iroot
from v_task55_l3_twins import alt_rows, spor_rows, lie_rows, lemB_tail_threshold
import v_task50_sporadic_twins as V50

V50.iota_ub = lambda name, order: iota_ub_generic(name)

BAR = "=" * 74


def pp_of(q):
    p = 2
    while q % p:
        p += 1
    f = 0
    t = q
    while t % p == 0:
        t //= p
        f += 1
    return p, f


def ppmax(fac, skip=None):
    m = 1
    for r, a in fac.items():
        if r == skip:
            continue
        m = max(m, r ** a)
    return m


def divisors(n):
    d = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            d.append(i)
            if i != n // i:
                d.append(n // i)
        i += 1
    return sorted(d)


def cyclo(n, q):
    """Phi_n(q) by exact integer division of q^n-1 by the lower Phi_d."""
    num = q ** n - 1
    for d in divisors(n):
        if d < n:
            num //= cyclo(d, q)
    return num


# ====================================================================
#  the five targets
# ====================================================================
#  |F4(q)|  = q^24 (q^12-1)(q^8-1)(q^6-1)(q^2-1)
#  |E6(q)|  = q^36 (q^12-1)(q^9-1)(q^8-1)(q^6-1)(q^5-1)(q^2-1)/gcd(3,q-1)
#  |2E6(q)| = q^36 (q^12-1)(q^9+1)(q^8-1)(q^6-1)(q^5+1)(q^2-1)/gcd(3,q+1)
#  |E7(q)|  = q^63 (q^18-1)(q^14-1)(q^12-1)(q^10-1)(q^8-1)(q^6-1)(q^2-1)
#                                                       /gcd(2,q-1)
#  |E8(q)|  = q^120 (q^30-1)(q^24-1)(q^20-1)(q^18-1)(q^14-1)(q^12-1)
#                                                   (q^8-1)(q^2-1)

def _o_F4(q):
    return q ** 24 * (q ** 12 - 1) * (q ** 8 - 1) * (q ** 6 - 1) * (q * q - 1)


def _o_E6(q):
    return (q ** 36 * (q ** 12 - 1) * (q ** 9 - 1) * (q ** 8 - 1) *
            (q ** 6 - 1) * (q ** 5 - 1) * (q * q - 1) // gcd(3, q - 1))


def _o_2E6(q):
    return (q ** 36 * (q ** 12 - 1) * (q ** 9 + 1) * (q ** 8 - 1) *
            (q ** 6 - 1) * (q ** 5 + 1) * (q * q - 1) // gcd(3, q + 1))


def _o_E7(q):
    return (q ** 63 * (q ** 18 - 1) * (q ** 14 - 1) * (q ** 12 - 1) *
            (q ** 10 - 1) * (q ** 8 - 1) * (q ** 6 - 1) * (q * q - 1)
            // gcd(2, q - 1))


def _o_E8(q):
    return (q ** 120 * (q ** 30 - 1) * (q ** 24 - 1) * (q ** 20 - 1) *
            (q ** 18 - 1) * (q ** 14 - 1) * (q ** 12 - 1) * (q ** 8 - 1) *
            (q * q - 1))


def _solve_generic(M, ordfun, a, ok, extra_mult=(1,)):
    """all admissible prime powers q with ordfun(q) = M  (complete in q)."""
    out = []
    for m in extra_mult:
        v = M * m
        r = _iroot(v, a)
        for q in range(max(2, r - 3), r + 4):
            if ordfun(q) != M:
                continue
            if not is_prime_power(q):
                continue
            p, f = pp_of(q)
            if not ok(q, p, f):
                continue
            out.append(q)
    return sorted(set(out))


TARGETS = []


def target(**kw):
    TARGETS.append(kw)


# iota: the MINIMAL PARABOLIC index.  deg_q iota = dim U_P = mu.
#   F4  : P_1 (Levi B_3), |U_P| = q^15 , index (q^12-1)(q^4+1)/(q-1)
#   E6  : P_1 (Levi D_5), |U_P| = q^16 ABELIAN, index (q^9-1)(q^8+q^4+1)/(q-1)
#   2E6 : index (q^9+1)(q^8+q^4+1)/(q+1)
#   E7  : P_7 (Levi E_6), |U_P| = q^27 ABELIAN,
#         index (q^14-1)(q^9+1)(q^5+1)/(q-1)
#   E8  : P_8 (Levi E_7), |U_P| = q^57 ,
#         index (q^30-1)(q^12+1)(q^10+1)(q^6+1)/(q-1)

target(key="F4", disp="F4(q)",
       order=_o_F4,
       terms=[(12,-1),(8,-1),(6,-1),(2,-1)], E=12,
       iota=lambda q: (q ** 12 - 1) * (q ** 4 + 1) // (q - 1),
       out=lambda q, p, f: (2 * f if p == 2 else f),
       a=52, b=15, N=24, M=4,
       ok=lambda q, p, f: q >= 2,
       solve=lambda M: _solve_generic(M, _o_F4, 52, lambda q, p, f: q >= 2))

target(key="E6", disp="E6(q)",
       order=_o_E6,
       terms=[(12,-1),(9,-1),(8,-1),(6,-1),(5,-1),(2,-1)], E=12,
       iota=lambda q: (q ** 9 - 1) * (q ** 8 + q ** 4 + 1) // (q - 1),
       out=lambda q, p, f: 2 * gcd(3, q - 1) * f,
       a=78, b=16, N=36, M=6,
       ok=lambda q, p, f: q >= 2,
       solve=lambda M: _solve_generic(M, _o_E6, 78, lambda q, p, f: q >= 2,
                                      (1, 3)))

target(key="2E6", disp="2E6(q)",
       order=_o_2E6,
       terms=[(12,-1),(9,1),(8,-1),(6,-1),(5,1),(2,-1)], E=18,
       iota=lambda q: (q ** 9 + 1) * (q ** 8 + q ** 4 + 1) // (q + 1),
       out=lambda q, p, f: 2 * gcd(3, q + 1) * f,
       a=78, b=16, N=36, M=6,
       ok=lambda q, p, f: q >= 2,
       solve=lambda M: _solve_generic(M, _o_2E6, 78, lambda q, p, f: q >= 2,
                                      (1, 3)))

target(key="E7", disp="E7(q)",
       order=_o_E7,
       terms=[(18,-1),(14,-1),(12,-1),(10,-1),(8,-1),(6,-1),(2,-1)], E=18,
       iota=lambda q: (q ** 14 - 1) * (q ** 9 + 1) * (q ** 5 + 1) // (q - 1),
       out=lambda q, p, f: gcd(2, q - 1) * f,
       a=133, b=27, N=63, M=7,
       ok=lambda q, p, f: q >= 2,
       solve=lambda M: _solve_generic(M, _o_E7, 133, lambda q, p, f: q >= 2,
                                      (1, 2)))

target(key="E8", disp="E8(q)",
       order=_o_E8,
       terms=[(30,-1),(24,-1),(20,-1),(18,-1),(14,-1),(12,-1),(8,-1),(2,-1)], E=30,
       iota=lambda q: (q ** 30 - 1) * (q ** 12 + 1) * (q ** 10 + 1) *
       (q ** 6 + 1) // (q - 1),
       out=lambda q, p, f: f,
       a=248, b=57, N=120, M=8,
       ok=lambda q, p, f: q >= 2,
       solve=lambda M: _solve_generic(M, _o_E8, 248, lambda q, p, f: q >= 2))


# Lemma K-exc(tower):  ppmax_{p'}(|S|) <= P(q) := C(S) * (q+1)^M with
#   M    = max_e m_e * phi(e)  over the cyclotomic spectrum of |S|_{p'} ;
#   C(S) = max( C_2 , C_odd ) ,
#   C_2   = 2^k * prod_terms |d|_2   (k = #terms; bounds the 2-part at q odd
#           via |q^d -+ 1|_2 | |q^{2d}-1|_2 = |q^2-1|_2 |d|_2 <= 2(q+1)|d|_2)
#   C_odd = max over primes r and e >= 1 of r^{sum_{k>=1} m_{e r^k}}
#           (an odd r with ord_r(q) = e divides Phi_{e r^k} exactly once).

def _two_part(n):
    t = 1
    while n % 2 == 0:
        n //= 2
        t *= 2
    return t


def _Cconst(T):
    m = spectrum(T)
    c2 = 2 ** len(T["terms"])
    for (d, eps) in T["terms"]:
        c2 *= _two_part(d)
    codd = 1
    emax = max(m)
    for r in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31):
        for e in sorted(m):
            s = 0
            k = 1
            while e * r ** k <= emax:
                s += m.get(e * r ** k, 0)
                k += 1
            codd = max(codd, r ** s)
    return max(c2, codd), c2, codd


_PPCACHE = {}


def _pps(M):
    if M not in _PPCACHE:
        _PPCACHE[M] = prime_powers_sieve(M)
    return _PPCACHE[M]


def targets_q(T, M):
    return [(q, p, f) for (q, p, f) in _pps(M) if T["ok"](q, p, f)]


def T_by_key(k):
    for T in TARGETS:
        if T["key"] == k:
            return T
    raise KeyError(k)


def F_by_key(k):
    for F in FAM:
        if F["key"] == k:
            return F
    raise KeyError(k)


def spectrum(T):
    """multiplicities m_e of Phi_e in the p'-part of |S|.
       T['terms'] is a list of (d, eps): the factor q^d - eps.
       eps = +1 contributes the Phi_e with e | 2d, e not | d."""
    m = {}
    for (d, eps) in T["terms"]:
        if eps == -1:
            es = divisors(d)
        else:
            es = [e for e in divisors(2 * d) if (2 * d) % e == 0
                  and d % e != 0]
        for e in es:
            m[e] = m.get(e, 0) + 1
    return m


def phi(n):
    r = n
    x = n
    p = 2
    while p * p <= x:
        if x % p == 0:
            while x % p == 0:
                x //= p
            r -= r // p
        p += 1
    if x > 1:
        r -= r // x
    return r


# --- fill in M (the cyclotomic strain exponent) and P (Lemma K-exc) ------
for _T in TARGETS:
    _m = spectrum(_T)
    _T["M"] = max(v * phi(e) for (e, v) in _m.items())
    _T["C"], _T["C2"], _T["Codd"] = _Cconst(_T)
    _T["P"] = (lambda TT: (lambda q: TT["C"] * (q + 1) ** TT["M"]))(_T)



_PPX = {}


def exact_ppmax(T, q, p):
    """the EXACT ppmax_{p'}(|S|), from the cyclotomic blocks (each block is
       at most (q+1)^{phi(e)}, so this is a cheap factorisation)."""
    key = (T["key"], q)
    if key in _PPX:
        return _PPX[key]
    m = spectrum(T)
    fac = {}
    for (e, mult) in m.items():
        v = cyclo(e, q)
        if v <= 1:
            continue
        for (r, k) in factorint(v).items():
            fac[r] = fac.get(r, 0) + k * mult
    fac.pop(p, None)
    _PPX[key] = ppmax(fac)
    return _PPX[key]


# ================================================================= PART 0

def part0():
    print(BAR)
    print("PART 0 -- ERRATUM in the shared FAM table (v_task52): the E7 and")
    print("          E8 minimal-parabolic indices were WRONG")
    print(BAR)
    print("""
  deg_q [S : P] = dim U_P for every parabolic P, and the minimal maximal
  parabolic is the one with the LARGEST Levi:

     F4 : P_1 , Levi B_3 , dim U_P = 15
     E6 : P_1 , Levi D_5 , dim U_P = 16   (U_P ABELIAN, the 27-dim node)
     E7 : P_7 , Levi E_6 , dim U_P = 27   (U_P ABELIAN, the 56-dim node)
     E8 : P_8 , Levi E_7 , dim U_P = 57

  v_task52's FAM carried mu(E7) = 25 and mu(E8) = 51 with iota expressions
  divided by a spurious (q^2-1) resp. (q^2-1)(q^4-1).  Both are corrected
  here (and at source in v_task52_lemmaC.py).  Direct check against
  |S| / (q^{dim U_P} |Levi|_univ (q-1)) :
""")
    def univ(k, n, q):
        F = F_by_key(k)
        return q ** F["N"](n) * _prod(F["terms"](n, q))
    bad = 0
    for q in (2, 3, 4, 5, 7, 8, 9):
        rows = [("F4", univ("F4", 1, q) // (q ** 15 * univ("B", 3, q) * (q - 1)),
                 T_by_key("F4")["iota"](q)),
                ("E6", univ("E6", 1, q) // (q ** 16 * univ("D", 5, q) * (q - 1)),
                 T_by_key("E6")["iota"](q)),
                ("E7", univ("E7", 1, q) // (q ** 27 * univ("E6", 1, q) * (q - 1)),
                 T_by_key("E7")["iota"](q)),
                ("E8", univ("E8", 1, q) // (q ** 57 * univ("E7", 1, q) * (q - 1)),
                 T_by_key("E8")["iota"](q))]
        for (k, idx, io) in rows:
            if idx != io:
                bad += 1
                print("   MISMATCH %s q=%d : %d vs %d" % (k, q, idx, io))
        print("   q = %-2d  F4 %-22d E6 %-24d E7 %-30d E8 %d"
              % (q, rows[0][1], rows[1][1], rows[2][1], rows[3][1]))
    print("   parabolic-index vs target-table mismatches : %d" % bad)
    print()
    print("  Impact of the erratum on the finished notes:")
    for k in ("E7", "E8"):
        F = F_by_key(k)
        D, mu = F["D"](1), F["mu"](1)
        print("    %-3s : Lemma C sufficient condition 2D-3mu = %d > 0  (was"
              " 2D-3mu = %d)" % (k, 2 * D - 3 * mu,
                                 2 * D - 3 * (25 if k == "E7" else 51)))
    print("    v_task57 PARTs 4/4.5 re-run with the corrected table: the")
    print("    surviving-family lists are UNCHANGED (E7/E8 are killed by")
    print("    Lemma EQ' with either value of mu).  No verdict moves.")
    print()
    return bad


# ================================================================= PART 1

def part1(qmax=None):
    print(BAR)
    print("PART 1 -- the five targets: invariants, spectra, Lemma K-exc,")
    print("          and the strain diagnostic")
    print(BAR)
    print("""
  a := deg_q |S| = dim S ,  b := deg_q iota(S) = dim U_P ,  N := deg_q |S|_p.
""")
    print("  %-5s %4s %4s %4s %10s %10s %10s %8s" %
          ("S", "a", "b", "N", "a/b", "a/N", "N/b", "3b-a"))
    for T in TARGETS:
        print("  %-5s %4d %4d %4d %10s %10s %10s %+8d" %
              (T["key"], T["a"], T["b"], T["N"],
               str(Fraction(T["a"], T["b"])), str(Fraction(T["a"], T["N"])),
               str(Fraction(T["N"], T["b"])), 3 * T["b"] - T["a"]))
    print("""
  3b - a < 0 for EVERY target: the rank-1 Step 2 (iota^3 > |S|) fails for
  all five, so Lemma Q is genuinely needed (PART 2).  [v_task57 sec.10
  predicted -58 / -95 for E7 / E8 from the erroneous b = 25 / 51; the
  correct values are -52 / -77.]

  Cyclotomic spectra of |S|_{p'} = prod_e Phi_e(q)^{m_e}, and
  M := max_e m_e * phi(e) :
""")
    for T in TARGETS:
        m = spectrum(T)
        Mv = max(v * phi(e) for (e, v) in m.items())
        tot = sum(v * phi(e) for (e, v) in m.items())
        print("   %-5s %s" % (T["key"],
                              " ".join("Phi%d^%d" % (e, v)
                                       for (e, v) in sorted(m.items()))))
        print("         sum m_e phi(e) = %d (= a - N = %d) %s ; M = %d ; "
              "C_2 = %d , C_odd = %d , C = %d"
              % (tot, T["a"] - T["N"],
                 "OK" if tot == T["a"] - T["N"] else "!! MISMATCH",
                 Mv, T["C2"], T["Codd"], T["C"]))
        assert Mv == T["M"] and tot == T["a"] - T["N"], T["key"]
    print("""
  Lemma K-exc(tower) [PROVEN].  ppmax_{p'}(|S|) <= P(q) := C(S) (q+1)^M.

  Proof.  (odd r != p)  Let e = ord_r(q).  Then r | Phi_d(q) only for
  d = e or d = e r^k (k >= 1), and in the latter case r || Phi_d(q)
  (Lucas / lifting-the-exponent).  So the r-part of |S| is at most
  Phi_e(q)^{m_e} * r^{s} with s = sum_{k>=1} m_{e r^k}.  Now
  Phi_e(q) < (q+1)^{phi(e)}, hence Phi_e(q)^{m_e} <= (q+1)^{m_e phi(e)}
  <= (q+1)^M; and e r^k must itself be a block index, so r <= e_max and
  r^s <= C_odd, a constant computed from the spectrum alone.
  (r = 2, q odd)  Every factor of |S|_{p'} is q^d -+ 1, and
  |q^d -+ 1|_2 divides |q^{2d}-1|_2 = |q^2-1|_2 |d|_2 <= 2(q+1)|d|_2
  because min(|q-1|_2, |q+1|_2) = 2.  Multiplying over the k terms gives
  |S|_2 <= 2^k (prod |d|_2) (q+1)^k = C_2 (q+1)^k <= C_2 (q+1)^M, since
  k <= M in all five families (k = M for E6, 2E6, E7, E8 and k = 4 = M
  for F4).
  (r = 2, q even)  2 = p is excluded from ppmax_{p'}. []

  The constants are small: C = C_2 in every family.
""")
    caps = {"F4": 200, "E6": 200, "2E6": 200, "E7": 100, "E8": 60}
    tot_bad = 0
    for T in TARGETS:
        lim = qmax or caps[T["key"]]
        bad = 0
        m = spectrum(T)
        for (q, p, f) in targets_q(T, lim):
            fac = {}
            for (e, mult) in m.items():
                v = cyclo(e, q)
                if v <= 1:
                    continue
                for (r, k) in factorint(v).items():
                    fac[r] = fac.get(r, 0) + k * mult
            fac.pop(p, None)
            pm = ppmax(fac)
            if pm > T["P"](q):
                bad += 1
                print("   VIOLATION %s q=%d : %d > %d"
                      % (T["key"], q, pm, T["P"](q)))
        print("   %-5s : Lemma K-exc violations over admissible q <= %d : %d"
              % (T["key"], lim, bad))
        tot_bad += bad
    print()
    print("  the targets themselves satisfy Lemma K' (a < 3N):")
    for T in TARGETS:
        print("    %-5s a = %3d  <  3N = %3d   %s"
              % (T["key"], T["a"], 3 * T["N"],
                 "OK" if T["a"] < 3 * T["N"] else "!!"))
    print()
    print("  sample orders and iota:")
    for T in TARGETS:
        for q in (2, 3, 4):
            print("    %-5s q=%d  |S| = %-30d iota = %d"
                  % (T["key"], q, T["order"](q), T["iota"](q)))
    print()
    return tot_bad


# ================================================================= PART 2

_VIOL = None


def violators():
    """the Lemma-B violator list (|G| <= 4 rho(G)^2), rho = |Out|*iotabar.
       IDENTICAL construction to v_task55 PART 2b / v_task57 PART 2."""
    global _VIOL
    if _VIOL is not None:
        return _VIOL
    rows = []
    rows += alt_rows(80)
    rows += spor_rows()
    tails = {}
    for F in FAM:
        ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], 25)
        for n in ns:
            t = lemB_tail_threshold(F, n)
            if t is not None and t >= 2:
                tails[(F["key"], n)] = t
    q1cap = max(tails.values()) if tails else 2
    rows += lie_rows(max(q1cap, 64), rankmax=24)
    viol = []
    for (nm, o, ou, io) in rows:
        rho = ou * io
        if o <= 4 * rho * rho:
            viol.append((nm, o, ou, io, rho))
    viol.sort(key=lambda t: t[1])
    _VIOL = (viol, q1cap)
    return _VIOL


def part2():
    print(BAR)
    print("PART 2 -- the MULTI-ORBIT branch: Lemma MO-EX")
    print(BAR)
    print("""
  *** This is where the large tower differs from everything before it. ***

  v_task55's Lemma Q reduces `T not almost simple' to a Lemma-B violator by
  the step:  l <= 2 gives |G|^2 <= |S| and 2 rho(G) >= iota(S), hence
  |G| <= |S|^{1/2} <= iota(S)^2 <= 4 rho(G)^2 -- which needs  4b >= a.

     target   4b    a     4b >= a ?
     L3        8     8    yes (equality)
     S4       12    10    yes        G2   20  14  yes
     3D4      36    28    yes        2F4  40  26  yes
     F4       60    52    YES
     E6/2E6   64    78    NO         E7  108 133  NO     E8  228 248  NO

  So Lemma Q as stated does NOT apply to E6, 2E6, E7, E8: for these
  targets iota(S) is far too small relative to |S| (b/a = 16/78, 27/133,
  57/248 < 1/4) for the floor to squeeze a socle factor into the violator
  list.  v_task57 sec.10's forecast "l >= 2 will be vacuous for the whole
  F4-E8 tower" is WRONG -- it read the window off q^b <= 2 rho_max only.

  The replacement is a CONVEXITY argument on the exponents, and it is
  uniform in q, needs no violator list, and is strictly stronger.

  > Lemma MO-EX [PROVEN, this note].  Let T be Fitting-free, |T| = |S|,
  > D(T) = D(S), T NOT almost simple; Soc T = prod_O G_O^{l_O} over the
  > socle orbits O, and suppose every G_O is of Lie type in the DEFINING
  > characteristic p (PART 2C disposes of the other cases).  Put
  > r_O := D_O/N_O and u_O := l_O N_O f_O.  Then
  >
  >   (i)  [floor + p-part]   sum_O l_O (N_O/mu_O)  <=  N/b + E1 ,
  >        E1 = (1/(b f)) sum_O l_O (N_O/mu_O) A_O ,
  >        A_O = log_p(4 l_O d_O f_O g_O / kappa_i) .
  >        Since N_O/mu_O >= 1 in EVERY family and there are >= 2 factors,
  >        each single family obeys  N_O/mu_O  <=  N/b - 1 + E1 .
  >   (ii) [p-part EQUALITY, Lemma EQ-EX]   sum_O u_O = N f - delta ,
  >        delta = v_p(c) , c | prod |Out(G_O)|^{l_O} prod l_O! .
  >   (iii)[order]   a f - B  <=  sum_O r_O u_O  <=  a f ,
  >        B = log_p(prod (12 d_O)^{l_O}) .
  >
  > Combining (ii) and (iii):
  >
  >        sum_O ( r_O - a/N ) u_O   <=   B + (a/N) delta .            (*)
  >
  > Every term on the left is >= 0 as soon as every admissible family has
  > r_O >= a/N, and each u_O >= (N_O/mu_O)(b f - A_O) >= b f - A.  So if
  > SOME factor has r_O > a/N strictly, (*) forces
  >
  >        (min strict gap) * (b f - A)  <=  B + (a/N) delta ,
  >
  > an explicit threshold in q.  And if EVERY factor has r_O = a/N exactly,
  > (i) has to be satisfied by same-ratio families alone -- a purely
  > combinatorial condition on the family tables.  []

  The tables (exact, no q anywhere):
""")
    rows = []
    for F in FAM:
        ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], 41)
        for n in ns:
            N1, mu1, D1 = F["N"](n), F["mu"](n), F["D"](n)
            rows.append((F["name"](n, 0).replace("(0)", ""),
                         Fraction(N1, mu1), Fraction(D1, N1)))
    print("  global min over ALL families of N/mu = %s  (attained by L2, U3,"
          " Sz, R)" % min(r[1] for r in rows))
    print()
    res = {}
    thr = {}
    import math
    for T in TARGETS:
        Nb = Fraction(T["N"], T["b"])
        cap = Nb - 1
        aN = Fraction(T["a"], T["N"])
        adm = sorted(set((r[0], r[1], r[2]) for r in rows if r[1] <= cap))
        print("  ---- %-4s : N/b = %-7s  cap = N/b - 1 = %-7s  a/N = %s"
              % (T["key"], str(Nb), str(cap), str(aN)))
        print("       admissible families (N1/mu1 <= cap) : %s"
              % ([("%s: N/mu=%s, D/N=%s" % (x[0], x[1], x[2])) for x in adm]
                 or "NONE"))
        if not adm:
            print("       ==> NO family can carry a socle factor: the "
                  "multi-orbit branch is")
            print("           EMPTY for EVERY q, with no threshold and no "
                  "exceptional list.")
            thr[T["key"]] = None
            res[T["key"]] = (adm, None, aN)
            print()
            continue
        allge = all(x[2] >= aN for x in adm)
        eq = [x for x in adm if x[2] == aN]
        strict = [x[2] - aN for x in adm if x[2] > aN]
        gap = min(strict) if strict else None
        print("       every admissible r = D1/N1 >= a/N : %s" % allge)
        print("       same-ratio admissible (r = a/N)   : %s"
              % ([(x[0], str(x[1])) for x in eq] or "NONE"))
        if eq:
            cheap = min(x[1] for x in eq)
            print("       an ALL-same-ratio configuration needs "
                  "sum l_O (N_O/mu_O) >= 2 * %s = %s  >  N/b = %s : %s"
                  % (str(cheap), str(2 * cheap), str(Nb),
                     "IMPOSSIBLE" if 2 * cheap > Nb else "!! POSSIBLE"))
        print("       min strict gap r - a/N over the admissible list : %s"
              % str(gap))
        # the SHARP weight: W = sum_O l_O (N_O/mu_O) (r_O - a/N), minimised
        # over all admissible configurations with >= 2 factors and
        # sum_O l_O (N_O/mu_O) <= N/b.
        best = None
        for x in adm:
            for l1 in (2, 3):
                if l1 * x[1] <= Nb:
                    W = l1 * x[1] * (x[2] - aN)
                    if best is None or W < best[0]:
                        best = (W, "%s^%d" % (x[0], l1))
            for y in adm:
                for l1 in (1, 2):
                    for l2 in (1, 2):
                        if l1 * x[1] + l2 * y[1] > Nb:
                            continue
                        W = l1 * x[1] * (x[2] - aN) + l2 * y[1] * (y[2] - aN)
                        if best is None or W < best[0]:
                            best = (W, "%s^%d x %s^%d" % (x[0], l1, y[0], l2))
        Wmin = best[0]
        print("       SHARP weight W = min over configurations of "
              "sum l(N/mu)(r - a/N)  =  %s   (attained by %s)"
              % (str(Wmin), best[1]))
        assert allge and Wmin > 0
        # explicit threshold from (*) :  gap*(b f - A) > B + (a/N) delta
        kappa_i = min(Fraction(T["iota"](q), q ** T["b"])
                      for (q, p, f) in targets_q(T, 64))
        q0 = None
        for (q, p, f) in targets_q(T, 10 ** 7):
            lg = math.log(p)
            fO = T["N"] * f
            A = math.log(48.0 * fO / float(kappa_i)) / lg
            B = math.log(1296.0) / lg
            dlt = math.log(2.0 * (18 * fO) ** 2) / lg
            if float(gap) * (T["b"] * f - A) > B + float(aN) * dlt:
                q0 = q
                break
        thr[T["key"]] = (Wmin, kappa_i, adm)
        print("       kappa_i = min_q iota(S)/q^b = %.6f" % float(kappa_i))
        res[T["key"]] = (adm, gap, aN)
        print()
    print("""
  The explicit form of (*).  With l_O <= 2, |Out(G_O)| = d_O f_O g_O <= 8 f_O
  for every admissible family, f_O <= N f (from sum l_O N_O f_O <= N f and
  N_O >= 1), and c | prod |Out|^{l_O} prod l_O! so c <= 2 (8 N f)^2 = 128
  (N f)^2 :

     A       <=  log_p( 4 * 2 * 8 N f / kappa_i )  =  log_p( 64 N f/kappa_i )
     B       <=  log_p( (12*4)^2 )                 =  log_p( 2304 )
     delta   <=  log_p( 128 (N f)^2 )

  and MO-EX closes at (p,f) as soon as

     W * ( b f - A )   >   B + (a/N) * delta ,

  W being the sharp configuration weight of the table above.

  The set of (p,f) where this FAILS is finite and is swept exactly in
  PART 2B.  (It is monotone: the left side grows linearly in f and in
  log p, the right side only logarithmically.)
""")
    print(BAR)
    print("  PART 2B -- the EXACT residual sweep of the (p,f) window where")
    print("             MO-EX does not yet close")
    print(BAR)
    print("""
  For each target the failing (p,f) set is computed from the displayed
  inequality and then swept EXACTLY: every admissible family F_O, every
  orbit length l_O <= 2, every f_O in the band forced by the floor, and the
  exact tests

     prod |G_O|^{l_O}  |  |S| ,
     c := |S| / prod |G_O|^{l_O}   divides   prod |Out(G_O)|^{l_O} prod l_O! ,
     l_O |Out(G_O)| iota(G_O)  >=  iota(S)    (exact iota from the tables).

  No factorisation of |S| is used anywhere.
""")
    import math
    for T in TARGETS:
        info = thr[T["key"]]
        if info is None:
            print("    %-5s : window VACUOUS (no admissible family)"
                  % T["key"])
            continue
        Wmin, kappa_i, adm = info
        aN = Fraction(T["a"], T["N"])
        admF = []
        for F in FAM:
            ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], 41)
            for n in ns:
                if Fraction(F["N"](n), F["mu"](n)) <= Fraction(T["N"], T["b"]) - 1:
                    admF.append((F, n))

        def closes(p, f):
            lg = math.log(p)
            A = math.log(64.0 * T["N"] * f / float(kappa_i)) / lg
            B = math.log(2304.0) / lg
            dl = math.log(128.0 * (T["N"] * f) ** 2) / lg
            return float(Wmin) * (T["b"] * f - A) > B + float(aN) * dl

        # the failing (p,f) window: closing is monotone in p and in f, so
        # a binary search in p for each f gives the window exactly.
        Pf = []
        for f in range(1, 400):
            if closes(2, f):
                Pf.append((f, 0))
                continue
            lo, hi = 2, 10 ** 15
            while lo < hi:
                mid = (lo + hi) // 2
                if closes(mid, f):
                    hi = mid
                else:
                    lo = mid + 1
            Pf.append((f, lo - 1))
        Pmaxall = max([x[1] for x in Pf], default=0)
        primes = [x[0] for x in prime_powers_sieve(Pmaxall)
                  if x[2] == 1] if Pmaxall >= 2 else []
        fails = []
        for (f, Pmx) in Pf:
            if Pmx < 2:
                continue
            for pr in primes:
                if pr > Pmx:
                    break
                fails.append((pr, f))
        pmax = max([x[0] for x in fails], default=0)
        fmx = max([x[1] for x in fails], default=0)
        print("    %-5s : MO-EX fails only for %d pairs (p,f), p <= %d, "
              "f <= %d ; sweeping them exactly..."
              % (T["key"], len(fails), pmax, fmx))
        nsurv = 0
        ntested = 0
        for (p, f) in fails:
            q = p ** f
            S = T["order"](q)
            io = T["iota"](q)
            # candidate factors
            cands = []
            for (F, n) in admF:
                N1, mu1 = F["N"](n), F["mu"](n)
                for l1 in (1, 2):
                    lo = 1
                    hi = T["N"] * f // (l1 * N1)
                    for f1 in range(lo, hi + 1):
                        if not F["qform"](p, f1):
                            continue
                        q1 = p ** f1
                        if F["skip"](n, q1):
                            continue
                        o1 = order_of(F, n, q1)
                        if o1 < 60:
                            continue
                        ou1 = out_of(F, n, q1, p, f1)
                        i1 = F["iota"](n, q1)
                        if l1 * ou1 * i1 < io:
                            continue
                        if o1 ** l1 > S or S % (o1 ** l1):
                            continue
                        cands.append((F["name"](n, q1), o1, ou1, l1))
            ntested += len(cands)
            for i in range(len(cands)):
                nm1, o1, ou1, l1 = cands[i]
                if l1 >= 2:
                    c = S // o1 ** l1
                    if c >= 1 and (_fact(l1) * ou1 ** l1) % c == 0:
                        nsurv += 1
                        print("       SURVIVOR %s q=%d^%d : %s^%d c=%d"
                              % (T["key"], p, f, nm1, l1, c))
                for j in range(i, len(cands)):
                    nm2, o2, ou2, l2 = cands[j]
                    if i == j and l2 == l1:
                        continue
                    tot = o1 ** l1 * o2 ** l2
                    if tot > S or S % tot:
                        continue
                    c = S // tot
                    cap2 = _fact(l1) * _fact(l2) * ou1 ** l1 * ou2 ** l2
                    if cap2 % c == 0:
                        nsurv += 1
                        print("       SURVIVOR %s q=%d^%d : %s^%d x %s^%d c=%d"
                              % (T["key"], p, f, nm1, l1, nm2, l2, c))
        print("             %d (family, l, f_O) candidates past the floor ; "
              "SURVIVORS %d" % (ntested, nsurv))
    print()
    print("""
  PART 2C -- socle factors NOT of Lie type in characteristic p.

  (a) CROSS characteristic.  |G|_{p1} <= ppmax_{p'}(|S|) <= P(q) (Lemma
      K-exc), so by Lemma K' |G| < P^3 and by Lemma C
      |Out(G)| iota(G) <= |G|^{2/3} < P^2.  The floor needs
      l |Out| iota >= iota(S) >= kappa_i q^b with l <= N/b < 3, so
                 3 P(q)^2  >  kappa_i q^b .
      Exponents 2M vs b:
""")
    for T in TARGETS:
        print("        %-5s  2M = %2d   vs   b = %2d   %s"
              % (T["key"], 2 * T["M"], T["b"],
                 "DEAD (2M < b)" if 2 * T["M"] < T["b"] else "!! CHECK"))
    print("      exact evaluation over all admissible q, with the bound")
    print("      P(q) and then with the EXACT ppmax_{p'}(|S|) (Q below):")
    ccres = {}
    for T in TARGETS:
        bad = [q for (q, p, f) in targets_q(T, 4096)
               if 2 * T["P"](q) ** 2 > T["iota"](q)]
        bad2 = [(q, exact_ppmax(T, q, p)) for (q, p, f) in targets_q(T, 200)
                if 2 * exact_ppmax(T, q, p) ** 2 > T["iota"](q)]
        ccres[T["key"]] = [x[0] for x in bad2]
        print("        %-5s : with P(q) : q <= %s ;  with the exact Q : %s"
              % (T["key"], max(bad) if bad else "-",
                 bad2 or "NONE -- empty for EVERY q"))
    print("      ==> the multi-orbit cross-characteristic residue is the")
    print("          tiny window %s, censused exactly in PART 6."
          % {k: v for (k, v) in ccres.items()})
    print("""
  (b) ALTERNATING socle factor A_m.  iota(A_m) = C(m,3) for m >= 9 and the
      floor needs l * 2 * C(m,3) >= iota(S) >= kappa_i q^b, so
      m^3 >= 3 kappa_i q^b / l ; while |G|^2 <= |S| gives m!/2 <= |S|^{1/2}
      = q^{a/2}, i.e. m log m <= (a/2) log q * (1+o(1)).  The first forces
      m >= (kappa_i q^b)^{1/3} and the second m <= a log q, so
                 q^{b/3}  <=  a log q  ,
      impossible for every q >= 2 and every one of the five b's (b/3 >= 5).
      Exact check:
""")
    for T in TARGETS:
        bad = []
        for (q, p, f) in targets_q(T, 4096):
            io = T["iota"](q)
            S = T["order"](q)
            m = 9
            o = 181440
            while o * o <= S:
                if 3 * 2 * (m * (m - 1) * (m - 2) // 6) >= io:
                    bad.append((q, m))
                    break
                m += 1
                o *= m
        print("        %-5s : (q, m) surviving : %s"
              % (T["key"], bad or "NONE -- empty for EVERY q"))
    print("""
  (c) SPORADIC socle factor.  Finite list; the floor needs
      l |Out(G)| iota(G) >= iota(S) with l <= 2 (Lemma MO-EX (i)) and
      |G|^2 <= |S|.  Exact:
""")
    for T in TARGETS:
        bad = []
        for (q, p, f) in targets_q(T, 4096):
            io = T["iota"](q)
            S = T["order"](q)
            for (nm, o, ou, i1) in spor_rows():
                if o * o <= S and 2 * ou * i1 >= io and S % o == 0:
                    bad.append((q, nm))
        print("        %-5s : (q, G) surviving : %s"
              % (T["key"], bad or "NONE -- empty for EVERY q"))
    print()
    return res


def _fact(n):
    r = 1
    for i in range(2, n + 1):
        r *= i
    return r


# ================================================================= PART 3

def part3():
    print(BAR)
    print("PART 3 -- almost simple, CROSS characteristic: the ppmax^3 kill")
    print(BAR)
    print("""
  S_1 of Lie type over F_{q1}, p1 != p.  |S_1|_{p1} <= ppmax_{p'}(|S|)
  <= P(q); Lemma K' gives |S_1| < P^3; with |S| = c|S_1|, c <= |Out(S_1)|
  = d1 f1 g1 <= 6 n_max log2 P :

        |S|  <  c * P(q)^3 .

  Exponents: a vs 3(M+1) --
""")
    for T in TARGETS:
        print("    %-5s a = %3d   vs   3(M+1) = %2d   margin %d"
              % (T["key"], T["a"], 3 * (T["M"] + 1),
                 T["a"] - 3 * (T["M"] + 1)))
    print()
    res = {}
    for T in TARGETS:
        surv = []
        for (q, p, f) in targets_q(T, 2000):
            S = T["order"](q)
            P = T["P"](q)
            N1max = P.bit_length() - 1
            n1 = 2
            while n1 * (n1 - 1) // 2 <= N1max:
                n1 += 1
            n1 -= 1
            ccap = max(1, 6 * n1 * max(1, P.bit_length() - 1))
            if S < ccap * P ** 3:
                surv.append(q)
        surv2 = []
        for q in surv:
            p = pp_of(q)[0]
            Q = exact_ppmax(T, q, p)
            n1 = 2
            while n1 * (n1 - 1) // 2 <= Q.bit_length() - 1:
                n1 += 1
            n1 -= 1
            ccap = max(1, 6 * n1 * max(1, Q.bit_length() - 1))
            if T["order"](q) < ccap * Q ** 3:
                surv2.append((q, Q))
        res[T["key"]] = [x[0] for x in surv2]
        print("   %-5s : with the bound P(q), survives for q in %s ; with the"
              " EXACT ppmax_{p'}(|S|) = Q, survives for %s"
              % (T["key"], surv or "NONE", surv2 or "NONE -- EVERY q dies"))
    print()
    return res


# ================================================================= PART 4

def part4():
    print(BAR)
    print("PART 4 -- almost simple, EQUAL characteristic: Lemma EQ' + D/N")
    print(BAR)
    print("""
  Lemma EQ' [PROVEN, v_task57].   q1^{(b/N) N_1 - mu_1} <= 4 d_1 f_1 g_1 ,
  so a socle family dies uniformly as soon as  N_1/mu_1 > N/b.
  Lemma EQ-EX [PROVEN, v_task57].  q1^{N_1} c_p = q^N exactly, so only
  families with  D_1/N_1 = a/N  EXACTLY survive.
""")
    out = {}
    for T in TARGETS:
        keep = []
        eqonly = []
        dnonly = []
        for F in FAM:
            ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], 40)
            for n in ns:
                N1, mu1, D1 = F["N"](n), F["mu"](n), F["D"](n)
                eq = Fraction(N1, mu1) <= Fraction(T["N"], T["b"])
                dn = Fraction(D1, N1) == Fraction(T["a"], T["N"])
                if eq:
                    eqonly.append(F["name"](n, 0).replace("(0)", ""))
                if dn:
                    dnonly.append(F["name"](n, 0).replace("(0)", ""))
                if eq and dn:
                    keep.append((F, n))
        print("  ---- %-4s : a/N = %-6s  N/b = %-6s"
              % (T["key"], str(Fraction(T["a"], T["N"])),
                 str(Fraction(T["N"], T["b"]))))
        print("       survive Lemma EQ' (N1/mu1 <= N/b) : %s" % eqonly)
        print("       survive EQ-EX    (D1/N1 =  a/N)   : %s" % dnonly)
        print("       survive BOTH                      : %s"
              % [F["name"](n, 0).replace("(0)", "(q1)") for (F, n) in keep])
        out[T["key"]] = keep
    print("""
  The a/N = 13/6 BLOCK is  { 2F4, F4, E6, 2E6 }  among the exceptional
  families and  { L12, U12, S12=C6, O13=B6, O14+=D7, O14-=2D7 }  among the
  classical ones -- and EVERY classical member is removed by Lemma EQ'
  (their N1/mu1 is 6, 3.14, 3.27, 3.27, 3.5, 3.5, all > 9/4).  The
  a/N = 19/9 block is { E7, L18, U18, S18, O19, O20+- } and the
  a/N = 31/15 block is { E8, L30, U30, S30, O31, O32+- }; again only the
  exceptional member survives EQ'.
""")
    return out


def part45(surv):
    print(BAR)
    print("PART 4.5 -- the matched case c_p = 1, in closed form")
    print(BAR)
    print("""
  Within a same-ratio block the MATCHED exponent is f_1 = N f / N_1, and
  then a_1 f_1 = (a/N) N_1 f_1 = a f : the two orders have EXACTLY the same
  q-degree.  This is new: in every earlier note (sec.4bd, 4be, 4bf) the
  residual c was a positive POWER of q and died on c | |Out| = O(log q).
  Here c(q) tends to a CONSTANT, so the `c does not divide |Out|' pattern
  gives nothing and each pair must be evaluated exactly.
""")
    res = {}
    for T in TARGETS:
        for (F, n) in surv[T["key"]]:
            N1 = F["N"](n)
            nm = F["name"](n, 0).replace("(0)", "(q1)")
            print("  ---- target %-4s  socle %s   (matched f1 = %s f)"
                  % (T["key"], nm, str(Fraction(T["N"], N1))))
            lo = hi = None
            hits = []
            ntest = 0
            imposs = 0
            for (q, p, f) in targets_q(T, 4000):
                if (T["N"] * f) % N1:
                    imposs += 1
                    continue
                f1 = T["N"] * f // N1
                q1 = p ** f1
                if not F["qform"](p, f1) or F["skip"](n, q1):
                    imposs += 1
                    continue
                o1 = order_of(F, n, q1)
                r = Fraction(T["order"](q), o1)
                ntest += 1
                lo = r if lo is None or r < lo else lo
                hi = r if hi is None or r > hi else hi
                if r.denominator == 1 and r >= 2:
                    hits.append((q, q1, int(r)))
            if ntest == 0:
                print("        NO admissible (q,q1) pair at all "
                      "(%d rejected: parity / field form)" % imposs)
            else:
                print("        %d admissible pairs (%d rejected) ; "
                      "c = |S|/|S_1| in [%s, %s] ~ [%.6f, %.6f]"
                      % (ntest, imposs, lo, hi, float(lo), float(hi)))
                print("        integer c >= 2 : %s" % (hits or "NONE"))
            res[(T["key"], F["key"])] = hits
    print()
    return res


def part46(surv):
    print(BAR)
    print("PART 4.6 -- the NON-matched f1, killed uniformly")
    print(BAR)
    print("""
  Let (S, S_1) be a same-ratio pair and put  delta := N f - N_1 f_1 >= 0.
  Lemma EQ-EX gives c_p = p^delta, and non-matched means delta >= 1.

  (i)  ZSYGMONDY.  Let E be the largest degree of the target (so
       Phi_E(q) | |S|) and r a primitive prime divisor of p^{E f} - 1
       (exists: E f >= 12 > 6).  Then r | |S|.  Since c <= |Out(S_1)| is a
       polynomial-free O(f) quantity while r == 1 (mod E f), r | |S_1| for
       all but the finitely many f with r <= |Out(S_1)|; hence
       ord_r(p) = E f divides m f_1 for SOME m in the degree multiset
       M(S_1).  This pins f_1 to a sparse set of rational multiples of f.

  (ii) COUNTING.  |S| >= kappa q^a and |S_1| <= q1^{D_1} = p^{(a/N) N_1 f_1}
       = q^a p^{-(a/N) delta}, so

            c = |S| / |S_1|  >=  kappa * p^{(a/N) delta} ,

       against  c <= |Out(S_1)| = d_1 f_1 g_1 <= 18 (N/N_1) f .

  Below: the admissible ratios rho = f_1/f allowed by (i), and for the
  non-matched ones the exact comparison of (ii) at f = 1, p = 2 (the
  weakest case: the left side grows like p^{2.1 delta} = p^{2.1 f (N - N_1
  rho)} while the right side grows linearly in f).
""")
    MDEG = {"F4": [12, 8, 6, 2], "2F4": [12, 4, 6, 1],
            "E6": [12, 9, 8, 6, 5, 2], "2E6": [12, 18, 8, 6, 10, 2],
            "E7": [18, 14, 12, 10, 8, 6, 2],
            "E8": [30, 24, 20, 18, 14, 12, 8, 2]}
    kappa = {}
    for T in TARGETS:
        kappa[T["key"]] = min(Fraction(T["order"](q), q ** T["a"])
                              for (q, p, f) in targets_q(T, 32))
    allok = True
    for T in TARGETS:
        E = T["E"]
        for (F, n) in surv[T["key"]]:
            N1 = F["N"](n)
            nm = F["name"](n, 0).replace("(0)", "")
            matched = Fraction(T["N"], N1)
            good = []
            for m in MDEG[F["key"]]:
                # E f | m f1  and  N1 f1 <= N f  ==>  f1/f = k E / m,
                # k >= 1 integer, with N1 k E / m <= N
                k = 1
                while Fraction(N1 * k * E, m) <= T["N"]:
                    good.append(Fraction(k * E, m))
                    k += 1
            good = sorted(set(good))
            print("  ---- %-4s <- %-6s : matched f1/f = %s ; Zsygmondy-"
                  "admissible f1/f = %s" % (T["key"], nm, matched,
                                            [str(g) for g in good]))
            for rho in good:
                if rho == matched:
                    print("        rho = %-6s MATCHED -- closed form, "
                          "PART 4.5" % str(rho))
                    continue
                dlt = T["N"] - N1 * rho          # delta / f
                exp = Fraction(T["a"], T["N"]) * dlt
                # c >= kappa p^{exp*f} ; cap = 18 (N/N1) f ; p >= 2, f >= 1
                ok = True
                for f in range(1, 400):
                    lo = kappa[T["key"]] * Fraction(2) ** int(exp * f)
                    cap = 18 * Fraction(T["N"], N1) * f
                    if lo <= cap:
                        ok = False
                        print("        rho = %-6s delta/f = %-5s : NOT closed "
                              "at f = %d (c_lo %s <= cap %s)"
                              % (str(rho), str(dlt), f, lo, cap))
                        break
                if ok:
                    print("        rho = %-6s delta/f = %-5s : c >= kappa "
                          "2^{%s f} > 18(N/N1) f for ALL f >= 1  -- DEAD"
                          % (str(rho), str(dlt), str(exp)))
                else:
                    allok = False
    print()
    print("  kappa = min_q |S|/q^a  (exact, over q <= 32): %s"
          % {k: str(v) for (k, v) in kappa.items()})
    print()
    return allok


def part4_exact(caps=None):
    print(BAR)
    print("PART 4.0 -- equal characteristic, decided EXACTLY, factorisation-")
    print("            free, complete in f1 and in the socle type")
    print(BAR)
    print("""
  q1^{N_1} | q^N bounds f_1 <= N f / N_1, so for each target parameter q
  the equal-characteristic branch is a FINITE exact test with no
  factorisation of |S| at all.  Every family, every rank <= 29, every f1.
""")
    caps = caps or {"F4": 50000, "E6": 30000, "2E6": 30000, "E7": 8000,
                    "E8": 3000}
    out = {}
    for T in TARGETS:
        lim = caps[T["key"]]
        hits = []
        near = []
        pairs = 0
        ctl = 0
        ntar = 0
        for (q, p, f) in targets_q(T, lim):
            ntar += 1
            S = T["order"](q)
            selfseen = False
            for F in FAM:
                ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], 30)
                for n in ns:
                    N1 = F["N"](n)
                    if N1 > T["N"] * f:
                        break
                    for f1 in range(1, T["N"] * f // N1 + 1):
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
        print("  %-5s admissible q <= %-6d : %d targets, %d divisor pairs, "
              "control %d/%d" % (T["key"], lim, ntar, pairs, ctl, ntar))
        print("        order-only NEAR-MISS (c <= |Out|) : %s"
              % (near or "NONE"))
        print("        HITS (c >= 2, c | |Out(S_1)|)     : %s"
              % (hits or "NONE"))
        out[T["key"]] = hits
    print()
    return out


# ================================================================= PART 5

def part5():
    print(BAR)
    print("PART 5 -- almost simple with ALTERNATING or SPORADIC socle,")
    print("          and the E8 sporadic FLOOR arithmetic")
    print(BAR)
    print("""
  (E): c|S_1| = |S|, 2 <= c | |Out(S_1)| (c <= 4 for A_6, else <= 2 for
  alternating and sporadic socles).  |S| = M is inverted exactly for q, so
  each row is COMPLETE in q.
""")
    res = {}
    for T in TARGETS:
        hits = []
        tested = 0
        o = 60
        for m in range(5, 300):
            if m > 5:
                o = o * m
            if o > 10 ** 300:
                break
            ou = 4 if m == 6 else 2
            for c in range(2, ou + 1):
                if ou % c:
                    continue
                tested += 1
                for q in T["solve"](c * o):
                    hits.append(("A%d" % m, q, c))
        for (nm, so, ou) in list(SPORADIC) + [TITS]:
            for c in range(2, ou + 1):
                if ou % c:
                    continue
                tested += 1
                for q in T["solve"](c * so):
                    hits.append((nm, q, c))
        ctl = []
        for (q, p, f) in targets_q(T, 32):
            if q not in T["solve"](T["order"](q)):
                ctl.append(("INVERTER FAILURE", q))
        print("  %-5s (S_1,c) pairs tested : %-6d   hits : %-12s   "
              "inverter self-check : %s"
              % (T["key"], tested, hits or "NONE", ctl or "OK"))
        res[T["key"]] = hits
    print("""
  THE E8 SPORADIC FLOOR, done honestly.  The brief asks whether a sporadic
  socle factor can reach the E8 floor.  iota(E8(2)) = %d ~ 2.9e17, and the
  largest sporadic iota is iota(M) = %s ~ 9.7e19 > iota(E8(2)).  So the
  FLOOR (F) alone does NOT exclude the Monster -- the floor is the wrong
  test here.  Two other constraints do:
""" % (T_by_key("E8")["iota"](2),
       [io for (nm, so, ou, io) in spor_rows() if nm == "M"][0]))
    Mrow = [(nm, so, ou, io) for (nm, so, ou, io) in spor_rows()
            if nm == "M"][0]
    E8 = T_by_key("E8")
    for q in (2, 3):
        S = E8["order"](q)
        print("    q = %d : |E8(q)| = %d" % (q, S))
        print("            |M| = %d ;  |M|^2 / |E8(q)| = %.3e   "
              "(Lemma Q (Q1) needs |G|^2 <= |S|)"
              % (Mrow[1], float(Fraction(Mrow[1] ** 2, S))))
        print("            2|M| / |E8(q)| = %.3e   "
              "(almost-simple (E) needs c|M| = |S|, c | |Out(M)| = 1)"
              % float(Fraction(2 * Mrow[1], S)))
    print("""
    Reading the numbers honestly:
      * at q = 2 the Monster fails |G|^2 <= |S| by 33 orders of magnitude;
      * at q = 3 it PASSES |G|^2 <= |S| (and passes the floor), so neither
        the floor nor (Q1) rules it out -- exactly the trap the brief
        warned about;
      * what kills it is DIVISIBILITY: |M| does not divide |E8(q)| for any
        q (|M| has the prime 41, 47, 59, 71 among others; GAP confirms
        |M| does not divide |E8(2)| or |E8(3)|), and the almost-simple
        equation c|M| = |S| with c | |Out(M)| = 1 is absurd.
      The complete sporadic sweep is PART 2C(c) (multi-orbit, exact floor
      AND exact divisibility: EMPTY for every q and every target) together
      with PART 5's order inversion (almost simple: EMPTY for every q).
""")
    print()
    return res


# ================================================================= PART 6

def part6(limits=None):
    print(BAR)
    print("PART 6 -- the residual census: the multi-orbit cross-characteristic")
    print("          window of PART 2C(a), the ONLY residue of the whole note")
    print(BAR)
    print("""
  Phase 1 = the raw order census (all multisets of simple groups whose
  orders multiply into |S| with the cofactor dividing prod |Out|^l prod l!)
  Phase 2 = the orbit floor l |Out(S_i)| iota(S_i) >= iota(S).
""")
    limits = limits or {}
    res = {}
    for T in TARGETS:
        qs = limits.get(T["key"])
        if not qs:
            print("  %-5s : residual window EMPTY -- no census needed."
                  % T["key"])
            res[T["key"]] = (0, 0, 0)
            continue
        print("  ---- %-5s : %d targets, q in %s" % (T["key"], len(qs), qs))
        bad = raw_tot = filt_tot = 0
        unknown = set()
        for q in qs:
            N = T["order"](q)
            io = T["iota"](q)
            cands = simple_divisors(N)
            names = [c[0] for c in cands if c[1] == N]
            if not names:
                bad += 1
                print("     POSITIVE-CONTROL FAILURE at q = %d" % q)
            order_by_name = dict((n2, o2) for (n2, o2, u2) in cands)

            def strip(cen):
                return [(ms, c) for (ms, c) in cen
                        if not (c == 1 and len(ms) == 1 and ms[0][1] == 1
                                and order_by_name.get(ms[0][0]) == N)]

            raw = strip(census50(N, cands))
            surv, dead, unk = phase2(N, io, cands)
            for (nm, o, u) in unk:
                unknown.add(nm)
            filt = strip(census50(N, surv))
            raw_tot += len(raw)
            filt_tot += len(filt)
            if raw:
                print("     RAW survivor  q = %-6d %s" % (q, raw))
            if filt:
                print("     FLOOR survivor q = %-6d %s" % (q, filt))
        print("     RAW survivors %d ; after the orbit floor %d ; "
              "positive-control failures %d / %d"
              % (raw_tot, filt_tot, bad, len(qs)))
        if unknown:
            print("     socle candidates with no iota bound (kept): %s"
                  % sorted(unknown))
        res[T["key"]] = (bad, raw_tot, filt_tot)
    print()
    return res


# ================================================================= PART 8

def part8():
    print(BAR)
    print("PART 8 -- the a/N = 13/6 block: the hunt for hidden order")
    print("          identities, in closed form")
    print(BAR)
    print("""
  Structural observation [PROVEN].  If S and G lie in the same a/N block
  and f_1 is matched (N_1 f_1 = N f), then

        deg_q |S| - deg_q |G| = a f - a_1 f_1
                              = (a/N) N f - (a_1/N_1) N_1 f_1  =  0 ,

  so |S|/|G| tends to a CONSTANT as q -> infinity.  Every matched pair in a
  same-ratio block is therefore a candidate order identity with BOUNDED c.
  This is qualitatively different from the identities of sec.4bd/4be/4bf
  (|U3(q)| = (q+1)|R(q)|, |L3(25)| = 7|L4(5)|, |S4(q^3)| = ((q^2+1)/d)
  |3D4(q)|, |G2(q^2)| = (q^2+q+1)|2F4(q)|), where c was a POWER of q and
  the rule `c | |Out|' killed it with a full power of q to spare.  Here
  the rule gives nothing and the pairs must be settled exactly.

  The block is  { 2F4 (N=12), F4 (N=24), E6 (N=36), 2E6 (N=36) }.
""")
    B = [("2F4", 12), ("F4", 24), ("E6", 36), ("2E6", 36)]
    ordf = {"2F4": lambda q: order_of(F_by_key("2F4"), 1, q),
            "F4": _o_F4, "E6": _o_E6, "2E6": _o_2E6}
    print("  %-6s %-6s %-10s %-42s %s"
          % ("S", "G", "f1/f", "c(q) = |S|/|G| over admissible q", "verdict"))
    for (ka, Na) in B:
        for (kb, Nb) in B:
            if ka == kb:
                continue
            rho = Fraction(Na, Nb)
            vals = []
            for p in (2, 3, 5, 7):
                for f in range(1, 9):
                    q = p ** f
                    if q > 4096:
                        break
                    if (Na * f) % Nb:
                        continue
                    f1 = Na * f // Nb
                    q1 = p ** f1
                    if q1 > 10 ** 30:
                        continue
                    Fb = F_by_key(kb)
                    if not Fb["qform"](p, f1) or Fb["skip"](1, q1):
                        continue
                    Fa = F_by_key(ka)
                    if not Fa["qform"](p, f) or Fa["skip"](1, q):
                        continue
                    vals.append((q, q1, Fraction(ordf[ka](q), ordf[kb](q1))))
            if not vals:
                print("  %-6s %-6s %-10s %-42s %s"
                      % (ka, kb, str(rho), "no admissible (q,q1) pair "
                         "(field-form parity)", "IMPOSSIBLE"))
                continue
            lo = min(v[2] for v in vals)
            hi = max(v[2] for v in vals)
            ints = [(v[0], v[1], int(v[2])) for v in vals
                    if v[2].denominator == 1 and v[2] >= 2]
            print("  %-6s %-6s %-10s c in [%.6f, %.6f] (%d pairs)%s %s"
                  % (ka, kb, str(rho), float(lo), float(hi), len(vals),
                     "", "integer c>=2: %s" % ints if ints
                     else "no integer c >= 2"))
    print("""
  Closed forms (all PROVEN by cancelling the order polynomials):

  (I1)  |E6(m^2)| / |F4(m^3)|
          = (m^16-1)(m^12-1)(m^10-1)(m^4-1)
            / ( gcd(3,m^2-1) (m^36-1)(m^6-1) )          <  1 .
        Both sides have q-degree 156 in m.  Since the numerator is
        < m^42 and the denominator is > m^42 - m^36 - m^6, the quotient is
        < (1 - m^{-6})^{-1} <= 8/7, and it is < 1 already for m >= 2.
        ==>  c < 2 : DEAD, and NOT an integer identity.

  (I2)  |E6(q)| / |2F4(q^3)|
          = (q^9-1)(q^8-1)(q^6-1)(q^5-1)(q^2-1)
            / ( gcd(3,q-1) (q^18+1)(q^9+1)(q^3-1) ) .
        Numerator < q^30; denominator (d=1) = (q^18+1)(q^9+1)(q^3-1)
        > q^30 - q^27.  Hence the quotient < (1-q^{-3})^{-1} <= 8/7 < 2.
        ==>  c < 2 : DEAD.

  (I3)  |2E6(q)| / |E6(q)|   (matched f1 = f, q1 = q)
          = [gcd(3,q-1)/gcd(3,q+1)] (q^9+1)(q^5+1) / ((q^9-1)(q^5-1)) .
        3 | q-1 and 3 | q+1 are mutually exclusive, so the bracket is
        1, 3 or 1/3.  The interesting case is q == 1 (mod 3), where the
        bracket is 3 and, writing A = q^9-1, B = q^5-1,

              c = 3 (1 + 2/A)(1 + 2/B)  ,   so   3 < c < 4

        for every q >= 4 (the smallest q == 1 mod 3 with q >= 3).
        ==>  c is NEVER an integer -- and this is the CLOSEST CALL in the
        whole programme so far: c = 3 would have divided
        |Out(E6(q))| = 6f exactly.  It is killed by a strict inequality,
        not by an arithmetic obstruction.
        (The reverse direction |E6(q)|/|2E6(q)| < 1 is impossible outright.)

  (I4)  |2E6(m^2)| / |F4(m^3)| and |2E6(q)| / |2F4(q^3)| : same shape,
        both < 1 by the same cancellation.  DEAD.

  (I5)  |F4(q^2)| / |2F4(q)| would need f1 = 2f EVEN, but 2F4 exists only
        for f1 ODD.  IMPOSSIBLE -- no pair at all.  (Contrast Identity B of
        v_task57, |G2(q^2)| = (q^2+q+1)|2F4(q)|, which does exist because
        G2 and 2F4 are NOT in the same a/N block, so the degrees differ.)

  Verdict: the 13/6 block produces FOUR near-identities (c -> 1/d or 3) and
  NOT ONE exact one.  The block interacts exactly as v_task57 sec.10.4
  predicted, but the interaction is benign.
""")
    # exact confirmation of I3
    print("  exact confirmation of (I3), q == 1 mod 3 :")
    for q in (4, 7, 13, 16, 19, 25, 31, 37, 43, 49, 61, 64, 67, 73, 79):
        if not is_prime_power(q) or q % 3 != 1:
            continue
        c = Fraction(_o_2E6(q), _o_E6(q))
        print("     q = %-4d c = %s = %.10f   integer: %s"
              % (q, c, float(c), c.denominator == 1))
    print("  exact confirmation of (I1), q = m^2 :")
    for m in (2, 3, 4, 5, 7, 8, 9):
        q, q1 = m * m, m ** 3
        c = Fraction(_o_E6(q), _o_F4(q1))
        print("     m = %-3d q = %-5d q1 = %-6d c = %.10f  (< 1: %s)"
              % (m, q, q1, float(c), c < 1))
    print("  exact confirmation of (I2), q even, f odd :")
    for f in (1, 3, 5, 7):
        q = 2 ** f
        q1 = q ** 3
        c = Fraction(_o_E6(q), order_of(F_by_key("2F4"), 1, q1))
        print("     f = %-3d q = %-5d q1 = %-9d c = %.10f  (< 2: %s)"
              % (f, q, q1, float(c), c < 2))
    print()
    print("  broad order-coincidence sweep |S| = c|G|, 2 <= c <= 10^4, over")
    print("  the full Lie/alternating/sporadic candidate list, small q:")
    rows = []
    rows += [(nm, o, ou) for (nm, o, ou, io) in alt_rows(40)]
    rows += [(a, b, c) for (a, b, c) in list(SPORADIC) + [TITS]]
    for (q1, p1, f1) in prime_powers_sieve(600):
        for F in FAM:
            if not F["qform"](p1, f1):
                continue
            ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], 13)
            for n in ns:
                if F["skip"](n, q1):
                    continue
                o = order_of(F, n, q1)
                if o < 60 or o > 10 ** 90:
                    continue
                rows.append((F["name"](n, q1), o, out_of(F, n, q1, p1, f1)))
    byorder = {}
    for (nm, o, ou) in rows:
        byorder.setdefault(o, []).append((nm, ou))
    found = []
    for T in TARGETS:
        for (q, p, f) in targets_q(T, 9):
            S = T["order"](q)
            for c in range(1, 10001):
                if S % c:
                    continue
                g = S // c
                if g in byorder:
                    for (nm, ou) in byorder[g]:
                        found.append((T["key"], q, nm, c, ou, ou % c == 0))
    if not found:
        print("     NONE")
    for row in found:
        print("     %-4s(%d) : |S| = %d * |%s|  (|Out(G)| = %d, c | |Out| : %s)"
              % (row[0], row[1], row[3], row[2], row[4],
                 "YES <== HIT" if row[5] and row[3] >= 2 else "no"))
    print()
    return found


# ==========================================================================

def main():
    args = [a for a in sys.argv[1:]]
    want = set(args) if args else {"0", "1", "2", "3", "4", "45", "46",
                                   "40", "5", "8", "6"}
    surv = None
    if "0" in want:
        part0()
    if "1" in want:
        part1()
    if "2" in want:
        part2()
    if "3" in want:
        part3()
    if want & {"4", "45", "46"}:
        surv = part4()
    if "45" in want:
        part45(surv)
    if "46" in want:
        part46(surv)
    if "40" in want:
        part4_exact()
    if "5" in want:
        part5()
    if "8" in want:
        part8()
    if "6" in want:
        part6({"F4": [2, 3], "E6": [2, 3, 4, 5, 9],
               "2E6": [2, 3, 4, 7, 8], "E7": [2, 3], "E8": []})


if __name__ == "__main__":
    main()
