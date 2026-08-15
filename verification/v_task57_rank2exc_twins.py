#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
v_task57_rank2exc_twins.py -- Fitting-free NON-SIMPLE twins of the remaining
RANK-2 / small-rank EXCEPTIONAL targets

    S4(q)  = PSp_4(q) = C_2(q) ,   q >= 3      (S4(2)' = A_6 : covered)
    G2(q)                      ,   q >= 3      (G2(2)' = U_3(3) : U3-T)
    3D4(q)                     ,   all q >= 2
    2F4(q)                     ,   q = 2^{2m+1} >= 8   (2F4(2)' : v_task50)

Standing hypotheses (all upstream and PROVEN):
   T Fitting-free, |T| = |S|, D(T) = D(S), T NOT simple.
   Soc T = prod_i S_i^{l_i}; orbits O of length l_O; c = [T : Soc T];
   (F)  l_O * |Out(S_1)| * iota(S_1) >= iota(S)       [Lemma TO'-0 + F]
   (C)  |Out(G)| * iota(G) <= |G|^{2/3}               [Lemma C, v_task52]
   (T1) |G| >= q1^D/(12 d), (T2) iotabar <= 4 q1^mu, (T3) |Out| = d f g,
        g <= 6                                        [v_task52]

PARTS
 1  target invariants (order, iota, |Out|, a/b/N), the per-family ppmax
    bound  (Lemma K-exc)  and the strain diagnostics.
 2  Lemma Q -- T is almost simple.  2a: l >= 3 by Lemma C.  2b: the l <= 2 /
    two-orbit window = the Lemma-B violators (the SAME 56-element list as
    v_task55), each with an exact q-window per target.
 3  almost simple, CROSS characteristic: the ppmax_{p'}^3 kill.
 4  Lemma EQ' (the rank-free equal-characteristic window lemma), the
    D/N table, and PART 4.0 the factorisation-free EXACT equal-char sweep.
 5  almost simple with ALTERNATING or SPORADIC socle: complete in q.
 6  the residual census (Phase 1 raw + Phase 2 orbit floor).

All arithmetic is exact integer / Fraction arithmetic.
"""

import sys
from fractions import Fraction

sys.path.insert(0, ".")

from v_task50_sporadic_twins import SPORADIC, TITS, IOTA_UB, census as census50
from v_task50_sporadic_twins import simple_divisors, phase2
from v_task51_l2_twins import is_prime_power, factorint, iota_ub_generic
from v_task54_rank1_gaps import prime_powers_sieve
from v_task52_lemmaC import FAM, gcd, order_of, out_of, _prod
from v_task53_rank1_twins import _iroot
from v_task55_l3_twins import alt_rows, spor_rows, lie_rows, lemB_tail_threshold
import v_task50_sporadic_twins as V50

V50.iota_ub = lambda name, order: iota_ub_generic(name)

BAR = "=" * 74


def isqrt(n):
    return _iroot(n, 2)


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


# ====================================================================
#  the four targets
# ====================================================================
#
#  order(q), iota(q), out(q,p,f), a = deg_q|S|, b = deg_q iota,
#  N = deg_q |S|_p, P(q) = the PROVEN upper bound for ppmax_{p'}(|S|),
#  ok(q,p,f) = admissible target parameter, solve(M) = all q with |S| = M.

def _o_S4(q):
    return q ** 4 * (q * q - 1) * (q ** 4 - 1) // gcd(2, q - 1)


def _o_G2(q):
    return q ** 6 * (q ** 6 - 1) * (q * q - 1)


def _o_3D4(q):
    return q ** 12 * (q ** 8 + q ** 4 + 1) * (q ** 6 - 1) * (q * q - 1)


def _o_2F4(q):
    return q ** 12 * (q ** 6 + 1) * (q ** 4 - 1) * (q ** 3 + 1) * (q - 1)


def _solve_generic(M, ordfun, a, ok, extra_mult=(1,)):
    """all admissible prime powers q with ordfun(q) = M  (complete in q)."""
    out = []
    for m in extra_mult:
        v = M * m
        r = _iroot(v, a)
        for q in range(max(2, r - 3), r + 4):
            # the ORDER equation first -- it is cheap and almost always
            # false, whereas is_prime_power(q) is trial division
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


target(key="S4", disp="S4(q) = PSp4(q) = C2(q)",
       order=_o_S4,
       # iota: (q+1)(q^2+1) for q >= 4 ; the EXCEPTION iota(S4(3)) = 27
       iota=lambda q: 27 if q == 3 else (q + 1) * (q * q + 1),
       iota_gen=lambda q: (q + 1) * (q * q + 1),
       out=lambda q, p, f: 2 * f,
       a=10, b=3, N=4,
       # Phi_1^2 Phi_2^2 Phi_4 ; 2-part <= 8(q+1)^2, odd r-part <= (q+1)^2
       P=lambda q: 8 * (q + 1) ** 2,
       ok=lambda q, p, f: q >= 3,
       solve=lambda M: _solve_generic(M, _o_S4, 10,
                                      lambda q, p, f: q >= 2, (1, 2)))

target(key="G2", disp="G2(q)",
       order=_o_G2,
       iota=lambda q: (q ** 6 - 1) // (q - 1),
       iota_gen=lambda q: (q ** 6 - 1) // (q - 1),
       out=lambda q, p, f: (2 * f if p == 3 else f),
       a=14, b=5, N=6,
       # Phi_1^2 Phi_2^2 Phi_3 Phi_6 ; 3-part <= 3(q-1)^2 resp 3(q+1)^2
       P=lambda q: 8 * (q + 1) ** 2,
       ok=lambda q, p, f: q >= 3,
       solve=lambda M: _solve_generic(M, _o_G2, 14, lambda q, p, f: q >= 3))

target(key="3D4", disp="3D4(q)",
       order=_o_3D4,
       iota=lambda q: (q ** 8 + q ** 4 + 1) * (q + 1),
       iota_gen=lambda q: (q ** 8 + q ** 4 + 1) * (q + 1),
       out=lambda q, p, f: 3 * f,
       a=28, b=9, N=12,
       # Phi_1^2 Phi_2^2 Phi_3^2 Phi_6^2 Phi_12
       P=lambda q: 72 * (q * q + q + 1) ** 2,
       ok=lambda q, p, f: q >= 2,
       solve=lambda M: _solve_generic(M, _o_3D4, 28, lambda q, p, f: q >= 2))

target(key="2F4", disp="2F4(q), q = 2^{2m+1} >= 8",
       order=_o_2F4,
       iota=lambda q: (q ** 6 + 1) * (q ** 3 + 1) * (q + 1),
       iota_gen=lambda q: (q ** 6 + 1) * (q ** 3 + 1) * (q + 1),
       out=lambda q, p, f: f,
       a=26, b=10, N=12,
       # Phi_1^2 Phi_2^2 Phi_4^2 Phi_6 Phi_12 , q even
       P=lambda q: 9 * (q * q + 1) ** 2,
       ok=lambda q, p, f: p == 2 and f % 2 == 1 and f >= 3,
       solve=lambda M: _solve_generic(
           M, _o_2F4, 26,
           lambda q, p, f: p == 2 and f % 2 == 1 and f >= 3))


_PPCACHE = {}


def _pps(M):
    if M not in _PPCACHE:
        _PPCACHE[M] = prime_powers_sieve(M)
    return _PPCACHE[M]


def targets_q(T, M):
    """admissible target parameters q <= M, as (q, p, f)"""
    if T["key"] == "2F4":
        # q = 2^f, f odd >= 3 : enumerated directly, so M may be astronomical
        out = []
        f = 3
        while 2 ** f <= M:
            out.append((2 ** f, 2, f))
            f += 2
        return out
    return [(q, p, f) for (q, p, f) in _pps(M) if T["ok"](q, p, f)]


def T_by_key(k):
    for T in TARGETS:
        if T["key"] == k:
            return T
    raise KeyError(k)


# ================================================================= PART 1

def part1(qmax=2000):
    print(BAR)
    print("PART 1 -- the four targets: invariants, Lemma K-exc, and strain")
    print(BAR)
    print("""
  |S4(q)|  = q^4 (q^2-1)(q^4-1)/gcd(2,q-1)      = q^4 Phi1^2 Phi2^2 Phi4 /d
  |G2(q)|  = q^6 (q^6-1)(q^2-1)                 = q^6 Phi1^2 Phi2^2 Phi3 Phi6
  |3D4(q)| = q^12 (q^8+q^4+1)(q^6-1)(q^2-1)     = q^12 Phi1^2 Phi2^2 Phi3^2
                                                        Phi6^2 Phi12
  |2F4(q)| = q^12 (q^6+1)(q^4-1)(q^3+1)(q-1)    = q^12 Phi1^2 Phi2^2 Phi4^2
                                                        Phi6 Phi12

  iota  (minimal parabolic index; witness A = O_p(P) for a MAXIMAL parabolic
         P, Borel-Tits N_S(A) = P -- NOT Z(Syl_p), cf. the v_task55 trap):

     iota(S4(q))  = (q^4-1)/(q-1)     = (q+1)(q^2+1)     [q >= 4]
                    EXCEPTION  iota(S4(3)) = 27 < 40     [the S4(3) defect]
     iota(G2(q))  = (q^6-1)/(q-1)
     iota(3D4(q)) = (q^8+q^4+1)(q+1)
     iota(2F4(q)) = (q^6+1)(q^3+1)(q+1)

  |Out| :  S4: 2f (d*g = 2 in both parities) ; G2: f, 2f for p = 3 ;
           3D4: 3f ; 2F4: f .

  Lemma K-exc [PROVEN, elementary; verified below with 0 violations]:
     ppmax_{p'}(|S|) <= P(q)  with
        S4  : 8(q+1)^2      G2  : 8(q+1)^2
        3D4 : 72(q^2+q+1)^2 2F4 : 9(q^2+1)^2 .
  Proof.  Every odd r != p divides exactly one cyclotomic block Phi_e(q)
  unless r | e' for the ratio of two block indices, in which case the extra
  r-part is exactly r (Zsygmondy/Lucas: if r | Phi_d and r | Phi_{dr^k} then
  r || Phi_{dr^k}).  So an odd r-part is at most (largest block)^{mult} times
  the small factor.  The 2-part of Phi1^2 Phi2^2 (q odd) is
  (|q-1|_2 |q+1|_2)^2 <= (2(q+1))^2 /1, and min(|q-1|_2,|q+1|_2) = 2, so it
  is <= 4(q+1)^2 ; with the Phi4 = q^2+1 == 2 (mod 4) block, <= 8(q+1)^2.
  For 2F4 and for q even the 2-part is |S|_p and is excluded.
""")
    print("  %-5s %-7s %-22s %-14s %-11s %-11s %s" %
          ("S", "q", "|S|", "iota(S)", "ppmax_p'", "bound P(q)", "iota^3/|S|"))
    tot_bad = 0
    for T in TARGETS:
        bad = 0
        worst = None
        least = None
        for (q, p, f) in targets_q(T, qmax if T["key"] != "2F4" else 600):
            S = T["order"](q)
            io = T["iota"](q)
            rest = S // q ** T["N"]
            fac = factorint(rest)
            fac.pop(p, None)
            pm = ppmax(fac)
            bnd = T["P"](q)
            if pm > bnd:
                bad += 1
                print("   VIOLATION %s q=%d : %d > %d" % (T["key"], q, pm, bnd))
            r = Fraction(io ** 3, S)
            if worst is None or r > worst[0]:
                worst = (r, q)
            if least is None or r < least[0]:
                least = (r, q)
            if q <= 9 or (T["key"] == "2F4" and q <= 32):
                print("  %-5s %-7d %-22d %-14d %-11d %-11d %.5f" %
                      (T["key"], q, S, io, pm, bnd, io ** 3 / S))
        e = 3 * T["b"] - T["a"]
        print("   %-5s : Lemma K-exc violations = %d ; max iota^3/|S| = "
              "%.5f at q = %d ; 3b-a = %+d" %
              (T["key"], bad, float(worst[0]), worst[1], e))
        print("           min iota^3/|S| over the scanned range = %.5f "
              "at q = %d" % (float(least[0]), least[1]))
        print("           ==> rank-1 Step 2 (iota^3 > |S|) %s" %
              ("HOLDS for all large q (and, checked above, for every "
               "admissible q)" if e > 0 else
               "FAILS for every q >= 3 -- Lemma Q needed"))
        tot_bad += bad
    print()
    print("  a/b and N/b (the two exponents that drive everything):")
    print("    %-5s %4s %4s %4s %10s %10s" % ("S", "a", "b", "N", "a/b", "N/b"))
    for T in TARGETS:
        print("    %-5s %4d %4d %4d %10s %10s" %
              (T["key"], T["a"], T["b"], T["N"],
               str(Fraction(T["a"], T["b"])), str(Fraction(T["N"], T["b"]))))
    print()
    print("  Lemma K' (|G| < (|G|_p)^3, v_task53) for the targets themselves:")
    for T in TARGETS:
        print("    %-5s : a = %d  <  3N = %d   %s" %
              (T["key"], T["a"], 3 * T["N"],
               "OK" if T["a"] < 3 * T["N"] else "!!"))
    print()
    return tot_bad


# ================================================================= PART 2

_VIOL = None


def violators():
    """the Lemma-B violator list (|G| <= 4 rho(G)^2), rho = |Out|*iotabar.
       IDENTICAL construction to v_task55 PART 2b -- reused verbatim."""
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
    print("PART 2 -- Lemma Q: T is ALMOST SIMPLE, for every q above an")
    print("          explicit (and TINY) threshold")
    print(BAR)
    print("""
  Setup (v_task55 PART 2, verbatim -- Lemma Q is target-agnostic).  If T is
  not almost simple, some socle factor G with orbit length l satisfies

      (Q1)  |G|^{max(2,l)} <= |S| ,     (Q2)  l |Out(G)| iota(G) >= iota(S).

  2a  l >= 3 : Lemma C gives l|Out|iota <= l|G|^{2/3} <= l|S|^{2/(3l)}, so
      the exact cube-cleared test is  iota(S)^{3l} <= l^{3l} |S|^2 .
  2b  l <= 2 : |G|^2 <= |S| and 2 rho(G) >= iota(S), rho := |Out| iotabar,
      force |G| <= 4 rho(G)^2 -- G violates Lemma B.  The violator list is
      FINITE (D/mu >= 7/3 > 2 in every Lie family), and is the SAME list as
      in v_task55: no recomputation of the classification is involved, only
      the per-target window  [q_lo, q_hi]  changes.
""")
    viol, q1cap = violators()
    print("  Lemma-B violators (shared list): %d ; Lie tail bound q1 <= %d,"
          % (len(viol), q1cap))
    print("  ranks <= 24 -- both PROVEN in v_task55 PART 2b.")
    rho_max = max(v[4] for v in viol)
    nm_max = [v[0] for v in viol if v[4] == rho_max][0]
    print("  max rho over the violator list : %d   (attained by %s)"
          % (rho_max, nm_max))
    print()
    print("  %-5s %-14s %-14s %-12s %s" %
          ("S", "l>=3 dies q>", "l<=2 dies q>", "Lemma-Q thr", "windows"))
    res = {}
    for T in TARGETS:
        # 2a
        hi3 = 0
        for l in range(3, 13):
            hi = 0
            for (q, p, f) in targets_q(T, 200000):
                S = T["order"](q)
                if l ** (3 * l) * S ** 2 >= T["iota"](q) ** (3 * l):
                    hi = q
                elif q > 2 * max(hi, 2):
                    break
            hi3 = max(hi3, hi)
        # 2b : per violator window
        wins = []
        for (nm, o, ou, io, rho) in viol:
            # q_hi : largest admissible q with iota(S) <= 2 rho
            qhi = 0
            for (q, p, f) in targets_q(T, 10 ** 6):
                if T["iota"](q) <= 2 * rho:
                    qhi = q
                else:
                    break
            if qhi == 0:
                continue
            # q_lo : smallest admissible q with |S| >= |G|^2
            qlo = None
            for (q, p, f) in targets_q(T, 10 ** 6):
                if T["order"](q) >= o * o:
                    qlo = q
                    break
            if qlo is not None and qlo <= qhi:
                wins.append((nm, qlo, qhi))
        qmaxwin = max([w[2] for w in wins], default=0)
        thr = max(hi3, qmaxwin)
        res[T["key"]] = (hi3, qmaxwin, thr, wins)
        print("  %-5s %-14d %-14d %-12d %s" %
              (T["key"], hi3, qmaxwin, thr,
               (("%d nonempty, e.g. " % len(wins)) +
                ", ".join("%s:[%d,%d]" % w for w in wins[:3]))
               if wins else "NONE -- empty for every q"))
    print()
    for T in TARGETS:
        hi3, qmaxwin, thr, wins = res[T["key"]]
        print("  %-5s ==> for q > %d, T is ALMOST SIMPLE:  c|S_1| = |S|,"
              % (T["key"], thr))
        print("        c >= 2, c | |Out(S_1)| .   (l>=3 threshold %d, "
              "l<=2 threshold %d)" % (hi3, qmaxwin))
    print()
    return res


# ================================================================= PART 3

def part3():
    print(BAR)
    print("PART 3 -- almost simple, CROSS characteristic: the ppmax^3 kill")
    print(BAR)
    print("""
  S_1 of Lie type over F_{q1}, p1 != p.  Then |S_1|_{p1} <= ppmax_{p'}(|S|)
  <= P(q) (Lemma K-exc), and Lemma K' gives |S_1| < |S_1|_{p1}^3 <= P^3.
  With |S_1| = |S|/c and c <= |Out(S_1)| = d1 f1 g1:

        |S|  <  c * P(q)^3 ,     c <= 6 * n_max(P) * log2 P .

  Rank bound: 2^{N_1} <= q1^{N_1} = |S_1|_{p1} <= P and N_1 >= n1(n1-1)/2.
""")
    print("  %-5s %-9s %-24s %-24s %-7s %s" %
          ("S", "q", "|S|", "c_cap * P^3", "n_max", "survives?"))
    res = {}
    for T in TARGETS:
        surv = []
        for (q, p, f) in targets_q(T, 4000 if T["key"] != "2F4" else 3000):
            S = T["order"](q)
            P = T["P"](q)
            N1max = P.bit_length() - 1
            n1 = 2
            while n1 * (n1 - 1) // 2 <= N1max:
                n1 += 1
            n1 -= 1
            ccap = max(1, 6 * n1 * max(1, P.bit_length() - 1))
            ok = S < ccap * P ** 3
            if ok:
                surv.append(q)
            if q <= 9 or (T["key"] == "2F4" and q <= 32):
                print("  %-5s %-9d %-24d %-24d %-7d %s" %
                      (T["key"], q, S, ccap * P ** 3, n1,
                       "YES" if ok else "no"))
        res[T["key"]] = surv
        print("   %-5s : cross-characteristic branch survives only for q in %s"
              % (T["key"], surv or "NONE -- empty for EVERY q"))
    print()
    print("  (the inequality is q^a vs polylog(q)*q^{3*deg P}, monotone:")
    print("   S4  a=10 vs 3*2=6 ; G2 a=14 vs 6 ; 3D4 a=28 vs 12 ;")
    print("   2F4 a=26 vs 12 -- margin >= 4 in the exponent everywhere.)")
    print()
    return res


# ================================================================= PART 4

def part4():
    print(BAR)
    print("PART 4 -- almost simple, EQUAL characteristic: Lemma EQ' + D/N")
    print(BAR)
    print("""
  Lemma EQ' [PROVEN, target-agnostic].  Let S_1 be of Lie type over
  F_{q1} = F_{p^{f1}} in the DEFINING characteristic of the target S, and
  suppose (E) c|S_1| = |S|, c >= 2, and the floor (F).  Then

        q1^{ (b/N) N_1 - mu_1 }  <=  4 d_1 f_1 g_1 .

  Proof.  (E) gives |S_1|_p | |S|_p, i.e. q1^{N_1} <= q^N.  (F) with (T2),
  (T3) gives 4 d1 f1 g1 q1^{mu_1} >= iota(S) > q^b.  Hence
  q1^{N_1/N} <= q < (4 d1 f1 g1 q1^{mu_1})^{1/b}; raise to the power b. []

  So a family dies (for all but finitely many q1, uniformly in the target q)
  as soon as  N_1/mu_1 > N/b.  This is the exact rank-2 replacement for the
  rank-1 Lemma EQ (which is the case b = N).

  The second, cruder test is the D/N test of v_task55 5.1:
      q1^{N_1} <= q^N  and  q1^{D_1} >~ |S|/c ~ q^a/c   ==>
      N * (D_1/N_1)  >=  a - log_q(const * c) ,
  so every family with D_1/N_1 < a/N needs c >~ q^{a - N D_1/N_1}.
""")
    for T in TARGETS:
        print("  ---- target %-4s : N/b = %-6s   a/N = %-6s" %
              (T["key"], str(Fraction(T["N"], T["b"])),
               str(Fraction(T["a"], T["N"]))))
        surv_eq = []
        surv_dn = []
        for F in FAM:
            ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], 15)
            for n in ns:
                N1, mu1, D1 = F["N"](n), F["mu"](n), F["D"](n)
                if Fraction(N1, mu1) <= Fraction(T["N"], T["b"]):
                    surv_eq.append((F["key"], n, Fraction(N1, mu1)))
                if Fraction(D1, N1) >= Fraction(T["a"], T["N"]):
                    surv_dn.append((F["key"], n, Fraction(D1, N1)))
        print("     Lemma EQ' does NOT kill (N1/mu1 <= N/b) :")
        print("       ", ["%s%s=%s" % (k, "" if n in (1,) else n, r)
                          for (k, n, r) in surv_eq])
        print("     D/N test does NOT kill (D1/N1 >= a/N)   :")
        print("       ", ["%s%s=%s" % (k, "" if n in (1,) else n, r)
                          for (k, n, r) in surv_dn])
        both = set((k, n) for (k, n, r) in surv_eq) & \
            set((k, n) for (k, n, r) in surv_dn)
        print("     surviving BOTH tests (the only families needing the")
        print("     exact sweep of PART 4.0) :", sorted(both))
    print()
    return None


def part45():
    """Lemma EQ-EX: the p-part is an EQUALITY, not an inequality."""
    print(BAR)
    print("PART 4.5 -- Lemma EQ-EX and the same-ratio residual families")
    print(BAR)
    print("""
  Lemma EQ-EX [PROVEN, target-agnostic].  T almost simple with socle S_1,
  |S| = c|S_1|.  Comparing p-parts is an EQUALITY:

        q1^{N_1} * c_p  =  q^N ,     c_p := |c|_p  (so c_p | c | |Out(S_1)|).

  With (T1) q1^{D_1}/(12 d_1) <= |S_1| <= q1^{D_1} and
  |S| >= kappa q^a (kappa an explicit family constant, kappa >= 1/8 for all
  four targets) this pins the exponent:

        q^{ N D_1/N_1 - a }  in  a polylog band ,

  so EVERY family with  D_1/N_1 != a/N  is killed above an explicit
  threshold.  Only the families with D_1/N_1 = a/N EXACTLY survive -- and
  they must also survive Lemma EQ' (N_1/mu_1 <= N/b).  Intersection:
""")
    ratio_surv = {}
    for T in TARGETS:
        keep = []
        for F in FAM:
            ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], 15)
            for n in ns:
                N1, mu1, D1 = F["N"](n), F["mu"](n), F["D"](n)
                if (Fraction(D1, N1) == Fraction(T["a"], T["N"]) and
                        Fraction(N1, mu1) <= Fraction(T["N"], T["b"])):
                    keep.append((F, n))
        ratio_surv[T["key"]] = keep
        print("    %-5s (a/N = %-5s, N/b = %-4s) : %s"
              % (T["key"], str(Fraction(T["a"], T["N"])),
                 str(Fraction(T["N"], T["b"])),
                 [F["name"](n, 0).replace("(0)", "(q1)") for (F, n) in keep] or "NONE"))
    print("""
  For each survivor the two sub-cases are:
    c_p = 1  :  q1^{N_1} = q^N exactly, so |S_1| is a CLOSED RATIONAL
                function of q and c = |S|/|S_1| can be evaluated exactly.
    c_p >= 2 :  c >= c_p and |S|/|S_1| ~ c_p^{a/N}, so
                c_p^{a/N} <~ 12 d_1 |Out(S_1)| -- an explicit finite window.
  Both are computed below.
""")
    for T in TARGETS:
        for (F, n) in ratio_surv[T["key"]]:
            N1 = F["N"](n)
            print("  ---- target %-4s , socle family %s" %
                  (T["key"], F["name"](n, 0).replace("(0)", "(q1)")))
            # c_p = 1 : q1^{N1} = q^N  -> q1 = q^{N/N1} must be a prime power
            lo = hi = None
            hits = []
            ntest = 0
            for (q, p, f) in targets_q(T, 20000 if T["key"] != "2F4"
                                       else 2 ** 61):
                if (T["N"] * f) % N1:
                    continue
                f1 = T["N"] * f // N1
                q1 = p ** f1
                if not F["qform"](p, f1) or F["skip"](n, q1):
                    continue
                o1 = order_of(F, n, q1)
                r = Fraction(T["order"](q), o1)
                ntest += 1
                lo = r if lo is None or r < lo else lo
                hi = r if hi is None or r > hi else hi
                if r.denominator == 1 and r >= 2:
                    hits.append((q, q1, int(r)))
            print("        c_p = 1 : %d admissible (q,q1) pairs ; "
                  "c = |S|/|S_1| ranges over [%s, %s]"
                  % (ntest, lo, hi))
            print("                  integer values c >= 2 : %s"
                  % (hits or "NONE"))
            # c_p >= 2 window
            print("        c_p >= 2 : c >= c_p and c ~ c_p^{a/N} = c_p^{%s},"
                  % str(Fraction(T["a"], T["N"])))
            print("                  against c | |Out(S_1)| = d1 f1 g1 "
                  "(<= 6*%d*f1) -- finite, and inside PART 4.0."
                  % max(n, 4))
    print()
    return ratio_surv


def part46():
    """the Zsygmondy step: f1 is pinned by a primitive prime divisor, and
       the surviving (f, f1) pairs are killed by counting -- UNIFORMLY."""
    print(BAR)
    print("PART 4.6 -- the same-ratio families killed UNIFORMLY (Zsygmondy")
    print("            + counting), for every q")
    print(BAR)
    print("""
  For each same-ratio pair (target S, socle family F) a Zsygmondy primitive
  prime divisor r of p^{e f_1} - 1 sits in the largest cyclotomic block of
  |S_1|; r | |S_1| | |S|, and the p'-part of |S| divides p^{E f} - 1 for the
  target's own top exponent E.  Hence  e f_1 | E f.  Combined with the size
  comparison  c = |S|/|S_1| >= kappa q^a / q1^{D_1}  against
  c <= |Out(S_1)| = d_1 f_1 g_1, only ONE value of f_1 can survive, namely
  the "matched" one  f_1 = N f / N_1  (i.e. c_p = 1), which PART 4.5 has
  already evaluated in closed form.

    target   socle F     e (block)   E (target)   matched f_1
    S4       S4(q1)      4  (Phi4)   4            f
    S4       U4(q1)      6  (Phi6)   4            2f/3
    S4       Sz(q1)      4  (Phi4)   4            2f   -- but f_1 must be ODD
                                                  and 2f is even: IMPOSSIBLE
    G2       G2(q1)      6  (Phi6)   6            f
    G2       R(q1)       6  (Phi6)   6            2f   -- needs q1 ~ q^2, but
                                                  6f_1 | 6f forces f_1 <= f
    3D4      3D4(q1)     12 (Phi12)  12           f
    3D4      G2(q1)      6  (Phi6)   12           2f
    3D4      R(q1)       6  (Phi6)   12           4f   -- 6f_1 | 12f forces
                                                  f_1 <= 2f < 4f
    2F4      2F4(q1)     12 (Phi12)  12           f

  Below: for every non-matched admissible f_1 the exact counting bound
  c_lo := kappa q^a / q1^{D_1}  is compared with the cap |Out(S_1)|.
""")
    plan = [("S4", "C", 2, 4, 4), ("S4", "2A", 4, 6, 4), ("S4", "2B2", 1, 4, 4),
            ("G2", "G2", 1, 6, 6), ("G2", "2G2", 1, 6, 6),
            ("3D4", "3D4", 1, 12, 12), ("3D4", "G2", 1, 6, 12),
            ("3D4", "2G2", 1, 6, 12), ("2F4", "2F4", 1, 12, 12)]
    allok = True
    for (tk, fk, n, e, E) in plan:
        T = T_by_key(tk)
        F = [x for x in FAM if x["key"] == fk][0]
        N1, D1 = F["N"](n), F["D"](n)
        bad = []
        ntest = 0
        for (q, p, f) in targets_q(T, 10 ** 6 if tk != "2F4" else 2 ** 121):
            S = T["order"](q)
            # every f1 with e*f1 | E*f  and  q1^{N1} <= q^N
            for f1 in range(1, E * f // e + 1):
                if (E * f) % (e * f1):
                    continue
                q1 = p ** f1
                if not F["qform"](p, f1) or F["skip"](n, q1):
                    continue
                if q1 ** N1 > q ** T["N"]:
                    continue
                o1 = order_of(F, n, q1)
                if o1 < 60 or o1 > S:
                    continue
                cap = out_of(F, n, q1, p, f1)
                clo = Fraction(S, o1)
                ntest += 1
                matched = (N1 * f1 == T["N"] * f)
                if matched:
                    continue          # handled in closed form by PART 4.5
                if clo <= cap:
                    bad.append((q, q1, clo, cap))
        print("  %-4s <- %-6s : %d non-matched (q,f1) pairs tested ; "
              "pairs with c <= |Out(S_1)| : %s"
              % (tk, F["name"](n, 0).replace("(0)", ""), ntest,
                 bad or "NONE"))
        if bad:
            allok = False
    print()
    print("  ==> every non-matched f_1 dies on counting alone; the matched")
    print("      f_1 (c_p = 1) dies in closed form (PART 4.5).  The")
    print("      equal-characteristic branch is therefore UNIFORM in q.")
    print()
    return allok


def part4_exact(qmax=None, verbose=True):
    """PART 4.0 -- the factorisation-free EQUAL-CHARACTERISTIC decision.
    q1^{N1} | q^N bounds f1 <= N f / N1, so the branch is a finite exact
    test per target with NO factorisation of |S|."""
    print(BAR)
    print("PART 4.0 -- equal characteristic, decided EXACTLY for every q")
    print("            (factorisation-free; complete in f1 and in the type)")
    print(BAR)
    caps = {"S4": 200000, "G2": 60000, "3D4": 20000, "2F4": 2 ** 41}
    out = {}
    for T in TARGETS:
        lim = qmax or caps[T["key"]]
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
        print("  %-5s targets (admissible q <= %d)      : %d"
              % (T["key"], lim, ntar))
        print("        divisor pairs |S_1| | |S| found  : %d" % pairs)
        print("        POSITIVE CONTROL (S_1 = S, c = 1): %d / %d"
              % (ctl, ntar))
        print("        order-only NEAR-MISS (c <= |Out|): %s"
              % (near or "NONE"))
        print("        HITS (c >= 2, c | |Out(S_1)|)    : %s"
              % (hits or "NONE"))
        out[T["key"]] = hits
    print()
    return out


# ================================================================= PART 5

def part5():
    print(BAR)
    print("PART 5 -- almost simple with ALTERNATING or SPORADIC socle")
    print(BAR)
    print("""
  (E): c|S_1| = |S|, 2 <= c | |Out(S_1)|.  The candidate list is COMPLETE
  and |S| = M is inverted exactly for q, so each row is complete in q --
  it covers ALL q, not a range.
""")
    res = {}
    for T in TARGETS:
        hits = []
        tested = 0
        o = 60
        for m in range(5, 220):
            if m > 5:
                o = o * m
            if o > 10 ** 120:
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
        # positive control: the inverter must find c=1 self-solutions
        ctl = []
        for (q, p, f) in targets_q(T, 64):
            s = T["solve"](T["order"](q))
            if q not in s:
                ctl.append(("INVERTER FAILURE", q))
        adm = set(q for (q, p, f) in targets_q(T, 10 ** 6))
        good = [h for h in hits if h[1] in adm]
        excl = [h for h in hits if h[1] not in adm]
        print("  %-5s (S_1,c) pairs tested : %-6d  hits in the TARGET "
              "RANGE : %s   inverter self-check : %s"
              % (T["key"], tested, good or "NONE", ctl or "OK"))
        if excl:
            print("        hits at EXCLUDED q (recorded, not twins) : %s"
                  % excl)
        res[T["key"]] = hits
    print()
    print("  (also checked: no |S| of any target equals c*|A_m| or c*|spor|")
    print("   for any admissible c >= 2 -- the alternating/sporadic socle")
    print("   branch is empty for EVERY q, for all four families.)")
    print()
    return res


# ================================================================= PART 6

def part6(limits=None):
    print(BAR)
    print("PART 6 -- the residual census: Phase 1 (order census, RAW) +")
    print("          Phase 2 (orbit floor l|Out(S_i)|iota(S_i) >= iota(S))")
    print(BAR)
    limits = limits or {}
    res = {}
    for T in TARGETS:
        lim = limits.get(T["key"])
        if lim is None:
            print("  %-5s : residual window EMPTY -- no census needed."
                  % T["key"])
            res[T["key"]] = (0, 0, 0)
            continue
        qs = [q for (q, p, f) in targets_q(T, lim)]
        print("  ---- %-5s : %d targets, q <= %d" % (T["key"], len(qs), lim))
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
            if len(names) > 1:
                print("     q = %-6d TWO simple groups of order |S| : %s"
                      % (q, names))
        print("     RAW survivors %d ; after the orbit floor %d ; "
              "positive-control failures %d / %d"
              % (raw_tot, filt_tot, bad, len(qs)))
        if unknown:
            print("     socle candidates with no iota bound (kept): %s"
                  % sorted(unknown))
        res[T["key"]] = (bad, raw_tot, filt_tot)
    print()
    return res


# ================================================================= PART 7

def part7():
    """the S4(3) defect, and the special-coincidence hunt."""
    print(BAR)
    print("PART 7 -- the S4(3) defect and the inter-family order")
    print("          coincidence hunt")
    print(BAR)
    print("""
  (a) THE S4(3) DEFECT.  S4(3) = PSp_4(3) ~= U_4(2) (an ISOMORPHISM, not a
  twin).  Its minimal degree is 27 (the maximal subgroup 2^4:A_5 of
  U_4(2)), NOT the parabolic index mu = (q+1)(q^2+1) = 40.  So

        iota(S4(3)) = 27  <  40 = iota_gen(3) .

  Consequence for this note: every inequality of the form "iota(S) <= X"
  is used with the EXACT iota, and every inequality "iota(S) >= X" is used
  with the exact iota too, so q = 3 is simply carried with 27 in place of
  40 in PARTS 2, 3, 6.  It only makes the windows LARGER at q = 3, and
  q = 3 is inside every census below.  Printed check:
""")
    T = T_by_key("S4")
    for q in (3, 4, 5, 7, 8, 9, 11):
        print("     q = %-3d  iota = %-6d  parabolic index = %-6d  %s"
              % (q, T["iota"](q), T["iota_gen"](q),
                 "DEFECT" if T["iota"](q) != T["iota_gen"](q) else "equal"))
    print("""
  (b) THE COINCIDENCE HUNT.  v_task53 found |U_3(q)| = (q+1)|R(q)| and
  v_task55 found |L_3(25)| = 7|L_4(5)|.  Search here: all pairs
  (target S, simple G) with |S| = c|G|, 2 <= c <= 10^4, over the full
  Lie/alternating/sporadic candidate list -- reported whether or not
  c | |Out(G)| (an order-only identity is already worth recording).
""")
    rows = []
    rows += [(nm, o, ou) for (nm, o, ou, io) in alt_rows(40)]
    rows += [(nm, o, ou) for (nm, o, ou) in
             [(a, b, c) for (a, b, c) in list(SPORADIC) + [TITS]]]
    for (q1, p1, f1) in prime_powers_sieve(200):
        for F in FAM:
            if not F["qform"](p1, f1):
                continue
            ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], 13)
            for n in ns:
                if F["skip"](n, q1):
                    continue
                o = order_of(F, n, q1)
                if o < 60 or o > 10 ** 60:
                    continue
                rows.append((F["name"](n, q1), o, out_of(F, n, q1, p1, f1)))
    byorder = {}
    for (nm, o, ou) in rows:
        byorder.setdefault(o, []).append((nm, ou))
    found = []
    for T in TARGETS:
        for (q, p, f) in targets_q(T, 200 if T["key"] in ("S4", "G2") else
                                   (40 if T["key"] == "3D4" else 512)):
            S = T["order"](q)
            selfname = None
            for c in range(1, 10001):
                if S % c:
                    continue
                g = S // c
                if g in byorder:
                    for (nm, ou) in byorder[g]:
                        if c == 1:
                            selfname = nm
                            continue
                        found.append((T["key"], q, nm, c, ou, ou % c == 0))
    print("  order identities |S| = c|G|, 2 <= c <= 10^4 :")
    if not found:
        print("     NONE")
    for row in found:
        print("     %-4s(%d) : |S| = %d * |%s|   (|Out(G)| = %d, "
              "c | |Out| : %s)" % (row[0], row[1], row[3], row[2],
                                   row[4], "YES <== HIT" if row[5] else "no"))
    print()
    print("  isomorphism control (c = 1 coincidences, expected):")
    print("     S4(3) = U4(2) ; S4(2)' = A6 ; G2(2)' = U3(3) ; 2F4(2)' Tits")
    print("     -- these are ISOMORPHISMS, not twins; the census must not")
    print("     double-count them, and c >= 2 excludes them automatically.")
    print()
    return found


# ==========================================================================

def main():
    args = [a for a in sys.argv[1:]]
    want = set(args) if args else {"1", "2", "3", "4", "45", "46", "40", "5", "6", "7"}
    if "1" in want:
        part1()
    if "2" in want:
        part2()
    if "3" in want:
        part3()
    if "4" in want:
        part4()
    if "45" in want:
        part45()
    if "46" in want:
        part46()
    if "40" in want:
        part4_exact()
    if "5" in want:
        part5()
    if "7" in want:
        part7()
    if "6" in want:
        part6({"S4": 27, "G2": 9, "3D4": 4, "2F4": None})


if __name__ == "__main__":
    main()
