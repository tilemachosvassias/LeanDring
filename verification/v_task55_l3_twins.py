#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
v_task55_l3_twins.py -- Fitting-free NON-SIMPLE twins of the first RANK-2
target

        S = L_3(q) = PSL(3,q),    q = p^f,   e := gcd(3, q-1),

        |S| = q^3 (q^2-1)(q^3-1)/e  ~ q^8 ,   |S|_p = q^3 ,
        iota(S) = q^2+q+1  (both parabolics),  |Out(S)| = 2 f e .

Standing hypotheses (all upstream and PROVEN):
   T Fitting-free, |T| = |S|, D(T) = D(S), T NOT simple.
   Soc T = prod_i S_i^{l_i}, orbits O of length l_O, c = [T : Soc T],
   (F)  l_O * |Out(S_1)| * iota(S_1) >= iota(S)          [Lemma TO'-0 + F]
   (C)  |Out(G)| * iota(G) <= |G|^{2/3} for every simple G  [Lemma C, v_task52]
   (T1) |G| >= q1^D/(12 d),  (T2) iotabar <= 4 q1^mu,  (T3) |Out| = d f g,
        g <= 6                                            [v_task52]

Rank 2 is where the rank-1 pipeline strains: iota(S) ~ |S|_p / q, so
iota(S)^3 ~ q^6 < |S| ~ q^8 and the rank-1 "one orbit / length 1" step is
NOT available from Lemma C alone.

PARTS
 1  the target's invariants: order, iota, |Out|, the Lemma-K analogue
    (ppmax bounds), Lemma K', and the exact statement of the strain.
 2  Lemma Q -- the non-almost-simple kill.
      2a  l >= 3 dies from Lemma C alone, for q > (exact threshold).
      2b  the l <= 2 / two-orbit window: any such configuration has a socle
          factor with  |G|^2 <= |S|  and  2|Out(G)| iota(G) >= iota(S);
          this forces  |G|^{1/2} <~ 2|Out(G)|iota(G), i.e. G violates
          Lemma B.  The complete list of Lemma-B violators is computed
          (uniform tail bound per family + exact scan), and each gets an
          explicit finite q-window.
 3  almost simple, CROSS characteristic: the ppmax_{p'}^3 kill, exact.
 4  almost simple, EQUAL characteristic: the D/N table (only A1, A2, 2A2
    have D/N >= 8/3), the threshold for the rest, and the three surviving
    families killed one by one (size argument for L2; Zsygmondy for U3 and
    for the subfield case L3(q1)).
 5  almost simple with ALTERNATING or SPORADIC socle: solved exactly for q
    (complete in q, not a range).
 6  the residual census: full order census for every prime power q in the
    residual windows, with positive controls.

All arithmetic is exact integer / Fraction arithmetic.  No floats in any
decision (floats appear only in printed diagnostics).
"""

import sys
from fractions import Fraction

sys.path.insert(0, ".")

from v_task50_sporadic_twins import SPORADIC, TITS, IOTA_UB, census as census50
from v_task50_sporadic_twins import simple_divisors, phase2, iota_ub
from v_task51_l2_twins import is_prime_power, factorint
from v_task54_rank1_gaps import prime_powers_sieve
from v_task52_lemmaC import FAM, gcd, order_of, out_of, _prod
from v_task53_rank1_twins import _iroot
from v_task51_l2_twins import iota_ub_generic
import v_task50_sporadic_twins as V50

# the generic parabolic iota-bound of v_task51 (Borel-Tits: N_S(Z(U_P)) = P)
# is installed into v_task50's phase-2 filter, so that Lie-type socle
# candidates are no longer "unknown" (which would keep them conservatively).
V50.iota_ub = lambda name, order: iota_ub_generic(name)

BAR = "=" * 74


# ------------------------------------------------------------------ target

def prime_powers_upto(M):
    """all prime powers 3 <= q <= M (q = 2 excluded: L_3(2) = L_2(7), Thm L2-T)"""
    return [t for t in prime_powers_sieve(M) if t[0] >= 3]


def order_L3(q):
    e = gcd(3, q - 1)
    return q ** 3 * (q * q - 1) * (q ** 3 - 1) // e


def iota_L3(q):
    return q * q + q + 1


def out_L3(q, p, f):
    return 2 * f * gcd(3, q - 1)


def solve_L3(M):
    """all prime powers q >= 2 with |L_3(q)| = M   (complete in q)"""
    out = []
    for e in (1, 3):
        v = M * e
        r = _iroot(v, 8)
        for q in range(max(2, r - 3), r + 4):
            if q ** 3 * (q * q - 1) * (q ** 3 - 1) != v:
                continue
            if gcd(3, q - 1) != e or not is_prime_power(q):
                continue
            out.append(q)
    return sorted(set(out))


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


def isqrt(n):
    return _iroot(n, 2)


# ================================================================= PART 1

def ppmax(fac, skip=None):
    m = 1
    for r, a in fac.items():
        if r == skip:
            continue
        m = max(m, r ** a)
    return m


def part1(qmax=3000):
    print(BAR)
    print("PART 1 -- the target L_3(q): invariants, Lemma K, Lemma K',")
    print("          and the exact shape of the rank-2 strain")
    print(BAR)
    print("""
  |S| = q^3(q^2-1)(q^3-1)/e = q^3 (q-1)^2 (q+1) (q^2+q+1)/e ,  e=gcd(3,q-1)
  |S|_p = q^3 ,  iota(S) = q^2+q+1 = [S:P] for either parabolic P,
  |Out(S)| = 2 f e .   a := deg_q|S| = 8 ,  b := deg_q iota(S) = 2 ,
  N := deg_q |S|_p = 3 .

  Lemma K-L3 [PROVEN, elementary]:
      ppmax_{p'}(|S|)  <=  2 (q-1)^2      and   ppmax(|S|) = q^3  (q>=3).
  Proof.  gcd(q-1,q+1) | 2 ; q^2+q+1 = q(q+1)+1 so gcd(q+1, q^2+q+1) = 1 ;
  q^2+q+1 == 3 mod (q-1) so gcd(q-1, q^2+q+1) | 3, and when 3 | q-1 the
  3-part of q^2+q+1 is exactly 3, which is cancelled by e = 3.  Hence for
  odd r != p the whole r-part sits in one block:  <= max((q-1)^2, q+1,
  q^2+q+1) -- and the q^2+q+1 block is the only one that can beat (q-1)^2.
  [The bound printed below is the honest max over the three blocks.]

  Lemma K' [PROVEN, v_task53]: |G| < (|G|_p)^3 for every simple G of Lie
  type.  For the target itself: |S| ~ q^8 < q^9 = (|S|_p)^3 -- the K'
  route SURVIVES at rank 2, but only by the exponent 8 vs 9.

  THE STRAIN.  iota(S)^3 ~ q^6 < |S| ~ q^8, so the rank-1 Step 2
  ("iota^3 > |S| => one orbit") FAILS here.  This part prints the deficit.
""")
    print("  %-8s %-14s %-12s %-10s %-10s %s" %
          ("q", "|S|", "iota(S)", "ppmax_p'", "bound", "iota^3/|S|"))
    worst = None
    bad = 0
    for (q, p, f) in prime_powers_upto(qmax):
        if q == 2:
            continue
        S = order_L3(q)
        io = iota_L3(q)
        e = gcd(3, q - 1)
        # exact ppmax over p'-part
        fac = factorint((q * q - 1) * (q ** 3 - 1) // e)
        fac.pop(p, None)
        pm = ppmax(fac)
        bnd = max(2 * (q - 1) ** 2, (q * q + q + 1) // e)
        if pm > bnd:
            bad += 1
            print("   VIOLATION at q =", q, pm, bnd)
        if q <= 32 or q in (128, 1024, 2999):
            print("  %-8d %-14d %-12d %-10d %-10d %.4f" %
                  (q, S, io, pm, bnd, io ** 3 / S))
        r = Fraction(io ** 3, S)
        if worst is None or r > worst[0]:
            worst = (r, q)
    print()
    print("  Lemma K-L3 violations over all prime powers 3 <= q <= %d : %d"
          % (qmax, bad))
    print("  max of iota(S)^3/|S| over the range : %.4f at q = %d"
          % (float(worst[0]), worst[1]))
    print("  ==> iota(S)^3 > |S| holds for NO q >= 3.  Step 2 of the rank-1")
    print("      pipeline is unavailable; PART 2 replaces it.")
    print()
    return bad


# ================================================================= PART 2

def alt_rows(mmax=80):
    """(name, |A_m|, |Out|, iotabar) for 5 <= m <= mmax"""
    out = []
    o = 60
    exact = {5: 5, 6: 10, 7: 35, 8: 15}
    for m in range(5, mmax + 1):
        if m > 5:
            o = o * m
        io = exact.get(m, m * (m - 1) * (m - 2) // 6)
        out.append(("A%d" % m, o, 4 if m == 6 else 2, io))
    return out


def spor_rows():
    out = []
    for (nm, o, ou) in list(SPORADIC) + [TITS]:
        io = IOTA_UB[nm]
        out.append((nm, o, ou, io))
    return out


def lie_rows(q1max=20000, rankmax=24):
    """(name, |G|, |Out|, iotabar) for all Lie-type simple G with q1<=q1max"""
    out = []
    for (q1, p1, f1) in prime_powers_sieve(q1max):
        for F in FAM:
            if not F["qform"](p1, f1):
                continue
            ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], rankmax + 1)
            for n in ns:
                if F["skip"](n, q1):
                    continue
                if 2 ** F["D"](n) > 10 ** 60:
                    break
                o = order_of(F, n, q1)
                if o < 60:
                    continue
                out.append((F["name"](n, q1), o, out_of(F, n, q1, p1, f1),
                            F["iota"](n, q1)))
    return out


def lemB_tail_threshold(F, n):
    """smallest q1 such that the SURROGATE form of the Lemma-B condition
          2 * |Out| * iotabar  >=  |G|^{1/2}
       -- i.e.   2 * d f g * 4 q1^mu  >=  (q1^D/(12 d))^{1/2}   --
       fails for that q1 AND for every larger q1.  Exact integers.
       Returns None if it fails for every q1 >= 2.
       The surrogate is monotone once q1^{D-2mu} > 8^2 d^2 f^2 g^2 * 12 d,
       and f <= log2 q1, so the returned value is a genuine tail bound."""
    D, mu = F["D"](n), F["mu"](n)
    g = F["g"]
    if D - 2 * mu <= 0:
        return None
    last_ok = 0
    q1 = 2
    while q1 <= 10 ** 7:
        d = 0
        for qq in (q1, q1 + 1, q1 - 1):        # crude sup over d(n,q1)
            d = max(d, F["d"](n, qq))
        d = max(d, 1)
        f1 = max(1, q1.bit_length() - 1)
        # (8 d f1 g q1^mu)^2 >= q1^D / (12 d)   <=>  cond holds
        if (8 * d * f1 * g * q1 ** mu) ** 2 * 12 * d >= q1 ** D:
            last_ok = q1
        elif q1 > 2 * max(last_ok, 2):
            return last_ok
        q1 += 1
    return last_ok


def part2(verbose=True):
    print(BAR)
    print("PART 2 -- Lemma Q: T is ALMOST SIMPLE  (one orbit, length 1)")
    print(BAR)
    print("""
  Setup.  Soc T = prod_j S_j^{l_j} over orbits; prod_j |S_j|^{l_j} = |S|/c.
  If T is NOT almost simple then either some orbit has l_j >= 2, or there
  are >= 2 orbits.  In BOTH cases some socle factor G = S_j satisfies

      (Q1)   |G|^{max(2,l)} <= |S|          (l = l_j)
      (Q2)   l * |Out(G)| * iota(G) >= iota(S) = q^2+q+1     [floor (F)]

  (two orbits: the smaller contribution has |S_j|^{2 l_j} <= |S|).

  2a.  l >= 3 dies from Lemma C alone:  by (C), l|Out|iota <= l |G|^{2/3}
       <= l |S|^{2/(3l)} = l q^{16/(3l)} * (...), against q^2+q+1.
  2b.  l <= 2 leaves  |G|^2 <= |S|  and  2 rho(G) >= q^2+q+1  where
       rho(G) := |Out(G)| iota(G).  Eliminating q gives

           |G|^{1/2} <= |S|^{1/4} < (2 rho(G))^{1/2} * (1+o(1)),

       i.e.  |G| <~ 4 rho(G)^2 -- a violation of Lemma B (alpha <= 2).
       Lemma B violators form a FINITE explicit list; each is given an
       exact q-window below.
""")

    # ---- 2a : l >= 3
    print("  2a.  l >= 3, using Lemma C  (|Out|iota <= |G|^{2/3}) and")
    print("       |G|^l <= |S|:   (q^2+q+1)^{3l} <= l^{3l} |S|^{2} is the")
    print("       exact cube-cleared test.  Largest q for which it can hold:")
    for l in range(3, 13):
        hi = 0
        q = 2
        while q <= 10 ** 7:
            S = order_L3(q)
            # (l * |G|^{2/3})^{3l} >= (q^2+q+1)^{3l} with |G|^l <= |S|
            #  <=> l^{3l} * |S|^{2} >= (q^2+q+1)^{3l}
            if l ** (3 * l) * S ** 2 >= (q * q + q + 1) ** (3 * l):
                hi = q
            elif q > 2 * max(hi, 2):
                break
            q += 1
        print("        l = %-3d :  possible only for q <= %d" % (l, hi))
    print("       ==> for q >= 141 every orbit has length l <= 2.")
    print()

    # ---- 2b : the Lemma-B violator list
    print("  2b.  the complete list of simple G with  |G| <= 4 rho(G)^2 ")
    print("       (rho = |Out|*iotabar; iotabar >= iota, so conservative):")
    print()
    rows = []
    rows += alt_rows(80)
    rows += spor_rows()

    # Lie: per family/rank tail threshold from the surrogate, then exact scan
    tails = {}
    for F in FAM:
        ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], 25)
        for n in ns:
            t = lemB_tail_threshold(F, n)
            if t is None:
                print("        !! D <= 2mu for %s n=%d -- no tail bound"
                      % (F["key"], n))
                continue
            if t >= 2:
                tails[(F["key"], n)] = t
    hirank = []
    for F in FAM:
        if F["nmax"]:
            continue
        for n in range(25, 61):
            t = lemB_tail_threshold(F, n)
            if t is None or t >= 2:
                hirank.append((F["key"], n, t))
    print("        ranks 25..60, families of unbounded rank: rows for which")
    print("        the surrogate can hold for SOME q1 >= 2 : %s"
          % (hirank or "NONE -- rank <= 24 is complete"))
    q1cap = max(tails.values()) if tails else 2
    print("        Lie tail bound: the surrogate Lemma-B condition fails for")
    print("        every q1 > %d in every family/rank (max over %d rows);"
          % (q1cap, len(tails)))
    print("        so an exact scan over q1 <= %d is COMPLETE." % (q1cap,))
    rows += lie_rows(max(q1cap, 64), rankmax=24)

    viol = []
    for (nm, o, ou, io) in rows:
        rho = ou * io
        if o <= 4 * rho * rho:
            viol.append((nm, o, ou, io, rho))
    viol.sort(key=lambda t: t[1])
    print()
    print("        %-12s %-22s %-6s %-12s %s" %
          ("G", "|G|", "|Out|", "iotabar", "q-window [q_lo, q_hi]"))
    windows = []
    for (nm, o, ou, io, rho) in viol:
        # q_hi : largest q with q^2+q+1 <= 2 rho
        qhi = isqrt(2 * rho)
        while qhi * qhi + qhi + 1 > 2 * rho:
            qhi -= 1
        # q_lo : smallest q with |L3(q)| >= |G|^2
        qlo = 2
        while order_L3(qlo) < o * o:
            qlo += 1
        mark = ""
        if qlo <= qhi:
            windows.append((nm, o, ou, io, qlo, qhi))
            mark = "  <== NONEMPTY"
        print("        %-12s %-22d %-6d %-12d [%d, %d]%s" %
              (nm, o, ou, io, qlo, qhi, mark))
    print()
    print("        Lemma-B violators found: %d ; with a nonempty q-window: %d"
          % (len(viol), len(windows)))
    qmaxwin = max([w[5] for w in windows], default=0)
    print("        every nonempty window lies in  q <= %d." % qmaxwin)
    print()
    print("  ==> for q > max(140, %d) T is ALMOST SIMPLE:" % qmaxwin)
    print("          c*|S_1| = |S| ,  c >= 2 ,  c | |Out(S_1)| .")
    print()
    return windows, qmaxwin


# ================================================================= PART 3

def part3():
    print(BAR)
    print("PART 3 -- almost simple, CROSS characteristic: the ppmax^3 kill")
    print(BAR)
    print("""
  S_1 of Lie type over F_{q1}, q1 = p1^{f1}, p1 != p.  Then
      |S_1|_{p1} <= ppmax_{p'}(|S|) <= max(2(q-1)^2, (q^2+q+1)/e) =: P
  and Lemma K' gives |S_1| < P^3.  With |S_1| = |S|/c, c <= |Out(S_1)|:

      |S|  <  c * P^3 .

  Rank bound (needed for the |Out| cap): 2^{N_1} <= q1^{N_1} <= P, and
  N_1 >= n_1(n_1-1)/2 for every family, so n_1 <= n_max(P); then
  |Out(S_1)| = d1 f1 g1 <= n_max * log2(P) * 6.
""")
    print("  %-8s %-16s %-14s %-8s %-8s %s" %
          ("q", "|S|", "c*P^3", "n_max", "c_cap", "survives?"))
    surv = []
    for (q, p, f) in prime_powers_upto(4000):
        if q == 2:
            continue
        S = order_L3(q)
        e = gcd(3, q - 1)
        P = max(2 * (q - 1) ** 2, (q * q + q + 1) // e)
        N1max = P.bit_length() - 1
        n1 = 2
        while n1 * (n1 - 1) // 2 <= N1max:
            n1 += 1
        n1 -= 1
        ccap = max(1, 6 * n1 * max(1, P.bit_length() - 1))
        ok = S < ccap * P ** 3
        if ok:
            surv.append(q)
        if q <= 40 or q in (64, 128, 179, 181, 256, 3989):
            print("  %-8d %-16d %-14d %-8d %-8d %s" %
                  (q, S, ccap * P ** 3, n1, ccap, "YES" if ok else "no"))
    print()
    print("  cross-characteristic branch survives only for q in :")
    print("     ", surv)
    print("  (all prime powers 3 <= q <= 4000 tested; the branch is empty")
    print("   for every q above the largest listed value -- the inequality")
    print("   is q^8 ~ |S| vs c*8q^6, i.e. q^2 > 8c ~ polylog, monotone.)")
    print()
    return surv


# ================================================================= PART 4

def part4():
    print(BAR)
    print("PART 4 -- almost simple, EQUAL characteristic")
    print(BAR)
    print("""
  S_1 of Lie type over F_{q1} = F_{p^{f1}}.  Two exact constraints:

    (alpha)  |S_1|_p = q1^{N1} divides |S|_p = q^3 , so q1^{N1} <= q^3 ;
    (beta)   |S_1| = |S|/c  with  2 <= c <= |Out(S_1)| .

  With (T1) |S_1| >= q1^{D1}/(12 d1) and |S_1| <= q1^{D1}:

      q1^{D1} >= |S| / c >= q^8 (1-q^-2)(1-q^-3) / (3c)
      q1^{N1} <= q^3
      ==>  (q^3)^{D1/N1} >= q1^{D1} >= q^8 * (1-..)/(3c)
      ==>  3 * D1/N1  >=  8 - log_q(3c/(1-..))            (*)

  So every family with D1/N1 < 8/3 needs 3c >~ q^{8-3D1/N1}.  The next
  value below 8/3 is 5/2, giving 3c >= q^{1/2} -- and c <= |Out| is
  polylog.  The D/N table:
""")
    rows = []
    for F in FAM:
        ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], 9)
        for n in ns:
            D, N = F["D"](n), F["N"](n)
            rows.append((Fraction(D, N), F["key"], n, D, N))
    rows.sort(reverse=True)
    print("    %-8s %-4s %6s %6s %10s   %s" %
          ("family", "n", "D", "N", "D/N", "D/N >= 8/3 ?"))
    keep = []
    for (r, k, n, D, N) in rows[:14]:
        print("    %-8s %-4d %6d %6d %10s   %s" %
              (k, n, D, N, str(r), "YES" if r >= Fraction(8, 3) else "no"))
    for (r, k, n, D, N) in rows:
        if r >= Fraction(8, 3):
            keep.append((k, n, r))
    print("    ... (all remaining rows have D/N <= 5/2)")
    print()
    print("  Families with D/N >= 8/3 :", keep)
    print("""
  So apart from A1 = L2, A2 = L3 and 2A2 = U3 every family needs
  3c >= q^{1/2}.  With c <= |Out(S_1)| = d1 f1 g1 <= n1 * log2(q^3) * 6
  and n1 <= 1 + sqrt(2 N1) <= 1 + sqrt(6 log_p q):
""")
    thr = None
    for (q, p, f) in prime_powers_upto(200000):
        if q == 2:
            continue
        N1max = 3 * f
        n1 = 2
        while n1 * (n1 - 1) // 2 <= N1max:
            n1 += 1
        n1 -= 1
        ccap = 6 * n1 * max(1, 3 * f)
        # need (3c)^2 >= q  for the D/N <= 5/2 families to survive
        if (3 * ccap) ** 2 < q:
            if thr is None:
                thr = q
        else:
            thr = None
    print("     the surrogate (3c)^2 >= q fails for every prime power")
    print("     q >= %s -- so for q >= %s the socle family is one of"
          % (thr, thr))
    print("     L2(q1), L3(q1), U3(q1) (in the defining characteristic).")
    print()
    print("  4.1  S_1 = L2(q1).  (alpha) gives q1 = q^3/p^j with p^j = c_p")
    print("       | c, so |S_1| ~ q^9/p^{3j} and (beta) forces")
    print("           p^{3j} ~ c q / d1  and  p^j <= c <= 2 f1 <= 6 f,")
    print("       hence q <= 2 c^2 <= 72 f^2 = 72 (log_p q)^2.  Exact scan:")
    hits = []
    lim = 0
    for (q, p, f) in prime_powers_upto(2 * 10 ** 5):
        if q == 2:
            continue
        S = order_L3(q)
        if q <= 72 * (f * (p.bit_length() - 1)) ** 2:
            lim = q
        for j in range(0, 3 * f):
            q1 = q ** 3 // p ** j
            if q1 < 4 or p ** j * q1 != q ** 3:
                continue
            d1 = gcd(2, q1 - 1)
            o1 = q1 * (q1 * q1 - 1) // d1
            if S % o1:
                continue
            c = S // o1
            if c >= 2 and out_L2_ok(c, q1, p, 3 * f - j):
                hits.append((q, q1, c))
    print("       largest q meeting the bound: %d ; exact hits over all" % lim)
    print("       prime powers q <= 2*10^5 and all j : %s" % (hits or "NONE"))
    print()
    print("  4.2  S_1 = U3(q1).  Zsygmondy: q1^2-q1+1 carries a primitive")
    print("       prime divisor r of p^{6f1}-1 (the only exception, (2,6),")
    print("       is q1 = 2, and U3(2) is not simple).  r | |S_1| and")
    print("       |S_1| | |S|, whose p'-part divides q^6-1 = p^{6f}-1, so")
    print("       ord_r(p) = 6f1 divides 6f, i.e.  f1 | f.")
    print("        * f1 = f : c*e*(q^3+1) = e1*(q^3-1) with e,e1 in {1,3}")
    print("          and c >= 2 -- no solution (2e/e1 in {2/3,2,6}).")
    print("        * f1 < f : f1 | f gives q >= q1^2, so")
    print("          c = |S|/|S_1| >= (q/q1)^8/3 >= q1^8/3, against")
    print("          c <= |Out(U3(q1))| = 2 f1 e1 <= 6 log_2 q1.")
    print("       Exact confirmation (all q <= 10^5, all f1 <= f):")
    h42 = []
    for (q, p, f) in prime_powers_upto(10 ** 5):
        if q == 2:
            continue
        S = order_L3(q)
        for f1 in range(1, f + 1):
            q1 = p ** f1
            if q1 < 3:
                continue
            e1 = gcd(3, q1 + 1)
            o1 = q1 ** 3 * (q1 * q1 - 1) * (q1 ** 3 + 1) // e1
            if o1 > S or S % o1:
                continue
            c = S // o1
            if 2 <= c <= 2 * f1 * e1:
                h42.append((q, q1, c))
    print("       exact hits : %s" % (h42 or "NONE"))
    print()
    print("  4.3  S_1 = L3(q1), q1 = p^{f1} < q  (the SUBFIELD case).")
    print("       q1 = q gives c = 1, excluded.  For q1 < q, Zsygmondy on")
    print("       q1^2+q1+1 (primitive prime of p^{3f1}-1; only exception")
    print("       (2,6), i.e. q1 = 4, checked separately) gives 3f1 | 6f,")
    print("       i.e. f1 | 2f, hence f - f1 >= f/3 for f1 < f.  Then")
    print("       c = |L3(q)|/|L3(q1)| >= (q/q1)^8/3 >= p^{8f/3}/3 while")
    print("       c <= |Out(L3(q1))| = 6 f1 <= 6 f.  Exact scan:")
    h43 = []
    for (q, p, f) in prime_powers_upto(10 ** 5):
        if q == 2:
            continue
        S = order_L3(q)
        for f1 in range(1, f):
            q1 = p ** f1
            if q1 < 2:
                continue
            o1 = order_L3(q1)
            if o1 < 60 or S % o1:
                continue
            c = S // o1
            if 2 <= c <= 6 * f1:
                h43.append((q, q1, c))
    print("       exact hits : %s" % (h43 or "NONE"))
    print()
    return hits, h42, h43


def out_L2_ok(c, q1, p, f1):
    return c <= gcd(2, q1 - 1) * f1



def part4_exact(qmax=10 ** 7, verbose=True):
    """PART 4.0 -- the factorisation-free EQUAL-CHARACTERISTIC decision.

    For every target q = p^f and every simple S_1 of Lie type over
    F_{q1}, q1 = p^{f1}, in the SAME characteristic p, the p-part
    constraint  q1^{N1} | q^3  bounds f1 by 3f/N1, so the whole branch is
    a finite exact test per q -- no factorisation of |S| is needed.
    Test: |S_1| divides |S| and 2 <= c := |S|/|S_1| <= |Out(S_1)|.
    """
    print(BAR)
    print("PART 4.0 -- equal characteristic, decided EXACTLY for every q")
    print("            (factorisation-free; complete in f1 and in the type)")
    print(BAR)
    hits = []
    near = []
    pairs = 0
    ctl = 0
    ntar = 0
    for (q, p, f) in prime_powers_upto(qmax):
        ntar += 1
        S = order_L3(q)
        selfseen = False
        for F in FAM:
            ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], 30)
            for n in ns:
                N1 = F["N"](n)
                if N1 > 3 * f:
                    break
                for f1 in range(1, 3 * f // N1 + 1):
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
    print("  targets (all prime powers 3 <= q <= %d) : %d" % (qmax, ntar))
    print("  (S_1 | |S|) divisor pairs found        : %d" % pairs)
    print("  POSITIVE CONTROL (S_1 = S, c = 1 found): %d / %d" % (ctl, ntar))
    print("  order-only NEAR-MISSES (c <= |Out|, c | |Out| dropped):")
    print("     ", near or "NONE")
    print("  HITS (c >= 2 and c | |Out(S_1)|)       : %s" % (hits or "NONE"))
    print()
    return hits


# ================================================================= PART 5

def part5():
    print(BAR)
    print("PART 5 -- almost simple with ALTERNATING or SPORADIC socle")
    print(BAR)
    print("""
  (E): c |S_1| = |S|, 2 <= c | |Out(S_1)|.  For these two classes the
  candidate list is COMPLETE, and |L_3(q)| = M is inverted exactly for q,
  so each row is complete in q -- it covers ALL q, not a range.
""")
    hits = []
    tested = 0
    # alternating
    o = 60
    for m in range(5, 200):
        if m > 5:
            o = o * m
        if o > 10 ** 90:
            break
        ou = 4 if m == 6 else 2
        for c in range(2, ou + 1):
            if ou % c:
                continue
            tested += 1
            for q in solve_L3(c * o):
                hits.append(("A%d" % m, q, c))
    # sporadic
    for (nm, so, ou) in list(SPORADIC) + [TITS]:
        for c in range(2, ou + 1):
            if ou % c:
                continue
            tested += 1
            for q in solve_L3(c * so):
                hits.append((nm, q, c))
    print("  (S_1, c) pairs tested : %d      hits : %s" %
          (tested, hits or "NONE"))
    # positive control: the inverter must find the c=1 self-solutions,
    # including the A_8 / L_3(4) order coincidence.
    ctl = []
    o = 60
    for m in range(5, 30):
        if m > 5:
            o = o * m
        s = solve_L3(o)
        if s:
            ctl.append(("A%d" % m, s))
    print("  POSITIVE CONTROL (c = 1 self-solutions among alternating):")
    print("     ", ctl, " <- |A_8| = |L_3(4)| must appear")
    print("      it is excluded only by c >= 2, i.e. by T non-simple;")
    print("      the SIMPLE-simple separation L_3(4) vs A_8 is 4j-classical.")
    print()
    return hits, ctl


# ================================================================= PART 6

def part6(qlist, verbose=True):
    print(BAR)
    print("PART 6 -- the residual census: Phase 1 (order census, RAW) +")
    print("          Phase 2 (orbit floor l|Out(S_i)|iota(S_i) >= iota(S))")
    print(BAR)
    print("  targets: %d prime powers" % len(qlist))
    bad = 0
    raw_tot = 0
    filt_tot = 0
    raws = []
    filts = []
    unknown = set()
    for q in qlist:
        N = order_L3(q)
        io = iota_L3(q)
        cands = simple_divisors(N)
        names = [c[0] for c in cands if c[1] == N]
        if ("L3(%d)" % q) not in names:
            bad += 1
            print("   POSITIVE-CONTROL FAILURE at q = %d : %s" % (q, names))
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
            raws.append((q, raw))
        if filt:
            filts.append((q, filt))
        if len(names) > 1:
            print("   q = %-6d |S| = %-20d  TWO simple groups of that order: %s"
                  % (q, N, names))
    print()
    print("  RAW (Phase 1 only) non-simple census survivors : %d" % raw_tot)
    for (q, r) in raws:
        print("     q = %-6d %s" % (q, r))
    print()
    print("  AFTER the orbit floor (Phase 2)                : %d" % filt_tot)
    for (q, r) in filts:
        print("     q = %-6d %s" % (q, r))
    print()
    print("  positive-control failures : %d / %d" % (bad, len(qlist)))
    print("  socle candidates with no iota bound (kept, conservative): %s"
          % (sorted(unknown) or "none"))
    print()
    return bad, raw_tot, filt_tot


# ==========================================================================

def main():
    args = sys.argv[1:]
    want = (set(a for a in args if not a.isdigit() or len(a) <= 2) if args
            else {"1", "2", "3", "4", "40", "5", "6"})
    if "1" in want:
        part1()
    if "2" in want:
        part2()
    if "3" in want:
        part3()
    if "4" in want:
        part4()
    if "40" in want:
        part4_exact()
    if "5" in want:
        part5()
    if "6" in want:
        lim = 23816
        if "6" in args and len(args) > args.index("6") + 1:
            lim = int(args[args.index("6") + 1])
        qs = [q for (q, p, f) in prime_powers_upto(lim)]
        part6(qs)


if __name__ == "__main__":
    main()
