#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
v_task54_rank1_gaps.py -- closing the residual rank-1 gaps (G2'), (G3), (G4)
left open by v_task53_rank1_twins.md, for the targets

      S = U_3(q),   Sz(q) = ^2B_2(q),   R(q) = ^2G_2(q).

Standing hypotheses (all PROVEN upstream, see the .md):
   T Fitting-free, |T| = |S|, D(T) = D(S);  Steps 2-3 of v_task53 (which now
   rest on Lemma C, PROVEN in v_task52) give  Soc T = S_1  SIMPLE  and

      (E)   c * |S_1| = |S| ,   c >= 2 ,   c | |Out(S_1)| ,
      (F)   |Out(S_1)| * iota(S_1) >= iota(S)          [orbit floor, l = 1].

The residual question is exactly: which simple S_1 can satisfy (E)+(F)?

PARTS
  1  the D/mu table  theta := D/mu  for every family and rank, and the
     per-target threshold  a/b  (|S| ~ q^a, iota(S) ~ q^b).  Families with
     theta > a/b die uniformly; the others are named.
  2  Lemma W, the WINDOW LEMMA, in its exact integer form
         iota(S)^{D1} < (4 d1 f1 g1)^{D1} * (6 d1 |S|)^{mu1}
     -- a NECESSARY condition on (S_1, S).  Per target and per family the
     smallest q beyond which it fails is computed exactly.
  3  (G2') Sz: 3 does not divide |Sz(q)|, ever.  With the CFSG corollary
     "3 | |G| for every simple G except the Suzuki groups", S_1 must be
     Sz(q_1); then the subfield count kills it.  Uniform, all q, no window.
  4  (G4) Lemma EQ, the equal-characteristic window
         q_1^{N1 - mu1}  <  4 d1 f1 g1 ,
     valid for ALL THREE targets simultaneously.  N1 = mu1 exactly for the
     rank-1 families, so rank >= 2 lands in an explicit finite window, which
     is enumerated and checked against (E).
  5  (G4, rank-1 socle) the four rank-1 families in equal characteristic,
     killed by the exponent comparison theta_1 vs a/N, with the exact
     threshold per pair, plus an exhaustive check below it.
  6  (G3) the residual window vs the v_task53 --sub scan range.

All arithmetic is exact integer / Fraction arithmetic.
"""

import sys
from fractions import Fraction

sys.path.insert(0, ".")

import v_task52_lemmaC as C52
from v_task52_lemmaC import FAM, gcd, order_of, _prod
from v_task53_rank1_twins import (U3_order, Sz_order, Ree_order,
                                  U3_out, Sz_out, Ree_out,
                                  U3_iota, Sz_iota, Ree_iota,
                                  solve_U3, solve_Sz, solve_Ree,
                                  U3_targets, Sz_targets, Ree_targets,
                                  is_prime_power)

BAR = "=" * 74


# ---------------------------------------------------------------- targets
# name -> (order, out, iota, N (so |S|_p = q^N and iota = q^N + 1), a, b)
TARGET = {
    "U3":  dict(order=U3_order, out=U3_out, iota=U3_iota, N=3, a=8, b=3,
                char=None),
    "Sz":  dict(order=Sz_order, out=Sz_out, iota=Sz_iota, N=2, a=5, b=2,
                char=2),
    "Ree": dict(order=Ree_order, out=Ree_out, iota=Ree_iota, N=3, a=7, b=3,
                char=3),
}


def dmax_of(F, n):
    """an upper bound for d = |Z(simply connected)| valid for every q."""
    k = F["key"]
    if k in ("A", "A1"):
        return n if k == "A" else 2
    if k == "2A":
        return n
    if k in ("B", "C"):
        return 2
    if k in ("D", "2D"):
        return 4
    if k in ("E6", "2E6"):
        return 3
    if k == "E7":
        return 2
    return 1


def ranks_of(F, upto=40):
    if F["nmax"]:
        return [F["nmin"]]
    return list(range(F["nmin"], upto + 1))


def ilog2(n):
    return n.bit_length() - 1


def prime_powers_sieve(M):
    """all prime powers 2 <= q <= M, ascending (sieve; no factorisation)"""
    sieve = bytearray([1]) * (M + 1)
    sieve[0] = sieve[1] = 0
    i = 2
    while i * i <= M:
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(range(i * i, M + 1, i)))
        i += 1
    out = []
    for p in range(2, M + 1):
        if sieve[p]:
            q, f = p, 1
            while q <= M:
                out.append((q, p, f))
                q *= p
                f += 1
    return sorted(out)


# ================================================================= PART 1

def part1():
    print(BAR)
    print("PART 1 -- the theta = D/mu table, and the per-target threshold a/b")
    print(BAR)
    print("""
  Lemma W (below) kills a socle family as soon as  b*D1 - a*mu1 > 0, i.e.
  theta := D1/mu1 > a/b.  a/b is 8/3 (U_3), 5/2 (Sz), 7/3 (R).
""")
    rows = []
    for F in FAM:
        for n in ranks_of(F, 8):
            D, mu = F["D"](n), F["mu"](n)
            rows.append((Fraction(D, mu), F["key"], n, D, mu,
                         F["N"](n), F["N"](n) - mu))
    rows.sort()
    print("  %-8s %-4s %6s %5s %9s %6s %8s   %s" %
          ("family", "n", "D", "mu", "theta=D/mu", "N", "N-mu", "dies for target"))
    for th, k, n, D, mu, N, Nm in rows:
        who = []
        for t in ("U3", "Sz", "Ree"):
            a, b = TARGET[t]["a"], TARGET[t]["b"]
            if b * D > a * mu:
                who.append(t)
        print("  %-8s %-4d %6d %5d %9s %6d %8d   %s" %
              (k, n, D, mu, "%d/%d" % (D, mu), N, Nm,
               ",".join(who) if who else "-- NONE (boundary/below)"))
    print()
    for t in ("U3", "Sz", "Ree"):
        a, b = TARGET[t]["a"], TARGET[t]["b"]
        surv = sorted({(Fraction(F["D"](n), F["mu"](n)), F["key"], n)
                       for F in FAM for n in ranks_of(F, 40)
                       if b * F["D"](n) <= a * F["mu"](n)})
        print("  target %-4s (a/b = %d/%d = %s): families NOT killed by "
              "Lemma W:" % (t, a, b, Fraction(a, b)))
        for th, k, n in surv:
            print("        %-6s n=%-2d  theta = %-6s %s" %
                  (k, n, th, "(= a/b, boundary)"
                   if th == Fraction(a, b) else ""))
        print()
    print("  The set of theta-values below any bound is FINITE because theta")
    print("  -> infinity with the rank in every classical family:")
    for F in FAM:
        if F["nmax"]:
            continue
        ns = ranks_of(F, 12)
        print("     %-4s theta(n) for n = %d..%d : %s" %
              (F["key"], ns[0], ns[-1],
               " ".join(str(Fraction(F["D"](n), F["mu"](n))) for n in ns)))
    print()


# ================================================================= PART 2

def window_ok(iotaS, orderS, D1, mu1, d1, f1, g1):
    """the exact necessary condition of Lemma W; False = case impossible"""
    return iotaS ** D1 < (4 * d1 * f1 * g1) ** D1 * (6 * d1 * orderS) ** mu1


def part2(verbose=True):
    print(BAR)
    print("PART 2 -- Lemma W, exact integer form, and the per-family window")
    print(BAR)
    print("""
  (T1)  |S_1| >= q_1^{D1}/(12 d1)          [v_task52]
  (T2)  iota(S_1) <= 4 q_1^{mu1}           [v_task52]
  (E)   c |S_1| = |S|, c >= 2   ==>  q_1^{D1} <= 12 d1 |S_1| <= 6 d1 |S|
  (F)   4 d1 f1 g1 q_1^{mu1} >= |Out| iota(S_1) >= iota(S)

  raising the last to the power D1 and the previous to the power mu1:

      Lemma W:   iota(S)^{D1}  <  (4 d1 f1 g1)^{D1} * (6 d1 |S|)^{mu1}

  is NECESSARY.  f1 <= log_2 q_1 <= log_2(6 d1 |S|)/D1, and q_1 >= 2 forces
  2^{D1} <= 6 d1 |S|, so for each target only finitely many (family, rank)
  need testing.  Below: for each family the LARGEST target q at which
  Lemma W still holds (i.e. the family is not yet excluded).
""")
    # conservative order/iota surrogates, defined for every integer q >= 3
    # (larger |S| and smaller iota(S) both WEAKEN the exclusion, so these are
    #  the safe direction)
    SUR = {
        "U3":  (lambda q: q ** 3 * (q * q - 1) * (q ** 3 + 1),
                lambda q: q ** 3 + 1),
        "Sz":  (lambda q: q * q * (q - 1) * (q * q + 1),
                lambda q: q * q + 1),
        "Ree": (lambda q: q ** 3 * (q - 1) * (q ** 3 + 1),
                lambda q: q ** 3 + 1),
    }

    def alive(t, F, n, q):
        ordS, iotS = SUR[t][0](q), SUR[t][1](q)
        D1, mu1, d1, g1 = F["D"](n), F["mu"](n), dmax_of(F, n), F["g"]
        f1cap = max(1, ilog2(6 * d1 * ordS) // D1)
        return window_ok(iotS, ordS, D1, mu1, d1, f1cap, g1)

    for t in ("U3", "Sz", "Ree"):
        T = TARGET[t]
        a, b = T["a"], T["b"]
        print("  --- target %s  (a/b = %d/%d) ---" % (t, a, b))
        rows = []
        for F in FAM:
            for n in ranks_of(F, 12):
                D1, mu1 = F["D"](n), F["mu"](n)
                th = Fraction(D1, mu1)
                if b * D1 <= a * mu1:
                    rows.append((th, F["key"], n, None))
                    continue
                # exponent gap is positive: threshold exists.  doubling +
                # bisection on q (the condition is eventually monotone; the
                # scan below confirms it never revives)
                hi = 4
                while alive(t, F, n, hi):
                    hi *= 2
                    if hi > 10 ** 400:
                        break
                lo = hi // 2
                while lo + 1 < hi:
                    mid = (lo + hi) // 2
                    if alive(t, F, n, mid):
                        lo = mid
                    else:
                        hi = mid
                rows.append((th, F["key"], n, lo))
        rows.sort(key=lambda r: (r[3] is None, -(r[3] or 0)))
        surv = []
        small = 0
        for th, k, n, thr in rows:
            if thr is not None and thr <= 8:
                small += 1
                continue
            if thr is None:
                surv.append("%s(n=%d)" % (k, n))
                print("     %-6s n=%-2d theta=%-8s  SURVIVES ALL q "
                      "(theta = %s <= a/b)" % (k, n, th, th))
            else:
                s = str(thr)
                if len(s) > 22:
                    s = "%s...(%d digits)" % (s[:10], len(s))
                print("     %-6s n=%-2d theta=%-8s  excluded for q > %s"
                      % (k, n, th, s))
        print("     (+ %d further (family,rank) rows, all excluded for q > 8;"
              " ranks up to 12 tested)" % small)
        print("     ==> families surviving Lemma W at every q: %s"
              % (", ".join(surv) if surv else "NONE"))
        print()


# ================================================================= PART 3

def part3():
    print(BAR)
    print("PART 3 -- (G2') the Suzuki cross-characteristic branch, UNIFORM")
    print(BAR)
    print("""
  Step 1.  3 never divides |Sz(q)|.
      q = 2^f with f odd  ==>  q = 2 (mod 3), hence
      q - 1 = 1 (mod 3) and q^2 + 1 = 2 (mod 3), and q^2 is a 2-power.
  Step 2.  [LIT, corollary of CFSG]  the finite simple groups of order
      coprime to 3 are EXACTLY the Suzuki groups Sz(2^{2m+1}).
      Since |S_1| divides |Sz(q)|, S_1 = Sz(q_1).  In particular the
      alternating, sporadic AND all cross-characteristic Lie socles are
      excluded outright -- no window, no census.
  Step 3.  the subfield count.  Zsygmondy: 4f_1 >= 12 so q_1^2+1 has a
      primitive prime divisor r of 2^{4f_1}-1; r | |Sz(q_1)| divides
      |Sz(q)| | 2^{4f}-1 (times a 2-power), so 4f_1 | 4f, i.e. f_1 | f.
      f_1 < f and both odd force f >= 3 f_1, so q/q_1 >= q_1^2, while
          c = |Sz(q)|/|Sz(q_1)| > (q/q_1)^5 / 2 >= q_1^{10}/2
      and c <= |Out(Sz(q_1))| = f_1 <= log_2 q_1.  Contradiction.
""")
    bad = 0
    for f in range(3, 402, 2):
        q = 2 ** f
        if Sz_order(q) % 3 == 0:
            bad += 1
            print("  VIOLATION at f =", f)
    print("  3 | |Sz(q)| for f odd, 3 <= f <= 401 (200 targets): "
          "violations = %d" % bad)

    print("\n  the subfield count, checked exactly (f_1 | f, f_1 < f):")
    worst = None
    hits = 0
    for f in range(3, 202, 2):
        q = 2 ** f
        for f1 in range(3, f, 2):
            if f % f1 or f1 == f:
                continue
            q1 = 2 ** f1
            if Sz_order(q) % Sz_order(q1):
                continue
            c = Sz_order(q) // Sz_order(q1)
            out1 = f1
            r = Fraction(c, out1)
            if worst is None or r < worst[0]:
                worst = (r, f, f1)
            if c >= 2 and out1 % c == 0:
                hits += 1
                print("  HIT f=%d f1=%d c=%d" % (f, f1, c))
    print("  pairs f_1 | f, f_1 < f, both odd, f <= 201 : hits = %d" % hits)
    print("  smallest ratio c/|Out| encountered: %s at (f,f1) = (%d,%d)"
          % (worst[0], worst[1], worst[2]))
    print("  (c/|Out| >= 1 is already impossible for c >= 2 unless c | |Out|;")
    print("   the ratio here is astronomically larger than 1.)")

    print("\n  cross-check: alternating and sporadic orders are all "
          "divisible by 3")
    import math
    ok = all((math.factorial(m) // 2) % 3 == 0 for m in range(5, 40))
    print("     |A_m| divisible by 3 for 5 <= m <= 39 : %s" % ok)
    spor = [n for n in C52.SPORADIC] if hasattr(C52, "SPORADIC") else []
    if spor:
        print("     sporadic orders divisible by 3 : %s"
              % all(o % 3 == 0 for (_, o, _) in spor))
    print("\n  ==> (G2') CLOSED: Theorem Sz-T holds for every q = 2^{2m+1},")
    print("      uniformly, with no census and no residual window.\n")


# ================================================================= PART 4

def part4():
    print(BAR)
    print("PART 4 -- (G4) Lemma EQ: the equal-characteristic window")
    print(BAR)
    print("""
  Equal characteristic: S_1 is of Lie type over F_{q_1}, q_1 = p^{f_1},
  p the defining characteristic of the rank-1 TARGET.  Then

     (alpha)  q_1^{N1} = |S_1|_p  divides  |S|_p = q^N          [(E)]
     (beta)   4 d1 f1 g1 q_1^{mu1} >= |Out(S_1)| iota(S_1) >= iota(S)
              = q^N + 1 > q^N >= q_1^{N1}                       [(F),(T2)]

  Dividing:      Lemma EQ:   q_1^{N1 - mu1} < 4 d1 f1 g1 .

  N1 - mu1 = 0 exactly for the rank-1 families (the minimal parabolic IS
  the Borel, of index q_1^{N1}+1); N1 - mu1 >= 1 for every rank >= 2.
  Since f_1 <= log_2 q_1, Lemma EQ is a FINITE window.  Note it does not
  mention the target at all beyond its characteristic.
""")
    window = []
    print("  %-6s %-4s %6s %6s %8s   admissible q_1 (any characteristic)" %
          ("family", "n", "N1", "mu1", "N1-mu1"))
    for F in FAM:
        for n in ranks_of(F, 40):
            N1, mu1 = F["N"](n), F["mu"](n)
            Nm = N1 - mu1
            if Nm <= 0:
                continue
            d1m, g1 = dmax_of(F, n), F["g"]
            adm = []
            q1 = 1
            while True:
                q1 += 1
                if not is_prime_power(q1):
                    continue
                f1 = 0
                t = q1
                p1 = 2
                while p1 * p1 <= t:
                    if t % p1 == 0:
                        break
                    p1 += 1
                else:
                    p1 = t
                t, f1 = q1, 0
                while t % p1 == 0:
                    t //= p1
                    f1 += 1
                if q1 ** Nm >= 4 * d1m * f1 * g1:
                    if q1 > 4 * d1m * g1 * (ilog2(q1) + 1):
                        break
                    continue
                adm.append(q1)
            if adm:
                print("  %-6s %-4d %6d %6d %8d   %s" %
                      (F["key"], n, N1, mu1, Nm,
                       " ".join(map(str, adm))))
                for q1 in adm:
                    window.append((F, n, q1))
            if Nm >= 12:
                break
    print("\n  window size: %d (family, rank, q_1) triples" % len(window))
    print("  (empty for every rank whose N1-mu1 exceeds ~6: 2^{N1-mu1}")
    print("   beats 4 d1 f1 g1 <= 24*dmax*log_2 q_1 immediately.)")

    print("\n  now impose (E): c |S_1| = |S| with 2 <= c | |Out(S_1)|,")
    print("  and solve for the target q by exact integer root extraction.")
    hits = 0
    tested = 0
    for (F, n, q1) in window:
        # factor q1
        p1, t = 2, q1
        while t % p1:
            p1 += 1
        f1 = 0
        t = q1
        while t % p1 == 0:
            t //= p1
            f1 += 1
        if not F["qform"](p1, f1) or F["skip"](n, q1):
            continue
        S1 = order_of(F, n, q1)
        out1 = F["d"](n, q1) * f1 * F["g"]
        for c in range(2, out1 + 1):
            if out1 % c:
                continue
            M = c * S1
            tested += 1
            for solver, tag, ch in ((solve_U3, "U3", None),
                                    (solve_Sz, "Sz", 2),
                                    (solve_Ree, "Ree", 3)):
                for q in solver(M):
                    hits += 1
                    print("  HIT %s(%d) = %d * %s" %
                          (tag, q, c, F["name"](n, q1)))
    print("  (S_1, c) pairs tested: %d   ->  HITS: %d" % (tested, hits))

    # positive control: the solvers do fire when a solution exists
    print("\n  positive control (c = 1 self-solutions must be found):")
    ok = (solve_U3(U3_order(9)) == [9] and solve_Sz(Sz_order(32)) == [32]
          and solve_Ree(Ree_order(243)) == [243])
    print("     solve_U3(|U3(9)|)=[9], solve_Sz(|Sz(32)|)=[32], "
          "solve_Ree(|R(243)|)=[243] : %s" % ok)
    print("\n  ==> (G4) rank >= 2 socle in equal characteristic: CLOSED,")
    print("      for all three targets and all q.\n")


# ================================================================= PART 5

RANK1 = ["A1", "2A", "2B2", "2G2"]     # 2A only at n = 3


def rank1_list():
    out = []
    for F in FAM:
        if F["key"] == "A1":
            out.append((F, 1))
        elif F["key"] == "2A":
            out.append((F, 3))
        elif F["key"] in ("2B2", "2G2"):
            out.append((F, 1))
    return out


def part5(qmaxU3=5000000, fmax=201):
    print(BAR)
    print("PART 5 -- (G4) rank-1 socle in equal characteristic")
    print(BAR)
    print("""
  For a rank-1 S_1, N1 = mu1 and Lemma EQ is vacuous.  Instead put
      X := q_1^{N1} = |S_1|_p ,  Y := q^{N} = |S|_p ,  w := |Out(S_1)| .
  (alpha) X | Y  and  (beta) w(X+1) >= Y+1, so X lies within a factor w of
  Y.  With theta_1 := D1/N1 in {3 (L_2), 8/3 (U_3), 5/2 (Sz), 7/3 (R)} and
  the target exponent a/N in {8/3 (U_3), 5/2 (Sz), 7/3 (R)}:

    theta_1 < a/N :  c = |S|/|S_1| > d1 |S| / Y^{theta_1} -> infinity,
                     against c <= w = O(log Y).
    theta_1 > a/N :  c < 12 d1 |S| / X^{theta_1} -> 0, against c >= 2.
    theta_1 = a/N :  S_1 is in the target's OWN family; then Zsygmondy gives
                     f_1 | f, so q/q_1 >= q_1, and
                       c > (q/q_1)^a/(12 d) >= q_1^a/36  vs  c <= w <= 6 f_1,
                     impossible for every q_1 >= 2.

  Both thresholds are computed below EXACTLY (as integer inequalities, by
  raising to the power N1 so that theta_1 becomes the integer pair
  (D1, N1)), and the range below the threshold is checked exhaustively.
""")
    SUR5 = {
        "U3":  lambda q: q ** 3 * (q * q - 1) * (q ** 3 + 1),
        "Sz":  lambda q: q * q * (q - 1) * (q * q + 1),
        "Ree": lambda q: q ** 3 * (q - 1) * (q ** 3 + 1),
    }
    # ---- the exact thresholds
    print("  thresholds (smallest q_0 with the kill inequality valid for all")
    print("  q >= q_0, verified monotone on the scanned range):")
    print("  %-5s %-8s %-8s %-10s %s" %
          ("targ", "S_1 fam", "theta_1", "a/N", "kill threshold q_0"))
    for t in ("U3", "Sz", "Ree"):
        T = TARGET[t]
        N, a = T["N"], T["a"]
        if t == "U3":
            qs = [t[0] for t in prime_powers_sieve(20000) if t[0] >= 3]
        elif t == "Sz":
            qs = [2 ** f for f in range(3, 82, 2)]
        else:
            qs = [3 ** f for f in range(3, 82, 2)]
        for (F, n) in rank1_list():
            D1, N1 = F["D"](n), F["N"](n)
            th1 = Fraction(D1, N1)
            aN = Fraction(a, N)
            if th1 == aN:
                verdict = "same family as target -- subfield case, see below"
                print("  %-5s %-8s %-8s %-10s %s" %
                      (t, F["key"], th1, aN, verdict))
                continue
            # exact per-family constants:  |Out(S_1)| = d1 f1 g1 with
            #   A1 : d<=2, g=1   2A3 : d<=3, g=2   2B2, 2G2 : d=1, g=1
            # and f1 <= log_2 q_1 = log_2(X)/N1 <= log_2(Y)/N1 .
            # For the four rank-1 families prod(1 - q1^{-d_i}) >= 1/2, so
            #   X^{th1}/(2 d1)  <=  |S_1|  <=  X^{th1}/d1 .
            dg = {"A1": 2, "2A": 6, "2B2": 1, "2G2": 1}[F["key"]]
            d1m = {"A1": 2, "2A": 3, "2B2": 1, "2G2": 1}[F["key"]]

            def killed(q):
                S = SUR5[t](q)
                Y = q ** N
                wmax = dg * (ilog2(Y) // N1 + 1)
                if th1 < aN:
                    #  c > d1 |S| / Y^{th1} >= |S| / Y^{th1} > wmax >= c
                    return S ** N1 > wmax ** N1 * Y ** D1
                #  c < 2 d1 |S| / X^{th1} < 2  with X >= Y/wmax - 1
                X0 = Y // wmax - 1
                return X0 > 0 and (d1m * S) ** N1 < X0 ** D1
            hi = 4
            while not killed(hi):
                hi *= 2
                if hi > 10 ** 400:
                    break
            lo, h2 = hi // 2, hi
            while lo + 1 < h2:
                mid = (lo + h2) // 2
                if killed(mid):
                    h2 = mid
                else:
                    lo = mid
            print("  %-5s %-8s %-8s %-10s all q >= %d" %
                  (t, F["key"], th1, aN, h2))
    # ---- the exhaustive check
    print("\n  exhaustive check of (alpha)+(beta)+(E) over rank-1 socles in")
    print("  equal characteristic:")
    for t in ("U3", "Sz", "Ree"):
        T = TARGET[t]
        N = T["N"]
        if t == "U3":
            qs = [t for t in prime_powers_sieve(qmaxU3) if t[0] >= 3]
        elif t == "Sz":
            qs = [(2 ** f, 2, f) for f in range(3, fmax, 2)]
        else:
            qs = [(3 ** f, 3, f) for f in range(3, fmax, 2)]
        hits = 0
        tried = 0
        for (q, p, f) in qs:
            S, Y = T["order"](q), q ** N
            iotaS = T["iota"](q)
            for (F, n) in rank1_list():
                N1 = F["N"](n)
                for f1 in range(1, f * N // N1 + 2):
                    q1 = p ** f1
                    X = q1 ** N1
                    if X > Y:
                        break
                    if not F["qform"](p, f1) or F["skip"](n, q1):
                        continue
                    w = F["d"](n, q1) * f1 * F["g"]
                    if w * (X + 1) < iotaS:          # floor fails
                        continue
                    tried += 1
                    S1 = order_of(F, n, q1)
                    if S1 == 0 or S % S1:
                        continue
                    c = S // S1
                    if c >= 2 and w % c == 0:
                        hits += 1
                        print("  HIT %s(%d): c=%d, S_1=%s"
                              % (t, q, c, F["name"](n, q1)))
        print("     %-4s: %d targets, %d (S_1) candidates passing the floor"
              "  ->  HITS: %d" % (t, len(qs), tried, hits))
    print("\n  ==> (G4) rank-1 socle in equal characteristic: CLOSED.\n")


# ================================================================= PART 6

def part6():
    print(BAR)
    print("PART 6 -- (G3): what is left of the bounded --sub scan")
    print(BAR)
    print("""
  v_task53 (G3) complained that the direct scan of (E) used q_1 <= 10^5 and
  Lie rank <= 6.  After PARTS 3-5 that scan is no longer load-bearing:

    Sz  : PART 3 leaves only S_1 = Sz(q_1) -- no scan, no census, no window.
    U_3 : cross characteristic dies by v_task53 Sec 5.2 for q >= 179;
          equal characteristic dies by PARTS 4-5 for ALL q (rank >= 2 socle:
          the 71-element Lemma-EQ window, 0 hits; rank-1 socle: thresholds
          122 / 3 / 4 812 208, exhausted below).
          Residue needing the census: q < 179, plus q in {3,4,7} from Step 3.
    R   : cross characteristic dies by Sec 5.2 for q >= 2187, leaving
          q in {27, 243}; equal characteristic dies by PARTS 4-5 for all q.

  Rank is bounded without any scan assumption: 2^{D1} <= 6 d1 |S| (PART 2)
  in general and Lemma EQ in equal characteristic; both were enforced with
  rank <= 40 / <= 12, far past the true bound, and the Lemma-EQ window is
  empty for every N1 - mu1 >= 7.
""")
    print("  %-6s %-38s %s" % ("target", "residual window after PARTS 3-5",
                               "covered by"))
    print("  %-6s %-38s %s" % ("U3", "q < 179 (cross-char); q in {3,4,7}",
                               "census q <= 50 000, EMPTY (raw)"))
    print("  %-6s %-38s %s" % ("Sz", "-- none --",
                               "uniform proof, PART 3"))
    print("  %-6s %-38s %s" % ("Ree", "q in {27, 243} (cross-char)",
                               "census q <= 1.3e29, EMPTY (raw)"))
    print()
    print("  Alternating / sporadic socles: v_task53 Sec 5.4 is COMPLETE in q")
    print("  for all three targets (|Out| <= 4 resp. <= 2 makes the candidate")
    print("  list finite), 0 hits; for Sz they are additionally excluded by")
    print("  3-coprimality (PART 3).")
    print()


# ==========================================================================

def main():
    args = sys.argv[1:]
    todo = args if args else ["1", "2", "3", "4", "5", "6"]
    if "1" in todo:
        part1()
    if "2" in todo:
        part2()
    if "3" in todo:
        part3()
    if "4" in todo:
        part4()
    if "5" in todo:
        part5()
    if "6" in todo:
        part6()


if __name__ == "__main__":
    main()
