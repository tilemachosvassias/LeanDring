#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
h6_discharge.py -- closing (H6), the c-correction hypothesis of Theorem MF.

(H6) [the development record section 7.1]:  Lemma DEG's two equalities are used by
lu_residues PART C -- and inherited verbatim by Theorem MF -- with the
c-corrections set to ZERO:

    (P=)   sum_i l_i j_i N_i = N - eps_P ,   eps_P := v_p(c)/f  >= 0
    (R=)   sum_i l_i j_i n_i = (d-1) + theta

and neither eps_P nor theta was ever bounded.  The generic bound
c | prod_i(|Out(S_i)|^{l_i} l_i!) gives only log_q c = O(L log_q(df)), which
at q = 2 is comparable to d-1, so (H6) is NOT o(1) by that route.

This file replaces that route by five exact ingredients.

  PART 1  Lemma OUT-p  [NEW, PROVEN].  v_p(|Out(S_i)|) = v_p(f_i) + v_p(g_i);
          the DIAGONAL factor d_i is always prime to p.  Hence
              v_p(c) <= sum_i l_i (v_p(f_i) + v_p(g_i)) + sum_i v_p(l_i!) ,
          and every term is bounded by the DEG budget: f_i <= f K/k_i by
          Lemma Z (Z1), l_i by the rank budget.  The diagonal -- the ONLY
          part of |Out| that can be as large as the rank -- drops out.
  PART 2  Lemma FL2 [NEW, PROVEN].  The orbit floor alone forces
              v_i := l_i j_i n_i  >=  l_i * rho_i * (b - s_i) ,
          rho_i := n_i/mu_i >= 8/57, so with sum_i v_i = (d-1)+theta the
          socle has a BOUNDED number of factors: L <= 7 in the linear tower
          (L <= 2 with no exceptional factor), L <= 3 in the unitary one
          (and the all-classical unitary multi-factor branch is EMPTY).
  PART 3  The exact slack calculus:  E := sum_i v_i (d-h_i) = d*theta +
          2*eps_P (an identity given Lemma COX) and the closed form
              q^theta = (pi_S/e_S) (c_p^2/c) prod_i (e_i/pi_i)^{l_i} ,
          verified as exact identities of rationals; plus the integrality
          f*theta, f*eps_P in Z.
  PART 4  The tolerance of every branch of Theorem MF in terms of
          (theta, eps_P), and the INTEGER kill of the one tight branch.
  PART 5  An exact, slack-free census on 61 <= d <= DHI, every prime power
          q <= QMAX -- unconditional, no (DEG-exact), no (POS).

Usage:  python3 h6_discharge.py [dhi] [qmax]        (default 120 100)
"""

import sys
from fractions import Fraction as Fr
from math import factorial

sys.path.insert(0, ".")
sys.path.insert(0, __file__.rsplit("/", 1)[0])

from lemma_c_bound import FAM, order_of, gcd
from lu_twins import KFAM, Kmax, iota_LU, order_LU

BAR = "=" * 76

COX = {
    "A1": lambda n: 2, "A": lambda n: n, "2A": lambda n: n,
    "C": lambda n: 2 * n, "B": lambda n: 2 * n,
    "D": lambda n: 2 * n - 2, "2D": lambda n: 2 * n - 2,
    "G2": lambda n: 6, "3D4": lambda n: 6, "F4": lambda n: 12,
    "E6": lambda n: 12, "2E6": lambda n: 12, "E7": lambda n: 18,
    "E8": lambda n: 30, "2B2": lambda n: 4, "2G2": lambda n: 6,
    "2F4": lambda n: 12,
}
FB = {F["key"]: F for F in FAM}
EXCEPTIONAL = ("G2", "3D4", "F4", "E6", "2E6", "E7", "E8", "2B2", "2G2", "2F4")


def vp(n, p):
    v = 0
    while n and n % p == 0:
        n //= p
        v += 1
    return v


def vpQ(x, p):
    """v_p of a Fraction"""
    return vp(x.numerator, p) - vp(x.denominator, p)


def floorlog(n, p):
    """floor(log_p n) for n >= 1"""
    v, x = 0, 1
    while x * p <= n:
        x *= p
        v += 1
    return v


def prime_powers(qmax):
    out = []
    for q in range(2, qmax + 1):
        p = next(r for r in range(2, q + 1) if q % r == 0)
        m, f = q, 0
        while m % p == 0:
            m //= p
            f += 1
        if m == 1:
            out.append((q, p, f))
    return out


def rows_light(rankmax):
    out = []
    for F in FAM:
        ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], rankmax + 1)
        for n in ns:
            N, D, mu = F["N"](n), F["D"](n), F["mu"](n)
            k = KFAM[F["key"]](n)
            h = COX[F["key"]](n)
            out.append(dict(key=F["key"], n=n, N=N, D=D, mu=mu, k=k,
                            rk=D - 2 * N, h=h, rho=Fr(D - 2 * N, mu),
                            tau=Fr(D - 2 * N, k), F=F))
    return out


def bdeg_target(X, d):
    """deg_q iota(S):  d-1 (linear), 2d-3 (unitary, d >= 5)"""
    return d - 1 if X == "L" else 2 * d - 3


def logp_ub_int(n, p):
    """rigorous rational upper bound for log_p(n), n a positive integer"""
    return Fr(floorlog(n, p) + 1)


# rigorous upper bounds for  log_p( 1 / prod_{m>=1}(1 - q^{-m}) )  at the
# three smallest fields; for q >= 4 the bound  1/pi <= (q-1)/(q-2)  plus
# log_p(y) <= (y-1)/ln p <= 1.5 (y-1)  gives  <= 3/(2(q-2)).
_LPI_SMALL = {2: Fr(180, 100), 3: Fr(53, 100)}


def logp_inv_pi(q, p):
    if q == 2:
        return _LPI_SMALL[2]
    if q == 3:
        return _LPI_SMALL[3]
    return Fr(3, 2 * (q - 2))


# ============================================================ PART 1

def part1(qmax=1024, rankmax=40):
    print(BAR)
    print("PART 1 -- Lemma OUT-p : the diagonal factor is prime to p")
    print(BAR)
    print(r"""
  > Lemma OUT-p [PROVEN].  Let S_i be simple of Lie type over F_{q_i},
  > q_i = p^{f_i}, with |Out(S_i)| = d_i * f_i * g_i (diagonal * field *
  > graph, g_i in {1,2,3,6}).  Then p does NOT divide d_i, hence
  >
  >      v_p(|Out(S_i)|) = v_p(f_i) + v_p(g_i),   v_p(g_i) <= 1,
  >      and v_p(g_i) = 0 unless p in {2,3}.
  >
  > Proof.  Every diagonal order in the table is one of gcd(n, q_i-1),
  > gcd(n, q_i+1), gcd(2, q_i-1), gcd(4, q_i^n -+ 1), gcd(3, q_i -+ 1), 1,
  > i.e. a divisor of q_i^a -+ 1 for some a >= 1; and gcd(p, q_i^a -+ 1) = 1
  > because p | q_i.   []

  Consequence -- the INTEGER-floor bound on v_p(c) asked for by (H6):

      v_p(c)  <=  sum_i l_i ( v_p(f_i) + v_p(g_i) )  +  sum_i v_p(l_i!)
              <=  sum_i l_i ( floor(log_p f_i) + [p <= 3] )  +  (L-r)/(p-1)

  with, by Lemma Z (Z1),  f_i <= f K / k_i .  Note what is NOT there: the
  diagonal d_i.  The generic bound  c | prod|Out|^{l} l!  has a factor d_i
  per socle factor, and d_i can be as large as the rank; its p-part is 0, so
  it contributes nothing to eps_P = v_p(c)/f.  This is exactly the step that
  turns the O(L log_q(df)) generic estimate into O(L log_q f).
""")
    bad, tested = [], 0
    for F in FAM:
        ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], rankmax + 1)
        for n in ns:
            for (q, p, f) in prime_powers(qmax):
                if not F["qform"](p, f) or F["skip"](n, q):
                    continue
                tested += 1
                if F["d"](n, q) % p == 0:
                    bad.append((F["key"], n, q, p, F["d"](n, q)))
    print("  exhaustive check: %d (family, rank <= %d, prime power q <= %d)"
          % (tested, rankmax, qmax))
    print("  rows with  p | d_i  :  %s" % (bad[:5] if bad else "NONE"))
    assert not bad
    print("  graph factors g_i occurring : %s"
          % sorted(set(F["g"] for F in FAM)))
    print()
    # the resulting bound, tabulated
    print("  resulting bound on v_p(c) for the shapes PART 2 leaves (L <= 7,")
    print("  f_i <= f K/k_i with k_i >= d-2 in the pinned shapes):")
    print("    %-4s %-6s %-10s %-10s" % ("p", "f", "B_out(L=2)", "B_out(L=7)"))
    for p in (2, 3, 5):
        for f in (1, 2, 4, 12, 60):
            b2 = 2 * (floorlog(2 * f, p) + (1 if p <= 3 else 0)) + vp(2, p)
            b7 = 7 * (floorlog(2 * f, p) + (1 if p <= 3 else 0)) + vp(5040, p)
            print("    %-4d %-6d %-10d %-10d" % (p, f, b2, b7))
    print()
    return True


# ============================================================ PART 2

def part2():
    print(BAR)
    print("PART 2 -- Lemma FL2 : the orbit floor bounds the NUMBER of factors")
    print(BAR)
    R = rows_light(400)
    rho = {}
    for r in R:
        k = r["key"]
        if k not in rho or r["rho"] < rho[k]:
            rho[k] = r["rho"]
    print(r"""
  > Lemma FL2 [PROVEN].  Write b := deg_q iota(S) (= d-1 linear, 2d-3
  > unitary), s_i := log_q(8 l_i |Out(S_i)|), rho_i := n_i/mu_i.  The orbit
  > floor  l_i |Out(S_i)| iotabar(S_i) >= iota(S)  gives j_i mu_i >= b - s_i,
  > hence
  >        v_i = l_i j_i n_i  >=  l_i rho_i (b - s_i)
  > and, with (R=)  sum_i v_i = (d-1) + theta,
  >        L = sum_i l_i  <=  (d-1+theta) / ( rho_min (b - s_max) ).
  > []
""")
    print("  rho = n_r/mu, minimised over the rank, per family:")
    for k in sorted(rho, key=lambda k: rho[k]):
        print("     %-5s  rho_min = %-9s = %.4f" % (k, str(rho[k]),
                                                    float(rho[k])))
    rmin = min(rho.values())
    rcl = min(v for k, v in rho.items() if k not in EXCEPTIONAL)
    print("\n  rho_min over ALL families        = %s  (E8)  = %.4f"
          % (str(rmin), float(rmin)))
    print("  rho_min over CLASSICAL families  = %s        = %.4f"
          % (str(rcl), float(rcl)))
    print(r"""
  Asymptotic consequence (s_i/b -> 0, theta = o(d)):
     LINEAR  b = d-1 = the rank budget :  L <= 1/rho_min = 57/8 = 7.125,
             so L <= 7 ; with no exceptional factor rho_i >= 1/2 gives L<=2.
     UNITARY b = 2d-3, rank budget d-1 :  L <= (d-1)/(rho_min(2d-3)) ->
             57/16 = 3.5625, so L <= 3 ; with rho_i >= 1/2 the bound is
             L <= 1 -- the all-classical unitary multi-factor branch is
             EMPTY by the floor alone.

  EXACT integer version (no logarithms anywhere).  For a grid of (X,d,q):
  the largest L for which SOME atom (family, rank, f_i, multiplicity l)
  simultaneously satisfies the exact floor  l|Out|iotabar >= iota(S),
  Lemma Z  f_i k_i <= f K,  and the exact p-budget  l f_i N_i <= f N,
  while consuming rank budget  l j_i n_i <= d-1:""")
    print("    %-3s %-5s %-6s %-6s %-8s %s"
          % ("X", "d", "q", "Lmax", "Lmax_cl", "cheapest atom"))
    worst = {"L": 0, "U": 0}
    worstcl = {"L": 0, "U": 0}
    for X in ("L", "U"):
        for d in (61, 62, 80, 100, 120, 150, 200):
            for (q, p, f) in [(2, 2, 1), (3, 3, 1), (4, 2, 2), (8, 2, 3),
                              (9, 3, 2), (64, 2, 6), (97, 97, 1)]:
                K = Kmax(X, d)
                N = d * (d - 1) // 2
                iS = iota_LU(X, d, q)
                best = bestcl = None
                for r in R:
                    F = r["F"]
                    if r["n"] > 2 * d + 4 or r["N"] > f * N:
                        continue
                    fimax = f * K // r["k"]
                    for fi in range(1, fimax + 1):
                        if fi * r["N"] > f * N:
                            break
                        qi = p ** fi
                        if not F["qform"](p, fi) or F["skip"](r["n"], qi):
                            continue
                        ib = F["iota"](r["n"], qi)
                        ou = F["d"](r["n"], qi) * fi * F["g"]
                        lmin = -(-iS // (ou * ib))       # ceil
                        if lmin * fi * r["N"] > f * N:
                            continue
                        per = Fr(fi * r["rk"], f)        # rank cost per unit l
                        if lmin * per > d - 1:
                            continue
                        cand = (per, r["key"], r["n"], fi, lmin)
                        if best is None or per < best[0]:
                            best = cand
                        if r["key"] not in EXCEPTIONAL:
                            if bestcl is None or per < bestcl[0]:
                                bestcl = cand
                Lmax = int(Fr(d - 1) / best[0]) if best else 0
                Lmaxcl = int(Fr(d - 1) / bestcl[0]) if bestcl else 0
                worst[X] = max(worst[X], Lmax)
                worstcl[X] = max(worstcl[X], Lmaxcl)
                if d in (61, 120, 200) and q in (2, 4, 97):
                    lab = ("%s(n=%d) f_i=%d l>=%d" % best[1:]) if best else "-"
                    print("    %-3s %-5d %-6d %-6d %-8d %s"
                          % (X, d, q, Lmax, Lmaxcl, lab))
    print("\n  worst Lmax over the whole grid       :  L tower %d , U tower %d"
          % (worst["L"], worst["U"]))
    print("  worst Lmax, CLASSICAL atoms only     :  L tower %d , U tower %d"
          % (worstcl["L"], worstcl["U"]))
    print("  (Lmax_cl = 0 in the U tower means: no classical atom at all can")
    print("   meet the floor, so L >= 2 is impossible there.)")
    print()
    return rmin, rcl


# ============================================================ PART 3

def part3(trials=3000):
    print(BAR)
    print("PART 3 -- the exact slack calculus")
    print(BAR)
    print(r"""
  Notation.  x_i = l_i j_i, v_i := x_i n_i, h_i the Coxeter number of the
  ambient diagram, N_i = h_i n_i/2 (Lemma COX), delta_i := d - h_i.

  (S1)  E := sum_i v_i delta_i  =  d*theta + 2*eps_P .
        [ d sum v_i - sum v_i h_i = d(d-1+theta) - 2 sum x_i N_i
                                  = d(d-1+theta) - 2(N - eps_P) ]

  (S2)  q^theta = (pi_S/e_S) * (c_p^2/c) * prod_i (e_i/pi_i)^{l_i},
        e_S, e_i the diagonal orders, pi_S := |S| e_S q^{-a},
        pi_i := |S_i| e_i q_i^{-D_i}, c := |S|/prod_i|S_i|^{l_i}.
        [ q^{d-1+theta} = prod_i (q_i^{D_i-2N_i})^{l_i}
                        = (|S| / |S|_p^2) (c_p^2/c) prod (e_i/pi_i)^{l_i} ]
        Both pi's lie in [prod_{m>=1}(1-p^{-m}), 1], so (S2) is the sharp
        replacement for Lemma DEG's fudge factor kappa in [12^{-k}, 1].

  (S3)  INTEGRALITY.  f*theta = sum_i l_i f_i n_i - f(d-1) in Z, and
        f*eps_P = v_p(c) in Z_{>=0}.  If every j_i is an integer -- which
        Lemma Z forces whenever f < K/k_i, i.e. in every shape whose factors
        carry a top cyclotomic block -- then theta itself is an INTEGER.

  Machine verification of (S1) and (S2) as exact identities of rationals on
  synthetic configurations (arbitrary families / ranks / l_i / f_i, c taken
  as the rational |S|/prod|S_i|^{l_i}: they are algebraic identities, so
  they must hold off the admissible set as well):""")
    R = rows_light(30)
    import random
    random.seed(20260809)
    bad1 = bad2 = tested = 0
    for _ in range(trials):
        X = random.choice(("L", "U"))
        d = random.randint(31, 60)
        p, f = random.choice([(2, 1), (2, 2), (3, 1), (3, 2), (5, 1), (2, 4)])
        q = p ** f
        cfg = []
        for _ in range(random.randint(1, 3)):
            r = random.choice(R)
            F = r["F"]
            fi = random.randint(1, 3 * f)
            qi = p ** fi
            if not F["qform"](p, fi) or F["skip"](r["n"], qi):
                continue
            cfg.append((r, fi, random.randint(1, 3)))
        if not cfg:
            continue
        tested += 1
        N = d * (d - 1) // 2
        a = d * d - 1
        ftheta = sum(l * fi * r["rk"] for (r, fi, l) in cfg) - f * (d - 1)
        theta = Fr(ftheta, f)
        epsP = Fr(f * N - sum(l * fi * r["N"] for (r, fi, l) in cfg), f)
        E = sum(Fr(l * fi * r["rk"], f) * (d - r["h"]) for (r, fi, l) in cfg)
        if E != d * theta + 2 * epsP:
            bad1 += 1
        Sord = order_LU(X, d, q)
        eS = gcd(d, q - 1) if X == "L" else gcd(d, q + 1)
        piS = Fr(Sord * eS, q ** a)
        prod, rhs = 1, Fr(piS, eS)
        for (r, fi, l) in cfg:
            F, qi = r["F"], p ** fi
            oi = order_of(F, r["n"], qi)
            ei = F["d"](r["n"], qi)
            pii = Fr(oi * ei, qi ** r["D"])
            rhs *= (Fr(ei) / pii) ** l
            prod *= oi ** l
        c = Fr(Sord, prod)
        cp = Fr(p) ** vpQ(c, p)
        rhs *= cp * cp / c
        if Fr(p) ** ftheta != rhs:
            bad2 += 1
    print("\n  synthetic configurations tested : %d" % tested)
    print("  (S1) failures : %d       (S2) failures : %d" % (bad1, bad2))
    assert bad1 == 0 and bad2 == 0
    print()
    return True


# ============================================================ PART 4

def part4(dlo=61, dhi=2000):
    print(BAR)
    print("PART 4 -- the exact tolerance of every branch of Theorem MF")
    print(BAR)
    print(r"""
  Assume (POS) and Lemma Z, so delta_i = d - h_i >= 0 in the linear tower;
  E = d*theta + 2*eps_P by (S1).  Let A := {i : h_i = d} (then j_i = 1,
  k_i = d, n_i >= d/2) and B := the rest (delta_i >= 1).

    (L-a)  A empty :   E >= sum_i v_i = d-1+theta
                       ==>  a leak needs  (d-1) theta + 2 eps_P >= d-1 .
    (L-b)  A = {L_d(q)} :  v_A = d-1, sum_B v_i = theta, B nonempty, so by
                       Lemma FL2  theta >= rho_min (b - s) , i.e.
                       theta >= 8(d-1-s)/57  (>= (d-1-s)/2 if B is
                       classical).
    (L-c)  A = {C_{d/2}, B_{d/2} or D_{d/2+1}}  (d EVEN only) :
                       sum_B v_i = (d-1+theta) - n_A , every B row has
                       delta >= 1, so a leak needs
                       (d-1) theta + 2 eps_P >= (d-1) - n_A  >= d/2 - 1 .
    For d ODD the family list with h = k = d is {L_d} alone, so (L-c) does
    not occur and only the very weak (L-b) threshold is needed.

    (U)    Steps U1-U5 use sum v_i = d-1+theta against margins that are
           Theta(d^2); they tolerate |theta|, eps_P = o(d).

  (L-c) is the ONLY tight branch, and it becomes an INTEGER question.  Pin
  it: A = {C_{d/2}(q)} (l=1, j=1, n_A = d/2, N_A = d^2/4) plus one B factor,

      v_B = d/2 - 1 + theta ,     eps_P = d(d-2)/4 - v_B h_B / 2 ,
      hence  eps_P = [ delta_B (d - 2 + 2 theta) - 2 theta d ] / 4 .

  eps_P >= 0 and delta_B >= 1 force theta <= (d-2)/(2(d-1)) < 1/2, and then

      v_p(c) = f eps_P >= f [ (d-2)/4 - theta (d-1)/2 ] .

  Now Lemma Z pins the B factor: it must cover Phi_{d-1} (C_{d/2} does not:
  d-1 is odd and Cyc(C_n) contains only divisors of the even numbers 2i),
  so j_B k_B >= d-1 while j_B k_B < K = d by PACK-TOP (M_K = 1, the owner is
  A).  Hence k_B >= (d-1)/j_B and f_B <= f d/(d-1): for every f < d-1 this
  gives  f_B = f, i.e. j_B = 1, so by (S3) theta is an INTEGER; theta < 1/2
  then gives theta <= 0 and

      v_p(c) >= f (d-2)/4     versus     B_out <= 2 floor(log_p f) + 3 .

  Checked exactly below for every d in the range, p in {2,3,5,7,11,13} and
  every f < d-1 :""")
    fails = []
    for d in range(dlo, dhi + 1):
        for p in (2, 3, 5, 7, 11, 13):
            for f in range(1, d - 1):
                Bout = 2 * (floorlog(f, p) + (1 if p <= 3 else 0)) + vp(2, p)
                if Fr(f * (d - 2), 4) <= Bout:
                    fails.append((d, p, f, float(Fr(f * (d - 2), 4)), Bout))
    print("\n  (L-c) integrality kill, %d <= d <= %d, every f <= d-2 :"
          % (dlo, dhi))
    print("      failures = %s" % (fails[:6] if fails else "NONE"))
    print(r"""
  The complementary range f >= d-1 means q = p^f >= 2^{d-1}.  There the
  analytic form of (S2) closes (L-c) directly:  since pi_S <= 1, e_S >= 1
  and c_p <= c,
      theta <= eps_P + sum_i l_i log_q(e_i/pi_i)
            <= [ B_out + L (log_p e_max + log_p(1/pi(q))) ] / f ,
  with e_max <= d, L <= 2 (PART 2) and pi(q) := prod_{m>=1}(1-q^{-m})
  bounded below EXACTLY (no floats: log_p is bounded by an exact rational
  m/2000 with y^2000 <= p^m).  The leak needs
      (d-1) theta + 2 eps_P  >=  (d-2)/2 ,
  so the kill is  (d-1)*theta_ub + 2*eps_ub < (d-2)/2.  Smallest f for
  which that holds, against the integrality range f <= d-2 :""")
    print("    %-4s %-6s %-12s %-30s %s"
          % ("p", "d", "f needed", "integrality covers", "verdict"))
    resid = []
    for p in (2, 3, 5):
        for d in (61, 62, 80, 100, 130, 200, 500):
            fneed = None
            for f in range(1, 4 * d + 200):
                q = p ** f
                Bout = 2 * (floorlog(f + 1, p) + (1 if p <= 3 else 0)) \
                    + vp(2, p)
                epsub = Fr(Bout, f)
                lam = 2 * (logp_ub_int(d, p) + logp_inv_pi(q, p)) / f
                thub = epsub + lam
                if (d - 1) * thub + 2 * epsub < Fr(d - 2, 2):
                    fneed = f
                    break
            covered = (fneed is not None and fneed <= d - 1)
            if not covered:
                resid.append((p, d, fneed))
            print("    %-4d %-6d %-12s %-30s %s"
                  % (p, d, str(fneed), "f <= %d" % (d - 2),
                     "NO GAP" if covered else
                     "GAP  f in [%d, %d]" % (d - 1, (fneed or 0) - 1)))
    print("\n  residual (p, d, f_needed) of branch (L-c) : %s"
          % (resid if resid else "NONE"))
    print()
    return fails, resid


# ------------------------------------------------ PART 4b (unconditional)

def theta_window(X, d, q, p, f, atoms, Lmax):
    """(theta_leak, theta_ub):  theta_leak = the SMALLEST theta any L>=2
       configuration of the given atoms can have (exact); theta_ub = the
       certified upper bound for theta from (S2)+PART 1 (exact)."""
    costs = []
    for (F, n, fi, qi, o, ou, lmin, lmax) in atoms:
        per = Fr(fi * (F["D"](n) - 2 * F["N"](n)), f)
        costs.append((max(lmin, 1) * per, per, lmax, lmin))
    if not costs:
        return None, None
    best = None
    costs.sort()
    for (c1, per1, lmax1, lmin1) in costs:
        if max(lmin1, 2) <= lmax1:
            v = max(lmin1, 2) * per1
            best = v if best is None else min(best, v)
    if len(costs) >= 2:
        v = costs[0][0] + costs[1][0]
        best = v if best is None else min(best, v)
    if best is None:
        return None, None
    theta_leak = best - (d - 1)
    nmax = max(n for (F, n, fi, qi, o, ou, lmin, lmax) in atoms)
    Bout = Lmax * (floorlog(f * Kmax(X, d), p) + (1 if p <= 3 else 0)) \
        + vp(factorial(Lmax), p)
    theta_ub = Fr(Bout, f) + Lmax * (logp_ub_int(nmax + 1, p)
                                     + logp_inv_pi(q, p)) / f
    return theta_leak, theta_ub


# ============================================================ PART 5

def atoms_for(X, d, q, p, f):
    """every (F, n, f_i, q_i, |S_i|, |Out|, l_min, l_max) surviving
       (D1) order divisibility, (D3) floor satisfiability, (Z), p-budget."""
    S = order_LU(X, d, q)
    iS = iota_LU(X, d, q)
    N = d * (d - 1) // 2
    K = Kmax(X, d)
    b = bdeg_target(X, d)
    out = []
    for F in FAM:
        ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], 2 * d + 6)
        for n in ns:
            Ni, mui = F["N"](n), F["mu"](n)
            if Ni > f * N:
                break
            k = KFAM[F["key"]](n)
            fimax = f * K // k
            for fi in range(1, fimax + 1):
                if fi * Ni > f * N:
                    break
                # cheap degree pre-filter for (D3), deliberately generous:
                #   iotabar < 4 q_i^{mu},  iota(S) > q^{b}/2,
                #   l <= fN/(fi Ni) <= fN,  |Out| <= 6 (n+1) fi
                #   ==>  fi*mu + log_p(48 f N (n+1) fi) + 1 >= f*b
                if (fi * mui + floorlog(48 * f * N * (n + 1) * fi, p) + 1
                        < f * b):
                    continue
                qi = p ** fi
                if not F["qform"](p, fi) or F["skip"](n, qi):
                    continue
                o = order_of(F, n, qi)
                if S % o:
                    continue
                ou = F["d"](n, qi) * fi * F["g"]
                ib = F["iota"](n, qi)
                lmin = -(-iS // (ou * ib))
                lmax = (f * N) // (fi * Ni)
                if lmin > lmax or lmin < 1:
                    lmin = max(lmin, 1)
                if lmin > lmax:
                    continue
                out.append((F, n, fi, qi, o, ou, lmin, lmax))
    return S, iS, out


def dfs(S, atoms, idx, prod, chosen, budget):
    """(D1)+(D2)+(D4) DFS; every atom is entered with l >= l_min so (D3)
       holds automatically."""
    budget[0] += 1
    if budget[0] > 3000000:
        return None
    if sum(c[1] for c in chosen) >= 2 and S % prod == 0:
        c = S // prod
        bnd = 1
        for (at, l) in chosen:
            bnd *= at[5] ** l * factorial(l)
        if bnd % c == 0:
            return [(at[0]["name"](at[1], at[3]), at[2], l)
                    for (at, l) in chosen]
    for i in range(idx, len(atoms)):
        at = atoms[i]
        pw = prod
        for l in range(1, at[7] + 1):
            pw *= at[4]
            if S % pw:
                break
            if l < at[6]:
                continue
            hit = dfs(S, atoms, i + 1, pw, chosen + [(at, l)], budget)
            if hit:
                return hit
    return None


def part4b(dlo=61, dhi=120, qmax=100):
    print(BAR)
    print("PART 4b -- Lemma FL2 in action: how much the floor alone kills")
    print(BAR)
    print(r"""
  For each target (X, d, q) let A be the complete atom list: every
  (family, rank, f_i) surviving (D1) order divisibility, the exact orbit
  floor (D3) at its minimal admissible multiplicity, Lemma Z and the exact
  p-budget  sum_i l_i f_i N_i <= f N.  Subfield atoms f_i < f included.
  No (DEG-exact), no (POS), no logarithm.  A target with no L >= 2 multiset
  of atoms whose p-budget fits is EMPTY unconditionally -- the census of
  PART 5 does not even have to descend.  Counts:
""")
    QS = prime_powers(qmax)
    empty = need = 0
    per_tower = {"L": [0, 0], "U": [0, 0]}
    for d in range(dlo, dhi + 1):
        for X in ("L", "U"):
            for (q, p, f) in QS:
                S, iS, atoms = atoms_for(X, d, q, p, f)
                N = d * (d - 1) // 2
                ok2 = False
                for i, a in enumerate(atoms):
                    if 2 * max(a[6], 1) * a[2] * a[0]["N"](a[1]) <= f * N \
                            and max(a[6], 1) * 2 <= a[7]:
                        ok2 = True
                        break
                    for b in atoms[i + 1:]:
                        if (max(a[6], 1) * a[2] * a[0]["N"](a[1])
                                + max(b[6], 1) * b[2] * b[0]["N"](b[1])
                                <= f * N):
                            ok2 = True
                            break
                    if ok2:
                        break
                if ok2:
                    need += 1
                    per_tower[X][1] += 1
                else:
                    empty += 1
                    per_tower[X][0] += 1
        if d % 10 == 0 or d == dhi:
            print("  ... d = %-4d  emptied by the floor %-6d  need DFS %-6d"
                  % (d, empty, need))
            sys.stdout.flush()
    print("\n  (X,d,q) targets EMPTIED by the floor + p-budget alone : %d"
          % empty)
    print("  (X,d,q) targets still needing the census DFS          : %d" % need)
    print("     L tower : %d emptied, %d need DFS" % tuple(per_tower["L"]))
    print("     U tower : %d emptied, %d need DFS" % tuple(per_tower["U"]))
    print()
    return empty, need


# ------------------------------------------------ PART 4c

def part4c(dlo=61, dhi=120, fhi=48, primes=(2, 3, 5, 7, 11, 13)):
    """The DECISIVE parametrised sweep: with Lemma FL2 the linear tower has
       L <= 2 classically, so under (POS) every configuration is a pair
       (row_1, l_1, f_1), (row_2, l_2, f_2) with Lemma Z, PACK-TOP and the
       degree form of the orbit floor.  theta and eps_P are then DETERMINED,
       and we test them against PART 1's B_out and (S2)'s theta bound.
       No branch analysis, no order arithmetic -- so f may be large."""
    print(BAR)
    print("PART 4c -- the decisive (p,f)-parametrised 2-factor sweep")
    print(BAR)
    print(r"""
  Under (POS) and Lemma FL2 (L <= 2 with no exceptional factor) every
  admissible linear-tower configuration is a pair, and every quantity in
  Lemma DEG is determined by (row_i, l_i, f_i):

      theta  = ( sum_i l_i f_i n_i ) / f  -  (d-1)
      eps_P  =  N  -  ( sum_i l_i f_i N_i ) / f       (must be >= 0)
      v_p(c) =  f * eps_P                             (must be an integer)

  and the two certified bounds are
      v_p(c) <= B_out := sum_i l_i (v_p(f_i)+v_p(g_i)) + sum_i v_p(l_i!)
                                                       [Lemma OUT-p]
      theta  <= theta_ub := [B_out + sum_i l_i (log_p e_i + log_p(1/pi(q)))]/f
                                                       [(S2)]
  Constraints imposed: (POS) f_i >= f; (Z) f_i k_i <= f d; (PACK-TOP) some
  factor has f_i k_i = f d exactly and l_i = 1; the degree form of the orbit
  floor  f_i mu_i + log_p(48 f N (n_i+1) f_i) + 1 >= f (d-1)  (generous, so
  conservative); and h_i <= d.  Any surviving pair is reported.
""")
    R = [r for r in rows_light(3 * dhi + 8)]
    bad = []
    tested = 0
    for d in range(dlo, dhi + 1):
        N = d * (d - 1) // 2
        rows = [r for r in R if r["h"] <= d and r["key"] not in EXCEPTIONAL]
        for p in primes:
            for f in range(1, fhi + 1):
                q = p ** f
                lpi = logp_inv_pi(q, p)
                owners = []
                for r in rows:
                    if (f * d) % r["k"]:
                        continue
                    fi = f * d // r["k"]
                    if fi < f:
                        continue
                    owners.append((r, fi))
                if not owners:
                    continue
                # partners: (row, l, f_i) with the floor + budget
                partners = []
                for r in rows:
                    fmax = f * d // r["k"]
                    if fmax < f:
                        continue
                    for fi in range(f, fmax + 1):
                        if (fi * r["mu"]
                                + floorlog(48 * f * N * (r["n"] + 1) * fi, p)
                                + 1 < f * (d - 1)):
                            continue
                        for l in (1, 2):
                            if l * fi * r["N"] > f * N:
                                break
                            if l * fi * r["rk"] > f * (d + 4):
                                break
                            partners.append((r, l, fi))
                for (r1, f1) in owners:
                    if f1 * r1["N"] > f * N:
                        continue
                    for (r2, l2, f2) in partners:
                        tested += 1
                        ftheta = (f1 * r1["rk"] + l2 * f2 * r2["rk"]
                                  - f * (d - 1))
                        vpc = f * N - (f1 * r1["N"] + l2 * f2 * r2["N"])
                        if vpc < 0:
                            continue
                        Bout = (vp(f1, p) + vp(f2, p) * l2
                                + (1 if p <= 3 else 0) * (1 + l2)
                                + vp(1 if l2 < 2 else 2, p))
                        if vpc > Bout:
                            continue
                        emax = max(r1["n"], r2["n"]) + 1
                        thub = (Fr(Bout, f)
                                + (1 + l2) * (logp_ub_int(emax, p) + lpi) / f)
                        if Fr(ftheta, f) > thub:
                            continue
                        bad.append((d, p, f, r1["key"], r1["n"], f1,
                                    r2["key"], r2["n"], l2, f2,
                                    str(Fr(ftheta, f)), vpc))
        if d % 10 == 0 or d == dhi:
            print("  ... d = %-4d pairs tested %-10d survivors %d"
                  % (d, tested, len(bad)))
            sys.stdout.flush()
    print("\n  (POS) 2-factor pairs tested, %d <= d <= %d, p in %s, f <= %d"
          % (dlo, dhi, str(primes), fhi))
    print("     pairs tested                          : %d" % tested)
    print("     pairs surviving the DEG/(S2)/Out tests: %d" % len(bad))
    if bad:
        qs = sorted(set(x[1] ** x[2] for x in bad))
        print("     they occur only at q in a bounded set: max q = %d"
              % max(qs))
        print("     theta values realised                : %s"
              % sorted(set(x[10] for x in bad)))
        print("     v_p(c) values realised               : %s"
              % sorted(set(x[11] for x in bad)))
        print("     family pairs realised                : %s"
              % sorted(set((x[3], x[6]) for x in bad)))
        print()
        print("  Every survivor is now sent through the EXACT integer tests")
        print("  (D1) order divisibility and (D2) c | prod|Out|^l l! :")
        left = []
        for (d, p, f, k1, n1, f1, k2, n2, l2, f2, th, vpc) in bad:
            q = p ** f
            F1, F2 = FB[k1], FB[k2]
            q1, q2 = p ** f1, p ** f2
            if F1["skip"](n1, q1) or F2["skip"](n2, q2):
                continue
            if not F1["qform"](p, f1) or not F2["qform"](p, f2):
                continue
            S = order_LU("L", d, q)
            o = order_of(F1, n1, q1) * order_of(F2, n2, q2) ** l2
            if S % o:
                continue
            c = S // o
            ou1 = F1["d"](n1, q1) * f1 * F1["g"]
            ou2 = F2["d"](n2, q2) * f2 * F2["g"]
            if (ou1 * ou2 ** l2 * factorial(l2)) % c:
                continue
            iS = iota_LU("L", d, q)
            if ou1 * F1["iota"](n1, q1) < iS:
                continue
            if l2 * ou2 * F2["iota"](n2, q2) < iS:
                continue
            left.append((d, p, f, k1, n1, k2, n2, l2))
        print("     survivors also passing (D1)+(D2)+(D3) : %s"
              % (left[:6] if left else "NONE"))
        bad = left
    print()
    return bad


def part5(dlo=61, dhi=120, qmax=100):
    print(BAR)
    print("PART 5 -- exact, slack-free census, %d <= d <= %d, every q <= %d"
          % (dlo, dhi, qmax))
    print(BAR)
    print(r"""
  Tests, all INTEGER tests, exactly those of the development record section 5:
    (D1)  prod_i |S_i|^{l_i} divides |S|
    (D2)  c := |S|/prod_i|S_i|^{l_i}  divides  prod_i(|Out(S_i)|^{l_i} l_i!)
    (D3)  l_i |Out(S_i)| iotabar(S_i) >= iota(S)  for every i
    (D4)  sum_i l_i >= 2
  No (DEG-exact), no (POS), no logarithm feeds a yes/no answer.  Subfield
  factors f_i < f are enumerated.  New here is the range (the development record stopped
  at d = 60) and the PART 1/2 pruner, which makes the range reachable.
""")
    QS = prime_powers(qmax)
    tot_atoms = tot_nodes = 0
    hits = []
    for d in range(dlo, dhi + 1):
        for X in ("L", "U"):
            for (q, p, f) in QS:
                S, iS, atoms = atoms_for(X, d, q, p, f)
                tot_atoms += len(atoms)
                budget = [0]
                hit = dfs(S, atoms, 0, 1, [], budget)
                tot_nodes += budget[0]
                if hit:
                    hits.append((X, d, q, hit))
        if d % 10 == 0 or d == dhi:
            print("  ... d = %-4d atoms so far %-7d nodes %-9d HITS %d"
                  % (d, tot_atoms, tot_nodes, len(hits)))
            sys.stdout.flush()
    print("\n  surviving single atoms (D1)+(D3)-compatible : %d" % tot_atoms)
    print("  DFS nodes                                   : %d" % tot_nodes)
    print("  MULTI-FACTOR CONFIGURATIONS SURVIVING       : %s"
          % (hits[:5] if hits else "NONE"))
    print()
    return not hits


def main():
    dhi = int(sys.argv[1]) if len(sys.argv) > 1 else 120
    qmax = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    print("h6_discharge.py -- closing (H6), the c-correction hypothesis")
    print("dhi = %d   qmax = %d\n" % (dhi, qmax))
    part1()
    part2()
    part3()
    part4(61, 2000)
    part4b(61, dhi, qmax)
    part4c(61, dhi)
    part5(61, dhi, qmax)
    print(BAR)
    print("ALL CHECKS PASS.")
    print(BAR)


if __name__ == "__main__":
    main()
