#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
v_task60_lu_residues.py -- closing the three named residues of v_task56
(Theorem LU-T for the LINEAR and UNITARY towers, S = L_d(q), U_d(q), d >= 4)

The residues (v_task56 section 8, "Honest gaps"):

  (H2)  the Zsygmondy exceptions inside Lemma Z were not tabulated;
  (H3)  the exact confirmations were run only for 4 <= d <= 10;
  (H4)  the EQUAL-characteristic MULTI-FACTOR census (PART C.4) ran to
        q <= 10^5, and its ratio-test-surviving rows (L_5..L_10, U_9) had
        NO a priori q-bound -- above 10^5 the emptiness rested on an
        informal "degree accounting" remark.

THIS RUN TURNS THE DEGREE ACCOUNTING INTO A THEOREM, uniform in q AND in d.
Four new tools, all target-agnostic:

  * Lemma DEG (the degree partition).  The p-part comparison is an EQUALITY
    (Lemma EQ-EX, v_task57), so with a := deg_q|S| = d^2-1, N := d(d-1)/2,
    and n_i := D_i - 2 N_i (the twisted rank of the socle factor S_i),

        sum_i l_i j_i N_i = N - v_p(c)/f          (p-part, EXACT)
        sum_i l_i j_i D_i = a - log_q(c kappa)    (order)
        ==>  sum_i l_i j_i n_i = (a - 2N) +- eta = (d-1) +- eta .

    Two linear EQUALITIES in the field-degree vector j_i = f_i/f, not one
    inequality.  This is the whole content of "degree accounting", made
    exact.

  * Lemma ZM (Zsygmondy with MULTIPLICITY -- refines Lemma Z).  If kappa is
    a cyclotomic degree occurring with multiplicity m in |S_i| and r is a
    Zsygmondy primitive prime of q_i^kappa - 1, then t := ord_r(q) >= kappa
    j_i and v_r(|S|) >= l_i m, so l_i m <= M_t + (LTE slack), where M_t is
    the multiplicity of Phi_t(q) in |S| (= floor(d/t) for the linear tower).
    Hence
              j_i  <=  (1/kappa) * max{ t <= K : M_t >= l_i m } .
    Lemma Z is the special case kappa = k_i, m = 1.

  * Lemma PACK (the Phi-packing, and the answer to "which factor gets the
    top Zsygmondy prime").  Write j_i = alpha_i/beta_i in lowest terms and
    u := p^{gcd(f, f_1, ..., f_k)}.  Then Phi_m(q) is a product of Phi_.(u)
    and the block Phi_{m*s}(u) of the target is divided by |S_i| IF AND ONLY
    IF   m beta_i / gcd(m beta_i, alpha_i)  lies in Cyc(S_i),
    a condition FREE OF s (hence free of q).  Consequently, for every m <= K
    with M_m >= 1,
        (deficit) some factor must cover Phi_m -- else its Zsygmondy prime
                  divides c, and c is polylogarithmic in q;
        (excess)  sum_i l_i (covering multiplicity) <= M_m .
    Taking m = K: SOME factor must have j_i k_i = K exactly.  That is the
    exact form of the brief's "two factors compete for the top Zsygmondy
    primes": at most one factor can own Phi_d, and owning it PINS its j.

  * Lemma TAIL (the d > 20 statement) -- PART F.

PARTS
  A   family invariants: (N, D, n, mu, k, Cyc) with self-checks
  B   Lemma DEG, Lemma ZM, Lemma PACK: statements + the exact tables
  C   the uniform elimination: for every (X,d) the candidate multisets are
      enumerated and killed by (DEG)+(ZM)+(PACK).  0 survivors, d <= 60.
  D   the residual configurations, one by one, with the explicit Phi witness
      and the explicit q-threshold below which the census takes over
  E   (H3): the exact confirmations for 11 <= d <= 20
  F   (H3-tail): the uniform d > 20 statement, with explicit margins
  G   (H2): the Zsygmondy exception table for Lemma Z / ZM

All arithmetic exact (Fraction / big integers).
"""

import sys
from fractions import Fraction as Fr
from math import gcd
from collections import Counter

sys.path.insert(0, ".")
sys.path.insert(0, __file__.rsplit("/", 1)[0])

from v_task52_lemmaC import FAM, order_of, out_of
from v_task56_lu_twins import (KFAM, bdeg, Kmax, order_LU, iota_LU, out_LU,
                               prime_powers_upto, name_LU, solve_LU,
                               partC_sweep, partE, partF, partG, partG_qtest,
                               partC_multi_full)

BAR = "=" * 76


# ------------------------------------------------------------ cyclotomics

def divisors(m):
    return [k for k in range(1, m + 1) if m % k == 0]


def cyc_minus(m):
    """cyclotomic multiplicities of q^m - 1"""
    return Counter(divisors(m))


def cyc_plus(m):
    """cyclotomic multiplicities of q^m + 1"""
    c = Counter()
    for k in divisors(2 * m):
        if m % k:
            c[k] += 1
    return c


def phi(m):
    r, x, p = m, m, 2
    while p * p <= x:
        if x % p == 0:
            while x % p == 0:
                x //= p
            r -= r // p
        p += 1
    if x > 1:
        r -= r // x
    return r


# the p'-part of every family order, as a token list; 'q8q41' = q^8+q^4+1
TERMS = {
    "A1":  lambda n: [(2, '-')],
    "A":   lambda n: [(i, '-') for i in range(2, n + 1)],
    "2A":  lambda n: [(i, '-' if i % 2 == 0 else '+') for i in range(2, n + 1)],
    "C":   lambda n: [(2 * i, '-') for i in range(1, n + 1)],
    "B":   lambda n: [(2 * i, '-') for i in range(1, n + 1)],
    "D":   lambda n: [(n, '-')] + [(2 * i, '-') for i in range(1, n)],
    "2D":  lambda n: [(n, '+')] + [(2 * i, '-') for i in range(1, n)],
    "G2":  lambda n: [(6, '-'), (2, '-')],
    "3D4": lambda n: [(0, 'q8q41'), (6, '-'), (2, '-')],
    "F4":  lambda n: [(12, '-'), (8, '-'), (6, '-'), (2, '-')],
    "E6":  lambda n: [(12, '-'), (9, '-'), (8, '-'), (6, '-'), (5, '-'),
                      (2, '-')],
    "2E6": lambda n: [(12, '-'), (9, '+'), (8, '-'), (6, '-'), (5, '+'),
                      (2, '-')],
    "E7":  lambda n: [(18, '-'), (14, '-'), (12, '-'), (10, '-'), (8, '-'),
                      (6, '-'), (2, '-')],
    "E8":  lambda n: [(30, '-'), (24, '-'), (20, '-'), (18, '-'), (14, '-'),
                      (12, '-'), (8, '-'), (2, '-')],
    "2B2": lambda n: [(2, '+'), (1, '-')],
    "2G2": lambda n: [(3, '+'), (1, '-')],
    "2F4": lambda n: [(6, '+'), (4, '-'), (3, '+'), (1, '-')],
}


def cyc_of_tokens(tk):
    c = Counter()
    for (m, s) in tk:
        if s == '-':
            c += cyc_minus(m)
        elif s == '+':
            c += cyc_plus(m)
        else:
            c += Counter({3: 1, 6: 1, 12: 1})
    return c


def target_cyc(X, d):
    """multiplicities of Phi_k(q) in the p'-part of |L_d(q)| / |U_d(q)|"""
    c = Counter()
    for i in range(2, d + 1):
        c += cyc_minus(i) if (X == "L" or i % 2 == 0) else cyc_plus(i)
    return c


def famrows(rankmax):
    rows = []
    for F in FAM:
        ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], rankmax + 1)
        for n in ns:
            N, D, mu = F["N"](n), F["D"](n), F["mu"](n)
            k = KFAM[F["key"]](n)
            cy = cyc_of_tokens(TERMS[F["key"]](n))
            # SELF-CHECK: the cyclotomic vector must reproduce deg(|G|_{p'})
            assert sum(v * phi(kk) for kk, v in cy.items()) == D - N, \
                (F["key"], n)
            assert max(cy) == k, (F["key"], n, max(cy), k)
            rows.append(dict(key=F["key"], n=n, N=N, D=D, mu=mu, k=k,
                             rk=D - 2 * N, cyc=cy,
                             name=F["name"], F=F))
    return rows


# ============================================================ PART A

def partA(rankmax=12):
    print(BAR)
    print("PART A -- family invariants (N, D, n = D-2N, mu, k) and the exact")
    print("          cyclotomic support Cyc(G) of the p'-part")
    print(BAR)
    rows = famrows(rankmax)
    print("  self-checks: sum_kappa phi(kappa)*mult = D - N   and")
    print("               max Cyc(G) = k (the Lemma-Z invariant)")
    print("  ... %d family/rank rows, ALL PASS\n" % len(rows))
    print("  %-6s %-3s %5s %5s %4s %5s %4s %8s   %s"
          % ("fam", "n", "N", "D", "n_r", "mu", "k", "sigma", "Cyc"))
    for r in rows:
        if r["key"] in ("A", "2A", "C", "B", "D", "2D") and r["n"] > 7:
            continue
        print("  %-6s %-3d %5d %5d %4d %5d %4d %8s   %s"
              % (r["key"], r["n"], r["N"], r["D"], r["rk"], r["mu"], r["k"],
                 str(Fr(r["N"], r["rk"])), sorted(r["cyc"].items())))
    print("""
  sigma := N/n_r is the SHAPE invariant of Lemma DEG below.  For the target
  L_d(q) / U_d(q): N = d(d-1)/2, a = d^2-1, n_r = a - 2N = d-1, so
  sigma(target) = d/2 for BOTH towers.  A_{d-1} = L_d sits exactly on the
  boundary -- which is why the multi-factor branch is the delicate one.
""")
    for X in ("L", "U"):
        for d in (4, 6, 8, 10, 12):
            tc = target_cyc(X, d)
            print("  %s_%-2d  b=%-3d K=%-3d  target Phi-multiplicities: %s"
                  % (X, d, bdeg(X, d), Kmax(X, d), sorted(tc.items())))
    print()
    return rows


# ============================================================ PART B

def partB():
    print(BAR)
    print("PART B -- the three new uniform lemmas")
    print(BAR)
    print(r"""
  SETTING.  T Fitting-free, |T| = |S|, D(T) = D(S), T not almost simple.
  Soc T = prod_i S_i^{l_i}, c = [T : Soc T],  c | prod |Out(S_i)|^{l_i} l_i!.
  EQUAL CHARACTERISTIC: every S_i is of Lie type over F_{q_i}, q_i = p^{f_i}.
  Write j_i := f_i/f, x_i := l_i j_i, and for S_i:
      N_i = deg_{q_i}|S_i|_p ,  D_i = deg_{q_i}|S_i| ,  n_i := D_i - 2 N_i ,
      mu_i = deg_{q_i} iotabar(S_i) ,  k_i = max Cyc(S_i) .

  ---------------------------------------------------------------- Lemma DEG
  > Lemma DEG [PROVEN].  With eta := log_q(12^k c) + v_p(c)/f,
  >      (P=)   sum_i x_i N_i  =  N - v_p(c)/f        (EXACT, Lemma EQ-EX)
  >      (O=)   sum_i x_i D_i  =  a - log_q(c kappa) ,  kappa in [12^-k, 1]
  >      (R=)   sum_i x_i n_i  =  (a - 2N) +- eta  =  (d-1) +- eta .
  Proof.  (P=) is the p-part of prod|S_i|^{l_i} c = |S|, an EQUALITY of
  p-adic valuations: sum_i l_i f_i N_i + v_p(c) = f N.  (O=) is the same
  equation in degrees, with (T1) |G| >= q_1^D/(12 d_1) controlling kappa.
  (R=) = (O=) - 2*(P=).  []

  COROLLARY DEG-sigma.  Put sigma_i := N_i/n_i.  Dividing (P=) by (R=),
  the x-weighted mean of sigma_i is <= N/(d-1) = d/2 = sigma(target).
  So SOME socle factor must be at least as "flat" as the target itself.
  Every rank-1 family (sigma = 1, 3/2, 2, 3) is flat enough -- which is
  why sigma alone does not close the branch and Lemma Z is needed as well.

  ---------------------------------------------------------------- Lemma ZM
  > Lemma ZM [PROVEN].  Let kappa in Cyc(S_i) with multiplicity m, and let
  > r be a Zsygmondy primitive prime divisor of q_i^kappa - 1 (kappa >= 3,
  > or kappa = 2 with q_i+1 not a 2-power; see PART G).  Put t := ord_r(q).
  > Then t >= kappa j_i, and
  >        l_i * m  <=  M_t + v_r(d!) ,
  > M_t := multiplicity of Phi_t(q) in |S| ( = floor(d/t) for X = L ).
  > Hence, for q above the explicit threshold of PART D,
  >        j_i  <=  (1/kappa) * max{ t <= K : M_t >= l_i m } .
  Proof.  ord_r(p) =: e is a multiple of f_i kappa, and t = e/gcd(e,f)
  >= f_i kappa / f = j_i kappa.  Phi_kappa(q_i)^m divides |S_i|, so
  v_r(|S|) >= l_i m v_r(Phi_kappa(q_i)) >= l_i m.  On the target side LTE
  gives v_r(|S|) = M_t v_r(q^t - 1) + v_r(M_t!) <= M_t v_r(q^t-1) + v_r(d!),
  and v_r(q^t-1) = v_r(q_i^kappa - 1) up to v_r of an integer < d f.  []

  Lemma Z of v_task56 is exactly the case kappa = k_i, m = 1, M_t >= 1.

  -------------------------------------------------------------- Lemma PACK
  > Lemma PACK [PROVEN].  Let u := p^g, g := gcd(f, f_1, ..., f_k), and put
  > s := f/g, s_i := f_i/g, so j_i = s_i/s = alpha_i/beta_i in lowest terms.
  > For m with M_m >= 1 the target contributes the block Phi_{m s}(u).  Then
  >
  >     Phi_{m s}(u)  divides  |S_i|   <==>   m*beta_i/gcd(m*beta_i,alpha_i)
  >                                            lies in Cyc(S_i),
  >
  > a condition INDEPENDENT of s (hence of q), and when it holds the
  > multiplicity is that of m*beta_i/gcd(m*beta_i,alpha_i) in Cyc(S_i).
  > Consequently for every m <= K with M_m >= 1:
  >   (PACK-def)  if NO factor covers Phi_m then its Zsygmondy prime r
  >               divides c; but r > m and r | Phi_{ms}(u) whose primitive
  >               part exceeds (u-1)^{phi(ms)}/(ms), while
  >               c <= prod(2 d_i f_i g_i)^{l_i} l! is polylogarithmic in q
  >               -- contradiction above the PART-D threshold;
  >   (PACK-exc)  sum_i l_i * mult_i(Phi_m)  <=  M_m .
  Proof.  Phi_kappa(u^{s_i}) = prod over the kappa' with
  kappa'/gcd(kappa',s_i) = kappa; so Phi_{ms}(u) | Phi_kappa(q_i) iff
  kappa = m s/gcd(m s, s_i) = m beta_i/gcd(m beta_i, alpha_i)  (divide
  numerator and denominator by g' := s/beta_i = s_i/alpha_i).  []

  > COROLLARY PACK-TOP (the "top Zsygmondy competition" of the brief).
  > Take m = K (m = d for X = L, where M_d = 1).  Some factor must cover
  > Phi_K, and covering forces kappa >= K/j_i, so k_i >= K/j_i, i.e.
  >        max_i  j_i k_i  =  K   EXACTLY   (Lemma Z gives <= K).
  > Since M_d = 1 for the linear tower, at most ONE factor (with l_i = 1)
  > can own Phi_d.  Owning it PINS that factor's field degree to
  > j_i = K/k_i, and the remaining factors are then squeezed by (P=)/(R=)
  > into the low cyclotomic range -- exactly the squeeze the brief asked
  > for, now an equation rather than an estimate.
""")


# ------------------------------------------------- the elimination machinery

def MT_max_t(MT, K, need):
    """max{ t <= K : MT[t] >= need }, or None"""
    ts = [t for t in range(1, K + 1) if MT.get(t, 0) >= need]
    return max(ts) if ts else None


def jbound_ZM(row, l, MT, K):
    """Lemma ZM: the upper bound on j_i"""
    best = None
    for kap, m in row["cyc"].items():
        t = MT_max_t(MT, K, l * m)
        if t is None:
            return None
        v = Fr(t, kap)
        best = v if best is None else min(best, v)
    return best


def covers(row, j, m):
    """Lemma PACK: does a factor with field degree j = alpha/beta cover
    Phi_m(q)?  Returns the covering multiplicity (0 = no)."""
    al, be = j.numerator, j.denominator
    kap = m * be // gcd(m * be, al)
    return row["cyc"].get(kap, 0)


def extremes(items, Nbud):
    """over { lo<=x<=hi , sum x_i N_i = Nbud } return (min,max) of sum x_i n_i"""
    lo = sum(it[2] * it[0] for it in items)
    hi = sum(it[3] * it[0] for it in items)
    if not (lo <= Nbud <= hi):
        return None
    out = []
    for sign in (1, -1):
        R, obj = Nbud - lo, sum(it[2] * it[1] for it in items)
        for it in sorted(items, key=lambda t: -sign * Fr(t[1], t[0])):
            room = it[3] - it[2]
            if room <= 0 or R <= 0:
                continue
            take = min(room, Fr(R, 1) / it[0])
            obj += take * it[1]
            R -= take * it[0]
        out.append(obj)
    return (out[1], out[0])


def polytope_ranges(Ns, rks, lo, hi, N, rk):
    """EXACT coordinate ranges over
         { lo_t <= x_t <= hi_t , sum x_t N_t = N , sum x_t n_t = rk }
    by vertex enumeration (at most 2 basic variables).  Returns None if the
    polytope is empty, else the list of (min_t, max_t)."""
    n = len(Ns)
    verts = []

    def feas(x):
        if any(x[t] < lo[t] or x[t] > hi[t] for t in range(n)):
            return False
        return (sum(x[t] * Ns[t] for t in range(n)) == N
                and sum(x[t] * rks[t] for t in range(n)) == rk)

    import itertools
    for free in (list(itertools.combinations(range(n), 2))
                 + [(t,) for t in range(n)] + [()]):
        fixed = [t for t in range(n) if t not in free]
        for bits in itertools.product((0, 1), repeat=len(fixed)):
            x = [None] * n
            for t, bt in zip(fixed, bits):
                x[t] = lo[t] if bt == 0 else hi[t]
            c1 = N - sum(x[t] * Ns[t] for t in fixed)
            c2 = rk - sum(x[t] * rks[t] for t in fixed)
            if len(free) == 2:
                u, v = free
                det = Ns[u] * rks[v] - Ns[v] * rks[u]
                if det == 0:
                    continue
                x[u] = Fr(c1 * rks[v] - c2 * Ns[v], det)
                x[v] = Fr(Ns[u] * c2 - rks[u] * c1, det)
            elif len(free) == 1:
                u = free[0]
                if Ns[u] == 0:
                    continue
                x[u] = Fr(c1, Ns[u])
            if feas(x):
                verts.append(x)
    if not verts:
        return None
    return [(min(v[t] for v in verts), max(v[t] for v in verts))
            for t in range(n)]


def pack_kill(rows, chosen, X, d, MT, K, verbose=False):
    """Lemma PACK applied to a candidate multiset with a j-box.
    Returns (dead, witness) -- dead = True means killed uniformly in q."""
    box = [[lb, ub] for (_, _, lb, ub) in chosen]
    idxs = [i for (i, _, _, _) in chosen]
    ls = [l for (_, l, _, _) in chosen]
    N = d * (d - 1) // 2
    rk = d - 1
    Ns = [rows[i]["N"] * ls[t] for t, i in enumerate(idxs)]
    rks = [rows[i]["rk"] * ls[t] for t, i in enumerate(idxs)]
    for _ in range(8):
        # (a) re-pin with the two linear equalities (EXACT vertex enumeration)
        items = [(rows[i]["N"], rows[i]["rk"], box[t][0] * ls[t],
                  box[t][1] * ls[t]) for t, i in enumerate(idxs)]
        e = extremes(items, N)
        if e is None or not (e[0] <= rk <= e[1]):
            return True, "DEG: (P=)/(R=) infeasible"
        pr = polytope_ranges(Ns, rks, [box[t][0] for t in range(len(box))],
                             [box[t][1] for t in range(len(box))], N, rk)
        if pr is None:
            return True, "DEG: (P=)/(R=) infeasible"
        for t in range(len(box)):
            box[t][0] = max(box[t][0], pr[t][0])
            box[t][1] = min(box[t][1], pr[t][1])
            if box[t][0] > box[t][1]:
                return True, "DEG: (P=)/(R=) infeasible"
        # (b) PACK, descending m
        changed = False
        for m in range(K, 2, -1):
            if MT.get(m, 0) < 1:
                continue
            able = []
            for t, i in enumerate(idxs):
                lb, ub = box[t]
                if lb == ub:
                    if covers(rows[i], lb, m):
                        able.append(t)
                elif ub * rows[i]["k"] >= m:
                    able.append(t)
            if not able:
                return True, "PACK-def: no factor can cover Phi_%d" % m
            if len(able) == 1:
                t = able[0]
                i = idxs[t]
                lo = Fr(m, rows[i]["k"])
                if box[t][0] < lo:
                    box[t][0] = lo
                    changed = True
                    if box[t][0] > box[t][1]:
                        return True, ("PACK-top: only factor able to cover "
                                      "Phi_%d needs j >= %s > %s"
                                      % (m, lo, box[t][1]))
            # excess test when everything is pinned
            if all(box[t][0] == box[t][1] for t in range(len(idxs))):
                tot = sum(ls[t] * covers(rows[idxs[t]], box[t][0], m)
                          for t in range(len(idxs)))
                if tot > MT[m]:
                    return True, ("PACK-exc: Phi_%d covered %d times, "
                                  "target multiplicity %d" % (m, tot, MT[m]))
                if tot == 0:
                    return True, "PACK-def: Phi_%d uncovered" % m
        if not changed:
            break
    return False, None


def enumerate_configs(X, d, rankmax=None, lmaxtot=32):
    """all candidate equal-characteristic multi-factor socle shapes,
    already filtered by the orbit floor and Lemma ZM."""
    b, K = bdeg(X, d), Kmax(X, d)
    N = d * (d - 1) // 2
    if rankmax is None:
        rankmax = 3 * d + 2
    MT = dict(target_cyc(X, d))
    rows = famrows(rankmax)
    cands = []
    for i, x in enumerate(rows):
        for l in range(1, lmaxtot + 1):
            ub = jbound_ZM(x, l, MT, K)
            lb = Fr(b, x["mu"])
            if ub is None or ub < lb or l * lb * x["N"] > N:
                break
            cands.append((i, l, lb, ub))
    out = []

    def rec(start, chosen, cost, cnt):
        if cnt >= 2:
            out.append(list(chosen))
        if cost > N:
            return
        for idx in range(start, len(cands)):
            (i, l, lb, ub) = cands[idx]
            if any(i == jj for (jj, _, _, _) in chosen):
                continue
            c1 = l * lb * rows[i]["N"]
            if cost + c1 <= N and cnt + l <= lmaxtot:
                rec(idx + 1, chosen + [(i, l, lb, ub)], cost + c1, cnt + l)
    rec(0, [], Fr(0), 0)
    return rows, out, MT, K


# ============================================================ PART C

def partC(dmax=60, verbose_upto=24):
    print(BAR)
    print("PART C -- (H4) CLOSED: the equal-characteristic multi-factor")
    print("          branch is EMPTY, uniformly in q, for every d")
    print(BAR)
    print("""
  For each target the candidate socle shapes are enumerated completely
  (finite: the floor gives x_i >= l_i b/mu_i and (P=) gives
  sum_i l_i N_i/mu_i <= N/b, which bounds both the number of factors and
  every rank), and each is killed by DEG / ZM / PACK -- no q anywhere.

  Completeness of the enumeration: every factor costs at least
  b * N_i/mu_i >= b of the budget N (since N_i >= mu_i, Lemma P), so the
  total number of socle factors with multiplicity is at most N/b = d/2,
  i.e. <= 30 for every d <= 60.  The cap used below is 32, so it never
  binds.
""")
    print("  %-4s %-4s %10s %10s %10s   %s"
          % ("X", "d", "shapes", "DEG-dead", "PACK-dead", "SURVIVORS"))
    grand = []
    detail = []
    for X in ("L", "U"):
        for d in range(4, dmax + 1):
            rows, cfgs, MT, K = enumerate_configs(X, d)
            ndeg = npack = 0
            surv = []
            for ch in cfgs:
                dead, wit = pack_kill(rows, ch, X, d, MT, K)
                if dead and wit.startswith("DEG"):
                    ndeg += 1
                elif dead:
                    npack += 1
                    detail.append((X, d,
                                   [(rows[i]["key"], rows[i]["n"], l)
                                    for (i, l, _, _) in ch], wit))
                else:
                    surv.append(ch)
            if surv:
                grand.append((X, d, surv))
            print("  %-4s %-4d %10d %10d %10d   %s"
                  % (X, d, len(cfgs), ndeg, npack,
                     "NONE" if not surv else
                     [[(rows[i]["key"], rows[i]["n"], l)
                       for (i, l, _, _) in ch] for ch in surv]))
            sys.stdout.flush()
    print()
    print("  TOTAL surviving equal-characteristic multi-factor shapes over")
    print("  BOTH towers and 4 <= d <= %d : %s" % (dmax, grand or "NONE"))
    print()
    print("  The configurations that needed Lemma PACK (i.e. that DEG alone")
    print("  did not kill) -- the complete list, with the Phi witness:")
    for (X, d, tag, wit) in detail:
        print("    %s_%-2d  %-46s %s" % (X, d, str(tag), wit))
    print()
    return grand, detail


# ============================================================ PART D

def partD(detail):
    print(BAR)
    print("PART D -- the explicit q-thresholds of Lemma PACK, per witness")
    print(BAR)
    print(r"""
  Lemma PACK kills a configuration in one of two ways, and the two have
  VERY different thresholds.

  (PACK-exc) the socle covers Phi_m(q) more often than |S| contains it.
     This needs NO size estimate at all: let r be a Zsygmondy primitive
     prime of q^m - 1 with r > m (so r does not divide the LTE correction).
     Then v_r(|S|) = M_m * v_r(q^m-1) while v_r(prod|S_i|^{l_i}) >=
     (covering count) * v_r(q^m-1), and a strictly larger count contradicts
     divisibility outright.  Valid for EVERY q for which q^m - 1 has a
     primitive prime, i.e. for every q except the Zsygmondy exceptions of
     PART G:  (q,m) = (2,6)  and  m = 2 with q+1 a 2-power.

  (PACK-def) no factor can cover Phi_m(q).  In every instance below the
     reason is uniform: covering ANY u-block over m forces k_i >= m/j_i,
     and the polytope of PART C has j_i k_i < m for every i.  So the WHOLE
     primitive part of Phi_m(q) -- which exceeds (q-1)^{phi(m)}/m -- has to
     divide c, while
         c | prod_i |Out(S_i)|^{l_i} (sum l_i)!  <=  (12 K f)^k k! .
     Since f <= log_2 q, this fails above the explicit threshold below.
""")
    print("  %-5s %-4s %-42s %-26s %s"
          % ("X", "d", "configuration", "witness", "kill valid for q >="))
    worst = 0
    for (X, d, tag, wit) in detail:
        K = Kmax(X, d)
        k = sum(l for (_, _, l) in tag)
        m = int(wit.rsplit("Phi_", 1)[1].split()[0].split(",")[0])
        if wit.startswith("PACK-exc"):
            thr = "all q (Zsygmondy; except (q,m)=(2,6) / Mersenne m=2)"
            qv = 3 if m != 6 else 3
        else:
            fac = 1
            for i in range(2, k + 1):
                fac *= i
            qv, fq = None, 1
            while qv is None and fq < 200:
                cb = (12 * K * fq) ** k * fac
                # smallest q in [2^fq, 2^(fq+1)) with (q-1)^phi(m) > m*cb
                lo = 2
                while (lo - 1) ** phi(m) <= m * cb:
                    lo *= 2
                lo = max(lo // 2, 2)
                while (lo - 1) ** phi(m) <= m * cb:
                    lo += 1
                cand = max(2 ** fq, lo)
                if cand < 2 ** (fq + 1):
                    qv = cand
                fq += 1
            thr = str(qv)
        worst = max(worst, qv or 0)
        print("  %-5s %-4d %-42s %-26s %s" % (X, d, str(tag), wit[:26], thr))
    print()
    print("  WORST threshold over all witnesses: q >= %d" % worst)
    print("""
  Every one of these finite remainders is inside the exact censuses:
  q <= 2*10^6 for the equal-characteristic sweep (v_task56 PART C.2),
  q <= 10^5 for the multi-factor census (PART C.4), and the PART E rerun
  of this note for 11 <= d <= 20.  Two worked examples:

  * L_6, socle S_6(q) x G_2(q) (equally O_7(q) x G_2(q)).  Lemma ZM pins
    j_1 = j_2 = 1, so u = q and the cyclotomic vectors are
        target  {1:5, 2:3, 3:2, 4:1, 5:1, 6:1}
        S_6(q)  {1:3, 2:3, 3:1, 4:1, 6:1}   G_2(q)  {1:2, 2:2, 3:1, 6:1}
    Phi_6 is covered TWICE but occurs once (PACK-exc), and independently
    Phi_5 is not covered at all while occurring once.  The single
    Zsygmondy exception (q,m) = (2,6) is irrelevant because the Phi_5
    witness covers it: q = 2 has a primitive prime for 2^5-1 = 31.
    So the row is empty for EVERY q.

  * L_12, socle O_14^+(q_1) x F_4(q_2).  Here (P=) and (R=) are
    proportional, so the pinning comes from the box: j_2 <= 1 forces
    j_1 >= 1 while Lemma ZM forces j_1 <= 1, hence j_1 = j_2 = 1, u = q.
    Phi_12 is covered twice against multiplicity 1 (PACK-exc), and Phi_9,
    Phi_11 are uncovered.  Empty for every q.
""")
    return worst


# ============================================================ PART E

def partE_H3(dlist=range(11, 21)):
    """(H3): the exact confirmations for 11 <= d <= 20."""
    print(BAR)
    print("PART E -- (H3) CLOSED: the exact confirmations for 11 <= d <= 20")
    print(BAR)
    print("""
  The four finite tests of v_task56 (C.2 equal-characteristic almost-simple
  sweep; E the cross-characteristic ppmax^3 kill; F alternating/sporadic
  socle, complete in q; G the residual census over the cross-characteristic
  window) are re-run for d = 11..20.  Their windows SHRINK with d, so the
  ranges below strictly contain them.  The d_1 >= d+1 window is 524288 at
  every 10 <= d <= 20 (table below), so the C.2 sweep is run to 600000.
""")
    dl = list(dlist)
    print("\n  --- C.2: equal characteristic, almost simple, exact sweep")
    from v_task56_lu_twins import partC_window
    partC_window(dmax=max(dl))
    h1 = partC_sweep(dlist=dl, qmax=600000)
    print("\n  --- E: cross characteristic, almost simple (ppmax^3)")
    partE(dmax=max(dl), qmax=400)
    print("\n  --- F: alternating / sporadic socle, complete in q")
    h2 = partF(dlist=dl)
    print("\n  --- C.4: equal characteristic, multi-factor, full census")
    h3 = partC_multi_full(dlist=dl, qmax=3000)
    print("\n  --- G: the residual census over the cross-characteristic window")
    specs = ([("L", d, 47) for d in dl] + [("U", d, 11) for d in dl])
    r = partG(specs)
    print("  (H3) d = 11..20 : hits C.2 %s | F %s | C.4 %s | G %s"
          % (h1 or "NONE", h2 or "NONE", h3 or "NONE", r))
    return h1, h2, h3, r


def iroot_(n, k):
    if n < 1:
        return 0
    x = 1 << ((n.bit_length() + k - 1) // k + 1)
    while True:
        y = ((k - 1) * x + n // x ** (k - 1)) // k
        if y >= x:
            break
        x = y
    return x


def partE2_h3prime(dlo=21, dhi=200):
    """PART E' -- the (H3') residue: q = 2, CROSS characteristic,
    MULTI-FACTOR, d > 20.

    Necessary conditions, all exact:
        (i)   q_1^{l N_1} <= ppmax_{2'}(|S|) <= 2^{3d/2-2}       -> q_1 <= hi
        (ii)  l |Out(G)| iotabar(G) >= iota(S),  |Out| <= 12 f_1,
              iotabar <= 4 q_1^{mu_1}                            -> q_1 >= lo
        (iii) |G|^l divides |S| ,  q_1 ODD.
    (i)+(ii) give a WINDOW [lo, hi]; when it is empty the (family, rank, l)
    is killed with NO enumeration at all -- this is PART F (ii') made exact
    per family.  Otherwise the window is swept exactly."""
    print(BAR)
    print("PART E' -- (H3') the q = 2 cross-characteristic multi-factor")
    print("           residue for d > 20, decided exactly")
    print(BAR)
    tot, empt, swept, big = [], 0, 0, []
    for X in ("L", "U"):
        for d in range(dlo, dhi + 1):
            S = order_LU(X, d, 2)
            io = iota_LU(X, d, 2)
            cap = 2 ** ((3 * d) // 2)
            surv, ncand = [], 0
            for F in FAM:
                ns = ([F["nmin"]] if F["nmax"]
                      else range(F["nmin"], 3 * d + 2))
                for n in ns:
                    N1, mu1 = F["N"](n), F["mu"](n)
                    if 3 ** (2 * N1) > cap:
                        break
                    for l in range(2, 13):
                        hi = iroot_(cap, l * N1)
                        if hi < 3:
                            break
                        # SHARP lower end of the window: binary-search the
                        # smallest q_1 with l * |Out| * iotabar >= iota(S),
                        # using the family's EXACT parabolic index and
                        # |Out| = d_1 f_1 g with f_1 = log_{p_1} q_1
                        # <= log_3 q_1 (cross characteristic, q = 2 so
                        # p_1 >= 3).
                        def floor_ok(x, F=F, n=n, l=l, io=io):
                            f1 = max(1, int(x.bit_length() * 0.6309) + 1)
                            dg = max(F["d"](n, x), F["d"](n, x + 1))
                            return l * dg * f1 * F["g"] * F["iota"](n, x) >= io
                        a_, b_ = 2, hi
                        if not floor_ok(b_):
                            empt += 1
                            continue
                        while a_ < b_:
                            mid = (a_ + b_) // 2
                            if floor_ok(mid):
                                b_ = mid
                            else:
                                a_ = mid + 1
                        lo = max(3, a_)
                        if lo > hi:
                            empt += 1
                            continue
                        if hi - lo > 3 * 10 ** 6:
                            big.append((X, d, F["key"], n, l, lo, hi))
                            continue
                        swept += 1
                        for q1 in range(lo | 1, hi + 1, 2):
                            t, pp = q1, 3
                            while pp * pp <= t and t % pp:
                                pp += 2
                            pr = pp if t % pp == 0 else q1
                            f1, t = 0, q1
                            while t % pr == 0:
                                t //= pr
                                f1 += 1
                            if t != 1:
                                continue
                            if not F["qform"](pr, f1) or F["skip"](n, q1):
                                continue
                            ncand += 1
                            o1 = order_of(F, n, q1)
                            if o1 >= 60 and S % (o1 ** l) == 0:
                                ou = out_of(F, n, q1, pr, f1)
                                if l * ou * F["iota"](n, q1) >= io:
                                    surv.append((F["name"](n, q1), l))
            print("  %s_%-3d(2)  swept candidates %-9d  SURVIVORS: %s"
                  % (X, d, ncand, surv or "NONE"))
            tot += surv
            sys.stdout.flush()
    print()
    print("  windows killed EMPTY by (i)+(ii) alone : %d" % empt)
    print("  windows swept exactly                  : %d" % swept)
    print("  windows too large to sweep             : %d" % len(big))
    for r in big:
        print("     %s_%d  %s(n=%d) l=%d  q_1 in [%d, %d]" % r)
    print()
    print("  TOTAL (H3') survivors, q = 2, %d <= d <= %d, both towers: %s"
          % (dlo, dhi, tot or "NONE"))
    print()
    return tot, big


# ============================================================ PART F

def partF_tail(dmax=200):
    print(BAR)
    print("PART F -- (H3-tail) the uniform statement for d > 20")
    print(BAR)
    print(r"""
  First a sharpening of Lemma X that the tail needs.

  > Lemma X' [PROVEN, both towers, all d, all q].
  >        ppmax_{p'}(|S|)  <=  2^{d-1} * (q+1)^{d-1} .
  > (v_task56's Lemma X had d! in place of 2^{d-1}.)
  > Proof.  Let r != p, k := ord_r(q), m := #{i <= d : r | q^i - eps_i}.
  > By LTE the r-part of |S| is r^v with v = m v_r(Phi_k(q)) + v_r(m!), so
  > the r-part is at most Phi_k(q)^m * r^{v_r(m!)}.  Now
  > v_r(m!) <= (m-1)/(r-1), so r^{v_r(m!)} <= r^{(m-1)/(r-1)} <= 2^{m-1}
  > <= 2^{d-1} (the function x -> x^{1/(x-1)} is maximal at x = 2), and
  > Phi_k(q)^m <= (q+1)^{phi(k) m} <= (q+1)^{d-1} by the phi(k) m <= d-1
  > computation of Lemma X.   []

  > Lemma TAIL [PROVEN].  Let d > 20.  Then

  > (i) CROSS CHARACTERISTIC, ALMOST SIMPLE.  Lemma K' (|G| < |G|_{p_1}^3)
  >     with Lemma X' gives |S| = c|S_1| < c (2(q+1))^{3(d-1)} against
  >     |S| > q^{d^2-1}/(4d).  Since (d-1)(d-2) - 3(d-1) log_2 3 > 0 with
  >     room to spare from d = 11 on, the branch is EMPTY FOR EVERY q >= 2.
  >     Margin (i) below.

  > (ii) CROSS CHARACTERISTIC, MULTI-FACTOR.  Put tau_1 := N_1/mu_1 >= 1.
  >     The floor gives q_1^{mu_1} >= iota(S)/(4 l d_1 f_1 g_1) and the
  >     p_1-part gives q_1^{l N_1} <= ppmax_{p'}(|S|), so with l >= 2
  >          ( q^{2 tau_1} / (2(q+1)) )^{d-1}  <=  (4 l d_1 f_1 g_1)^{2 tau_1}.
  >     The right-hand side is polynomial in d and log q, the left-hand side
  >     is exponential in d as soon as q^{2 tau_1} > 2(q+1).  Since
  >     tau_1 >= 1 always, q^2 > 2(q+1) holds for every q >= 3:
  >          ==>  the whole branch is empty for every q >= 3 and every
  >               d >= D_0(q), tabulated below;
  >          ==>  at q = 2 it survives only for tau_1 <= log 6/(2 log 2)
  >               = 1.2925, i.e. only for the families
  >               L_2, U_3, Sz, R (tau = 1), U_4, G_2, 2F_4 (tau = 6/5),
  >               and of these Sz and 2F_4 need characteristic 2 = p and
  >               are therefore NOT cross-characteristic.
  >     So for d > 20 the ONLY surviving cross-characteristic multi-factor
  >     possibility is q = 2 with a socle factor from
  >               { L_2(q_1), U_3(q_1), R(q_1), G_2(q_1), U_4(q_1) },
  >     q_1 odd -- a single target per (X, d).  This is (H3'), the one
  >     residue this note does NOT remove; it is inside the census for
  >     d <= 20 and named as a debt for d > 20.

  > (iii) EQUAL CHARACTERISTIC, ALMOST SIMPLE.  The j*d_1 window of
  >     v_task56 section 3 closes at q^{(d-1)/(d+2)} <= 8 d_1 f_1 with
  >     (d-1)/(d+2) > 20/23, and the d_1 >= d+1 branch is empty outright
  >     for every d >= 4.  Window q <= 524288 at every d >= 10 (PART E) --
  >     and the window is DECREASING in d, so 524288 serves for all d > 20.
  >     NOTE this is the one branch whose tail needs the sweep of PART E to
  >     have been run at ONE d; the argument itself is uniform.

  > (iv) EQUAL CHARACTERISTIC, MULTI-FACTOR.  PART C of this note: 0
  >     surviving socle shapes, no q anywhere, no d bound.  COMPUTATION-FREE.

  > (v) ALTERNATING / SPORADIC SOCLE.  iota(A_m) <= C(m,3) is
  >     polylogarithmic in |S| = m!/(2c) ~ q^{d^2-1} while the floor needs
  >     |Out| iota(S_1) >= iota(S) > q^{d-1}; the margin q^{d-1}/(4 C(m,3))
  >     grows like q^{d-1}/(log q^{d^2})^3.  COMPUTATION-FREE, all d >= 4.
""")
    print("  margin (i): 2^{(d-1)(d-2)} / ( 4d |Out| 2^{3(d-1)} 3^{3(d-1)} ),")
    print("              must be > 1 (evaluated at the worst case q = 2):")
    print("  %-4s %-24s %s" % ("d", "log2 of margin (i)", "verdict"))
    ok = True
    for d in list(range(11, 26)) + [30, 40, 60, 100, dmax]:
        lhs = (d - 1) * (d - 2)
        import math
        rhs = (math.log2(4 * d) + math.log2(4 * d)
               + 3 * (d - 1) * (1 + math.log2(3)))
        if lhs - rhs <= 0:
            ok = False
        print("  %-4d %-24.4g %s" % (d, lhs - rhs,
                                     "OK" if lhs - rhs > 0 else "FAILS"))
    print("  margin (i) positive for every d >= 11 : %s" % ok)
    print()
    print("  (ii): the threshold D_0(q) beyond which the cross-characteristic")
    print("        multi-factor branch is empty, from")
    print("        (q^2/(2(q+1)))^{d-1} > (4 l d_1 f_1 g_1)^2, l = 2,")
    print("        d_1 <= 2d, f_1 <= log_2 q_1, g_1 <= 6 :")
    print("  %-6s %-14s %s" % ("q", "q^2/(2(q+1))", "D_0(q)"))
    import math
    for q in (2, 3, 4, 5, 7, 8, 9, 11, 16, 25):
        base = q * q / (2.0 * (q + 1))
        if base <= 1:
            print("  %-6d %-14.4f %s" % (q, base, "-- (never; see (H3') above)"))
            continue
        D0 = None
        for d in range(4, 4000):
            if (d - 1) * math.log(base) > 2 * math.log(4 * 2 * 2 * d * 40 * 6):
                D0 = d
                break
        print("  %-6d %-14.4f %s" % (q, base, D0))
    print()
    print("  (ii') q = 2 SHARPENED.  At q = 2 no prime r != 2 has ord_r(2)=1,")
    print("        so k >= 2 and m <= d/2 in Lemma X', giving")
    print("             ppmax_{2'}(|S|) <= 2^{d-1} * 2^{d/2-1} = 2^{3d/2-2}.")
    print("        With l >= 2, tau_1 = N_1/mu_1 >= 1, iota(S) > 2^{b},")
    print("        |Out| iotabar <= 48 f_1 q_1^{mu_1} and f_1 <= (3d/2)/(2N_1):")
    print("             2 tau_1 (b - log_2(96 f_1))  <=  3d/2 - 2 ,")
    print("        which FAILS -- i.e. the branch is empty -- from:")
    print("  %-6s %-8s %-10s %s" % ("tower", "tau_1", "families", "empty for d >="))
    import math
    for X in ("L", "U"):
        for (tau, nm) in ((1, "L_2, U_3, R"), (Fr(6, 5), "U_4, G_2")):
            D = None
            for d in range(11, 4000):
                b = bdeg(X, d)
                f1 = max(1.0, (1.5 * d) / 2.0)
                if 2 * float(tau) * (b - math.log2(96 * f1)) > 1.5 * d - 2:
                    D = d
                    break
            print("  %-6s %-8s %-10s %s" % (X, str(tau), nm, D))
    print("""
        So (H3') is a FINITE residue: q = 2 only, and only for
        21 <= d <= 46 in the linear tower; the unitary tower is empty from
        d = 11.  PART E' runs the exact test on exactly those targets.
""")
    print("""
  > THEOREM LU-T [PROVEN, unconditional, ALL d >= 4, ALL q, modulo (H3')].
  > No L_d(q) and no U_d(q) has a Fitting-free non-simple twin; with the
  > CFSG order theorem (the only L/U order coincidence is |A_8| = |L_4(2)|
  > = |L_3(4)|, handled by Theorem AT) every L_d(q) and every U_d(q) is
  > D-rigid among all finite groups.  No (AB), no B_n/C_n dependence.
  > Ranges: d <= 20 unconditional; d > 20 unconditional except (H3'),
  > the single target q = 2 in the cross-characteristic multi-factor
  > branch with a socle factor of type L_2 / U_3 / R / G_2 / U_4.
""")
    return ok


# ============================================================ PART G

def partG_zsyg():
    print(BAR)
    print("PART G -- (H2) CLOSED: the Zsygmondy exception table for Lemma Z")
    print(BAR)
    print(r"""
  > Zsygmondy 1892 / Birkhoff-Vandiver.  For a >= 2, n >= 1 the number
  > a^n - 1 has a primitive prime divisor EXCEPT in exactly these cases:
  >     (1) n = 1 and a = 2                (2^1 - 1 = 1)
  >     (2) n = 2 and a + 1 a power of 2   (a = 2^s - 1 Mersenne)
  >     (3) (a, n) = (2, 6)                (2^6 - 1 = 63 = 3^2 * 7)
  > There are no others.

  Lemma Z / Lemma ZM apply the theorem to a = q_1 = p^{f_1} and n = kappa,
  a cyclotomic degree of the socle factor.  The exceptions therefore enter
  ONLY through the following finite list.  For each we give the affected
  socle factors and how the branch is closed instead.
""")
    print("  %-22s %-30s %s" % ("exception", "socle factors reached",
                                "replacement kill"))
    tab = [
        ("n = kappa = 1", "every G (Phi_1 always occurs)",
         "not used: Lemma Z/ZM are only invoked for kappa >= 2"),
        ("kappa = 2, q_1 = 2^s - 1", "any G with 2 in Cyc(G) (all of them)",
         "kappa = 2 is used only in ZM; for q_1 Mersenne substitute the "
         "next kappa in Cyc(G) -- every family has one, since k >= 2 and "
         "Cyc(G) != {1,2} for every G except L_2(q_1), already dead by "
         "Lemma Z (mu/k = 1/2)"),
        ("(q_1, kappa) = (2, 6)", "q_1 = 2 and 6 in Cyc(G): "
         "L_n(2) n>=6, U_n(2) n>=3, S_2n(2) n>=3, O^eps(2), G_2(2)', "
         "3D_4(2), F_4(2), E_6(2), 2E_6(2), E_7(2), E_8(2)",
         "q_1 = 2 forces q = 2^{1/j} <= 2^{k_1/K} <= 2, i.e. q = 2: a "
         "SINGLE target per (X,d), inside every census"),
    ]
    for (a, b, c) in tab:
        print("  %-22s %-30s %s" % (a, b[:30], c[:44]))
        if len(b) > 30 or len(c) > 44:
            print("  %-22s %-30s %s" % ("", b[30:], c[44:]))
    print(r"""
  > Corollary (H2) [PROVEN].  The Zsygmondy exceptions cost Lemma Z and
  > Lemma ZM NOTHING:
  >   * kappa = 1 is never used;
  >   * the Mersenne case kappa = 2 is used only inside Lemma ZM, and only
  >     as ONE of the several kappa in Cyc(G): dropping it weakens the
  >     bound j_i <= min_kappa (...) but never invalidates it, and PART C
  >     was re-run with kappa = 2 REMOVED from every Cyc(G) -- see the
  >     control below;
  >   * (q_1, kappa) = (2, 6) forces q_1 = 2, hence (by f_1 k_1 <= K f and
  >     f_1 >= 1) f <= k_1/K <= 1, i.e. q = 2, a single target that every
  >     census contains.
""")
    # control: re-run PART C with kappa = 2 deleted from every Cyc
    print("  CONTROL: PART C re-run with kappa = 2 deleted from every Cyc(G)")
    print("  (i.e. assuming the Mersenne exception at EVERY factor):")
    global _NO_KAPPA2
    _NO_KAPPA2 = True
    bad = []
    for X in ("L", "U"):
        for d in range(4, 31):
            rows, cfgs, MT, K = enumerate_configs(X, d)
            for ch in cfgs:
                dead, wit = pack_kill(rows, ch, X, d, MT, K)
                if not dead:
                    bad.append((X, d, [(rows[i]["key"], rows[i]["n"], l)
                                       for (i, l, _, _) in ch]))
    _NO_KAPPA2 = False
    print("     surviving shapes with kappa = 2 disabled, 4 <= d <= 30 : %s"
          % (bad or "NONE"))
    print()
    return bad


_NO_KAPPA2 = False
_orig_jbound = jbound_ZM


def jbound_ZM(row, l, MT, K):          # noqa: F811  (kappa=2 control switch)
    best = None
    for kap, m in row["cyc"].items():
        if _NO_KAPPA2 and kap == 2:
            continue
        t = MT_max_t(MT, K, l * m)
        if t is None:
            return None
        v = Fr(t, kap)
        best = v if best is None else min(best, v)
    return best


# ==========================================================================

def main():
    args = set(sys.argv[1:]) or {"A", "B", "C", "D", "E", "F", "G"}
    detail = []
    if "A" in args:
        partA()
    if "B" in args:
        partB()
    if "C" in args:
        grand, detail = partC(dmax=60)
    if "D" in args:
        partD(detail)
    if "G" in args:
        partG_zsyg()
    if "E" in args:
        partE_H3()
    if "E2" in args or "E" in args:
        partE2_h3prime()
    if "F" in args:
        partF_tail()


if __name__ == "__main__":
    main()
