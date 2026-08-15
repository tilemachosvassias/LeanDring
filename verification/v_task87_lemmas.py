#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
v_task87_lemmas.py -- the q-free closure of the ONE residual left by the
block-2 audit (v_task82 section 6): the EQUAL-characteristic MULTI-FACTOR
branch for L_d(q) / U_d(q) targets at d >= 33 and small q, where PART C of
v_task60 enumerates with a floor that has the (Z2) log-slack dropped and a
Lemma-ZM bound that has the v_r(d!) term dropped.

The closure replaces the enumeration ENTIRELY.  It uses

    (P=)  sum_i l_i j_i N_i = N              [Lemma EQ-EX / Lemma DEG]
    (R=)  sum_i l_i j_i n_i = d - 1          [Lemma DEG]
    (Z)   j_i k_i <= K                       [Lemma Z, v_task56]
    (TOP) some factor has j_1 k_1 = K exactly, with l_1 = 1
                                             [Corollary PACK-TOP, v_task60]
    (COX) 2 N_i = h_i n_i   (h_i = Coxeter number of the AMBIENT diagram)
                                             [NEW, this file, PART 1]

and NO orbit floor, NO census, NO q.

PARTS
  1  Lemma COX verified for all 17 families and all ranks <= RMAX,
     together with the derived per-family invariants h, k, n_r, tau = n_r/k,
     rho = N/k, and the four structural facts the proof consumes.
  2  M_K = 1 in both towers for every d (the hypothesis of PACK-TOP).
  3  The proof of Theorem MF, step by step, re-checked as an exhaustive
     numeric case distinction over families/ranks for every d in a range:
       L : "h_i <= d for all i"  ==>  all h_i = d  ==>  rank sum >= d
       U : |P| <= 1 ; owner != i_0 ; tau(owner) < 1/4 ==> owner in {R, 2F4};
           and the two closing inequalities.
  4  The finite residue at 4 <= d <= 30 (inside the censuses): the explicit
     list of shapes that the d >= 31 argument does not kill.
  5  Robustness: how much slack in (P=) / (R=) the proof tolerates.

Usage:  python3 v_task87_lemmas.py [dmax]        (default dmax = 2000)
"""

import sys
from fractions import Fraction as Fr

sys.path.insert(0, ".")
sys.path.insert(0, __file__.rsplit("/", 1)[0])

from v_task52_lemmaC import FAM
from v_task56_lu_twins import KFAM, bdeg, Kmax
from v_task60_lu_residues import famrows, target_cyc, phi

BAR = "=" * 76

# --------------------------------------------------------------- Lemma COX
# Coxeter number h of the AMBIENT (untwisted) root system of each family.
# For the twisted families 2A, 2D, 3D4, 2E6 the invariants (N, D) in FAM are
# the ambient ones, so h is the ambient Coxeter number.  For 2B2, 2G2, 2F4
# FAM carries the TWISTED (N, D) but 2N/n_r still equals the ambient h.
COX = {
    "A1":  lambda n: 2,
    "A":   lambda n: n,          # A_{n-1} = L_n(q)
    "2A":  lambda n: n,          # ^2A_{n-1} = U_n(q)
    "C":   lambda n: 2 * n,
    "B":   lambda n: 2 * n,
    "D":   lambda n: 2 * n - 2,
    "2D":  lambda n: 2 * n - 2,
    "G2":  lambda n: 6,
    "3D4": lambda n: 6,
    "F4":  lambda n: 12,
    "E6":  lambda n: 12,
    "2E6": lambda n: 12,
    "E7":  lambda n: 18,
    "E8":  lambda n: 30,
    "2B2": lambda n: 4,
    "2G2": lambda n: 6,
    "2F4": lambda n: 12,
}

CLASSICAL = ("A1", "A", "2A", "C", "B", "D", "2D")
UNBOUNDED = ("A", "2A", "C", "B", "D", "2D")


def rows(rankmax):
    """famrows + h, tau, rho  (uses v_task60's famrows, which recomputes the
    full cyclotomic vector -- O(rank^2) per row, so only for small rankmax)"""
    out = []
    for r in famrows(rankmax):
        h = COX[r["key"]](r["n"])
        r = dict(r)
        r["h"] = h
        r["tau"] = Fr(r["rk"], r["k"])
        r["rho"] = Fr(r["N"], r["k"])
        out.append(r)
    return out


def rows_light(rankmax):
    """same rows, from the closed-form (N, D, mu) of FAM and KFAM only --
    no cyclotomic vector, so linear in rankmax.  Cross-checked against
    rows() on the overlap in PART 1."""
    out = []
    for F in FAM:
        ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], rankmax + 1)
        for n in ns:
            N, D = F["N"](n), F["D"](n)
            k = KFAM[F["key"]](n)
            h = COX[F["key"]](n)
            out.append(dict(key=F["key"], n=n, N=N, D=D, mu=F["mu"](n), k=k,
                            rk=D - 2 * N, h=h, tau=Fr(D - 2 * N, k),
                            rho=Fr(N, k), F=F))
    return out


# ============================================================ PART 1

def part1(RMAX=400):
    print(BAR)
    print("PART 1 -- Lemma COX and the per-family invariants")
    print(BAR)
    print(r"""
  > Lemma COX [PROVEN].  Let G be a finite simple group of Lie type with
  > N = deg_{q_1}|G|_p, D = deg_{q_1}|G|, n_r := D - 2N, and let h be the
  > Coxeter number of the AMBIENT (untwisted) root system.  Then
  >
  >         2 N  =  h * n_r ,      i.e.   sigma := N/n_r = h/2 ,
  >
  > and  h <= k <= 2h,  where k := max Cyc(G) is the Lemma-Z invariant.
  >
  > Proof.  N = |Phi^+| = |Phi|/2 and |Phi| = (rank)*h for every root system,
  > while D - 2N = rank for the untwisted families and for 2A, 2D, 2E6, 3D4
  > (whose order polynomials carry the untwisted degrees; cf. v_task82 F7).
  > For 2B2, 2G2, 2F4 the pair (N, n_r) is (2,1), (3,1), (12,2) against the
  > ambient (4,2), (6,2), (24,4) -- both halved, so the ratio is unchanged.
  > h <= k because h is the largest degree of the Weyl group and every degree
  > occurs in the order polynomial; k > h exactly for the families whose
  > Frobenius twist doubles a factor (2A, 2D, 3D4, 2E6).   []

  The four facts the proof of Theorem MF consumes:
    (C1)  2 N_i = h_i n_i                      (Lemma COX)
    (C2)  h_i <= k_i                           (Lemma COX)
    (C3)  h_i = k_i  <==>  family is untwisted or in {2B2, 2G2, 2F4}
    (C4)  n_i >= h_i/2  for every CLASSICAL family
          (equivalently: h_i > 30 forces S_i classical, hence n_i >= h_i/2)
    (C5)  tau_i := n_i/k_i < 1/4  <==>  family in {2G2, 2F4}   (tau = 1/6);
          the runner-up is 2B2 with tau = 1/4 exactly.
""")
    R = rows(RMAX)
    bad = [r for r in R if 2 * r["N"] != r["h"] * r["rk"]]
    print("  (C1) 2N = h*n_r : %d family/rank rows checked, %d violations"
          % (len(R), len(bad)))
    assert not bad, bad[:3]
    bad = [r for r in R if not (r["h"] <= r["k"] <= 2 * r["h"])]
    print("  (C2) h <= k <= 2h : %d violations" % len(bad))
    assert not bad, bad[:3]
    eqhk = sorted(set(r["key"] for r in R if r["h"] == r["k"]))
    nehk = sorted(set(r["key"] for r in R if r["h"] != r["k"]))
    print("  (C3) h = k for : %s" % eqhk)
    print("       h < k for : %s" % nehk)
    bad = [r for r in R if r["key"] in CLASSICAL and 2 * r["rk"] < r["h"]]
    print("  (C4) n_r >= h/2 on classical rows : %d violations" % len(bad))
    assert not bad, bad[:3]
    hi = sorted(set(r["key"] for r in R if r["h"] > 30))
    print("       families reaching h > 30      : %s" % hi)
    assert set(hi) <= set(CLASSICAL), hi
    small = sorted(set((r["key"], str(r["tau"])) for r in R
                       if r["tau"] < Fr(1, 4)))
    quart = sorted(set(r["key"] for r in R if r["tau"] == Fr(1, 4)))
    print("  (C5) tau < 1/4 for : %s" % small)
    print("       tau = 1/4 for : %s" % quart)
    L = {(r["key"], r["n"]): r for r in rows_light(RMAX)}
    mism = [kk for kk, r in ((( r["key"], r["n"]), r) for r in R)
            if (L[kk]["N"], L[kk]["D"], L[kk]["k"], L[kk]["rk"], L[kk]["h"])
            != (r["N"], r["D"], r["k"], r["rk"], r["h"])]
    print("  rows_light() vs famrows() on %d rows : %d mismatches"
          % (len(R), len(mism)))
    assert not mism, mism[:3]
    print()
    print("  %-5s %-6s %6s %6s %5s %5s %6s %8s %8s"
          % ("fam", "rank", "N", "D", "n_r", "h", "k", "tau=n/k", "rho=N/k"))
    seen = set()
    for r in R:
        tag = r["key"]
        if tag in UNBOUNDED:
            if r["n"] > 6:
                continue
        elif tag in seen:
            continue
        seen.add(tag)
        print("  %-5s %-6d %6d %6d %5d %5d %6d %8s %8s"
              % (r["key"], r["n"], r["N"], r["D"], r["rk"], r["h"], r["k"],
                 str(r["tau"]), str(r["rho"])))
    print()
    print("  ASYMPTOTIC forms (used verbatim in PART 3):")
    print("    A_{n-1}=L_n : h=n,    n_r=n-1,  k=n         tau=(n-1)/n")
    print("    2A_{n-1}=U_n: h=n,    n_r=n-1,  k=2n (n odd) / 2n-2 (n even)")
    print("    C_n,B_n     : h=2n,   n_r=n,    k=2n        tau=1/2")
    print("    D_n         : h=2n-2, n_r=n,    k=2n-2      tau=n/(2n-2)")
    print("    2D_n        : h=2n-2, n_r=n,    k=2n        tau=1/2")
    print()
    return R


# ============================================================ PART 2

def part2(dmax=400):
    print(BAR)
    print("PART 2 -- M_K = 1 in both towers (the hypothesis of PACK-TOP)")
    print(BAR)
    bad = []
    for X in ("L", "U"):
        for d in range(4, dmax + 1):
            MT = target_cyc(X, d)
            K = Kmax(X, d)
            if MT.get(K, 0) != 1:
                bad.append((X, d, K, MT.get(K, 0)))
            if max(MT) != K:
                bad.append((X, d, "maxCyc", max(MT), K))
    print("  4 <= d <= %d, both towers : max Cyc(S) = K and M_K = 1" % dmax)
    print("  violations : %s" % (bad[:5] if bad else "NONE"))
    assert not bad
    print("""
  Consequence (PACK-TOP, v_task60 section 1.3).  Exactly one socle factor
  covers Phi_K; it has l_1 = 1 and covering multiplicity 1, and
        j_1 k_1 = K   EXACTLY
  (>= from covering, <= from Lemma Z).  For d >= 33, K = d resp. 2d / 2d-2
  is >= 33 > 6, so Zsygmondy's exceptions ((a,n)=(2,6); n=2; n=1) never
  apply at kappa = K: the primitive prime of q^K - 1 always exists.
""")
    return True


# ============================================================ PART 3

def owner_candidates(X, d, R):
    """all (row, j) with j*k = K and j >= 1 -- the possible Phi_K owners."""
    K = Kmax(X, d)
    out = []
    for r in R:
        if K % r["k"] and Fr(K, r["k"]) < 1:
            pass
        j = Fr(K, r["k"])
        if j < 1:
            continue
        out.append((r, j))
    return out


def part3(dlo=31, dhi=2000, RMAX=None):
    print(BAR)
    print("PART 3 -- Theorem MF, the proof re-checked as an exhaustive")
    print("          numeric case distinction, %d <= d <= %d" % (dlo, dhi))
    print(BAR)
    print(r"""
  THEOREM MF.  Let d >= 31 and S = L_d(q) or U_d(q), q = p^f.  Let T be
  Fitting-free with |T| = |S| and D(T) = D(S), Soc T = prod_i S_i^{l_i} with
  L := sum_i l_i >= 2 and every S_i of Lie type in characteristic p.  Assume
     (DEG-exact)  (P=) and (R=) hold with vanishing c-correction, and
     (POS)        j_i = f_i/f >= 1 for every i  (i.e. q_i >= q; automatic
                  when f = 1, i.e. whenever q is PRIME).
  Then no such T exists.  No q, no census, no orbit floor enters.

  Write v_i := l_i j_i n_i > 0.  (P=) and (C1) give sum_i v_i h_i = 2N =
  d(d-1); (R=) gives sum_i v_i = d-1.  So the v-weighted mean of the
  Coxeter numbers of the socle factors is EXACTLY the Coxeter number d of
  the target.  (Z) + (C2) give h_i <= k_i <= K/j_i <= K.  (POS) gives
  v_i >= l_i n_i >= n_i.
""")
    R = rows_light(RMAX or 2 * dhi + 4)

    # ---- LINEAR
    print("  ------ LINEAR TOWER (K = d) ------")
    print("""  Step L1.  h_i <= K/j_i = d/j_i <= d for every i.  Hence every term of
    sum_i v_i (d - h_i) = d*sum v_i - sum v_i h_i = d(d-1) - d(d-1) = 0
  is >= 0, so h_i = d for EVERY i, and then d = h_i <= k_i <= d/j_i forces
  j_i = 1 and k_i = d = h_i.
  Step L2.  So every factor lies in a family with h = k = d.  Enumerate:""")
    bad = []
    for d in range(dlo, dhi + 1):
        cand = [r for r in R if r["h"] == d and r["k"] == d]
        if not cand:
            bad.append((d, "no family with h=k=d"))
            continue
        mn = min(r["rk"] for r in cand)
        # L >= 2 forces sum_i l_i n_i >= 2*mn ; need > d-1 for the kill
        if 2 * mn <= d - 1:
            bad.append((d, "min rank %d too small" % mn,
                        [(r["key"], r["n"]) for r in cand]))
    print("    d in [%d,%d] : rows with h=k=d always have n_r >= d/2," % (dlo, dhi))
    print("    so L >= 2 gives sum_i l_i n_i >= d > d-1.  Failures : %s"
          % (bad[:5] if bad else "NONE"))
    assert not bad, bad[:5]
    for d in (31, 32, 33, 34, 60, 61, 100, 1000):
        if not (dlo <= d <= dhi):
            continue
        cand = [(r["key"], r["n"], r["rk"]) for r in R
                if r["h"] == d and r["k"] == d]
        print("      d = %-5d families with h = k = d : %s" % (d, cand))
    print("    LINEAR TOWER: EMPTY for every %d <= d <= %d.\n" % (dlo, dhi))

    # ---- UNITARY
    print("  ------ UNITARY TOWER (K = 2d for d odd, 2d-2 for d even) ------")
    print("""  Step U1.  P := {i : h_i > d}.  For i in P, h_i > d >= 31 > 30 = h(E8),
    so S_i is classical and (C4) gives n_i >= h_i/2 > d/2, hence
    v_i >= n_i > d/2.  Two such factors would give sum v_i > d > d-1, so
    |P| <= 1.
  Step U2.  If P is empty then sum_i v_i(d - h_i) = 0 with all terms >= 0,
    so h_i = d for every i; every family with h = d has n_r >= d/2 (checked
    below), so L >= 2 gives sum v_i >= d > d-1.  Contradiction.
  Step U3.  So |P| = 1, say P = {i0}.  The Phi_K owner is NOT i0: the owner
    has j_1 = K/k_1 >= 1 (POS), so rho_1 = N_1/k_1 = j_1 N_1 / K <= N/K by
    (P=), and every family whose rho meets that bound has h <= d (checked
    below).
  Step U4.  Hence v_1 + v_i0 <= d-1 with v_i0 > d/2, so v_1 < d/2 - 1, and
    v_1 = j_1 n_1 = K * tau_1 gives tau_1 < (d/2-1)/K < 1/4.  By (C5) the
    owner is 2G2 = R (tau = 1/6) or 2F4 (tau = 1/6).
  Step U5.  For those two owners the mean identity
        v_i0 (h_i0 - d) = sum_{i != i0} v_i (d - h_i) >= v_1 (d - h_1)
    together with v_i0 <= d-1-v_1 and h_i0 <= 2 n_i0 <= 2 v_i0 is
    numerically impossible.  Checked below for every d.""")
    fails = []
    for d in range(dlo, dhi + 1):
        K = Kmax("U", d)
        N = d * (d - 1) // 2
        # --- U2 : families with h = d, their minimal rank
        cand = [r for r in R if r["h"] == d]
        if not cand:
            fails.append((d, "U2", "no family with h=d"))
        else:
            mn = min(r["rk"] for r in cand)
            if 2 * mn <= d - 1:
                fails.append((d, "U2", "min rank %d" % mn))
        # --- U3 : no possible owner (j = K/k >= 1, rho <= N/K) has h > d
        bad_owner = [r for r in R
                     if r["k"] <= K and Fr(r["N"], r["k"]) <= Fr(N, K)
                     and r["h"] > d]
        if bad_owner:
            fails.append((d, "U3", [(r["key"], r["n"]) for r in bad_owner[:3]]))
        # --- U4 : the owners with tau < (d/2-1)/K
        thr = Fr(d - 2, 2 * K)
        owners = [r for r in R
                  if r["k"] <= K and Fr(r["N"], r["k"]) <= Fr(N, K)
                  and r["tau"] < thr]
        keys = sorted(set(r["key"] for r in owners))
        if not set(keys) <= {"2G2", "2F4"}:
            fails.append((d, "U4", keys))
        # --- U5 : the closing inequality for each surviving owner
        for r in owners:
            j1 = Fr(K, r["k"])
            if j1 < 1:
                continue
            # 2F4 needs 6 | K/2 ... we do NOT use any such parity argument
            v1 = j1 * r["rk"]
            h1 = r["h"]
            if v1 >= Fr(d, 2) - 1:          # already excluded by U4's bound
                continue
            vmax = Fr(d - 1) - v1           # upper bound for v_i0
            hmax = 2 * vmax                 # h_i0 <= 2 n_i0 <= 2 v_i0
            lhs = vmax * (hmax - d)         # >= v_i0 (h_i0 - d)
            rhs = v1 * (d - h1)             # <= sum_{i!=i0} v_i (d - h_i)
            if lhs >= rhs:
                fails.append((d, "U5", r["key"], str(lhs), str(rhs)))
    print("    %d <= d <= %d : failures %s" % (dlo, dhi, fails[:6] or "NONE"))
    assert not fails, fails[:6]
    print("    UNITARY TOWER: EMPTY for every %d <= d <= %d.\n" % (dlo, dhi))
    print("  THEOREM MF verified as a case distinction for every d in the")
    print("  range; the case distinction itself is finite and d-uniform, so")
    print("  the range is only a re-check of the closed-form steps.")
    print()

    # closed-form margins of U5 for the two owners
    print("  Closed form of Step U5 (the only step with a d-dependence):")
    print("""    owner R = 2G2 : k=6, n_r=1, h=6, j_1 = K/6, v_1 = K/6
        v_i0 <= (d-1) - K/6 ,  h_i0 - d <= 2 v_i0 - d
        need  (d-1-K/6)(2(d-1-K/6) - d)  <  (K/6)(d-6)
      K = 2d   : (d-1-d/3)(2(d-1-d/3)-d) = ((2d-3)/3)((d-6)/3)
                 vs (d/3)(d-6)  ->  2d-3 < 3d  <=>  d > -3   ALWAYS
      K = 2d-2 : ((2d-2)/3)... -> 2(d-4) < 3(d-6)  <=>  d > 10
    owner 2F4     : k=12, n_r=2, h=12, j_1 = K/12, v_1 = K/6
      K = 2d   : (2d-3)(d-6) < 3d(d-12)   <=>  d > 21.8
      K = 2d-2 : 2(d-1)(d-4) < 3(d-1)(d-12) ... <=> d > 28
    so d >= 31 is safe with margin in every branch.""")
    print()
    return True


# ============================================================ PART 4

def part4(dlo=4, dhi=30):
    print(BAR)
    print("PART 4 -- what the same argument leaves at 4 <= d <= 30")
    print(BAR)
    print("""  (These d are covered unconditionally by the exact censuses:
  v_task56/60 for d <= 20, v_task82's gap-fills for 21 <= d <= 32.  Listed
  only to show where the d >= 31 hypothesis is used.)""")
    R = rows_light(200)
    print("  %-3s %-3s  %s" % ("X", "d", "families the argument does not kill"))
    for X in ("L", "U"):
        for d in range(dlo, dhi + 1):
            K = Kmax(X, d)
            N = d * (d - 1) // 2
            if X == "L":
                cand = [(r["key"], r["n"], r["rk"]) for r in R
                        if r["h"] == d and r["k"] == d and 2 * r["rk"] <= d - 1]
            else:
                cand = [(r["key"], r["n"]) for r in R
                        if r["k"] <= K and Fr(r["N"], r["k"]) <= Fr(N, K)
                        and r["h"] > d]
            if cand:
                print("  %-3s %-3d  %s" % (X, d, cand))
    print()


# ============================================================ PART 5

def part5():
    print(BAR)
    print("PART 5 -- robustness: how much slack in (P=) / (R=) survives")
    print(BAR)
    print(r"""
  The c-corrections are, exactly,
      (P=)   sum_i l_i j_i N_i = N - eps_P ,    eps_P := v_p(c)/f  >= 0
      (R=)   sum_i l_i j_i n_i = (d-1) + theta ,
             theta = log_q( c_p * prod_i d_i^{l_i} / (e * c_{p'}) ) .
  v_task60's PART C sets eps_P = theta = 0 (its pack_kill uses N and d-1 as
  exact right-hand sides); Theorem MF above makes the SAME assumption, so it
  is strictly stronger than PART C -- it removes the floor, the enumeration
  and the d <= 60 cut-off, but it inherits (DEG-exact).  Below: exactly how
  much slack each step tolerates.

  LINEAR TOWER, theta = 0, eps_P >= 0 arbitrary.
      sum_i v_i (d - h_i) = 2 eps_P ,   all terms >= 0.
    * factors with h_i = d still force j_i = 1, k_i = d, n_i in
      {d-1, d/2, d/2+1}, so AT MOST ONE of them occurs (two give
      sum v_i >= d > d-1);
    * if that one is L_d (n = d-1) the remaining factors carry
      sum v_i = 0, i.e. there are none -- CONTRADICTION FOR EVERY eps_P.
      (This is the generic case: for d odd, L_d is the ONLY family with
      h = k = d, so the linear tower at ODD d is closed with no hypothesis
      on eps_P at all.)
    * for d even the leak needs 2 eps_P * L >= d/2 - 2, i.e.
      v_p(c) >= f(d-4)/(4L): a large p-part of the outer group.
  UNITARY TOWER: Step U1 uses only sum v_i = d-1 (+theta) and Step U5 has
  the margins printed in PART 3; both tolerate |theta| < 1 and eps_P < 1
  comfortably at d >= 33 (the U5 margins are Theta(d^2) against Theta(d)).

  So the honest statement is: Theorem MF is unconditional given (DEG-exact),
  which is the standing hypothesis of the whole PART-C machinery.  Making
  eps_P / theta rigorous is a SEPARATE, previously unnamed debt -- recorded
  as (H6) in the write-up.
""")
    # the odd-d linear claim, checked
    R = rows_light(1200)
    bad = []
    for d in range(5, 1200, 2):
        cand = sorted(set(r["key"] for r in R if r["h"] == d and r["k"] == d))
        if cand != ["A"]:
            bad.append((d, cand))
    print("  CHECK: for every ODD d in [5,1199] the only family with h = k = d")
    print("         is A (= L_d).  Exceptions: %s" % (bad[:5] or "NONE"))
    assert not bad
    print()


def main():
    dhi = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    print("v_task87_lemmas.py -- q-free closure of the d >= 33 residual")
    print("dmax = %d\n" % dhi)
    part1()
    part2(dmax=min(dhi, 400))
    part3(dlo=31, dhi=dhi)
    part4()
    part5()
    print(BAR)
    print("ALL CHECKS PASS.")
    print(BAR)


if __name__ == "__main__":
    main()
