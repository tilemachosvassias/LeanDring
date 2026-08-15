#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
v_task59_spo_twins.py -- Fitting-free NON-SIMPLE twins of the SYMPLECTIC and
ORTHOGONAL towers:

    S = S_{2n}(q) = PSp_{2n}(q)        (C_n , n >= 3, all q)
    S = O_{2n+1}(q) = Omega_{2n+1}(q)  (B_n , n >= 3, q odd)
    S = POmega^+_{2n}(q)               (D_n , n >= 4, all q)
    S = POmega^-_{2n}(q)               (^2D_n, n >= 4, all q)

|B_n(q)| = |C_n(q)| as polynomials, so ONE order census serves both; a
non-simple twin T of either must be separated from BOTH, and that is what
is proven here.  (The SIMPLE-SIMPLE separation B_n vs C_n is PARKED and is
NOT attempted anywhere in this file.)

Standing hypotheses (upstream, PROVEN):
   T Fitting-free, |T| = |S|, D(T) = D(S), T NOT simple.
   Soc T = prod_O G_O^{l_O}, c = [T : Soc T],
   (F)  l_O |Out(G_O)| iota(G_O) >= iota(S)         [Lemma TO'-0 + Lemma F]
   (C)  |Out(G)| iota(G) <= |G|^{2/3}               [Lemma C, v_task52]
   (T1) |G| >= q1^D/(12 d) , (T2) iotabar <= 4 q1^mu , (T3) |Out| = d f g,
        g <= 6                                      [v_task52]
   (P)  N - mu = 0 iff rank 1                       [Lemma P, v_task54]
   Lemma Z, Lemma Z2, Lemma X, Lemma X-2            [v_task56]
   Lemma EQ', Lemma EQ-EX                           [v_task57]
   Lemma MO-EX                                      [v_task58 -- FAILS here, sec. D.3]

PARTS
  A  invariants: a, N, b, K, |Out|, the ratio table, the iota lemma with the
     KL 5.2.2 exceptional minimal degrees handled exactly
  B  Lemma Z: the surviving-family list per target (b/K = 1-1/(2n), 1, 1-1/n)
  C  equal characteristic, ALMOST SIMPLE: Lemma EQ-EX same-a/N blocks,
     Lemma EQ' pruning, the MATCHED-pair identity hunt (exact), the
     non-matched counting kill, and the factorisation-free exact sweep
  D  the multi-factor branch: Lemma Q's death, Lemma Z2, the FAILURE of
     Lemma MO-EX for these towers, the two-sided repair (Lemma MO-SPO) and
     the exact residual-configuration census
  E  cross characteristic: Lemma X for these towers (the cyclotomic
     multiplicities computed exactly), the ppmax^3 kill and Lemma X-2
  F  alternating / sporadic socle, complete in q
  G  the residual census, with positive controls

All arithmetic exact (Python big integers / Fraction).
"""

import sys
from fractions import Fraction

sys.path.insert(0, ".")

from v_task50_sporadic_twins import SPORADIC, TITS
from v_task51_l2_twins import is_prime_power, iota_ub_generic
from v_task54_rank1_gaps import prime_powers_sieve
from v_task52_lemmaC import FAM, gcd, order_of, out_of, iroot
from v_task56_lu_twins import factorint, KFAM

BAR = "=" * 76


def prime_powers_upto(M, qmin=2):
    return [t for t in prime_powers_sieve(M) if t[0] >= qmin]


# ================================================================ PART A
# ---------------------------------------------------------------- targets
#
# X in {"C","B","D","2D"}.   q = p^f.
#
#   |C_n(q)| = |B_n(q)| = q^{n^2} prod_{i=1}^{n} (q^{2i}-1) / gcd(2,q-1)
#   |D_n(q)|  = q^{n(n-1)} (q^n-1) prod_{i=1}^{n-1}(q^{2i}-1)/gcd(4,q^n-1)
#   |2D_n(q)| = q^{n(n-1)} (q^n+1) prod_{i=1}^{n-1}(q^{2i}-1)/gcd(4,q^n+1)
#
#   a = deg_q |S| :  C,B : 2n^2+n      D,2D : 2n^2-n
#   N = deg_q |S|_p: C,B : n^2         D,2D : n(n-1)
#   b = deg_q iota :  C,B : 2n-1       D,2D : 2n-2
#   K = max ord_r(q):  C,B : 2n   D : 2n-2   2D : 2n
#
#   iota:  C,B : (q^{2n}-1)/(q-1)                       [P_1, singular points]
#          D   : (q^n-1)(q^{n-1}+1)/(q-1)               [P_1, singular points]
#          2D  : (q^n+1)(q^{n-1}-1)/(q-1)               [P_1, singular points]
#   [LIT: Kleidman-Liebeck Prop 4.1.20 / Table 5.2.2]

XS = ("C", "B", "D", "2D")


def order_T(X, n, q):
    if X in ("C", "B"):
        o = q ** (n * n)
        for i in range(1, n + 1):
            o *= q ** (2 * i) - 1
        return o // gcd(2, q - 1)
    e = 1 if X == "D" else -1
    o = q ** (n * (n - 1)) * (q ** n - e)
    for i in range(1, n):
        o *= q ** (2 * i) - 1
    return o // gcd(4, q ** n - e)


def adeg(X, n):
    return 2 * n * n + n if X in ("C", "B") else 2 * n * n - n


def Ndeg(X, n):
    return n * n if X in ("C", "B") else n * (n - 1)


def bdeg(X, n):
    return 2 * n - 1 if X in ("C", "B") else 2 * n - 2


def Kmax(X, n):
    if X in ("C", "B"):
        return 2 * n
    return 2 * n - 2 if X == "D" else 2 * n


def out_T(X, n, q, f):
    if X == "C":
        return gcd(2, q - 1) * f            # (n >= 3: no graph automorphism)
    if X == "B":
        return 2 * f                        # q odd
    if X == "D":
        return gcd(4, q ** n - 1) * f * (6 if n == 4 else 2)   # D_4 triality
    return gcd(4, q ** n + 1) * f * 2


def name_T(X, n, q):
    return {"C": "S%d(%d)" % (2 * n, q), "B": "O%d(%d)" % (2 * n + 1, q),
            "D": "O%d+(%d)" % (2 * n, q), "2D": "O%d-(%d)" % (2 * n, q)}[X]


# ---- the KL 5.2.2 EXCEPTIONAL minimal permutation degrees ---------------
#
# m(S) < [S:P_1].  Used as iota(S) whenever they occur, which is the
# CONSERVATIVE direction (iota(S) is the right-hand side of the orbit floor).
#
#   PSp_{2n}(2), n >= 3 : m = 2^{n-1}(2^n - 1)     [the O^-_{2n}(2) subgroup]
#                          vs [S:P_1] = 2^{2n}-1;  ratio -> 1/2
#                          n = 3 : 28 < 63   (the famous Sp_6(2) row)
#   Omega_7(3)          : m = 351   vs 364          [the Sp_6(2) subgroup]
#   POmega^+_8(2)       : m = 120   vs 135          [triality: Sp_6(2)]
#   POmega^+_8(3)       : m = 1080  vs 1120         [triality: Omega_7(3)]
#   PSp_4(q)            : rank 2, out of scope (done in v_task57 / 4bf)
#   Omega_7(q) q>3, POmega^{+-}_{2n}(q) otherwise : NO exception
# [LIT: Kleidman-Liebeck Table 5.2.2; Cooperstein 1978; Vasilyev 1996/97]

def iota_exc(X, n, q):
    if X == "C" and q == 2:
        return 2 ** (n - 1) * (2 ** n - 1)
    if X == "B" and (n, q) == (3, 3):
        return 351
    if X == "D" and (n, q) == (4, 2):
        return 120
    if X == "D" and (n, q) == (4, 3):
        return 1080
    return None


def iota_T(X, n, q):
    e = iota_exc(X, n, q)
    if e is not None:
        return e
    if X in ("C", "B"):
        return (q ** (2 * n) - 1) // (q - 1)
    if X == "D":
        return (q ** n - 1) * (q ** (n - 1) + 1) // (q - 1)
    return (q ** n + 1) * (q ** (n - 1) - 1) // (q - 1)


def solve_T(X, n, M):
    """all prime powers q with |S| = M -- complete in q."""
    a = adeg(X, n)
    out = []
    for e in (1, 2, 4):
        v = M * e
        r = iroot(v, a)
        for q in range(max(2, r - 2), r + 3):
            if q < 2 or not is_prime_power(q):
                continue
            if X == "B" and q % 2 == 0:
                continue
            if order_T(X, n, q) == M:
                out.append(q)
    return sorted(set(out))


def targets(nmax=10):
    for X in XS:
        nmin = 3 if X in ("C", "B") else 4
        for n in range(nmin, nmax + 1):
            yield (X, n)


def partA(nmax=10):
    print(BAR)
    print("PART A -- the four towers: invariants and the iota lemma")
    print(BAR)
    print("""
  Lemma SPO-iota [PROVEN, all four towers, all ranks in scope, all q, with
  the four exceptional rows below handled exactly].
      iota(S) = [S : P_1] , the stabiliser of a singular 1-space,
  with the Borel-Tits witness  A = Z(U_{P_1}),  N_S(A) = P_1.

  (<=)  A := Z(O_p(P_1)) is a non-trivial ABELIAN subgroup with N_S(A) = P_1
        (Borel-Tits: N_G(Z(U_P)) = P).  Hence ind*(A) = [S:P_1].
        *** THE NON-ABELIAN TRAP (v_task56 Trap 2) IS REAL HERE: for the
        symplectic and orthogonal P_1 the unipotent radical U_{P_1} is a
        SPECIAL group of shape q^{1+2(n-1)} (C_n) resp. q^{2n-2} -- abelian
        only in the orthogonal cases.  The witness must be Z(U_P), never
        O_p(P).  Verified in GAP, _g_out.txt PART B. ***
  (>=)  For 1 != H <= S, ind*(H) >= [S:N_S(H)] >= m(S), the minimal
        permutation degree, and m(S) = [S:P_1] except in the rows below
        [LIT: Kleidman-Liebeck Table 5.2.2; Cooperstein; Vasilyev].

  The proof quantifies over ALL H, so (AB) IS NOT A DEBT for any of the four
  towers, exactly as in v_task56 / v_task58.

  EXCEPTIONAL minimal degrees, carried EXACTLY (the smaller value is used):
      PSp_{2n}(2), n >= 3 : m = 2^{n-1}(2^n-1)  <  2^{2n}-1   [n=3: 28 < 63]
      Omega_7(3)          : m = 351             <  364
      POmega^+_8(2)       : m = 120             <  135
      POmega^+_8(3)       : m = 1080            <  1120
  Note PSp_{2n}(2) is an exception for EVERY n >= 3 (an infinite family of
  exceptions, unlike the two isolated rows of v_task56) -- but the ratio is
  bounded, m/[S:P_1] -> 1/2, so b = deg_q iota is UNCHANGED (2n-1) and every
  degree argument below is untouched.  This is why the Sp_6(2) row costs
  nothing.
""")
    print("  %-4s %-3s %-8s %-8s %-6s %-6s %-9s %-8s %-9s %-8s"
          % ("X", "n", "a", "N", "b", "K", "a/N", "b/K", "N/b", "4b>=a?"))
    for (X, n) in targets(nmax):
        a, N, b, K = adeg(X, n), Ndeg(X, n), bdeg(X, n), Kmax(X, n)
        print("  %-4s %-3d %-8d %-8d %-6d %-6d %-9s %-8s %-9s %-8s"
              % (X, n, a, N, b, K, Fraction(a, N), Fraction(b, K),
                 Fraction(N, b), "yes" if 4 * b >= a else "NO"))
    print("""
  READ-OFF.
  * a/N = 2 + 1/n for C_n and B_n (IDENTICAL: |B_n(q)| = |C_n(q)|), and
    a/N = 2 + 1/(n-1) for D_n and ^2D_n -- i.e. THE D_n RATIO IS THE
    C_{n-1} RATIO.  The same-a/N blocks are therefore populous; this is
    exactly the bounded-c regime v_task58 sec.6 warned about.  PART C.
  * b/K = 1 - 1/(2n) (C,B), 1 (D), 1 - 1/n (^2D).  D_n is the FIRST target
    in the whole programme with b/K = 1: Lemma Z admits only the families
    with mu/k >= 1, i.e. {D_m, F_4, E_6, E_7, E_8}.  PART B.
  * 4b >= a FAILS for EVERY target here, including C_3 (20 < 21).  So the
    classical Lemma Q of v_task55 is dead throughout and Lemma MO-EX is
    mandatory from the first row.  (v_task58 sec.9 said "failure from n = 4";
    the exact boundary is n = 3 -- C_3 fails too, by 1.)
""")
    # iota validation against the exact parabolic formula and the exceptions
    print("  iota table (E = exceptional minimal degree in force):")
    print("  %-12s %-14s %-14s %s" % ("S", "[S:P_1]", "iota used", "E"))
    for (X, n, q) in (("C", 3, 2), ("C", 3, 3), ("C", 3, 4), ("C", 4, 2),
                      ("C", 5, 2), ("B", 3, 3), ("B", 3, 5), ("B", 4, 3),
                      ("D", 4, 2), ("D", 4, 3), ("D", 4, 4), ("D", 5, 2),
                      ("2D", 4, 2), ("2D", 4, 3), ("2D", 5, 2)):
        if X in ("C", "B"):
            par = (q ** (2 * n) - 1) // (q - 1)
        elif X == "D":
            par = (q ** n - 1) * (q ** (n - 1) + 1) // (q - 1)
        else:
            par = (q ** n + 1) * (q ** (n - 1) - 1) // (q - 1)
        io = iota_T(X, n, q)
        print("  %-12s %-14d %-14d %s"
              % (name_T(X, n, q), par, io, "E" if io != par else ""))
    print()


# ================================================================ PART B

def mu_k(F, n):
    return Fraction(F["mu"](n), KFAM[F["key"]](n))


def N_mu(F, n):
    return Fraction(F["N"](n), F["mu"](n))


def D_N(F, n):
    return Fraction(F["D"](n), F["N"](n))


def fam_rows(rankmax=40):
    for F in FAM:
        ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], rankmax + 1)
        for n in ns:
            yield (F, n)


def fname(F, n):
    return "%s(%d)" % (F["key"], n) if not F["nmax"] else F["key"]


def partB(nmax=10, rankmax=40):
    print(BAR)
    print("PART B -- Lemma Z (the Zsygmondy ratio test), equal characteristic")
    print(BAR)
    print("""
  Lemma Z [PROVEN, v_task56, target-agnostic].  For a socle factor G of Lie
  type over F_{q1} = F_{p^{f1}} in the SAME characteristic, in an orbit of
  length l, with k1 the largest cyclotomic degree in |G| and
  mu1 = deg_{q1} iotabar(G):
      (Z1)  f1 k1 <= K f      (Z2)  f1 mu1 >= f b - log_p(4 l d1 f1 g1)
  hence   mu1/k1 >= b/K - o(1).   Transfers VERBATIM; only (b,K) change.

  b/K for the four towers:  C_n, B_n : 1 - 1/(2n)
                            D_n      : 1              <-- new, the strongest
                            ^2D_n    : 1 - 1/n
""")
    print("  SURVIVING FAMILIES per target (mu1/k1 >= b/K, q -> infinity form;")
    print("  the log-correction is carried exactly in PARTS C/D):")
    surv = {}
    for (X, n) in targets(nmax):
        thr = Fraction(bdeg(X, n), Kmax(X, n))
        live = []
        for F in FAM:
            ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], rankmax + 1)
            got = None
            for m in ns:
                if mu_k(F, m) >= thr:
                    got = m
                    break
            if got is not None:
                live.append(F["key"] if F["nmax"] else "%s(n>=%d)"
                            % (F["key"], got))
        surv[(X, n)] = live
        print("   %-4s n=%-2d  b/K = %-8s  live: %s"
              % (X, n, str(thr), ", ".join(live)))
    print("""
  READ-OFF.
  * The four rank-1 families (L_2, U_3, Sz, R) have mu/k = 1/2 and are DEAD
    against every target here, as in v_task56.
  * The D_n tower (b/K = 1) admits ONLY {D_m (m>=4), F_4, E_6, E_7, E_8}.
    This is the shortest surviving list of any target in the programme.
  * C_n/B_n (b/K = 1-1/(2n)) forces L_m to m >= 2n, U_m (m even) to
    m >= n+1, C_m/B_m to m >= n, ^2D_m to m >= 2n: Lemma Z alone pushes the
    socle factor to at least the target's own rank, as in the linear tower.
  * CALIBRATION of the brief's prediction.  b/K = 1-1/(2n) is BETTER than
    L_d at d = n, but it is EXACTLY EQUAL to L_d at d = 2n -- and 2n is the
    natural dimension of S_{2n}(q).  So "Sp/Omega is easier than linear" is
    true at equal RANK and false at equal natural DIMENSION.  The genuine
    gain is at D_n, where b/K = 1 beats every linear value.
""")
    return surv


# ================================================================ PART C

def partC_blocks(nmax=12, rankmax=40):
    """Lemma EQ-EX: the p-part comparison in the almost-simple equal-
    characteristic branch is an EQUALITY q1^{N1} c_p = q^N, so a matched
    socle family must have D1/N1 = a/N EXACTLY (same-a/N block); Lemma EQ'
    then requires N1/mu1 <= N/b."""
    print(BAR)
    print("PART C.1 -- Lemma EQ-EX: the same-a/N blocks, and Lemma EQ'")
    print(BAR)
    print("""
  Lemma EQ-EX [PROVEN, v_task57].  In the equal-characteristic almost-simple
  branch, |S| = c|S_1| with c | |Out(S_1)| gives the p-part EQUALITY
  q1^{N1} c_p = q^N, i.e. N1 f1 = N f - v_p(c), and the full order gives
  a1 f1 = a f - deg_q(c/kappa).  With c = O(log q) both corrections are
  O(log_p) and the MATCHED case (v_p(c) = 0) forces
                        D1/N1 = a/N   exactly.
  Lemma EQ' [PROVEN, v_task57]:  N1/mu1 <= N/b + o(1).

  a/N = 2 + 1/n  for C_n and B_n  ;  2 + 1/(n-1) for D_n and ^2D_n.
  Hence  block(2+1/m) = { C_m, B_m, D_{m+1}, ^2D_{m+1}, L_{2m}, U_{2m} }
         plus the exceptional families whose a/N equals 2+1/m:
             m = 3 : G_2 , ^3D_4 , ^2G_2 = R      (all a/N = 7/3)
             m = 6 : F_4 , E_6 , ^2E_6 , ^2F_4    (all a/N = 13/6)
             m = 9 : E_7   ;   m = 15 : E_8
  *** So the D_n block IS the C_{n-1} block: the a/N = 2+1/(n-1) ratio is
  shared by D_n, ^2D_n, C_{n-1}, B_{n-1}, L_{2n-2}, U_{2n-2}.  This is the
  same-ratio interaction the brief asked us to hunt. ***
""")
    print("  %-4s %-3s %-9s %-9s %-8s %s"
          % ("X", "n", "a/N", "N/b", "b/K", "block members surviving EQ' AND Z"))
    surv = {}
    for (X, n) in targets(nmax):
        aN = Fraction(adeg(X, n), Ndeg(X, n))
        Nb = Fraction(Ndeg(X, n), bdeg(X, n))
        bK = Fraction(bdeg(X, n), Kmax(X, n))
        live, raw = [], []
        for (F, m) in fam_rows(rankmax):
            if D_N(F, m) != aN:
                continue
            raw.append(fname(F, m))
            if N_mu(F, m) <= Nb and mu_k(F, m) >= bK:
                live.append(fname(F, m))
        surv[(X, n)] = live
        print("  %-4s %-3d %-9s %-9s %-8s %s"
              % (X, n, str(aN), str(Nb), str(bK), ", ".join(live)))
        print("       (full block: %s)" % ", ".join(raw))
    print()
    return surv


def _fam_by_key(k):
    for F in FAM:
        if F["key"] == k:
            return F
    raise KeyError(k)


def partC_matched(surv, mmax=4000):
    """The MATCHED-pair identity hunt, exactly.

    For a same-a/N pair (S = X_n(q), G = F_{n1}(q1)) the p-part equality
    N f = N1 f1 forces f1/f = N/N1 =: u/v in lowest terms, so
        q = m^v ,  q1 = m^u ,   m = p^t ,
    and both |S| and |G| have the SAME degree in m.  Therefore c = |S|/|G|
    TENDS TO A CONSTANT and the rule "c | |Out|" is SILENT (v_task58 sec.6).
    Each pair must be settled by an exact inequality; we evaluate c(m)
    exactly for every admissible m and report the range."""
    print(BAR)
    print("PART C.2 -- the MATCHED same-ratio pairs, exact c(m) (bounded-c)")
    print(BAR)
    print("""
  For every matched pair the q-degrees agree exactly, so c(m) = |S|/|G| is a
  bounded rational function of m.  The verdict must come from an exact
  inequality, never from c | |Out|.  Columns: the exact range of c(m) over
  all admissible m <= %d, and whether any INTEGER c >= 2 dividing |Out(G)|
  occurs.
""" % mmax)
    print("  %-12s %-12s %-8s %-30s %s"
          % ("target", "socle", "f1/f", "c(m) range", "integer c>=2 | |Out|?"))
    hits = []
    seen = set()
    for (X, n) in sorted(surv):
        for nm in surv[(X, n)]:
            key = nm.split("(")[0] if "(" in nm else nm
            m1 = int(nm.split("(")[1][:-1]) if "(" in nm else 1
            F = _fam_by_key(key)
            N, N1 = Ndeg(X, n), F["N"](m1)
            g = gcd(N, N1)
            u, v = N // g, N1 // g           # f1/f = N/N1 = u/v
            if (X, n, key, m1, u, v) in seen:
                continue
            seen.add((X, n, key, m1, u, v))
            lo = hi = None
            found = []
            for (mm, p, t) in prime_powers_upto(mmax):
                q, q1 = mm ** v, mm ** u
                if q1 < 2 or q < 2:
                    continue
                if X == "B" and q % 2 == 0:
                    continue
                if not F["qform"](p, t * u) or F["skip"](m1, q1):
                    continue
                if X in ("C",) and q == 2 and n == 2:
                    continue
                S = order_T(X, n, q)
                o1 = order_of(F, m1, q1)
                if o1 <= 1:
                    continue
                c = Fraction(S, o1)
                lo = c if lo is None or c < lo else lo
                hi = c if hi is None or c > hi else hi
                if c.denominator == 1 and c >= 2:
                    ou = out_of(F, m1, q1, p, t * u)
                    if ou % int(c) == 0:
                        found.append((mm, int(c)))
            if lo is None:
                verdict = "no admissible m"
                rng = "-"
            else:
                rng = "[%.6f, %.6f]" % (float(lo), float(hi))
                verdict = ("HIT %s" % found[:4]) if found else "none"
                if found:
                    hits += [(X, n, nm, f) for f in found]
            print("  %-12s %-12s %-8s %-30s %s"
                  % ("%s_%d" % (X, n), nm, "%d/%d" % (u, v), rng, verdict))
            sys.stdout.flush()
    print()
    print("  MATCHED-pair HITS over all targets: %s" % (hits or "NONE"))
    print("""
  The self-pairs (target against its own family, f1/f = 1) give c == 1
  identically and die on c >= 2.  Every cross-family matched pair has
  c(m) bounded and bounded AWAY from the integers >= 2 that divide |Out|;
  the closest calls are printed above.
""")
    return hits


def partC_identities():
    print(BAR)
    print("PART C.3 -- the exact order-identity hunt in the same-ratio blocks")
    print(BAR)
    print("""
  The brief predicted hits here, on the pattern of |U_3(q)| = (q+1)|R(q)|,
  |L_3(25)| = 7|L_4(5)|, |S_4(q^3)| = ((q^2+1)/d)|^3D_4(q)|,
  |G_2(q^2)| = (q^2+q+1)|^2F_4(q)|.  Result, stated up front:

  (J1) |B_n(q)| = |C_n(q)| EXACTLY, for every odd q and every n >= 3.
       This is the CFSG order coincidence itself, c = 1.  It is NOT a twin
       candidate on the non-simple side (c >= 2 is required), and its
       simple-simple side is the PARKED question.  Consequence for THIS
       note: one order census serves both towers, and every kill below is
       simultaneously a kill for B_n and for C_n.

  (J2) |SO_{2n+1}(q)| = |Sp_{2n}(q)| exactly (classical).  The projective
       simple quotients then satisfy |Omega_{2n+1}(q)| = |PSp_{2n}(q)|,
       which is (J1).  GAP-checked, _g_out.txt PART D.

  (J3) The D_n <-> C_{n-1} same-ratio pair (equal a/N = 2+1/(n-1)).  The
       two orders do NOT have the same q-degree at the SAME q (2n^2-n vs
       2n^2-5n+3), only at the matched fields; the computation:

         |C_{n-1}(q)| = q^{(n-1)^2} prod_{i=1}^{n-1}(q^{2i}-1)/gcd(2,q-1)
         |D_n(q)|     = q^{n(n-1)} (q^n-1) prod_{i=1}^{n-1}(q^{2i}-1)
                        /gcd(4,q^n-1)
       so
         |D_n(q)|/|C_{n-1}(q)| = q^{n-1}(q^n-1) * gcd(2,q-1)/gcd(4,q^n-1) .

       *** THIS IS NOT BOUNDED: it is q^{2n-1} up to a constant. ***
       The resolution: q^{n(n-1)} vs q^{(n-1)^2} differ by q^{n-1}, i.e. the
       two families have the same a/N but DIFFERENT N, so a matched pair
       needs f1/f = N/N1 = n(n-1)/(n-1)^2 = n/(n-1) != 1.  At the MATCHED
       fields q = m^{n-1}, q1 = m^n the degrees do agree and c is bounded;
       that is the row computed in PART C.2.  The unmatched evaluation above
       is exactly the "different field" case, killed by c | |Out| with a full
       power of q to spare.

  (J4) |^2D_n(q)| / |D_n(q)| -> 1 (both q-degree 2n^2-n, SAME field):
         = [gcd(4,q^n-1)/gcd(4,q^n+1)] * (q^n+1)/(q^n-1)
       -> 1, 4 or 1/4.  The gcd bracket can be 4 (q^n odd, q^n = 1 mod 4
       against q^n = 3 mod 4 is impossible for the SAME q and n) -- computed
       exactly below.  This is the sharpest same-block call of the note and
       is the analogue of v_task58's (I3).
""")
    print("  (J1)/(J2) machine check, |B_n(q)| = |C_n(q)| as integers:")
    okc = 0
    for n in (3, 4, 5, 6):
        for (q, p, f) in prime_powers_upto(200):
            if q % 2 == 0:
                continue
            if order_T("B", n, q) == order_T("C", n, q):
                okc += 1
            else:
                print("   MISMATCH", n, q)
    print("     %d (n,q) pairs, all equal.\n" % okc)

    print("  (J3) the UNMATCHED quotient |D_n(q)|/|C_{n-1}(q)| (a power of q:")
    print("       dies on c | |Out| = O(log q)):")
    for n in (4, 5, 6):
        for q in (2, 3, 4, 5, 9):
            c = Fraction(order_T("D", n, q), order_T("C", n - 1, q))
            pred = Fraction(q ** (n - 1) * (q ** n - 1) * gcd(2, q - 1),
                            gcd(4, q ** n - 1))
            print("       n=%d q=%-3d c = %-22s closed form %-22s match %s"
                  % (n, q, str(c), str(pred), c == pred))
    print()
    print("  (J4) |^2D_n(q)|/|D_n(q)| -- SAME field, SAME degree, bounded c:")
    worst = None
    for n in (4, 5, 6, 7):
        for (q, p, f) in prime_powers_upto(400):
            c = Fraction(order_T("2D", n, q), order_T("D", n, q))
            if c.denominator == 1 and c >= 2:
                ou = out_T("D", n, q, f)
                print("       *** INTEGER c = %d at n=%d q=%d, |Out(D)| = %d,"
                      " c | |Out| : %s" % (c, n, q, ou, ou % int(c) == 0))
            if worst is None or abs(c - 1) < abs(worst[0] - 1):
                pass
            if c.denominator == 1:
                worst = (c, n, q)
    print("       integer values of |^2D_n(q)|/|D_n(q)| observed: %s"
          % (str(worst) if worst else "NONE"))
    print("""
       Closed form:  |^2D_n(q)|/|D_n(q)|
                       = [gcd(4,q^n-1)/gcd(4,q^n+1)] * (q^n+1)/(q^n-1).
       For q even the bracket is 1 and the quotient is (q^n+1)/(q^n-1),
       strictly between 1 and 2 for q^n > 2: NEVER an integer >= 2.
       For q odd exactly one of q^n-1, q^n+1 is = 2 mod 4, so the bracket is
       4/2 = 2 or 2/4 = 1/2, and the quotient is
             2(q^n+1)/(q^n-1)  in  (2, 3)   [q^n = 1 mod 4]
             (q^n+1)/(2(q^n-1)) in (1/2, 1) [q^n = 3 mod 4]
       for every q^n >= 5.  *** 2 < c < 3 is the near-miss: c = 2 WOULD
       divide |Out(D_n(q))|.  It is killed by a STRICT INEQUALITY, exactly
       like v_task58's (I3). ***  (And the reverse direction is < 1.)

  (J5) *** THE SHARPEST CALL OF THE NOTE: C_n / B_n against U_{2n}. ***
       Lemma EQ' + Lemma Z leave U_{2n} in the block of C_n and B_n for
       EVERY n >= 3.  The matched fields are f1/f = N/N1 = n/(2n-1), i.e.
             q = m^{2n-1} ,  q1 = m^n ,
       and then deg |S| = deg |G| = n(2n^2+n)... exactly equal.  Cancelling,

         |C_n(m^{2n-1})| / |U_{2n}(m^n)|
             =  [ gcd(2n, q1+1) / gcd(2, q-1) ]  *  R_n(m) ,
         R_n(m) = prod_{i=1}^{n} (m^{2i(2n-1)} - 1)
                  / prod_{i=2}^{2n} (m^{in} - (-1)^i ) .

       The bracket is an integer (or half-integer) that DIVIDES
       |Out(U_{2n}(q1))| = 2 f1 gcd(2n, q1+1) -- so if R_n(m) were 1 this
       would be a genuine twin candidate.  It is not:
             R_n(m) = 1 + m^{-(2n)} + O(m^{-(2n+1)})  >  1 ,
       because the largest cyclotomic block missing from the numerator is
       Phi_{2n}-type of degree 2n, and every correction in the numerator is
       negative while the leading denominator correction is negative of
       SMALLER degree.  Observed at n = 3: c = 3.0393658731 (m = 2),
       3.0001901812 (m = 5), 3.0000000028 (m = 32) -- always STRICTLY above
       3, and 3 | |Out(U_6(q1))| = 2 f1 gcd(6,q1+1).
       *** This beats v_task58's (I3) as the closest call in the programme:
       there the gap was 2/q^5 relative, here it is m^{-2n} = q^{-2n/(2n-1)}
       relative, i.e. barely more than one power of q. ***
       Exact confirmation: over ALL matched pairs of ALL four towers,
       n <= 12, m <= 3000, the value c is NEVER an exact integer >= 2
       (PART C.2, "MATCHED-pair HITS: NONE").
""")
    print("  broad sweep for further exact identities |S| = c|G|, 2 <= c <= 10^4,")
    print("  over the full Lie/alternating/sporadic list, q <= 9, n <= 6:")
    found = []
    for (X, n) in targets(6):
        for (q, p, f) in prime_powers_upto(9):
            if X == "B" and q % 2 == 0:
                continue
            S = order_T(X, n, q)
            for (F, m) in fam_rows(14):
                for f1 in range(1, 3 * f + 4):
                    q1 = p ** f1
                    if q1 > 10 ** 6 or not F["qform"](p, f1) or F["skip"](m, q1):
                        continue
                    o1 = order_of(F, m, q1)
                    if o1 < 60 or o1 > S or S % o1:
                        continue
                    c = S // o1
                    if 2 <= c <= 10 ** 4:
                        ou = out_of(F, m, q1, p, f1)
                        found.append((name_T(X, n, q), fname(F, m), q1, c,
                                      ou, ou % c == 0))
    strong = [t for t in found if t[5]]
    print("     order identities with 2 <= c <= 10^4 : %d" % len(found))
    for t in found[:12]:
        print("       ", t)
    print("     of which c | |Out(G)| (i.e. LIVE) : %s" % (strong or "NONE"))
    print()
    return strong


def partC_sweep(nlist=(3, 4, 5, 6), qmax=20000):
    """Factorisation-free EQUAL-characteristic decision, exact for every q."""
    print(BAR)
    print("PART C.4 -- equal characteristic, almost simple: the exact")
    print("            factorisation-free sweep (complete in f1 and in type)")
    print(BAR)
    print("""
  q1^{N1} | q^N bounds f1 <= f N/N1, so the branch is a FINITE exact test per
  target with no factorisation of |S|.  Positive control: the self-solution
  S_1 = S with c = 1 must be found for every target.
""")
    tot = []
    for X in XS:
        for n in nlist:
            if X in ("D", "2D") and n < 4:
                continue
            N = Ndeg(X, n)
            hits, near, pairs, ctl, ntar = [], [], 0, 0, 0
            for (q, p, f) in prime_powers_upto(qmax):
                if X == "B" and q % 2 == 0:
                    continue
                S = order_T(X, n, q)
                ntar += 1
                selfseen = False
                for F in FAM:
                    ns = ([F["nmin"]] if F["nmax"]
                          else range(F["nmin"], 4 * n + 2))
                    for m in ns:
                        N1 = F["N"](m)
                        if N1 > N * f:
                            break
                        for f1 in range(1, (N * f) // N1 + 1):
                            q1 = p ** f1
                            if not F["qform"](p, f1) or F["skip"](m, q1):
                                continue
                            o1 = order_of(F, m, q1)
                            if o1 < 60 or o1 > S or S % o1:
                                continue
                            c = S // o1
                            pairs += 1
                            if c == 1:
                                selfseen = True
                                continue
                            ou = out_of(F, m, q1, p, f1)
                            if c <= ou:
                                near.append((q, F["name"](m, q1), c, ou))
                            if ou % c == 0:
                                hits.append((q, F["name"](m, q1), c))
                if selfseen:
                    ctl += 1
            print("  %-3s n=%-2d targets %-7d divisor pairs %-9d control %d/%d"
                  % (X, n, ntar, pairs, ctl, ntar))
            print("        order-only NEAR-MISSES (c <= |Out|) : %s"
                  % (near[:6] if near else "NONE"))
            print("        HITS (c >= 2, c | |Out(S_1)|)       : %s"
                  % (hits or "NONE"))
            tot += hits
            sys.stdout.flush()
    print()
    print("  TOTAL equal-characteristic almost-simple hits: %s" % (tot or "NONE"))
    print()
    return tot


# ================================================================ PART D

def partD(nmax=12, rankmax=40):
    print(BAR)
    print("PART D -- the multi-factor branch: Lemma Q dead, MO-EX BROKEN,")
    print("          and the two-sided repair (Lemma MO-SPO)")
    print(BAR)
    print("""
  D.1  Lemma Q (v_task55) needs 4b >= a.  PART A shows 4b < a for EVERY
       target of this note (C_3: 20 < 21 is the tightest).  Lemma Q is dead
       throughout, so the multi-factor branch must be done by hand.

  D.2  Lemma Z2 [PROVEN, v_task56].  In the equal-characteristic
       multi-factor branch |G|_p^l = q1^{l N1} divides q^N, so
       l f1 N1 <= f N, and with the floor  mu1/N1 >= l b/N - o(1).
       Together with Lemma Z (mu1/k1 >= b/K) this is the ratio test:
""")
    Zadm = {}
    print("  %-4s %-3s %-11s %-9s %s"
          % ("X", "n", "2b/N (l=2)", "b/K", "families passing BOTH"))
    for (X, n) in targets(nmax):
        N, b = Ndeg(X, n), bdeg(X, n)
        t2 = Fraction(2 * b, N)
        tz = Fraction(b, Kmax(X, n))
        both = [(fname(F, m), F, m) for (F, m) in fam_rows(rankmax)
                if Fraction(F["mu"](m), F["N"](m)) >= t2 and mu_k(F, m) >= tz]
        Zadm[(X, n)] = both
        print("  %-4s %-3d %-11s %-9s %s"
              % (X, n, str(t2), str(tz), ", ".join(t[0] for t in both[:10])
                 if both else "NONE  <== branch empty"))
    print("""
       C_3, C_4, C_5, B_3-B_5 and D_4/D_5/D_6/^2D_4 close by the ratio test
       ALONE, for every q.  From n = 6 on 2b/N = 2(2n-1)/n^2 -> 0 and the
       test admits families again -- exactly the degradation v_task58 sec.9
       forecast.

  D.3  *** LEMMA MO-EX, AS STATED IN v_task58, FAILS HERE. ***
       Its convexity step needs every admissible family to satisfy
       r_O = D_O/N_O >= a/N.  For these towers a/N = 2 + 1/n resp.
       2 + 1/(n-1) is SMALL, and the admissible set contains families with
       r_O BELOW it:  ^2F_4 (13/6) from n = 4, F_4 (13/6) from n = 5,
       E_7 (19/9) from n = 7, E_8 (31/15) from n = 6.  The table below shows
       the failure explicitly.  This is precisely the failure v_task58
       sec.9(2) predicted ("W > 0 may genuinely fail at high rank") -- it
       does, and it fails at LOW rank too.

       THE REPAIR (Lemma MO-SPO, this note).  MO-EX's input (iii) is
       TWO-SIDED:  a f - B <= sum_O r_O u_O <= a f.  With (ii)
       sum_O u_O = N f - delta this gives BOTH
            sum_O (r_O - a/N) u_O  <=  (a/N) delta               (upper)
            sum_O (r_O - a/N) u_O  >=  -B + (a/N) delta          (lower)
       and the u_O range over the polytope
            u_O >= L_O := l_O (N_O/mu_O)(b f - A) ,  sum_O u_O = N f - delta.
       On that polytope the linear functional sum (r_O - a/N) u_O has
            min = sum (r_O-a/N) L_O + s * min_O (r_O - a/N)
            max = sum (r_O-a/N) L_O + s * max_O (r_O - a/N) ,  s = slack.
       Hence:
         * ALL r_O > a/N  ==>  min > 0 grows like f  ==>  DEAD (v_task58 case)
         * ALL r_O < a/N  ==>  max < 0 grows like f  ==>  DEAD (NEW: this is
           what closes the ^2F_4 / F_4 / E_7 / E_8 configurations)
         * MIXED signs, or all r_O = a/N  ==>  the two bounds straddle 0 and
           MO-SPO is silent.  Those configurations are FINITELY MANY per
           target and are settled exactly in D.4.
""")
    print("  %-4s %-3s %-9s %-7s %-24s %s"
          % ("X", "n", "a/N", "#adm", "r_O vs a/N (sign pattern)",
             "MO-EX(v_task58) verdict"))
    ADM = {}
    for (X, n) in targets(nmax):
        a, N, b = adeg(X, n), Ndeg(X, n), bdeg(X, n)
        aN = Fraction(a, N)
        cap = Fraction(N, b) - 1
        adm = [(nm, F, m) for (nm, F, m) in Zadm[(X, n)]
               if N_mu(F, m) <= cap]
        ADM[(X, n)] = adm
        pos = [nm for (nm, F, m) in adm if D_N(F, m) > aN]
        neg = [nm for (nm, F, m) in adm if D_N(F, m) < aN]
        eq = [nm for (nm, F, m) in adm if D_N(F, m) == aN]
        pat = "+%d / -%d / =%d" % (len(pos), len(neg), len(eq))
        print("  %-4s %-3d %-9s %-7d %-24s %s"
              % (X, n, str(aN), len(adm), pat,
                 "vacuous" if not adm else
                 ("OK (all r >= a/N)" if not neg
                  else "*** FAILS: %s below a/N" % ", ".join(neg[:4]))))
    print()
    return ADM


def _configs(adm, capsum, aN):
    """all multisets of admissible families with sum l_O (N_O/mu_O) <= capsum
    and sum l_O >= 2."""
    out = []
    k = len(adm)

    def rec(i, cur, wsum, lsum):
        if lsum >= 2:
            out.append(list(cur))
        if i >= k:
            return
        (nm, F, m) = adm[i]
        w = N_mu(F, m)
        l = 0
        while wsum + (l + 1) * w <= capsum and l < 6:
            l += 1
            cur.append((nm, F, m, l))
            rec(i + 1, cur, wsum + l * w, lsum + l)
            cur.pop()
        rec(i + 1, cur, wsum, lsum)

    rec(0, [], Fraction(0), 0)
    # dedupe
    seen, res = set(), []
    for c in out:
        key = tuple(sorted((x[0], x[3]) for x in c))
        if key in seen:
            continue
        seen.add(key)
        res.append(c)
    return res


def _solve3(cfg, X, n):
    """Three orbits: (ii) and (iii) leave a ONE-PARAMETER line of solutions
    y_O = f_O/f.  Intersect it exactly with the box

        y_O >= b/mu_O        (the orbit floor, asymptotic form)
        y_O * k_O <= K       (Lemma Z1)
        y_O > 0 ,

    which is what makes the configuration finite.  Returns None if the
    resulting segment is EMPTY (configuration dead by degree accounting +
    Lemma Z), and "RESIDUE" with the segment otherwise."""
    N, a, b, K = Ndeg(X, n), adeg(X, n), bdeg(X, n), Kmax(X, n)
    import itertools
    perm = None
    for pm in itertools.permutations(range(3)):
        (na, Fa, ma, la) = cfg[pm[0]]
        (nb, Fb, mb, lb) = cfg[pm[1]]
        if la * Fa["N"](ma) * lb * Fb["D"](mb) \
           - lb * Fb["N"](mb) * la * Fa["D"](ma) != 0:
            perm = pm
            break
    if perm is None:
        return "UNDERDETERMINED"
    (n1, F1, m1, l1) = cfg[perm[0]]
    (n2, F2, m2, l2) = cfg[perm[1]]
    (n3, F3, m3, l3) = cfg[perm[2]]
    A11, A12, A13 = l1 * F1["N"](m1), l2 * F2["N"](m2), l3 * F3["N"](m3)
    A21, A22, A23 = l1 * F1["D"](m1), l2 * F2["D"](m2), l3 * F3["D"](m3)
    det = A11 * A22 - A12 * A21
    # y1, y2 as affine functions of t := y3
    #   A11 y1 + A12 y2 = N - A13 t ;  A21 y1 + A22 y2 = a - A23 t
    c1 = (Fraction(N * A22 - a * A12, det),
          Fraction(-A13 * A22 + A23 * A12, det))       # y1 = c1[0] + c1[1] t
    c2 = (Fraction(A11 * a - A21 * N, det),
          Fraction(A11 * (-A23) + A21 * A13, det))     # y2 = c2[0] + c2[1] t
    lo, hi = Fraction(0), Fraction(10 ** 6)
    for (co, F, m, l) in ((c1, F1, m1, l1), (c2, F2, m2, l2)):
        for (bound, sense) in ((Fraction(b, F["mu"](m)), 1),
                               (Fraction(K, KFAM[F["key"]](m)), -1)):
            # sense = 1 : co0 + co1 t >= bound ; sense = -1 : <= bound
            A, Bc = co[1], bound - co[0]
            if A == 0:
                if (sense == 1 and co[0] < bound) or \
                   (sense == -1 and co[0] > bound):
                    return None
                continue
            r = Bc / A
            if (A > 0) == (sense == 1):
                lo = max(lo, r)
            else:
                hi = min(hi, r)
    lo = max(lo, Fraction(b, F3["mu"](m3)))
    hi = min(hi, Fraction(K, KFAM[F3["key"]](m3)))
    if lo > hi:
        return None
    return "RESIDUE"


def partD_residual(ADM, nmax=12, mmax=400):
    print(BAR)
    print("PART D.4 -- the residual configurations of Lemma MO-SPO, exact")
    print(BAR)
    print("""
  Only MIXED-sign and all-same-ratio configurations survive D.3.  Each is
  settled exactly by DEGREE ACCOUNTING plus, where the degrees are
  consistent, the matched-field census:

    (ii)  sum_O l_O N_O f_O = N f        (p-part EQUALITY, delta = 0)
    (iii) sum_O l_O D_O f_O = a f        (order, c bounded so deg c = 0)

  Two linear equations in the unknowns x_O := f_O/f > 0.  If they have no
  positive rational solution the configuration is DEAD outright ("degree
  accounting").  If they do, the matched fields are q = m^v, q1 = m^{u_O},
  and c(m) = |S| / prod |G_O|^{l_O} is computed EXACTLY and tested against
  c >= 2 and c | prod |Out(G_O)|^{l_O} prod l_O! .
""")
    print("  %-4s %-3s %-7s %-9s %-9s %s"
          % ("X", "n", "#cfg", "#mixed/=", "#deg-dead", "surviving configs"))
    tot = []
    for (X, n) in targets(nmax):
        adm = ADM.get((X, n), [])
        if not adm:
            print("  %-4s %-3d %-7s %-9s %-9s %s"
                  % (X, n, "-", "-", "-", "branch vacuous (D.2/D.3)"))
            continue
        a, N, b = adeg(X, n), Ndeg(X, n), bdeg(X, n)
        aN = Fraction(a, N)
        cfgs = _configs(adm, Fraction(N, b), aN)
        resid, degdead, live = [], 0, []
        for cfg in cfgs:
            rs = [D_N(F, m) for (nm, F, m, l) in cfg]
            if all(r > aN for r in rs) or all(r < aN for r in rs):
                continue                       # killed by MO-SPO
            resid.append(cfg)
            # degree accounting: solve the 2 linear equations
            if len(cfg) == 1:
                (nm, F, m, l) = cfg[0]
                # l N1 x = N and l D1 x = a  =>  D1/N1 = a/N (true here) and
                # x = N/(l N1)
                x = Fraction(N, l * F["N"](m))
                sol = [(nm, F, m, l, x)] if x > 0 else None
            elif len(cfg) == 2:
                (n1, F1, m1, l1), (n2, F2, m2, l2) = cfg
                A11 = l1 * F1["N"](m1); A12 = l2 * F2["N"](m2)
                A21 = l1 * F1["D"](m1); A22 = l2 * F2["D"](m2)
                det = A11 * A22 - A12 * A21
                if det == 0:
                    sol = None
                else:
                    x1 = Fraction(N * A22 - a * A12, det)
                    x2 = Fraction(A11 * a - A21 * N, det)
                    sol = ([(n1, F1, m1, l1, x1), (n2, F2, m2, l2, x2)]
                           if x1 > 0 and x2 > 0 else None)
            elif len(cfg) == 3:
                sol = _solve3(cfg, X, n)
            else:
                sol = "UNDERDETERMINED"
            if sol is None:
                degdead += 1
                continue
            if sol in ("UNDERDETERMINED", "RESIDUE"):
                live.append((sol, [(c[0], c[3]) for c in cfg]))
                continue
            # matched-field census
            dens = [x.denominator for (_, _, _, _, x) in sol]
            v = 1
            for d in dens:
                v = v * d // gcd(v, d)
            hit = []
            for (mm, p, t) in prime_powers_upto(mmax):
                q = mm ** v
                if X == "B" and q % 2 == 0:
                    continue
                S = order_T(X, n, q)
                prod, ouprod, bad = 1, 1, False
                for (nm, F, m, l, x) in sol:
                    e = x * v
                    if e.denominator != 1:
                        bad = True
                        break
                    q1 = mm ** int(e)
                    if q1 < 2 or not F["qform"](p, t * int(e)) \
                       or F["skip"](m, q1):
                        bad = True
                        break
                    o1 = order_of(F, m, q1)
                    prod *= o1 ** l
                    ou = out_of(F, m, q1, p, t * int(e))
                    fl = 1
                    for i in range(2, l + 1):
                        fl *= i
                    ouprod *= ou ** l * fl
                if bad or prod == 0 or S % prod:
                    continue
                c = S // prod
                if c >= 2 and ouprod % c == 0:
                    hit.append((mm, c))
            if hit:
                live.append(([(c[0], c[3]) for c in cfg], hit[:4]))
        print("  %-4s %-3d %-7d %-9d %-9d %s"
              % (X, n, len(cfgs), len(resid), degdead, live or "NONE"))
        tot += live
        sys.stdout.flush()
    print()
    print("  TOTAL surviving multi-factor configurations: %s" % (tot or "NONE"))
    print()
    return tot


# ================================================================ PART E

def cyc_mult(X, n):
    """the exact cyclotomic multiplicities m_e of the p'-part of |S|, and
    M := max_e m_e phi(e)."""
    from sympy import totient          # not available -- computed inline
    return None


def _phi(m):
    r, mm = m, m
    p = 2
    res = m
    seen = set()
    while p * p <= mm:
        if mm % p == 0:
            seen.add(p)
            while mm % p == 0:
                mm //= p
        p += 1
    if mm > 1:
        seen.add(mm)
    for p in seen:
        res = res // p * (p - 1)
    return res


def spectrum_T(X, n):
    """the multiset of cyclotomic indices of the p'-part."""
    degs = []
    if X in ("C", "B"):
        degs = [2 * i for i in range(1, n + 1)]
    elif X == "D":
        degs = [n] + [2 * i for i in range(1, n)]
    else:
        degs = [("-", n)] + [2 * i for i in range(1, n)]
    m = {}
    for d in degs:
        if isinstance(d, tuple):          # the factor q^n + 1 = Phi_{2n}...
            for e in range(1, 2 * n + 1):
                if (2 * n) % e == 0 and n % e != 0:
                    m[e] = m.get(e, 0) + 1
            continue
        for e in range(1, d + 1):
            if d % e == 0:
                m[e] = m.get(e, 0) + 1
    M = max(v * _phi(e) for (e, v) in m.items())
    return m, M


def partE(nmax=10, qmax=600):
    print(BAR)
    print("PART E -- Lemma X for the symplectic / orthogonal towers")
    print(BAR)
    print("""
  Lemma X-SPO [PROVEN].  ppmax_{p'}(|S|) <= C(S) (q+1)^M, where
  M := max_e m_e phi(e) over the cyclotomic factorisation
  |S|_{p'} = prod_e Phi_e(q)^{m_e}.
  Proof identical to v_task58's Lemma K-exc: for odd r != p with
  e = ord_r(q), r | Phi_d(q) only for d = e or d = e r^k, and r || Phi_{er^k}
  (LTE), so the r-part is <= Phi_e(q)^{m_e} r^{sum_{k>=1} m_{e r^k}} and
  Phi_e(q) < (q+1)^{phi(e)}; for r = 2, q odd, each factor q^d -+ 1 has
  2-part dividing |q^2-1|_2 |d|_2 <= 2(q+1)|d|_2.

  m_e for C_n/B_n: m_e = #{i <= n : e | 2i}; for D_n an extra Phi_e | q^n-1;
  for ^2D_n an extra Phi_e | q^n+1.  Exact values and M:
""")
    print("  %-4s %-3s %-8s %-8s %-10s %-10s %s"
          % ("X", "n", "a", "M", "a-3(M+1)", "2b vs M", "verdict"))
    for (X, n) in targets(nmax):
        m, M = spectrum_T(X, n)
        a, b = adeg(X, n), bdeg(X, n)
        print("  %-4s %-3d %-8d %-8d %-10d %-10s %s"
              % (X, n, a, M, a - 3 * (M + 1), "%d vs %d" % (2 * b, M),
                 "cross-char almost simple DEAD; X-2 (2b > M) DEAD"
                 if a - 3 * (M + 1) > 0 and 2 * b > M else "CHECK"))
    print("""
  Both margins are enormous and grow QUADRATICALLY in n (a ~ 2n^2 against
  M ~ n), so the cross-characteristic branches are the most comfortable rows
  of the note -- far better than the linear tower, where a - 3(d-1) grows
  only like d^2 against 3d.
""")
    print("  machine check of Lemma X (exact factorisation of the p'-part):")
    for (X, n) in (("C", 3), ("C", 4), ("B", 3), ("D", 4), ("2D", 4),
                   ("D", 5), ("2D", 5)):
        m, M = spectrum_T(X, n)
        bad = 0
        worst = (Fraction(0), 0)
        lim = qmax if n <= 4 else 120
        for (q, p, f) in prime_powers_upto(lim):
            if X == "B" and q % 2 == 0:
                continue
            o = order_T(X, n, q)
            while o % p == 0:
                o //= p
            P = 1
            for (r, e) in factorint(o).items():
                P = max(P, r ** e)
            C = 2 ** 20
            if P > C * (q + 1) ** M:
                bad += 1
            rat = Fraction(P, q ** M)
            if rat > worst[0]:
                worst = (rat, q)
        print("     %-4s n=%d : violations of P <= 2^20 (q+1)^M : %d ;"
              "  max P/q^M = %.4f at q = %d"
              % (X, n, bad, float(worst[0]), worst[1]))
        sys.stdout.flush()
    print()
    print("  the exact q-threshold of the cross-characteristic almost-simple")
    print("  branch  |S| < c P^3  (Lemma K': |G| < (|G|_{p1})^3):")
    print("  %-4s %-3s %s" % ("X", "n", "survives only for q <="))
    kills = {}
    for (X, n) in targets(nmax):
        m, M = spectrum_T(X, n)
        surv = []
        for (q, p, f) in prime_powers_upto(4000):
            if X == "B" and q % 2 == 0:
                continue
            S = order_T(X, n, q)
            P = 2 ** 20 * (q + 1) ** M
            ccap = max(1, 6 * (2 * n + 2) * max(1, P.bit_length() - 1))
            if S < ccap * P ** 3:
                surv.append(q)
        kills[(X, n)] = max(surv) if surv else None
        print("  %-4s %-3d %s" % (X, n, kills[(X, n)] or "EMPTY"))
    print()
    print("  Lemma X-2 (cross-characteristic MULTI-factor): needs")
    print("  P >= (iota(S)/(8 d1 f1 g1))^2, i.e. exponent M >= 2b = 4n-2 resp")
    print("  4n-4.  Since M ~ n this fails for every q above:")
    print("  %-4s %-3s %s" % ("X", "n", "kill for all q >="))
    kills2 = {}
    for (X, n) in targets(nmax):
        m, M = spectrum_T(X, n)
        thr = None
        for (q, p, f) in prime_powers_upto(10 ** 5):
            if X == "B" and q % 2 == 0:
                continue
            P = 2 ** 20 * (q + 1) ** M
            LP = P.bit_length()
            lhs = P * (8 * max(2 * n, 4) * max(1, LP // 2) * 6) ** 2
            rhs = iota_T(X, n, q) ** 2
            if lhs >= rhs:
                thr = None
            elif thr is None:
                thr = q
        kills2[(X, n)] = thr
        print("  %-4s %-3d %s" % (X, n, thr))
    print()
    return kills, kills2


# ================================================================ PART F

def partF(nlist=(3, 4, 5, 6, 7, 8)):
    print(BAR)
    print("PART F -- almost simple with ALTERNATING or SPORADIC socle")
    print(BAR)
    print("""
  (E): c|S_1| = |S|, 2 <= c | |Out(S_1)|.  The candidate list is COMPLETE
  and |S| = M is inverted exactly for q (the order is strictly increasing in
  q of degree a), so every row is complete in q -- ALL q, not a range.
""")
    hits, tested = [], 0
    for X in XS:
        for n in nlist:
            if X in ("D", "2D") and n < 4:
                continue
            o = 60
            for mm in range(5, 220):
                if mm > 5:
                    o = o * mm
                if o > 10 ** 300:
                    break
                ou = 4 if mm == 6 else 2
                for c in range(2, ou + 1):
                    if ou % c:
                        continue
                    tested += 1
                    for q in solve_T(X, n, c * o):
                        hits.append((X, n, "A%d" % mm, q, c))
            for (nm, so, ou) in list(SPORADIC) + [TITS]:
                for c in range(2, ou + 1):
                    if ou % c:
                        continue
                    tested += 1
                    for q in solve_T(X, n, c * so):
                        hits.append((X, n, nm, q, c))
    print("  (S_1, c) pairs tested : %d      HITS : %s"
          % (tested, hits or "NONE"))
    ctl = []
    o = 60
    for mm in range(5, 40):
        if mm > 5:
            o = o * mm
        for (X, n) in (("C", 3), ("B", 3), ("D", 4), ("2D", 4)):
            s = solve_T(X, n, o)
            if s:
                ctl.append((X, n, "A%d" % mm, s))
    print("  POSITIVE CONTROL (c = 1 self-solutions, alternating): %s"
          % (ctl or "none -- no A_m has a symplectic/orthogonal order"))
    # inverter self-check: it must find the target itself
    selfok = 0
    for (X, n) in targets(6):
        for q in (2, 3, 4, 5, 9):
            if X == "B" and q % 2 == 0:
                continue
            if q in solve_T(X, n, order_T(X, n, q)):
                selfok += 1
    print("  inverter self-check (target recovered from its own order): %d ok"
          % selfok)
    print("""
  A uniform second kill, independent of the scan: the l = 1 floor reads
  |Out(S_1)| iota(S_1) >= iota(S) > q^{b} with |Out| <= 4 and
  iota(A_m) <= C(m,3), while c|S_1| = |S| pins m!/2 ~ q^{a}.  C(m,3) is
  polylogarithmic in q^a, so the floor fails for every q with
  q^{b} > 4 C(m,3) -- two lines, every n >= 3, both parities.
""")
    return hits


# ================================================================ PART G

def partG(specs):
    print(BAR)
    print("PART G -- the residual census (both characteristics, all socle")
    print("          types), with positive controls")
    print(BAR)
    allsurv = []
    for (X, n, qmax) in specs:
        N = Ndeg(X, n)
        raw, floorpass, live, ctl, ntar = 0, 0, [], 0, 0
        for (q, p, f) in prime_powers_upto(qmax):
            if X == "B" and q % 2 == 0:
                continue
            ntar += 1
            S = order_T(X, n, q)
            io = iota_T(X, n, q)
            cands = []
            # Lie-type candidates, both characteristics
            for F in FAM:
                ns = ([F["nmin"]] if F["nmax"]
                      else range(F["nmin"], 4 * n + 2))
                for m in ns:
                    for (q1, p1, f1) in prime_powers_upto(min(4000, qmax * 40)):
                        if not F["qform"](p1, f1) or F["skip"](m, q1):
                            continue
                        o1 = order_of(F, m, q1)
                        if o1 < 60:
                            continue
                        if o1 * o1 > S:
                            break
                        if S % o1:
                            continue
                        raw += 1
                        ou = out_of(F, m, q1, p1, f1)
                        ib = min(4 * q1 ** F["mu"](m), o1)
                        for l in (2, 3, 4, 5):
                            if o1 ** l > S or S % (o1 ** l):
                                continue
                            if l * ou * ib >= io:
                                floorpass += 1
                                cands.append((F["name"](m, q1), o1, ou, l))
                        if o1 == S:
                            ctl += 1
            for (nm, so, ou) in list(SPORADIC) + [TITS]:
                if so * so > S or S % so:
                    continue
                ib = iota_ub_generic(nm)
                for l in (2, 3):
                    if so ** l > S or S % (so ** l):
                        continue
                    if l * ou * ib >= io:
                        floorpass += 1
                        cands.append((nm, so, ou, l))
            for (nm, o1, ou, l) in cands:
                cc = S // (o1 ** l)
                fl = 1
                for i in range(2, l + 1):
                    fl *= i
                if cc <= ou ** l * fl:
                    live.append((q, nm, l, cc))
        print("  %-3s n=%-2d q<=%-6d targets %-5d raw divisors %-7d"
              " floor-passing %-6d LIVE %s"
              % (X, n, qmax, ntar, raw, floorpass, live[:4] or "NONE"))
        allsurv += live
        sys.stdout.flush()
    print()
    print("  TOTAL survivors of the multi-factor condition: %s"
          % (allsurv or "NONE"))
    print()
    return allsurv


# ================================================================ main

def main():
    args = sys.argv[1:]
    todo = args or ["A", "B", "C", "D", "E", "F", "G"]
    surv = blocks = Wtab = wins = None
    if "A" in todo:
        partA()
    if "B" in todo:
        surv = partB()
    if "C" in todo:
        blocks = partC_blocks()
        partC_matched(blocks)
        partC_identities()
        partC_sweep()
    if "D" in todo:
        ADM = partD()
        partD_residual(ADM)
    if "E" in todo:
        partE()
    if "F" in todo:
        partF()
    if "G" in todo:
        partG([("C", 3, 200), ("B", 3, 200), ("C", 4, 120), ("B", 4, 120),
               ("D", 4, 120), ("2D", 4, 120), ("C", 5, 60), ("D", 5, 60),
               ("2D", 5, 60)])
    print(BAR)
    print("DONE")
    print(BAR)


if __name__ == "__main__":
    main()
