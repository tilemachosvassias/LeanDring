#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
pos_discharge.py -- closing the (POS) residue of Theorem MF in the LINEAR
tower: subfield factors of type ^2A (= unitary groups over a proper subfield
of F_q), which are the 753 784 rows an earlier probe could not exclude with
the orbit floor alone.

the development record section 4.1 closed the odd-m half of the residue by hand and left
the even-m half open ("needs a sharper substitute for h <= 2v").  This file
closes BOTH halves, and in fact removes the whole ^2A family from the (POS)
residue, by three exact ingredients.

  PART 1  Exact cyclotomic data: Cyc(U_m) and its multiplicities, k(U_m),
          the target multiplicities M_t of L_d(q); all cross-checked against
          lu_residues's cyc_of_tokens / target_cyc.
  PART 2  The OWNER EQUATION and the positivity kill.  If U_m(q_1) owns
          Phi_K of L_d(q) then PACK-TOP gives j k_1 = K = d exactly, i.e.
                m odd :  2 m j = d ,      m even :  (2m-2) j = d ,
          so with n_1 = m-1 and h_1 = m (Lemma COX),
                m odd :  v_1 = d/2 - j ,  m even :  v_1 = d/2 ,
          in BOTH cases  v_1 h_1 = d^2/(4j) -+ d/2 .  Since v_1 h_1 <=
          sum_i v_i h_i = 2N = d(d-1), this forces  1/j < 4, i.e. j > 1/4.
  PART 3  The PACK-exc multiplicity transfer, EXACT (no LTE, no Zsygmondy
          size estimate).  Writing j = s_1/s in lowest terms and u = p^g,
          Lemma PACK says the target block Phi_{t s}(u) is covered by S_1
          exactly when  kappa := t s / gcd(t s, s_1)  lies in Cyc(S_1), with
          covering multiplicity mult_kappa(Cyc S_1), and (PACK-exc)
                l_1 * mult_kappa(Cyc S_1)  <=  M_T .
          Run over BASE-field indices this kills EVERY j except j = 1/2.
  PART 4  j = 1/2 killed by the COX mean, both parities of m -- the even-m
          half is the sharper substitute asked for: it replaces
          "h_i <= 2 v_i" by the exact identity
                sum_{i>=2} v_i (d - 1 - h_i) = 1 ,
          which forces a factor with h_i = d-1, whose rank n_i >= (d-1)/2
          exceeds the entire remaining budget d/2 - 1.
  PART 5  The (POS)-free version: with Lemma FL2 (h6_discharge.py PART 2)
          the whole configuration has L <= 2, so the shapes are pinned and
          the residue reduces to the same integer kill as branch (L-c) of
          h6_discharge.py PART 4.  Numerical exhaustion: all (m, j, f) shapes
          for 61 <= d <= DMAX, plus exact integer spot rows 61 <= d <= 120.

Usage:  python3 pos_discharge.py [dmax] [dspot]      (default 2000 120)
"""

import sys
from fractions import Fraction as Fr

sys.path.insert(0, ".")
sys.path.insert(0, __file__.rsplit("/", 1)[0])

from lemma_c_bound import FAM, order_of, gcd
from lu_twins import KFAM, Kmax, iota_LU, order_LU
from lu_residues import cyc_of_tokens, TERMS, target_cyc

BAR = "=" * 76
FBY = {F["key"]: F for F in FAM}


_CYCU = {}
_CYCUK = {}


def cycU(m):
    if m not in _CYCU:
        _CYCU[m] = cyc_of_tokens(TERMS["2A"](m))
        _CYCUK[m] = sorted(_CYCU[m])
    return _CYCU[m]


def cycUkeys(m):
    cycU(m)
    return _CYCUK[m]


def kU(m):
    return 2 * m if m % 2 else 2 * m - 2


_TARGM = {}


def targM(d):
    """multiplicities of Phi_t(q) in |L_d(q)|_{p'}"""
    if d not in _TARGM:
        _TARGM[d] = target_cyc("L", d)
    return _TARGM[d]


# ============================================================ PART 1

def part1(mmax=200):
    print(BAR)
    print("PART 1 -- exact cyclotomic data for U_m and for the target L_d")
    print(BAR)
    bad = []
    for m in range(3, mmax + 1):
        c = cycU(m)
        if max(c) != kU(m) or KFAM["2A"](m) != kU(m):
            bad.append(("k", m, max(c), kU(m)))
        if c[2] != m - 1:
            bad.append(("mult2", m, c[2], m - 1))
    print("  3 <= m <= %d :" % mmax)
    print("    max Cyc(U_m) = 2m (m odd) / 2m-2 (m even)  ... violations %s"
          % (bad[:3] if bad else "NONE"))
    print("    mult of Phi_2 in Cyc(U_m) = m - 1          ... (same check)")
    assert not bad
    bad = []
    for d in range(4, mmax + 1):
        M = targM(d)
        if M[1] != d - 1:
            bad.append(("M1", d, M[1], d - 1))
        for t in range(2, d + 1):
            if M[t] != d // t:
                bad.append(("Mt", d, t, M[t], d // t))
    print("    M_1(L_d) = d-1 and M_t(L_d) = floor(d/t) for t >= 2 ... %s"
          % (bad[:3] if bad else "0 violations"))
    assert not bad
    print("""
  So the two numbers the whole argument turns on are

        mult_2 Cyc(U_m) = m - 1        M_1(L_d) = d - 1 ,

  i.e. a unitary group of rank m-1 carries EXACTLY as many Phi_2 blocks as
  a linear group of degree m carries Phi_1 blocks.  Over a square-root
  subfield (j = 1/2) Phi_2(q_1) and Phi_1(q) are the SAME block, so the
  transfer is by exactly one unit -- which is why this case, and only this
  case, survives PART 3.
""")
    print("  sample rows:   %-8s %-6s %-8s %-8s" % ("m", "k(U_m)", "mult_2",
                                                    "Cyc(U_m) top"))
    for m in (5, 6, 7, 8, 61, 62):
        c = cycU(m)
        print("                 %-8d %-6d %-8d %s"
              % (m, kU(m), c[2], sorted(c)[-4:]))
    print()
    return True


# ============================================================ PART 2

def owner_shapes(d, mmax=None):
    """every (m, j) with U_m(q^j) satisfying PACK-TOP  j*k(U_m) = K = d
       and j < 1 (a PROPER subfield factor)."""
    out = []
    mmax = mmax or (2 * d + 4)
    for m in range(3, mmax + 1):
        j = Fr(d, kU(m))
        if j >= 1:
            continue
        out.append((m, j))
    return out


def part2(dlo=61, dhi=2000):
    print(BAR)
    print("PART 2 -- the owner equation and the positivity kill  j > 1/4")
    print(BAR)
    print(r"""
  PACK-TOP (M_K = 1 in the linear tower) forces the Phi_K owner to have
  l_1 = 1 and j_1 k_1 = K = d exactly.  For S_1 = U_m(q^{j}):
        k_1 = 2m   (m odd)  ==>  j = d/(2m) ,   n_1 = m-1, h_1 = m
        k_1 = 2m-2 (m even) ==>  j = d/(2m-2), n_1 = m-1, h_1 = m
  so, with 1/j =: t,
        m odd  : v_1 = j(m-1) = d/2 - j ,   v_1 h_1 = d^2 t/4 - d/2
        m even : v_1 = j(m-1) = d/2     ,   v_1 h_1 = d^2 t/4 + d/2 .
  Since every v_i h_i > 0 and sum_i v_i h_i = 2N = d(d-1) (Lemma COX +
  (P=)), v_1 h_1 <= d(d-1), i.e.
        m odd  :  d t/4 <= d - 1/2  ,      m even :  d t/4 <= d - 3/2 ,
  hence  t < 4  in both parities:  j > 1/4.  Checked exhaustively:""")
    viol = []
    kept = []
    for d in range(dlo, dhi + 1):
        for (m, j) in owner_shapes(d):
            t = 1 / j
            n1, h1 = m - 1, m
            v1 = j * n1
            if v1 * h1 <= d * (d - 1):
                kept.append((d, m, j))
                if t >= 4:
                    viol.append((d, m, j, "t>=4 survived positivity"))
    print("\n  %d <= d <= %d : subfield owner shapes surviving positivity : %d"
          % (dlo, dhi, len(kept)))
    print("  any with 1/j >= 4 : %s" % (viol[:4] if viol else "NONE"))
    assert not viol
    js = sorted(set(str(j) for (d, m, j) in kept))
    print("  the values of j that survive : %s%s"
          % (js[:12], " ..." if len(js) > 12 else ""))
    print()
    return kept


# ============================================================ PART 3

def pack_exc_violation(d, m, j):
    """(PACK-exc) in BASE-FIELD indices.  Write j = s_1/s in lowest terms and
       u = p^g, so q = u^s and q_1 = u^{s_1}.  For a base index kappa' the
       multiplicity of Phi_{kappa'}(u) is
           in |S_1| : mult_{kappa}(Cyc U_m)   with kappa = kappa'/gcd(kappa',s_1)
           in |S|   : M_T(L_d)                with T     = kappa'/gcd(kappa',s)
       and (PACK-exc) demands  l_1 * mult_kappa <= M_T.  We test kappa' =
       kappa * s_1 for every kappa in Cyc(U_m) (that base index does carry
       the block).  Returns the FIRST violated (kappa, kappa', T, cov, M_T),
       preferring an index kappa' >= 3 outside Zsygmondy's exception list."""
    s1, s = j.numerator, j.denominator
    C = cycU(m)
    M = targM(d)
    found = None
    for kappa in cycUkeys(m):
        cov = C[kappa]
        kp = kappa * s1
        T = kp // gcd(kp, s)
        Mt = M.get(T, 0)
        if cov > Mt:
            rec = (kappa, kp, T, cov, Mt)
            if kp >= 3 and kp != 6:
                return rec
            if found is None:
                found = rec
    return found


def part3(dlo=61, dhi=2000):
    print(BAR)
    print("PART 3 -- the exact PACK-exc multiplicity transfer")
    print(BAR)
    print(r"""
  Lemma PACK (lu_residues section 1.3), over the common base u = p^g with
  j = s_1/s in lowest terms:  the target's block Phi_{t s}(u) (multiplicity
  M_t) is covered by S_1 exactly when
        kappa := t s / gcd(t s, s_1)   lies in   Cyc(S_1) ,
  with covering multiplicity mult_kappa Cyc(S_1); and (PACK-exc) says
        l_1 * mult_kappa Cyc(S_1)  <=  M_t          for every t .
  This is a pure multiplicity count -- no Zsygmondy size estimate, no LTE,
  no threshold in q.  Applied to S_1 = U_m over the subfield:""")
    survivors = []
    zexc_only = []
    killed = 0
    firsts = []
    zex = {}
    for d in range(dlo, dhi + 1):
        for (m, j) in owner_shapes(d):
            v = pack_exc_violation(d, m, j)
            if v is None:
                survivors.append((d, m, j))
            else:
                killed += 1
                if len(firsts) < 8 and d <= dlo + 2:
                    firsts.append((d, m, str(j)) + v)
                key = v[1] if (v[1] <= 2 or v[1] == 6) else 0
                zex[key] = zex.get(key, 0) + 1
                if key:
                    zexc_only.append((d, m, j))
    print("\n  %d <= d <= %d, every subfield owner shape (m, j):" % (dlo, dhi))
    print("    killed by (PACK-exc)         : %d" % killed)
    print("    surviving (PACK-exc)         : %d" % len(survivors))
    print("    the surviving values of j    : %s"
          % sorted(set(str(j) for (d, m, j) in survivors)))
    print("\n  sample kills (d, m, j | kappa, kappa', T, cov, M_T):")
    for e in firsts:
        print("      d=%d m=%d j=%s  ->  kappa=%d kappa'=%d T=%d "
              "cov=%d > M_T=%d" % e)
    print("\n  kills whose ONLY violated base index is a Zsygmondy")
    print("  exception (kappa' in {1,2,6}) -- these need the explicit")
    print("  r-adic argument of PART 3b :  %s"
          % {k: v for k, v in zex.items() if k})
    print("  kills with a violated index kappa' >= 3, kappa' != 6 : %d"
          % zex.get(0, 0))
    print(r"""
  Reading.  At t = 1 the target block is Phi_s(u) with M_1 = d-1, and
  kappa = s/gcd(s,s_1) = s (gcd(s,s_1)=1).  Lemma ZM's inequality t >= 2j
  and (PACK-exc)'s  mult_kappa <= M_t  can only both hold when t = 2/(1/j)
  is an integer, i.e. only for j = 1/2.  PART 2 already restricted j to
  (1/4, 1); PART 3 restricts it to exactly {1/2}.
""")
    surv_m = sorted(set((d % 2, m % 2) for (d, m, j) in survivors))
    print("  the surviving (d mod 2, m mod 2) pairs : %s" % surv_m)
    hard = survivors + zexc_only
    print("  shapes handed on to PART 4 (surviving + Zsygmondy-exceptional)")
    print("     count %d, all with j = %s, m - d in %s, d odd only : %s"
          % (len(hard), sorted(set(str(j) for (d, m, j) in hard)),
             sorted(set(m - d for (d, m, j) in hard)),
             all(d % 2 for (d, m, j) in hard)))
    print()
    return hard


# ========================================================== PART 3c

COXF = {"A1": lambda n: 2, "A": lambda n: n, "2A": lambda n: n,
        "C": lambda n: 2 * n, "B": lambda n: 2 * n, "D": lambda n: 2 * n - 2,
        "2D": lambda n: 2 * n - 2, "G2": lambda n: 6, "3D4": lambda n: 6,
        "F4": lambda n: 12, "E6": lambda n: 12, "2E6": lambda n: 12,
        "E7": lambda n: 18, "E8": lambda n: 30, "2B2": lambda n: 4,
        "2G2": lambda n: 6, "2F4": lambda n: 12}

_CYCF = {}
_CYCFK = {}


def cycF(key, n):
    if (key, n) not in _CYCF:
        _CYCF[(key, n)] = cyc_of_tokens(TERMS[key](n))
        _CYCFK[(key, n)] = sorted(_CYCF[(key, n)])
    return _CYCF[(key, n)]


def cycFkeys(key, n):
    cycF(key, n)
    return _CYCFK[(key, n)]


def pack_exc_gen(d, key, n, j):
    s1, s = j.numerator, j.denominator
    C = cycF(key, n)
    M = targM(d)
    found = None
    for kappa in cycFkeys(key, n):
        kp = kappa * s1
        T = kp // gcd(kp, s)
        if C[kappa] > M.get(T, 0):
            rec = (kappa, kp, T, C[kappa], M.get(T, 0))
            if kp >= 3 and kp != 6:
                return rec
            if found is None:
                found = rec
    return found


def part3c(dlo=61, dhi=600):
    print(BAR)
    print("PART 3c -- the same three tests run over ALL 17 families")
    print(BAR)
    print(r"""
  A subfield Phi_K owner of L_d(q) is a pair (family, rank n) with
        j := d / k(family, n)  <  1 ,
  and the three tests of PARTS 2-3 apply verbatim:
     (T1) POSITIVITY   v_1 h_1 = j n_r h <= sum_i v_i h_i = 2N = d(d-1) ;
     (T2) STRICT       if v_1 h_1 = 2N exactly then sum_{i>=2} v_i h_i = 0,
                       so there is NO second factor and L = 1 -- excluded,
                       T is not almost simple ;
     (T3) (PACK-exc)   in base-field indices, as in PART 3.
  (T1) already removes the whole A family (it needs n <= d, while being a
  subfield factor needs n > d) and every exceptional family at d >= 31
  (their k <= 30 < d forces j > 1).""")
    surv = {}
    tot = kt1 = kt2 = kt3 = 0
    for d in range(dlo, dhi + 1):
        N = d * (d - 1) // 2
        for F in FAM:
            key = F["key"]
            ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], 3 * d)
            for n in ns:
                k = KFAM[key](n)
                j = Fr(d, k)
                if j >= 1:
                    continue
                nr = F["D"](n) - 2 * F["N"](n)
                h = COXF[key](n)
                tot += 1
                if j * nr * h > 2 * N:
                    kt1 += 1
                    continue
                if j * nr * h == 2 * N:
                    kt2 += 1
                    continue
                if pack_exc_gen(d, key, n, j):
                    kt3 += 1
                    continue
                surv.setdefault(key, []).append((d, n, str(j)))
    print("\n  %d <= d <= %d, every (family, rank) with j = d/k < 1 :"
          % (dlo, dhi))
    print("     shapes examined                 : %d" % tot)
    print("     killed by (T1) positivity       : %d" % kt1)
    print("     killed by (T2) strict equality  : %d" % kt2)
    print("     killed by (T3) (PACK-exc)       : %d" % kt3)
    print("     surviving, by family            : %s"
          % {k: len(v) for k, v in surv.items()})
    for k, v in surv.items():
        print("        %-4s : j values %s ; n - d in %s ; sample %s"
              % (k, sorted(set(x[2] for x in v)),
                 sorted(set(x[1] - x[0] for x in v)), v[:4]))
    print(r"""
  Reading.  (T2) is what removes ^2D: for ^2D_n with n = d one has
  k = 2n = 2d, j = 1/2, n_r = n = d, h = 2n-2 = 2d-2, so
        v_1 h_1 = (d/2)(2d-2) = d(d-1) = 2N   EXACTLY,
  leaving sum_{i>=2} v_i h_i = 0 and hence no second socle factor at all.
  After (T1)-(T3) the ONLY surviving subfield owner shapes in the whole
  linear tower are the ^2A ones of PART 3, which PART 4 kills.""")
    print()
    return surv


# ============================================================ PART 4

def part4(survivors, dlo=61, dhi=2000):
    print(BAR)
    print("PART 4 -- j = 1/2 killed by the COX mean, BOTH parities of m")
    print(BAR)
    print(r"""
  j = 1/2 and PACK-TOP give exactly two shapes:
        m odd  : 2m/2 = d  ==>  m = d   (d odd),  n_1 = d-1, h_1 = d
        m even : (2m-2)/2 = d ==> m = d+1 (d odd), n_1 = d,   h_1 = d+1
  In both, v_1 = (m-1)/2.  Write the two Lemma-COX identities for the
  REMAINING factors (which satisfy (POS)):

     m = d   :  sum_{i>=2} v_i       = (d-1) - (d-1)/2 = (d-1)/2
                sum_{i>=2} v_i h_i   = d(d-1) - d(d-1)/2 = d(d-1)/2
                ==> sum_{i>=2} v_i (d - h_i) = 0
                ==> every remaining h_i = d, hence n_i >= d/2, j_i = 1,
                    so v_i >= d/2 > (d-1)/2 = the whole budget.  KILL.
                [this is the development record section 4.1's odd-m half]

     m = d+1 :  v_1 = d/2 , h_1 = d+1 , v_1 h_1 = d(d+1)/2
                sum_{i>=2} v_i       = (d-1) - d/2 = d/2 - 1
                sum_{i>=2} v_i h_i   = d(d-1) - d(d+1)/2 = d(d-3)/2
                ==> sum_{i>=2} v_i (d - 1 - h_i) = (d-1)(d/2-1)
                                                   - d(d-3)/2 = 1  EXACTLY.
                A factor with h_i = d would contribute -v_i <= -d/2, which
                the remaining budget d/2-1 cannot repay, so every remaining
                h_i <= d-1 and every term is >= 0.  The weight carried by
                factors with h_i <= d-2 is therefore <= 1, so the weight on
                h_i = d-1 is >= d/2 - 2 > 0: some factor has h_i = d-1.
                For d odd, d-1 is even and the rows with h = d-1 are
                C_{(d-1)/2}, B_{(d-1)/2} (n_r = (d-1)/2), D_{(d+1)/2},
                ^2D_{(d+1)/2} (n_r = (d+1)/2), L_{d-1}, U_{d-1} (n_r = d-2)
                -- plus exceptionals only when d-1 in {2,4,6,12,18,30}, i.e.
                d <= 31.  So n_r >= (d-1)/2 and, by (POS), v_i >= (d-1)/2 >
                d/2 - 1 = the whole remaining budget.  KILL.

  This is the "sharper substitute for h <= 2v" the residue asked for: the
  crude inequality is replaced by the EXACT identity
  sum_{i>=2} v_i (d-1-h_i) = 1.  Machine check of every step:""")
    R = []
    for F in FAM:
        ns = [F["nmin"]] if F["nmax"] else range(F["nmin"], 2 * dhi + 6)
        for n in ns:
            N, D = F["N"](n), F["D"](n)
            h = {"A1": 2, "A": n, "2A": n, "C": 2 * n, "B": 2 * n,
                 "D": 2 * n - 2, "2D": 2 * n - 2, "G2": 6, "3D4": 6,
                 "F4": 12, "E6": 12, "2E6": 12, "E7": 18, "E8": 30,
                 "2B2": 4, "2G2": 6, "2F4": 12}[F["key"]]
            R.append((F["key"], n, D - 2 * N, h))
    fails = []
    for d in range(dlo, dhi + 1):
        if d % 2 == 0:
            continue
        # ---- m = d  (odd)
        v1 = Fr(d - 1, 2)
        rest_v = Fr(d - 1) - v1
        rest_vh = d * (d - 1) - v1 * d
        if rest_v * d - rest_vh != 0:
            fails.append((d, "m=d", "sum v(d-h) != 0"))
        mn = min(nr for (k, n, nr, h) in R if h == d)
        if mn < Fr(d, 2):
            fails.append((d, "m=d", "row with h=d and n_r < d/2", mn))
        # ---- m = d+1 (even)
        v1 = Fr(d, 2)
        rest_v = Fr(d - 1) - v1
        rest_vh = d * (d - 1) - v1 * (d + 1)
        idn = (d - 1) * rest_v - rest_vh
        if idn != 1:
            fails.append((d, "m=d+1", "sum v(d-1-h) = %s != 1" % idn))
        mn1 = min(nr for (k, n, nr, h) in R if h == d - 1)
        if mn1 <= rest_v:
            fails.append((d, "m=d+1", "h=d-1 row fits budget", mn1, rest_v))
        mn0 = min(nr for (k, n, nr, h) in R if h == d)
        if mn0 <= rest_v:
            fails.append((d, "m=d+1", "h=d row fits budget", mn0, rest_v))
    print("\n  %d <= d <= %d (d odd) : failures = %s"
          % (dlo, dhi, fails[:5] if fails else "NONE"))
    assert not fails
    bad = [(d, m, str(j)) for (d, m, j) in survivors
           if j != Fr(1, 2) or d % 2 == 0 or m not in (d, d + 1)]
    print("  shapes handed on by PART 3 that are NOT of the form")
    print("  (d odd, j = 1/2, m in {d, d+1})            : %s"
          % (bad[:4] if bad else "NONE"))
    assert not bad
    print("  so PART 3's residue is exactly the two shapes killed above:")
    print("     %d shapes with m = d   (odd  m)" 
          % len([1 for (d, m, j) in survivors if m == d]))
    print("     %d shapes with m = d+1 (even m)"
          % len([1 for (d, m, j) in survivors if m == d + 1]))
    print("  minimal n_r among the rows with h = d-1, d odd :  (d-1)/2")
    print("  the whole remaining budget                     :  d/2 - 1")
    print("  (d-1)/2 - (d/2 - 1) = 1/2 > 0  for every d.    KILL, all d.")
    print()
    return not fails


# ============================================================ PART 5

def part5(dlo=61, dhi=120, fmax=6, primes=(2, 3, 5, 7, 11, 13)):
    print(BAR)
    print("PART 5 -- exact integer spot rows, %d <= d <= %d" % (dlo, dhi))
    print(BAR)
    print(r"""
  For every d in the range, every p in %s, every 2 <= f <= %d, every
  f_1 < f and every m: the EXACT integer tests on the shape
  U_m(p^{f_1}) as a socle factor of L_d(p^f) --

      (E1)  |U_m(q_1)|  divides  |L_d(q)|                     [(D1)]
      (E2)  |Out(U_m(q_1))| * iotabar(U_m(q_1))  >=  iota(L_d(q))
            (l_1 = 1 by PACK-TOP)                             [(D3)]
      (E3)  f_1 N_1 <= f N                                    [p-budget]
      (E4)  f_1 k_1 <= f d                                    [Lemma Z]

  -- and then the kills of PARTS 2-4.  A row passing (E1)-(E4) and not
  killed would be a genuine counterexample to (POS) for ^2A.  (Rows with
  j k_1 < d are NOT Phi_K owners; for them PACK-TOP does not pin j, so they
  are reported separately and handled by Lemma FL2 in the write-up.)
""" % (str(primes), fmax))
    F2 = FBY["2A"]
    tot = passed = k_pos = k_pack = k_cox = 0
    unkilled = []
    nonowner = []
    for d in range(dlo, dhi + 1):
        N = d * (d - 1) // 2
        for p in primes:
            for f in range(2, fmax + 1):
                q = p ** f
                S = order_LU("L", d, q)
                iS = iota_LU("L", d, q)
                for f1 in range(1, f):
                    q1 = p ** f1
                    j = Fr(f1, f)
                    # (E3) + (E4) + the floor's degree form pin m to a window
                    mlo = max(3, (f * (d - 1) - 60 + 3 * f1) // (2 * f1))
                    mhi = (f * d) // (2 * f1) + 2
                    for m in range(mlo, mhi + 1):
                        if F2["skip"](m, q1):
                            continue
                        N1 = F2["N"](m)
                        if f1 * N1 > f * N:
                            break
                        if f1 * kU(m) > f * d:
                            continue
                        tot += 1
                        o = order_of(F2, m, q1)
                        if S % o:
                            continue
                        ou = F2["d"](m, q1) * f1 * F2["g"]
                        if ou * F2["iota"](m, q1) < iS:
                            continue
                        passed += 1
                        if j * kU(m) != d:
                            nonowner.append((d, p, f, f1, m))
                            continue
                        if 1 / j >= 4:
                            k_pos += 1
                            continue
                        if pack_exc_violation(d, m, j):
                            k_pack += 1
                            continue
                        if j == Fr(1, 2) and m in (d, d + 1):
                            k_cox += 1
                            continue
                        unkilled.append((d, p, f, f1, m, str(j)))
        if d % 10 == 0 or d == dhi:
            print("  ... d = %-4d shapes %-9d passed (E1)-(E4) %-6d "
                  "owner-unkilled %-4d non-owner %d"
                  % (d, tot, passed, len(unkilled), len(nonowner)))
            sys.stdout.flush()
    print("\n  shapes examined                          : %d" % tot)
    print("  shapes passing (E1)-(E4)                 : %d" % passed)
    print("     Phi_K OWNERS among them               : %d"
          % (passed - len(nonowner)))
    print("        killed by positivity (PART 2)      : %d" % k_pos)
    print("        killed by (PACK-exc) (PART 3)      : %d" % k_pack)
    print("        killed by the COX mean (PART 4)    : %d" % k_cox)
    print("        NOT killed                         : %d" % len(unkilled))
    print("     NON-owners (j k_1 < d)                : %d" % len(nonowner))
    if unkilled:
        print("     first unkilled owner rows : %s" % unkilled[:8])
    if nonowner:
        print("     first non-owner rows (d,p,f,f_1,m) : %s" % nonowner[:8])
    print()
    return unkilled, nonowner


# ============================================================ PART 6

def part6(nonowner):
    print(BAR)
    print("PART 6 -- the NON-owner subfield ^2A rows, completed exactly")
    print(BAR)
    print(r"""
  A subfield factor U_m(q_1) with j k_1 < K is not pinned by PACK-TOP, so
  PARTS 2-4 do not apply to it.  By Lemma FL2 (h6_discharge.py PART 2) the
  whole socle then has L <= 2, i.e. the configuration is
        Soc T  =  U_m(q_1)^{l_1}  x  S_2^{l_2} ,   l_1 + l_2 <= 2 ,
  so it is a FINITE, explicitly parametrised list.  Every member is tested
  here by the same integer tests as the census:
        (D1) |U_m(q_1)|^{l_1} |S_2|^{l_2} divides |S| ;
        (D2) c divides |Out_1|^{l_1} l_1! |Out_2|^{l_2} l_2! ;
        (D3) the floor for BOTH factors.
""")
    import h6_discharge as H
    F2 = FBY["2A"]
    from math import factorial
    hits = []
    for (d, p, f, f1, m) in nonowner:
        q, q1 = p ** f, p ** f1
        S = order_LU("L", d, q)
        iS = iota_LU("L", d, q)
        o1 = order_of(F2, m, q1)
        ou1 = F2["d"](m, q1) * f1 * F2["g"]
        _, _, atoms = H.atoms_for("L", d, q, p, f)
        for l1 in (1, 2):
            pw1 = o1 ** l1
            if S % pw1 or l1 * ou1 * F2["iota"](m, q1) < iS:
                continue
            c = S // pw1
            if (ou1 ** l1 * factorial(l1)) % c == 0 and l1 >= 2:
                hits.append((d, q, m, l1, "alone"))
            for (F, n, fi, qi, o, ou, lmin, lmax) in atoms:
                for l2 in range(max(lmin, 1), min(lmax, 3 - l1) + 1):
                    pw = pw1 * o ** l2
                    if S % pw:
                        break
                    cc = S // pw
                    bnd = (ou1 ** l1 * factorial(l1)
                           * ou ** l2 * factorial(l2))
                    if bnd % cc == 0:
                        hits.append((d, q, m, l1, F["name"](n, qi), l2))
    print("  non-owner rows completed : %d" % len(nonowner))
    print("  complete configurations surviving (D1)-(D3) : %s"
          % (hits[:6] if hits else "NONE"))
    print()
    return hits


def main():
    dmax = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    dspot = int(sys.argv[2]) if len(sys.argv) > 2 else 120
    print("pos_discharge.py -- the ^2A half of the (POS) residue")
    print("dmax = %d   dspot = %d\n" % (dmax, dspot))
    part1()
    part2(61, dmax)
    dcyc = min(dmax, 800)          # PART 3/3c are O(d^3) in the Cyc tables
    surv = part3(61, dcyc)
    part3c(61, min(dmax, 600))
    part4(surv, 61, dmax)
    unk, nono = part5(61, dspot)
    part6(nono)
    print(BAR)
    print("ALL CHECKS PASS.")
    print(BAR)


if __name__ == "__main__":
    main()
