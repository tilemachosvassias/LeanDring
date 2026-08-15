#!/usr/bin/env python3
"""
v_task81_arith.py -- INDEPENDENT adversarial re-derivations for the audit of
v_task50-54.  Everything here is re-derived from scratch; nothing is imported
from the audited scripts.  Exact integer / Fraction arithmetic throughout.

PART 1  Lemma C, re-proved by an INDEPENDENT and more elementary route:
        iota_ab(G) <= |G| / |Syl_p(G)|  (witness A = Z(Syl_p), N_G(A) >= Syl_p)
        so  Lemma C  <==  (|Out| )^3 * |G| <= (|G|_p)^3 .
        The finite failure window is enumerated over ALL families and ALL
        ranks and each member checked exactly with the minimal-parabolic
        upper bound.
PART 2  (E1) of v_task52 §4.1(e): the two closed-form families
        c*d*(q+2) = d1*(q-1)  and  c*d*(q-2) = d1*(q+1),  solved completely.
        Plus the "km != p^j" branch threshold.
PART 3  Lemma EQ / Lemma W arithmetic (v_task54 §2, §4) at named points.
PART 4  rank-1: 3-coprimality, Sz subfield count, U3/R ppmax^3 thresholds,
        and the ALTERNATING-socle branch (claimed "complete in q").
PART 5  (E2)/(E3) windows of v_task52 §4.2/§4.3.
"""
import sys
from fractions import Fraction
from math import factorial, comb, log2

sys.path.insert(0, __file__.rsplit('/', 1)[0])
from v_task81_census import (gcd, ord_L, ord_U, ord_BC, ord_Dplus, ord_Dminus,
                             ord_G2, ord_F4, ord_E6, ord_2E6, ord_E7, ord_E8,
                             ord_3D4, ord_Sz, ord_Ree, ord_2F4, factorise,
                             prime_powers_upto, icbrt, SPORADIC)

# ===================================================================== P1 ===
# family record: name, rank param n, order(q), N = #positive roots (= v_p(|G|)
# in units of log_p q), D = deg_q |G|, d(q) = the centre-order gcd, g = graph
# factor, and the minimal-parabolic index ibar_P(q) (an iota_ab upper bound by
# Borel-Tits).  All formulas typed independently.

def famlist(nmax=14):
    F = []
    F.append(("A1", 1, lambda q: ord_L(2, q), 1, 3,
              lambda q: gcd(2, q - 1), 1, lambda q: q + 1))
    for n in range(3, nmax + 1):
        F.append(("L%d" % n, n, (lambda n: lambda q: ord_L(n, q))(n),
                  n * (n - 1) // 2, n * n - 1,
                  (lambda n: lambda q: gcd(n, q - 1))(n), 2,
                  (lambda n: lambda q: (q ** n - 1) // (q - 1))(n)))
    for n in range(3, nmax + 1):
        F.append(("U%d" % n, n, (lambda n: lambda q: ord_U(n, q))(n),
                  n * (n - 1) // 2, n * n - 1,
                  (lambda n: lambda q: gcd(n, q + 1))(n), 2,
                  (lambda n: lambda q: (q ** n - (-1) ** n)
                   * (q ** (n - 1) - (-1) ** (n - 1)) // (q * q - 1))(n)))
    for n in range(2, nmax + 1):        # C_n = PSp(2n,q)  and  B_n = O_{2n+1}
        F.append(("C%d" % n, n, (lambda n: lambda q: ord_BC(n, q))(n),
                  n * n, 2 * n * n + n,
                  (lambda q: gcd(2, q - 1)), 2 if n == 2 else 1,
                  (lambda n: lambda q: (q ** (2 * n) - 1) // (q - 1))(n)))
    for n in range(3, nmax + 1):
        F.append(("B%d" % n, n, (lambda n: lambda q: ord_BC(n, q))(n),
                  n * n, 2 * n * n + n,
                  (lambda q: gcd(2, q - 1)), 1,
                  (lambda n: lambda q: (q ** (2 * n) - 1) // (q - 1))(n)))
    for n in range(4, nmax + 1):
        F.append(("D%d+" % n, n, (lambda n: lambda q: ord_Dplus(n, q))(n),
                  n * (n - 1), 2 * n * n - n,
                  (lambda n: lambda q: gcd(4, q ** n - 1))(n),
                  6 if n == 4 else 2,
                  (lambda n: lambda q: (q ** (n - 1) + 1) * (q ** n - 1)
                   // (q - 1))(n)))
        F.append(("D%d-" % n, n, (lambda n: lambda q: ord_Dminus(n, q))(n),
                  n * (n - 1), 2 * n * n - n,
                  (lambda n: lambda q: gcd(4, q ** n + 1))(n), 2,
                  (lambda n: lambda q: (q ** (n - 1) - 1) * (q ** n + 1)
                   // (q - 1))(n)))
    F.append(("G2", 2, ord_G2, 6, 14, lambda q: 1, 2,
              lambda q: (q ** 6 - 1) // (q - 1)))
    F.append(("F4", 4, ord_F4, 24, 52, lambda q: 1, 2,
              lambda q: (q ** 12 - 1) * (q ** 4 + 1) // (q - 1)))
    F.append(("E6", 6, ord_E6, 36, 78, lambda q: gcd(3, q - 1), 2,
              lambda q: (q ** 9 - 1) * (q ** 8 + q ** 4 + 1) // (q - 1)))
    F.append(("2E6", 6, ord_2E6, 36, 78, lambda q: gcd(3, q + 1), 2,
              lambda q: (q ** 9 + 1) * (q ** 8 + q ** 4 + 1) // (q + 1)))
    F.append(("E7", 7, ord_E7, 63, 133, lambda q: gcd(2, q - 1), 1,
              lambda q: (q ** 14 - 1) * (q ** 9 + 1) * (q ** 5 - 1)
              // ((q - 1) ** 3)))
    F.append(("E8", 8, ord_E8, 120, 248, lambda q: 1, 1,
              lambda q: (q ** 30 - 1) * (q ** 12 + 1) * (q ** 10 + 1)
              * (q ** 6 + 1) // ((q - 1) * (q ** 2 - 1))))
    F.append(("3D4", 4, ord_3D4, 12, 28, lambda q: 1, 3,
              lambda q: (q ** 8 + q ** 4 + 1) * (q + 1)))
    F.append(("2B2", 1, ord_Sz, 2, 5, lambda q: 1, 1, lambda q: q * q + 1))
    F.append(("2G2", 1, ord_Ree, 3, 7, lambda q: 1, 1,
              lambda q: q ** 3 + 1))
    F.append(("2F4", 2, ord_2F4, 12, 26, lambda q: 1, 1,
              lambda q: (q ** 6 + 1) * (q ** 3 + 1) * (q + 1)))
    return F


def nominal_mu(ibarP):
    """the exact degree in q of the polynomial-in-q parabolic index"""
    a, b = ibarP(1000), ibarP(1001)
    mu = 0
    while True:
        # deg is determined by ratio; use exact integer bracketing at Q=1000
        if 1000 ** (mu + 1) > 2 * a:
            break
        mu += 1
    return mu


def qrange(fam, qlim):
    """admissible q for the family, up to qlim"""
    nm = fam[0]
    out = []
    for (q, p, f) in prime_powers_upto(qlim):
        if nm in ("2B2", "2F4"):
            if p != 2 or f % 2 == 0 or f < 3:
                continue
        if nm == "2G2":
            if p != 3 or f % 2 == 0 or f < 3:
                continue
        if nm == "A1" and q in (2, 3):
            continue
        if nm == "U3" and q == 2:
            continue
        if nm == "C2" and q == 2:
            continue
        if nm == "G2" and q == 2:
            continue
        out.append((q, p, f))
    return out


def out_order(fam, q, p, f):
    nm, n, orderf, N, D, dfun, g, ibarP = fam
    d = dfun(q)
    gg = g
    if nm == "G2":
        gg = 2 if p == 3 else 1
    if nm == "F4":
        gg = 2 if p == 2 else 1
    if nm == "C2":
        gg = 2 if p == 2 else 1
    if nm.startswith("D") and nm.endswith("+") and n == 4:
        gg = 6
    if nm == "3D4":
        gg = 3
    if nm in ("2B2", "2G2", "2F4", "E7", "E8"):
        gg = 1
    tw = 1
    if nm.startswith("U") or nm == "2E6" or nm.endswith("-"):
        tw = 2          # field-graph group has order 2f
        gg = 1          # ... and there is NO further graph factor
    # |Out| = d * f * g   (for twisted unitary/2E6/2D the field group has
    # order 2f, which we fold into g via tw)
    return d * f * gg * tw


def part1(qlim_window=10 ** 7, nmax=14, verbose=True):
    print("=" * 74)
    print("PART 1  Lemma C  |Out(G)|*iota(G) <= |G|^{2/3}, independent route")
    print("=" * 74)
    print("Elementary bound used (NO Borel-Tits, NO minimal-degree theorems):")
    print("  A := Z(Syl_p(G)) is abelian, != 1, and Syl_p(G) <= N_G(A), so")
    print("  iota_ab(G) <= [G : Syl_p(G)] = |G| / |G|_p .")
    print("  Hence Lemma C is implied by the EXACT integer inequality")
    print("      (SC)   |Out(G)|^3 * |G|  <=  (|G|_p)^3 .")
    print()
    F = famlist(nmax)
    windows = []
    for fam in F:
        nm, n, orderf, N, D, dfun, g, ibarP = fam
        # surrogate window bound: (SC) is implied by 5.69*d^2 f^3 g^3 <= q^{3N-D}
        E = 3 * N - D
        if E <= 0 and nm != "A1":
            print("  !! family %s has 3N-D = %d <= 0 -- (SC) cannot close it" % (nm, E))
        # find window by brute force over q, using the exact (SC) test
        w = []
        for (q, p, f) in qrange(fam, qlim_window if E <= 1 else 4096):
            o = orderf(q)
            if o <= 1:
                continue
            ou = out_order(fam, q, p, f)
            if ou ** 3 * o > (q ** N) ** 3:
                w.append((q, p, f))
            else:
                # (SC) holds; for fixed family it stays true for larger q of
                # the same p once f grows -- but we do not rely on that:
                # the surrogate below proves the tail.
                pass
        if w:
            windows.append((nm, w))
    print("Failure window of (SC) (i.e. groups where (SC) does NOT already")
    print("prove Lemma C), searched over q <= %d for the families with"
          % qlim_window)
    print("3N-D <= 1 and q <= 4096 for the rest:")
    tot = 0
    for nm, w in windows:
        print("   %-6s : %d groups  q = %s" % (nm, len(w),
              [x[0] for x in w][:40]))
        tot += len(w)
    print("   TOTAL window size: %d" % tot)
    print()
    print("Tail proof (uniform, no computation):  |G| <= 5.69 * q^D / d and")
    print("  |Out| = d*f*g*tw, so (SC) follows from  5.69 * d^2 f^3 (g*tw)^3")
    print("  <= q^{3N-D}.  The table of 3N-D:")
    seen = set()
    for fam in famlist(nmax):
        nm, n, orderf, N, D, dfun, g, ibarP = fam
        key = nm.rstrip('0123456789+-') or nm
        print("     %-6s N=%-4d D=%-4d 3N-D = %d" % (nm, N, D, 3 * N - D))
    print()
    print("Now check Lemma C EXACTLY on every window group, with the sharper")
    print("minimal-parabolic bound ibar_P (Borel-Tits) -- (|Out|*ibar_P)^3 <= |G|^2 :")
    fails = []
    tight = []
    for nm, w in windows:
        fam = [x for x in famlist(nmax) if x[0] == nm][0]
        _, n, orderf, N, D, dfun, g, ibarP = fam
        for (q, p, f) in w:
            o = orderf(q)
            ou = out_order(fam, q, p, f)
            ib = ibarP(q)
            lhs = (ou * ib) ** 3
            rhs = o * o
            r = Fraction(lhs, rhs)
            if lhs > rhs:
                fails.append((nm, q, ou, ib, o, float(r) ** (1 / 3)))
            tight.append((float(r) ** (1 / 3.0), nm, q, ou, ib, o))
    tight.sort(reverse=True)
    print("   window groups checked: %d ;  FAILURES: %d" % (len(tight), len(fails)))
    for x in fails:
        print("     FAIL %s(%d): |Out|=%d ibar=%d |G|=%d ratio=%.3f" % x)
    print("   tightest 12 rows (ratio = |Out|*ibar / |G|^{2/3}):")
    for r, nm, q, ou, ib, o in tight[:12]:
        print("     %-6s q=%-6d |Out|=%-4d ibar=%-10d |G|=%-14d ratio=%.3f"
              % (nm, q, ou, ib, o, r))
    print()
    # alternating + sporadic
    print("  alternating: iota_ab(A_m) <= C(m,3) (witness <(123)>); check")
    af = []
    for m in range(5, 200):
        o = factorial(m) // 2
        ou = 4 if m == 6 else 2
        ib = comb(m, 3)
        if m == 5:
            ib = 5
        if m == 6:
            ib = 10
        if (ou * ib) ** 3 > o * o:
            af.append(m)
    print("     A_m, 5 <= m <= 199 : failures = %s" % (af or "NONE"))
    print("  sporadic: exact iota table of v_task39 (the value under audit):")
    from v_task81_census import SPOR_OUT
    IOT = {"M11": 55, "M12": 220, "M22": 77, "M23": 253, "M24": 759,
           "J1": 1045, "J2": 280, "J3": 17442, "J4": 173067389,
           "HS": 3850, "McL": 15400, "He": 8330, "Ru": 188500, "Suz": 22880,
           "ON": 2857239, "Co1": 1545600, "Co2": 46575, "Co3": 128800,
           "Fi22": 3510, "Fi23": 31671, "Fi24'": 4860485028, "HN": 1539000,
           "Ly": 9606125, "Th": 283599225, "B": 13571955000,
           "M": 97239461142009186000, "2F4(2)'": 1755}
    sf = []
    worst = (0, "")
    for nm, io in IOT.items():
        o = SPORADIC[nm]
        ou = SPOR_OUT[nm]
        r = (Fraction((ou * io) ** 3, o * o)) ** Fraction(1, 1)
        rr = float(r) ** (1 / 3.0)
        if (ou * io) ** 3 > o * o:
            sf.append(nm)
        if rr > worst[0]:
            worst = (rr, nm)
    print("     sporadic failures = %s ; tightest = %s at ratio %.3f"
          % (sf or "NONE", worst[1], worst[0]))
    print()
    print("  A1 TAIL: Lemma C for L2(q) with ibar=q+1 is exactly "
          "d^5 f^3 (q+1) <= q^2 (q-1)^2 ;")
    a1bad = []
    for (q, p_, f) in prime_powers_upto(3 * 10 ** 6):
        if q < 4:
            continue
        d = gcd(2, q - 1)
        if d ** 5 * f ** 3 * (q + 1) > q * q * (q - 1) ** 2:
            a1bad.append(q)
    print("        exact failures for prime powers q <= 3*10^6 : %s"
          % (a1bad or "NONE"))
    print("        tail: d<=2, f<=log2 q, so it follows from "
          "32 (log2 q)^3 (q+1) <= q^2(q-1)^2,")
    print("        whose RHS/LHS ~ q^3/log^3 q is increasing; true from q=17 on.")
    print()
    print("  sporadic Lemma C using ONLY the elementary bound")
    print("        iota_ab(S) <= |S|/|S|_r (no ATLAS input at all):")
    sf2 = []
    for nm in IOT:
        o = SPORADIC[nm]
        fac = factorise(o)
        best = min(o // (p ** e) for p, e in fac.items())
        if (SPOR_OUT[nm] * best) ** 3 > o * o:
            sf2.append((nm, best))
    print("        failures = %s" % ([x[0] for x in sf2] or "NONE"))
    return fails


# ===================================================================== P2 ===
def part2():
    print("=" * 74)
    print("PART 2  (E1) of v_task52 §4.1 -- the closed form, re-derived")
    print("=" * 74)
    print("Equation: c*|L2(q1)| = |L2(q)|, i.e. c*q1(q1^2-1)/d1 = q(q^2-1)/d,")
    print("with 2 <= c | |Out(L2(q1))| = d1*f1.")
    print()
    print("(i)  q1 = q+1 :  q1^2-1 = q(q+2)  =>  c*d*(q+2) = d1*(q-1)")
    print("(ii) q1 = q-1 :  q1^2-1 = q(q-2)  =>  c*d*(q-2) = d1*(q+1)")
    print("  [derived by cancelling q(q+1) resp. q(q-1) on both sides]")
    print()
    # exhaustive verification of the two reductions as identities
    bad = 0
    for q in range(4, 400):
        for q1 in (q + 1, q - 1):
            if q1 < 2:
                continue
            d = gcd(2, q - 1)
            d1 = gcd(2, q1 - 1)
            for c in range(1, 200):
                lhs = c * q1 * (q1 * q1 - 1) * d
                rhs = q * (q * q - 1) * d1
                if q1 == q + 1:
                    red = (c * d * (q + 2) == d1 * (q - 1))
                else:
                    red = (c * d * (q - 2) == d1 * (q + 1))
                if (lhs == rhs) != red:
                    bad += 1
    print("  identity check (q<400, c<200, both sign families): %d mismatches"
          % bad)
    print()
    print("(i) c*d*(q+2) = d1*(q-1) with c>=2, d>=1, d1<=2:")
    print("      LHS >= 2(q+2) > 2(q-1) >= RHS  ==>  NO SOLUTION, all q. OK")
    print()
    print("(ii) complete integer solve of c*d*(q-2) = d1*(q+1), c >= 2,")
    print("     over ALL prime powers q (not a scan: closed form).")
    print("   * q even  : d = 1, q1 = q-1 odd so d1 = 2  =>  c = 2(q+1)/(q-2)")
    print("               = 2 + 6/(q-2), integral iff (q-2) | 6, i.e.")
    print("               q-2 in {1,2,3,6} i.e. q in {3,4,5,8}; q even: q=4,8.")
    print("   * q odd   : d = 2, q1 = q-1 even so d1 = 1  =>  2c(q-2) = q+1;")
    print("               c >= 2 gives 4(q-2) <= q+1 i.e. q <= 3.")
    sols = []
    for q in range(4, 10 ** 6):
        d = gcd(2, q - 1)
        q1 = q - 1
        if q1 < 4:
            continue
        d1 = gcd(2, q1 - 1)
        num = d1 * (q + 1)
        den = d * (q - 2)
        if num % den == 0:
            c = num // den
            if c >= 2:
                sols.append((q, q1, c))
    print("   brute-force over 4 <= q <= 10^6 (all integers q, a superset of")
    print("   prime powers): solutions (q,q1,c) = %s" % sols)
    print("   filter to q, q1 both prime powers with L2 simple (q,q1 >= 4):")
    from v_task81_census import prime_powers_upto as pp
    pset = set(x[0] for x in pp(10 ** 6))
    real = [(q, q1, c) for (q, q1, c) in sols
            if q in pset and q1 in pset and q1 >= 4]
    print("      %s" % real)
    for (q, q1, c) in real:
        d1 = gcd(2, q1 - 1)
        f1 = 1
        t = q1
        p1 = min(factorise(q1))
        f1 = 0
        while t > 1:
            t //= p1
            f1 += 1
        print("      q=%d q1=%d c=%d ; |Out(L2(%d))| = d1*f1 = %d*%d = %d ; "
              "c | |Out| ? %s"
              % (q, q1, c, q1, d1, f1, d1 * f1, "YES" if (d1 * f1) % c == 0
                 else "NO -> configuration is NOT Fitting-free-admissible"))
    print()
    print("  ==> the ONLY solution of the q1 = q +- 1 sub-branch is")
    print("      (q,q1,c) = (8,7,3), killed by c=3 nmid |Out(L2(7))| = 2.")
    print()
    print("(iii) the km != p^j branch of v_task52 §4.1(d): q <= 2c(k+1)")
    print("      with c <= d1 f1 <= 2 log2(q1), q1 >= 0.777 q / c^(1/3),")
    print("      k <= 4(q+1)/q1.  Largest q consistent with the system:")
    worst = 0
    for q in range(4, 5000):
        cmax = int(2 * log2(2 * q + 2)) + 1
        ok = False
        for c in range(2, cmax + 1):
            # q1 >= (q(q^2-1)/(2c))^(1/3)
            q1min = icbrt(q * (q * q - 1) // (2 * c))
            if q1min < 2:
                q1min = 2
            k = (4 * (q + 1)) // q1min + 1
            if q <= 2 * c * (k + 1):
                ok = True
        if ok:
            worst = q
    print("      largest q for which the system is satisfiable: %d" % worst)
    print("      (v_task52 claims 600; anything <= 10^6 is inside the census)")


# ===================================================================== P3 ===
def part3():
    print("=" * 74)
    print("PART 3  Lemma EQ and Lemma W (v_task54 §2, §4), re-derived")
    print("=" * 74)
    print("Lemma EQ: S1 of Lie type in the DEFINING characteristic p of a")
    print("rank-1 target S.  (E) gives |S1|_p | |S|_p i.e. q1^{N1} <= q^N;")
    print("(F) gives |Out(S1)| * iota(S1) >= iota(S) = q^N + 1.")
    print("With iota(S1) <= 4 q1^{mu1} and |Out(S1)| = d1 f1 g1:")
    print("    4 d1 f1 g1 q1^{mu1} >= q^N + 1 > q^N >= q1^{N1}")
    print("    ==>  q1^{N1-mu1} < 4 d1 f1 g1 .                (Lemma EQ)")
    print("VERDICT on the derivation: valid, PROVIDED iota(S1) <= 4 q1^{mu1},")
    print("i.e. (T2).  Check (T2) exactly, all families, all ranks <= 14, q<=64:")
    F = famlist(14)
    bad = []
    for fam in F:
        nm, n, orderf, N, D, dfun, g, ibarP = fam
        # mu = deg_q of ibarP
        for (q, p, f) in qrange(fam, 64):
            ib = ibarP(q)
            mu = 0
            while q ** (mu + 1) <= ib:
                mu += 1
            # deg is the *nominal* degree; recompute nominal mu from q=large
            pass
        # nominal mu from a large q
        mu = nominal_mu(ibarP)
        for (q, p, f) in qrange(fam, 64):
            if ibarP(q) > 4 * q ** mu:
                bad.append((nm, q, ibarP(q), 4 * q ** mu))
    print("   (T2) violations: %s" % (bad[:10] if bad else "NONE"))
    print()
    print("Lemma P: N - mu = 0 exactly for the rank-1 families; >= 1 else.")
    for fam in F:
        nm, n, orderf, N, D, dfun, g, ibarP = fam
        mu = nominal_mu(ibarP)
        if nm in ("A1", "2B2", "2G2", "U3", "L3", "U4", "C2", "G2", "3D4",
                  "2F4", "L4", "U5", "C3", "B3", "D4+", "E6", "E7", "E8", "F4"):
            print("     %-5s N=%-4d mu=%-3d N-mu=%-4d  theta=D/mu=%s"
                  % (nm, N, mu, N - mu, Fraction(D, mu)))
    print()
    print("Lemma EQ window (rank >= 2, so N1-mu1 >= 1): all (family,q1) with")
    print("   q1^{N1-mu1} < 4 d1 f1 g1 :")
    tot = 0
    for fam in F:
        nm, n, orderf, N, D, dfun, g, ibarP = fam
        mu = nominal_mu(ibarP)
        k = N - mu
        if k <= 0:
            continue
        w = []
        for (q, p, f) in qrange(fam, 4096):
            ou = out_order(fam, q, p, f)
            if q ** k < 4 * ou:
                w.append(q)
        if w:
            print("     %-5s N-mu=%-3d  q1 in %s" % (nm, k, w))
            tot += len(w)
    print("   TOTAL window: %d  (v_task54 reports 71 triples)" % tot)


# ===================================================================== P4 ===
def part4():
    print("=" * 74)
    print("PART 4  rank-1 specifics")
    print("=" * 74)
    print("(a) 3 nmid |Sz(q)|, q = 2^f, f odd:")
    print("    q = 2^f with f odd => q = 2*4^{(f-1)/2} == 2*1 == 2 (mod 3)")
    print("    q-1 == 1, q^2 == 4 == 1 so q^2+1 == 2, and q^2 is a 2-power.")
    bad = [f for f in range(3, 402, 2) if ord_Sz(2 ** f) % 3 == 0]
    print("    exact check f odd, 3 <= f <= 401 : divisible-by-3 = %s"
          % (bad or "NONE"))
    print()
    print("(b) Sz subfield count (Lemma Sz-subfield). f1 | f, f/f1 odd >= 3,")
    print("    so q/q1 >= q1^2 and c = |Sz(q)|/|Sz(q1)| must be <= f1.")
    worst = None
    hits = []
    for f in range(3, 202, 2):
        for f1 in range(3, f, 2):
            if f % f1 or f1 == f:
                continue
            q, q1 = 2 ** f, 2 ** f1
            o, o1 = ord_Sz(q), ord_Sz(q1)
            if o % o1:
                continue
            c = o // o1
            if c <= f1:
                hits.append((f, f1, c))
            r = Fraction(c, f1)
            if worst is None or r < worst[0]:
                worst = (r, f, f1, c)
    print("    pairs with c <= |Out(Sz(q1))| = f1 : %s" % (hits or "NONE"))
    print("    smallest ratio c/f1 seen: %s at (f,f1)=(%d,%d), c=%d"
          % (worst[0], worst[1], worst[2], worst[3]))
    print()
    print("(c) U3 / R cross-characteristic ppmax_{p'}^3 kill (v_task53 §5.2).")
    print("    Claim: c * ppmax_{p'}(|S|)^3 < |S| for q >= 179 (U3), q >= 2187 (R).")
    print("    c <= |Out(S1)| <= 78*f1 with f1 <= log2(ppmax_{p'}).")
    for fam in ("U3", "R"):
        firstok = None
        lastbad = 0
        for (q, p, f) in prime_powers_upto(4000):
            if fam == "U3":
                if q < 3:
                    continue
                e = gcd(3, q + 1)
                S = q ** 3 * (q * q - 1) * (q ** 3 + 1) // e
                pp_ = 2 * (q + 1) ** 2
            else:
                if p != 3 or f % 2 == 0 or f < 3:
                    continue
                S = ord_Ree(q)
                pp_ = q * q - q + 1
            f1cap = max(1, int(log2(pp_)) + 1)
            c = 78 * f1cap
            if c * pp_ ** 3 < S:
                if firstok is None:
                    firstok = q
            else:
                lastbad = q
                firstok = None
        print("    %-4s : kill valid for all q > %d  (first q from which it "
              "holds for all larger scanned q: %s)" % (fam, lastbad, firstok))
    print()
    print("(d) exact ppmax bounds of v_task53 Input 4, re-derived numerically:")
    for fam in ("U3", "Sz", "R"):
        worstr = (Fraction(0), 0)
        for (q, p, f) in prime_powers_upto(400):
            if fam == "U3":
                if q < 3:
                    continue
                e = gcd(3, q + 1)
                S = q ** 3 * (q * q - 1) * (q ** 3 + 1) // e
                bound = max(q ** 3, 2 * (q + 1) ** 2)
            elif fam == "Sz":
                if p != 2 or f % 2 == 0 or f < 3:
                    continue
                S = ord_Sz(q)
                bound = q * q + 1
            else:
                if p != 3 or f % 2 == 0 or f < 3:
                    continue
                S = ord_Ree(q)
                bound = q ** 3
            fac = factorise(S)
            ppm = max(p_ ** e_ for p_, e_ in fac.items())
            r = Fraction(ppm, bound)
            if r > worstr[0]:
                worstr = (r, q)
            if ppm > bound:
                print("     VIOLATION %s q=%d ppmax=%d > bound=%d"
                      % (fam, q, ppm, bound))
        print("     %-4s : max ppmax/bound = %s at q=%d  (<=1 means bound holds)"
              % (fam, worstr[0], worstr[1]))
    print()
    print("(e) THE ALTERNATING-SOCLE BRANCH for U3 / R  (v_task53 §5.4 claims")
    print("    'complete in q' because |Out(A_m)| <= 4; but the scan only")
    print("    enumerated A_m with |A_m| <= 10^80, which is NOT all m).")
    print("    Independent uniform repair: the floor (F) with iota_ab(A_m)")
    print("    <= C(m,3) forces  |Out(A_m)| * C(m,3) >= iota(S) = q^N+1,")
    print("    hence m is bounded BELOW by ~ (3 q^N / |Out|)^{1/3}; while")
    print("    (E) forces c*|A_m| = |S| <= q^a, bounding m ABOVE.")
    for fam, N, a in (("U3", 3, 8), ("R", 3, 7)):
        firstok = None
        bad = []
        for (q, p, f) in prime_powers_upto(3000):
            if fam == "U3":
                if q < 3:
                    continue
                e = gcd(3, q + 1)
                S = q ** 3 * (q * q - 1) * (q ** 3 + 1) // e
            else:
                if p != 3 or f % 2 == 0 or f < 3:
                    continue
                S = ord_Ree(q)
            iota = q ** N + 1
            # smallest m with |Out(A_m)|*C(m,3) >= iota
            m = 5
            while True:
                ou = 4 if m == 6 else 2
                ib = 5 if m == 5 else (10 if m == 6 else comb(m, 3))
                if ou * ib >= iota:
                    break
                m += 1
                if m > 4000:
                    break
            mmin = m
            # (E): c*|A_m| = |S| with c >= 2 => |A_m| <= |S|/2
            ok = factorial(mmin) // 2 > S // 2
            if not ok:
                bad.append((q, mmin))
        print("    %-4s : q where the floor does NOT already kill every "
              "alternating socle: %s" % (fam, bad or "NONE"))
    print("    (a non-empty list means those q need the finite scan; an empty")
    print("     list means the alternating branch is closed for ALL q by proof)")


# ===================================================================== P5 ===
def part5():
    print("=" * 74)
    print("PART 5  (E2) and (E3) windows of v_task52 §4.2 / §4.3")
    print("=" * 74)
    print("(E2): Soc T = L2(q1)^2.  |L2(q1)|^2 <= |L2(q)| and the floor")
    print("      2*|Out(L2(q1))|*(q1+1) >= q+1, i.e. 4 f1 (q1+1) >= q+1.")
    lastbad = 0
    for q in range(4, 20000):
        # q1 <= (64 q^3/9)^{1/6}: use exact test |L2(q1)|^2 <= |L2(q)|
        d = gcd(2, q - 1)
        N = q * (q * q - 1) // d
        q1 = 2
        best = 0
        while True:
            d1 = gcd(2, q1 - 1)
            o1 = q1 * (q1 * q1 - 1) // d1
            if o1 * o1 > N:
                break
            f1 = int(log2(q1)) + 1
            if 4 * f1 * (q1 + 1) >= q + 1:
                best = max(best, q1)
            q1 += 1
        if best:
            lastbad = q
    print("      largest q for which SOME q1 satisfies both: %d" % lastbad)
    print("      (v_task52 claims the branch is empty for q > 839)")
    print()
    print("(E3): Soc T = A_m^l, l <= 2.  Lemma K: 2-part of |L2(q)| <= q+1,")
    print("      while |A_m|^l contributes 2^{l(v2(m!)-1)} >= 2^{v2(m!)-1};")
    print("      and the floor gives q+1 <= 2*|Out(A_m)|*C(m,3).")
    print("      So 2^{v2(m!)-1} <= 2*|Out(A_m)|*C(m,3):")
    def v2fact(m):
        s, k = 0, 2
        while k <= m:
            s += m // k
            k *= 2
        return s
    bad = []
    for m in range(5, 120):
        ou = 4 if m == 6 else 2
        if 2 ** (v2fact(m) - 1) <= 2 * ou * comb(m, 3):
            bad.append(m)
    print("      m satisfying the inequality: %s" % bad)
    print("      (v_task52 claims it fails for every m > 15)")


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    if which in ("all", "1"):
        part1()
        print()
    if which in ("all", "2"):
        part2()
        print()
    if which in ("all", "3"):
        part3()
        print()
    if which in ("all", "4"):
        part4()
        print()
    if which in ("all", "5"):
        part5()
        print()
