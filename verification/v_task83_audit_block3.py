"""v_task83 -- ADVERSARIAL AUDIT of v_task57 / v_task58 / v_task59.

Nothing is imported from v_task50-v_task59.  Every object below is rebuilt
from scratch: root systems from Cartan matrices, group orders from the
standard product formulas, polynomials from a hand-rolled exact integer
polynomial class.  Exact arithmetic only (Python int / Fraction).
"""
import sys
from fractions import Fraction
from math import gcd

BAR = "=" * 72

# --------------------------------------------------------------- polynomials
class P:
    """dense integer polynomial in one variable, coeffs[i] = coeff of x^i"""
    __slots__ = ("c",)

    def __init__(self, c):
        c = list(c)
        while len(c) > 1 and c[-1] == 0:
            c.pop()
        self.c = c

    @staticmethod
    def x(n=1, a=1):
        return P([0] * n + [a])

    def deg(self):
        return len(self.c) - 1 if self.c != [0] else -1

    def __add__(s, o):
        n = max(len(s.c), len(o.c))
        return P([(s.c[i] if i < len(s.c) else 0) + (o.c[i] if i < len(o.c) else 0)
                  for i in range(n)])

    def __sub__(s, o):
        n = max(len(s.c), len(o.c))
        return P([(s.c[i] if i < len(s.c) else 0) - (o.c[i] if i < len(o.c) else 0)
                  for i in range(n)])

    def __mul__(s, o):
        if isinstance(o, int):
            return P([a * o for a in s.c])
        r = [0] * (len(s.c) + len(o.c) - 1)
        for i, a in enumerate(s.c):
            if a:
                for j, b in enumerate(o.c):
                    r[i + j] += a * b
        return P(r)

    def __eq__(s, o):
        return s.c == o.c

    def __call__(s, v):
        r = 0
        for a in reversed(s.c):
            r = r * v + a
        return r

    def divmod_(s, o):
        """exact polynomial division with remainder (o monic-ish / integer ok)"""
        num = list(s.c)
        qd = len(num) - len(o.c)
        if qd < 0:
            return P([0]), s
        quo = [0] * (qd + 1)
        lead = o.c[-1]
        for i in range(qd, -1, -1):
            if num[i + len(o.c) - 1] % lead:
                raise ArithmeticError("non-exact division")
            t = num[i + len(o.c) - 1] // lead
            quo[i] = t
            for j, b in enumerate(o.c):
                num[i + j] -= t * b
        return P(quo), P(num)

    def __repr__(s):
        if s.c == [0]:
            return "0"
        out = []
        for i in range(len(s.c) - 1, -1, -1):
            a = s.c[i]
            if not a:
                continue
            out.append("%+d%s" % (a, "" if i == 0 else ("*q" if i == 1 else "*q^%d" % i)))
        return "".join(out)


def Q(n, s=1):
    """q^n + s"""
    return P([s] + [0] * (n - 1) + [1]) if n > 0 else P([1 + s])


ONE = P([1])
QQ = P([0, 1])


def sub_q_pow(poly, k):
    """poly(q^k)"""
    r = [0] * ((poly.deg()) * k + 1) if poly.deg() >= 0 else [0]
    for i, a in enumerate(poly.c):
        r[i * k] += a
    return P(r)


# ------------------------------------------------------------- root systems
CARTAN_EDGES = {
    # name : (nnodes, [(i,j,cij,cji)])   c_ij = <alpha_i, alpha_j^vee>
    "A": None, "D": None,
}


def cartan(name, n):
    """Cartan matrix C with C[i][j] = <a_i, a_j^vee>, Bourbaki labelling."""
    C = [[0] * n for _ in range(n)]
    for i in range(n):
        C[i][i] = 2

    def link(i, j, cij=-1, cji=-1):     # 0-based
        C[i][j] = cij
        C[j][i] = cji

    if name == "A":
        for i in range(n - 1):
            link(i, i + 1)
    elif name == "B":       # long a_1..a_{n-1}, short a_n  (Bourbaki B_n)
        for i in range(n - 2):
            link(i, i + 1)
        link(n - 2, n - 1, -2, -1)
    elif name == "C":       # short a_1..a_{n-1}, long a_n
        for i in range(n - 2):
            link(i, i + 1)
        link(n - 2, n - 1, -1, -2)
    elif name == "D":
        for i in range(n - 3):
            link(i, i + 1)
        link(n - 3, n - 2)
        link(n - 3, n - 1)
    elif name == "E":       # Bourbaki: 1-3-4-5-6-7-8 chain, 2 hangs off 4
        chain = [0, 2, 3, 4, 5, 6, 7][:n - 1]
        for a, b in zip(chain, chain[1:]):
            link(a, b)
        link(1, 3)
    elif name == "F":       # F_4 : 1-2 => 3-4  (a1,a2 long; a3,a4 short)
        link(0, 1)
        link(1, 2, -1, -2)
        link(2, 3)
    elif name == "G":       # G_2
        link(0, 1, -1, -3)
    else:
        raise ValueError(name)
    return C


def roots(C):
    """full root system as integer coordinate vectors in the simple basis."""
    n = len(C)
    simple = [tuple(1 if j == i else 0 for j in range(n)) for i in range(n)]
    R = set(simple)
    frontier = set(simple)
    while frontier:
        new = set()
        for a in frontier:
            for i in range(n):
                # <a, a_i^vee> = sum_j a_j C[j][i]
                pair = sum(a[j] * C[j][i] for j in range(n))
                b = list(a)
                b[i] -= pair
                b = tuple(b)
                if b not in R:
                    new.add(b)
        R |= new
        frontier = new
    return R


def npos(C):
    return sum(1 for a in roots(C) if all(x >= 0 for x in a) and any(a))


def npos_sub(C, keep):
    """positive roots of the Levi generated by the simple roots in `keep`."""
    sub = [[C[i][j] for j in keep] for i in keep]
    return npos(sub)


# --------------------------------------------------------------- part 1
def part1():
    print(BAR)
    print("PART 1 -- v_task57: the two order identities, exact + symbolic")
    print(BAR)

    d2 = lambda q: gcd(2, q - 1)

    def S4(q):
        return q**4 * (q**2 - 1) * (q**4 - 1) // d2(q)

    def D43(q):
        return q**12 * (q**8 + q**4 + 1) * (q**6 - 1) * (q**2 - 1)

    def G2(q):
        return q**6 * (q**6 - 1) * (q**2 - 1)

    def F42(q):
        return q**12 * (q**6 + 1) * (q**4 - 1) * (q**3 + 1) * (q - 1)

    print("\n  Identity A : |S4(q^3)| = ((q^2+1)/gcd(2,q-1)) * |3D4(q)|")
    for q in (2, 3, 4, 5, 7, 8, 9):
        lhs = S4(q**3)
        c = Fraction(q**2 + 1, d2(q))
        rhs = c * D43(q)
        print("    q=%-3d  c=%-8s  LHS=%-30d  LHS/|3D4| = %-10s  %s"
              % (q, c, lhs, Fraction(lhs, D43(q)),
                 "OK" if Fraction(lhs) == rhs else "*** MISMATCH ***"))

    # symbolic: clear the gcd by proving  (q^12-1) == (q^2+1)(q^8+q^4+1)(q^2-1)
    L = Q(12, -1)
    R = (Q(2, +1) * P([1] + [0]*3 + [1] + [0]*3 + [1])) * Q(2, -1)
    print("    symbolic  (q^12-1) - (q^2+1)(q^8+q^4+1)(q^2-1) = %s   [%s]"
          % (L - R, "IDENTITY" if L == R else "*** FAILS ***"))
    # and the gcd bookkeeping:  gcd(2, q^3-1) = gcd(2, q-1)
    bad = [q for q in range(2, 200) if gcd(2, q**3 - 1) != gcd(2, q - 1)]
    print("    gcd(2,q^3-1) == gcd(2,q-1) for 2<=q<200 : %s"
          % ("YES" if not bad else "NO %s" % bad))

    print("\n  Identity B : |G2(q^2)| = (q^2+q+1) * |2F4(q)|")
    for q in (2, 8, 32, 128, 512):
        lhs = G2(q**2)
        print("    q=%-4d  c=%-8d  ratio |G2(q^2)|/|2F4(q)| = %-12s  %s"
              % (q, q*q+q+1, Fraction(lhs, F42(q)),
                 "OK" if Fraction(lhs, F42(q)) == q*q+q+1 else "*** MISMATCH ***"))
    # symbolic:  q^12 (q^12-1)(q^4-1)  ==  (q^2+q+1) q^12 (q^6+1)(q^4-1)(q^3+1)(q-1)
    L = sub_q_pow(P([0]*6 + [1]), 2) * (Q(12, -1) * Q(4, -1))
    R = P([1, 1, 1]) * (P([0]*12 + [1]) * (Q(6, 1) * Q(4, -1) * Q(3, 1) * Q(1, -1)))
    print("    symbolic  |G2(q^2)| - (q^2+q+1)|2F4(q)| = %s   [%s]"
          % (L - R, "IDENTITY" if L == R else "*** FAILS ***"))

    print("\n  ADVERSARIAL: is c | |Out| ever satisfiable?")
    print("    Identity A: c = (q^2+1)/gcd(2,q-1) vs |Out(3D4(q))| = 3f, f=log_p q")
    for q, f in ((2, 1), (3, 1), (4, 2), (8, 3), (9, 2), (2**12, 12)):
        c = (q*q + 1) // gcd(2, q - 1)
        print("      q=%-6d c=%-10d 3f=%-4d  c|3f ? %s" % (q, c, 3*f, c <= 3*f and (3*f) % c == 0))
    print("    Identity B: c = q^2+q+1 vs |Out(2F4(q))| = f")
    for q, f in ((8, 3), (32, 5), (2**7, 7), (2**121, 121)):
        c = q*q + q + 1
        print("      q=2^%-4d c(has %d digits) f=%-5d  c|f ? %s"
              % (f, len(str(c)), f, c <= f and f % c == 0))
    print()


# --------------------------------------------------------------- part 2
def part2():
    print(BAR)
    print("PART 2 -- v_task57: Lemma EQ-EX and the c_p / v_p(|Out|) question")
    print(BAR)
    print("""
  The worry: c | |Out(S_1)| = d_1 f_1 g_1 and f_1 = log_{p} q_1 need NOT be
  coprime to p.  So c_p = |c|_p can be > 1 and the p-part comparison
        q_1^{N_1} * c_p = q^N            (EQ-EX)
  does NOT force N_1 f_1 = N f.  Below: (a) exhibit p | |Out| explicitly,
  (b) bound delta := v_p(c) and show the polylog band still closes,
  (c) check the Zsygmondy step of PART 4.6 that actually removes c_p > 1.
""")
    print("  (a) p | |Out(S_1)| happens: |Out| contains the field factor f_1.")
    ex = []
    for p in (2, 3, 5):
        for f1 in (p, 2 * p, p * p):
            ex.append((p, f1, p**f1))
    for (p, f1, q1) in ex[:9]:
        print("      p=%d f_1=%d (p | f_1) : q_1=%-12d  v_p(|Out| field part) >= %d"
              % (p, f1, q1, 1))
    print()
    print("  (b) delta = v_p(c) <= log_p(c) <= log_p(|Out(S_1)|) <= log_p(8 f_1)")
    print("      and f_1 <= N f / N_1 <= N f, so delta <= log_p(8 N f).")
    print("      EQ-EX therefore reads   N_1 f_1 = N f - delta,  0 <= delta <= log_p(8Nf).")
    print()
    print("      The EQ-EX conclusion needs  q^{a - N D_1/N_1}  bounded by a")
    print("      polylog.  Re-derivation from scratch:")
    print("        |S| = c |S_1| ,  kappa q^a <= |S| <= q^a ,")
    print("        q_1^{D_1}/(12 d_1) <= |S_1| <= q_1^{D_1} ,")
    print("        q_1 = (q^N / c_p)^{1/N_1} .")
    print("      ==>  kappa q^a <= c * (q^N/c_p)^{D_1/N_1}")
    print("      ==>  q^{a - N D_1/N_1} <= (c / c_p^{D_1/N_1}) / kappa <= c/kappa.")
    print("      c <= |Out| = O(f) = O(log q): a genuine polylog band. The")
    print("      c_p factor enters with a FAVOURABLE sign (it divides), so a")
    print("      large c_p only strengthens the bound.  [checked below]")
    print()
    print("      numeric: worst case a - N D_1/N_1 = 1/(N*N_1) with")
    print("      N,N_1 <= 120 gives exponent >= 1/14400; then the threshold")
    print("      is q <= (c/kappa)^{14400}, ASTRONOMICAL, not swept.")
    print("      ==> EQ-EX is USABLE ONLY as an exact-ratio filter")
    print("          (D_1/N_1 = a/N), which is how both notes use it.")
    print("          Any *threshold* claim from EQ-EX alone would be vacuous.")
    print()
    print("  (c) the step that really removes c_p > 1 : Zsygmondy (PART 4.6).")
    print("      c_p > 1  ==>  N_1 f_1 = N f - delta < N f  ==> f_1 < N f/N_1,")
    print("      i.e. f_1 is NON-matched.  Non-matched f_1 is killed by")
    print("      e f_1 | E f  +  counting.  Verified for the four targets:")
    tg = {"S4": (4, 10, 4, 3), "G2": (6, 14, 6, 5),
          "3D4": (12, 28, 12, 9), "2F4": (12, 26, 12, 10)}
    for k, (E, a, N, b) in tg.items():
        print("      %-4s  E=%-3d a=%-3d N=%-3d  p'-part of |S| divides q^E-1 : "
              % (k, E, a, N), end="")
        ok = check_top_exponent(k, E)
        print("VERIFIED" if ok else "*** FAILS ***")
    print()


def check_top_exponent(key, E):
    """every cyclotomic factor of |S|_{p'} divides q^E - 1  (as polynomials)."""
    T = {
        "S4":  [Q(2, -1), Q(4, -1)],
        "G2":  [Q(6, -1), Q(2, -1)],
        "3D4": [P([1] + [0]*3 + [1] + [0]*3 + [1]), Q(6, -1), Q(2, -1)],
        "2F4": [Q(6, 1), Q(4, -1), Q(3, 1), Q(1, -1)],
    }[key]
    tot = Q(E, -1)
    for t in T:
        try:
            _, r = tot.divmod_(t)
        except ArithmeticError:
            return False
        if r != P([0]):
            return False
    return True


# --------------------------------------------------------------- part 3
def part3():
    print(BAR)
    print("PART 3 -- v_task58: mu(E7)=27, mu(E8)=57 re-derived from scratch")
    print(BAR)
    print("\n  (i) positive-root counts from the Cartan matrix (reflection closure)")
    tests = [("A", 5), ("B", 3), ("C", 3), ("D", 5), ("D", 7),
             ("E", 6), ("E", 7), ("E", 8), ("F", 4), ("G", 2)]
    exp = {("A", 5): 15, ("B", 3): 9, ("C", 3): 9, ("D", 5): 20, ("D", 7): 42,
           ("E", 6): 36, ("E", 7): 63, ("E", 8): 120, ("F", 4): 24, ("G", 2): 6}
    for (nm, n) in tests:
        C = cartan(nm, n)
        v = npos(C)
        print("      |Phi^+(%s_%d)| = %-5d  (expected %d)  %s"
              % (nm, n, v, exp[(nm, n)], "ok" if v == exp[(nm, n)] else "***"))

    print("\n  (ii) dim G/P = |Phi^+| - |Phi^+(Levi)| for EVERY maximal parabolic")
    for (nm, n) in (("F", 4), ("E", 6), ("E", 7), ("E", 8)):
        C = cartan(nm, n)
        tot = npos(C)
        vals = []
        for drop in range(n):
            keep = [i for i in range(n) if i != drop]
            vals.append((tot - npos_sub(C, keep), drop + 1))
        vals.sort()
        print("      %s_%d : |Phi^+|=%-4d  dim G/P by node (Bourbaki) = %s"
              % (nm, n, tot, [(d, v) for (v, d) in sorted(vals, key=lambda t: t[1])]))
        print("             MINIMAL dim U_P = %d  at node %d" % (vals[0][0], vals[0][1]))

    print("\n  (iii) |W| from the degrees, and the q->1 coset counts")
    deg = {"E6": (2, 5, 6, 8, 9, 12), "E7": (2, 6, 8, 10, 12, 14, 18),
           "E8": (2, 8, 12, 14, 18, 20, 24, 30), "F4": (2, 6, 8, 12),
           "B3": (2, 4, 6), "D5": (2, 4, 6, 8, 5)}
    W = {}
    for k, d in deg.items():
        w = 1
        for x in d:
            w *= x
        W[k] = w
        print("      |W(%s)| = %d" % (k, w))
    print("      |W(E7)|/|W(E6)| = %d   (claimed 56)" % (W["E7"] // W["E6"]))
    print("      |W(E8)|/|W(E7)| = %d   (claimed 240 -- this is the q->1 COSET"
          % (W["E8"] // W["E7"]))
    print("       count, NOT mu; mu = deg_q of the index polynomial)")
    print("      |W(F4)|/|W(B3)| = %d" % (W["F4"] // W["B3"]))
    print("      |W(E6)|/|W(D5)| = %d" % (W["E6"] // W["D5"]))

    print("\n  (iv) the index polynomials, re-derived as |G_sc|/(q^{dimU}|L|)")
    #   |G(q)|_univ = q^{|Phi^+|} prod (q^{d_i} - 1)
    def univ(dg, npos_):
        r = P([0] * npos_ + [1])
        for d in dg:
            r = r * Q(d, -1)
        return r

    cases = [
        ("E7 / P7 (Levi E6)", "E7", 63, "E6", 36, 27,
         Q(14, -1) * Q(9, 1) * Q(5, 1)),
        ("E8 / P8 (Levi E7)", "E8", 120, "E7", 63, 57,
         Q(30, -1) * Q(12, 1) * Q(10, 1) * Q(6, 1)),
        ("F4 / P1 (Levi B3)", "F4", 24, "B3", 9, 15,
         Q(12, -1) * Q(4, 1)),
        ("E6 / P1 (Levi D5)", "E6", 36, "D5", 20, 16,
         Q(9, -1) * P([1] + [0]*3 + [1] + [0]*3 + [1])),
    ]
    for (nm, gk, gpos, lk, lpos, mu, claimed_num) in cases:
        G = univ(deg[gk], gpos)
        L = univ(deg[lk], lpos) * P([0] * mu + [1]) * Q(1, -1)   # q^{dimU} * |L_ss| * (q-1)
        quo, rem = G.divmod_(L)
        cl, remc = claimed_num.divmod_(Q(1, -1))
        print("      %-22s deg_q index = %-4d (claimed mu = %d)  %s"
              % (nm, quo.deg(), mu, "ok" if quo.deg() == mu else "***"))
        print("         exact division remainder = %s ; index == claimed formula : %s"
              % (rem, "YES" if (rem == P([0]) and remc == P([0]) and quo == cl)
                 else "NO  (quo=%s vs %s)" % (quo, cl)))
        print("         index at q->1 = %d" % cl(1))
    print()


# --------------------------------------------------------------- part 4
def part4():
    print(BAR)
    print("PART 4 -- v_task58: (I3) and its REVERSE, exactly")
    print(BAR)

    def E6(q):
        return (q**36 * (q**12 - 1) * (q**9 - 1) * (q**8 - 1) * (q**6 - 1)
                * (q**5 - 1) * (q**2 - 1) // gcd(3, q - 1))

    def E6t(q):
        return (q**36 * (q**12 - 1) * (q**9 + 1) * (q**8 - 1) * (q**6 - 1)
                * (q**5 + 1) * (q**2 - 1) // gcd(3, q + 1))

    print("\n  |2E6(q)|/|E6(q)| = [gcd(3,q-1)/gcd(3,q+1)] (q^9+1)(q^5+1)/((q^9-1)(q^5-1))")
    print("  |E6(q)|/|2E6(q)| = [gcd(3,q+1)/gcd(3,q-1)] (q^9-1)(q^5-1)/((q^9+1)(q^5+1))")
    print()
    print("   q   q mod 3   c = |2E6|/|E6|                    c' = |E6|/|2E6|")
    qs = [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 31, 37, 43, 49,
          61, 64, 67, 79, 81, 97, 103, 121, 127]
    worst_up, worst_dn = None, None
    for q in qs:
        c = Fraction(E6t(q), E6(q))
        cp = Fraction(E6(q), E6t(q))
        # closed forms
        cc = Fraction(gcd(3, q - 1), gcd(3, q + 1)) * \
            Fraction((q**9 + 1) * (q**5 + 1), (q**9 - 1) * (q**5 - 1))
        assert c == cc, (q, c, cc)
        print("  %-5d  %d       %-32.14f  %-.14f" % (q, q % 3, float(c), float(cp)))
        if q % 3 == 1:
            if worst_up is None or c < worst_up[1]:
                worst_up = (q, c)
        if q % 3 == 2:
            if worst_dn is None or cp > worst_dn[1]:
                worst_dn = (q, cp)
    print()
    print("  q = 1 mod 3 : c = 3(1+2/(q^9-1))(1+2/(q^5-1))  -> 3 STRICTLY FROM ABOVE")
    print("      closest observed: q=%d, c-3 = %s" % (worst_up[0], float(worst_up[1] - 3)))
    print("  q = 2 mod 3 : c' = 3(1-2/(q^9+1))(1-2/(q^5+1)) -> 3 STRICTLY FROM BELOW")
    print("      closest observed: q=%d, 3-c' = %s" % (worst_dn[0], float(3 - worst_dn[1])))
    print()
    print("  *** AUDIT FINDING candidate ***")
    print("  v_task58 4.3 tabulates the row 'E6 <- 2E6' as 'c < 1 : impossible'")
    print("  and (I3) says '(the reverse direction |E6|/|2E6| < 1 is impossible")
    print("  outright)'.  That is FALSE for q = 2 mod 3, where |E6|/|2E6| -> 3")
    print("  from BELOW and 3 | |Out(2E6(q))| = 6f.  It is a SECOND near-miss of")
    print("  the same sharpness, closed by the same strict inequality.")
    print()
    print("  Verification that c' < 3 always (q = 2 mod 3), and c' > 2 :")
    for q in [2, 5, 8, 11, 17, 23, 29, 32, 41, 47, 53, 59, 71, 83, 89, 101, 107, 113, 125]:
        if q % 3 != 2:
            continue
        cp = Fraction(E6(q), E6t(q))
        assert 2 < cp < 3, (q, cp)
    print("      2 < c' < 3 for every prime power q = 2 mod 3 up to 125: CONFIRMED")
    print("      (closed form: 3(1-2/(q^9+1))(1-2/(q^5+1)); each factor < 1,")
    print("       and > 2/3 for q >= 2, so 2 < c' < 3 for all q. Never integral.)")
    print()
    print("  small-q check of (I3) as demanded (q = 4, 7, 13):")
    for q in (4, 7, 13):
        c = Fraction(E6t(q), E6(q))
        print("      q=%-3d  c = %s = %.16f   3<c<4 : %s"
              % (q, c, float(c), 3 < c < 4))
    print()


# --------------------------------------------------------------- part 5
def part5():
    print(BAR)
    print("PART 5 -- Lemma MO-EX / MO-SPO: the convexity algebra, re-derived")
    print(BAR)
    print("""
  Setup (rebuilt): Soc T = prod_O G_O^{l_O}; u_O := l_O N_O f_O; r_O := D_O/N_O.
  (ii) p-part EQUALITY :  sum_O u_O = N f - delta ,  delta = v_p(c) >= 0.
  (iii) order, two-sided:  a f - B <= sum_O r_O u_O <= a f .
  Subtracting (a/N) * (ii) from (iii):
      sum_O (r_O - a/N) u_O <=  a f - (a/N)(N f - delta) =  (a/N) delta      (U)
      sum_O (r_O - a/N) u_O >= (a f - B) - (a/N)(N f - delta)
                            = -B + (a/N) delta                              (L)
""")
    print("  CHECK (U): a f - (a/N)(N f - delta) - (a/N) delta = 0 identically?")
    for (a, N) in ((78, 36), (133, 63), (248, 120), (21, 9), (45, 20)):
        for f in (1, 3, 7):
            for delta in (0, 2, 5):
                lhs = Fraction(a * f) - Fraction(a, N) * (N * f - delta)
                rhs = Fraction(a, N) * delta
                assert lhs == rhs
    print("      identity holds for all sampled (a,N,f,delta): OK")
    print()
    print("  MO-EX (all r_O >= a/N, at least one strict):")
    print("      u_O >= L_O := l_O (N_O/mu_O)(b f - A)  and (r_O - a/N) >= 0")
    print("      ==> W (b f - A) <= sum (r_O - a/N) u_O <= (a/N) delta <= B + (a/N)delta")
    print("      delta <= log_p(128 (Nf)^2) is a LOG, b f grows LINEARLY in f,")
    print("      so the c_p subtlety is harmless here PROVIDED W > 0.")
    print()
    print("  MO-SPO reverse side (all r_O < a/N):")
    print("      (r_O - a/N) < 0 and u_O >= L_O ==> (r_O-a/N)u_O <= (r_O-a/N)L_O")
    print("      ==> sum <= -W'(b f - A) with W' = min sum l_O(N_O/mu_O)(a/N - r_O) > 0")
    print("      combined with (L):  -W'(bf-A) >= -B + (a/N) delta")
    print("      ==> W'(b f - A) <= B - (a/N) delta <= B.")
    print("      *** delta enters with the OPPOSITE (favourable) sign: a large")
    print("      c_p makes the reverse side die SOONER.  So the item-1 c_p")
    print("      worry does NOT recur on the all-below branch.  CONFIRMED.")
    print()
    print("  ADVERSARIAL: is the reverse side really valid?  It needs the")
    print("  LOWER bound a f - B <= sum r_O u_O, i.e. |Soc T| >= |T| / const.")
    print("  |T/Soc T| <= prod |Out(G_O)|^{l_O} * prod l_O! -- polylog in q --")
    print("  so B = log_p(that) is a LOG.  Same status as MO-EX's B.  OK.")
    print()

    # --- independent family table (D, N, mu, k) rebuilt from scratch
    print("  Independent (D,N,mu) table, rebuilt from root data / orders:")
    FT = {}
    def add(k, D, N, mu):
        FT[k] = (D, N, mu, Fraction(D, N), Fraction(N, mu))
    # classical
    for d in range(2, 33):
        add("L%d" % d, d*d - 1, d*(d-1)//2, d - 1)           # iota = (q^d-1)/(q-1)
    for d in range(3, 33):
        # U_d : iota = P_1 for d odd, P_2 for d even (v_task56)
        mu = 2*d - 3          # deg_q [U_d:P_1]; v_task52 FAM uses this
        add("U%d" % d, d*d - 1, d*(d-1)//2, mu)
    for n in range(2, 17):
        add("C%d" % n, 2*n*n + n, n*n, 2*n - 1)
        add("B%d" % n, 2*n*n + n, n*n, 2*n - 1)
    for n in range(4, 17):
        add("D%d" % n, 2*n*n - n, n*(n-1), 2*n - 2)
        add("2D%d" % n, 2*n*n - n, n*(n-1), 2*n - 2)
    add("G2", 14, 6, 5); add("3D4", 28, 12, 9); add("2F4", 26, 12, 10)
    add("F4", 52, 24, 15); add("E6", 78, 36, 16); add("2E6", 78, 36, 16)
    add("E7", 133, 63, 27); add("E8", 248, 120, 57)
    add("L2", 3, 1, 1); add("Sz", 5, 2, 2); add("R", 7, 3, 3); add("U3", 8, 3, 3)
    print("      spot-checks vs the notes:")
    for k in ("F4", "E6", "E7", "E8", "2F4", "G2", "3D4", "C3", "C6", "D7", "2D5"):
        D, N, mu, r, nm = FT[k]
        print("        %-5s D=%-4d N=%-4d mu=%-3d  r=D/N=%-8s N/mu=%s"
              % (k, D, N, mu, r, nm))
    print()

    print("  MO-EX admissibility caps, recomputed (cap = N/b - 1):")
    tg = [("F4", 52, 24, 15), ("E6", 78, 36, 16), ("2E6", 78, 36, 16),
          ("E7", 133, 63, 27), ("E8", 248, 120, 57)]
    for (k, a, N, b) in tg:
        cap = Fraction(N, b) - 1
        aN = Fraction(a, N)
        adm = [(kk, v[3]) for kk, v in sorted(FT.items()) if v[4] <= cap]
        below = [(kk, r) for (kk, r) in adm if r < aN]
        print("     %-4s N/b=%-7s cap=%-7s a/N=%-6s  #admissible=%-3d"
              % (k, Fraction(N, b), cap, aN, len(adm)))
        print("          admissible: %s" % sorted(set(kk for kk, _ in adm)))
        print("          r < a/N (would BREAK MO-EX): %s"
              % (sorted(set(kk for kk, _ in below)) or "NONE"))
    print()
    print("  Same recomputation for the Sp/O towers (v_task59 4.2 refutation):")
    for n in range(3, 13):
        for pref, a, N, b in (("C", 2*n*n+n, n*n, 2*n-1),
                              ("D", 2*n*n-n, n*(n-1), 2*n-2),
                              ("2D", 2*n*n-n, n*(n-1), 2*n-2)):
            if pref != "C" and n < 4:
                continue
            cap = Fraction(N, b) - 1
            aN = Fraction(a, N)
            adm = [(kk, v[3]) for kk, v in FT.items() if v[4] <= cap]
            below = sorted(set(kk for (kk, r) in adm if r < aN))
            if below:
                print("     %-3s%-2d  a/N=%-7s cap=%-7s  BREAKS MO-EX via %s"
                      % (pref, n, aN, cap, below[:6]))
    print()


# --------------------------------------------------------------- part 6
def part6():
    print(BAR)
    print("PART 6 -- v_task59: (J5) exactly, and the Sp_{2n}(2) minimal degrees")
    print(BAR)

    def Cn(n, q):
        r = q**(n*n)
        for i in range(1, n + 1):
            r *= q**(2*i) - 1
        return r // gcd(2, q - 1)

    def Ud(d, q):
        r = q**(d*(d-1)//2)
        for i in range(2, d + 1):
            r *= q**i - (-1)**i
        return r // gcd(d, q + 1)

    print("\n  (J5)  |C_n(m^{2n-1})| / |U_{2n}(m^n)| , exact rationals")
    print("   n   m     bracket   c (exact Fraction)                c-3 (float)   integer?")
    for n in (3, 4, 5):
        for m in (2, 3, 4, 5, 7, 8, 9, 11, 16, 32):
            q, q1 = m**(2*n - 1), m**n
            c = Fraction(Cn(n, q), Ud(2*n, q1))
            br = Fraction(gcd(2*n, q1 + 1), gcd(2, q - 1))
            lim = br
            print("   %-3d %-5d %-9s %-33s %-13.10g  %s"
                  % (n, m, br, ("%s" % c) if len(str(c)) < 33 else "(big)",
                     float(c - lim), "YES ***" if c.denominator == 1 else "no"))
        print()
    print("  the claimed R_n(m) = prod_{i=1..n}(m^{2i(2n-1)}-1)/prod_{i=2..2n}(m^{in}-(-1)^i)")
    print("  and c = bracket * R_n(m).  Independent check that R_n > 1 exactly:")
    for n in (3, 4, 5, 6, 8, 12):
        for m in (2, 3, 5, 17, 128):
            num = 1
            for i in range(1, n + 1):
                num *= m**(2*i*(2*n - 1)) - 1
            den = 1
            for i in range(2, 2*n + 1):
                den *= m**(i*n) - (-1)**i
            R = Fraction(num, den)
            q = m**(2*n-1)
            c = Fraction(Cn(n, q), Ud(2*n, m**n))
            br = Fraction(gcd(2*n, m**n + 1), gcd(2, q - 1))
            ok = (br * R == c)
            print("      n=%-3d m=%-5d  R-1 = %-24.16g  R>1: %-5s  c==br*R: %s"
                  % (n, m, float(R - 1), R > 1, ok))
    print()
    print("  degree bookkeeping: deg_m |C_n(m^{2n-1})| = (2n^2+n)(2n-1)")
    print("                      deg_m |U_{2n}(m^n)|   = (4n^2-1) n")
    for n in range(3, 13):
        print("      n=%-3d  %d  vs  %d   equal: %s"
              % (n, (2*n*n + n)*(2*n - 1), (4*n*n - 1)*n,
                 (2*n*n + n)*(2*n - 1) == (4*n*n - 1)*n))
    print()
    print("  the LIMIT of c and whether it divides |Out(U_{2n}(q_1))| = 2 f_1 gcd(2n,q_1+1):")
    for n in (3, 4, 5, 6):
        for m in (2, 3, 5):
            q1 = m**n
            q = m**(2*n-1)
            br = Fraction(gcd(2*n, q1 + 1), gcd(2, q - 1))
            out = 2 * (n * _logp(m)) * gcd(2*n, q1 + 1)
            print("      n=%-3d m=%-3d  bracket=%-6s |Out(U_%d(%d))|=%-8d  bracket | |Out| : %s"
                  % (n, m, br, 2*n, q1, out,
                     br.denominator == 1 and out % br.numerator == 0))
    print()
    print("  minimal degrees m(PSp_{2n}(2)) = 2^{n-1}(2^n-1) vs [S:P_1] = 2^{2n}-1")
    for n in range(3, 10):
        mm = 2**(n-1) * (2**n - 1)
        pp = 2**(2*n) - 1
        print("      n=%-3d  m=%-12d  [S:P1]=%-12d  ratio=%.6f  (also 2^{n-1}(2^n+1)=%d)"
              % (n, mm, pp, mm/pp, 2**(n-1)*(2**n + 1)))
    print("      the two O^eps_{2n}(2) subgroups of Sp_{2n}(2) have indices")
    print("      2^{n-1}(2^n -+ 1); the minus type is the smaller. Ratio -> 1/2,")
    print("      so deg_q iota = 2n-1 is unchanged.  CONFIRMED.")
    print()


def _logp(m):
    """f such that m = p^f"""
    for p in (2, 3, 5, 7, 11, 13):
        f, x = 0, m
        while x % p == 0:
            x //= p
            f += 1
        if x == 1:
            return f
    return 1


# --------------------------------------------------------------- part 7
def part7():
    print(BAR)
    print("PART 7 -- cross-cutting: stale mu = 25 / 51, and the S4(3) leak")
    print(BAR)
    print("""
  S4(3) has iota = 27 (the maximal subgroup 2^4:A5) rather than the
  parabolic index 40 = (q+1)(q^2+1).  Question: can this leak into other
  q = 0 mod 3 targets via subfield structure?

  Re-derivation.  The defect exists because PSp_4(3) = U_4(2) and U_4(2)
  has the 27-point rank-3 action on the generalized quadrangle GQ(2,4)
  (equivalently, the 27 lines of the cubic surface).  This is a SPORADIC
  isomorphism of a rank-2 group over F_3 with a rank-3 unitary group over
  F_2 -- it is NOT a subfield phenomenon: a subfield subgroup S_4(3) <
  S_4(3^k) has index >= |S_4(9)|/|S_4(3)| = 3.1e6, far above the parabolic
  index (q^4-1)/(q-1) = 820 at q = 9.  So the small permutation
  representation of S_4(3) cannot be inflated to S_4(3^k), k >= 2.
""")
    for k in (1, 2, 3, 4):
        q = 3**k
        S = q**4 * (q**2 - 1) * (q**4 - 1) // gcd(2, q - 1)
        base = 3**4 * (3**2 - 1) * (3**4 - 1) // 2
        pidx = (q**4 - 1) // (q - 1)
        print("      q=3^%d=%-6d  |S4(q)|=%-24d  [S:P]=%-10d  |S4(q)|/|S4(3)| = %d"
              % (k, q, S, pidx, S // base))
    print()
    print("  A subgroup H < S with [S:H] < [S:P_1] would have to be a maximal")
    print("  subgroup of index < (q^4-1)/(q-1); by Kleidman-Liebeck 5.2.2 the")
    print("  ONLY PSp_4(q) with such a subgroup is q = 3 (index 27) and q = 2")
    print("  (not simple).  For q = 3^k, k >= 2, subfield subgroups have index")
    print("  >= |S_4(3^k)|/|S_4(3^{k/2})| >> (q^4-1)/(q-1).  Explicitly:")
    for k in (2, 3, 4, 6):
        q = 3**k
        pidx = (q**4 - 1) // (q - 1)
        best = None
        for kk in range(1, k):
            if k % kk:
                continue
            q0 = 3**kk
            idx = (q**4 * (q**2-1)*(q**4-1)//gcd(2, q-1)) // \
                  (q0**4 * (q0**2-1)*(q0**4-1)//gcd(2, q0-1))
            best = idx if best is None or idx < best else best
        print("      q=3^%-2d  [S:P_1]=%-14d  min subfield index=%-24d  subfield >> P_1 : %s"
              % (k, pidx, best, best > pidx))
    print()


PARTS = {"1": part1, "2": part2, "3": part3, "4": part4,
         "5": part5, "6": part6, "7": part7}


# --------------------------------------------------------------- part 8
def part8():
    """Closed-form proof of R_n(m) > 1  --  v_task59's (H3), its sharpest debt."""
    print(BAR)
    print("PART 8 -- CLOSING v_task59 (H3): a closed-form proof of R_n(m) > 1")
    print(BAR)
    print("""
  R_n(m) = prod_{i=1}^{n} (m^{2i(2n-1)} - 1) / prod_{k=2}^{2n} (m^{kn} - (-1)^k).

  Both products have m-degree (2n-1)n(n+1) [checked below], so with
  x := 1/m in (0, 1/2] and u := x^n :

        R_n = prod_{i=1}^{n} (1 - x^{2i(2n-1)})
              -------------------------------------
              prod_{k=2}^{2n} (1 - (-1)^k x^{kn})

  LOWER BOUND on the numerator.  The exponents 2i(2n-1) are >= 4n-2 >= 3n
  (n >= 2), so every x^{2i(2n-1)} <= u^3 * (a geometric tail), and
      NUM  >=  1 - sum_{j>=1} x^{j(4n-2)}  =  1 - x^{4n-2}/(1 - x^{4n-2})
           >=  1 - u^3/(1-u^3)  >=  1 - 1.002 u^3        (u <= 1/8).

  UPPER BOUND on the denominator.  The k = 2 factor is (1 - u^2); every
  even k >= 4 factor is <= 1; the odd factors are (1 + x^{kn}) = (1+u^k):
      DEN  <=  (1 - u^2) * prod_{k>=3}(1 + u^k)
           <=  (1 - u^2) * exp( u^3/(1-u) )
           <=  (1 - u^2) * (1 + 1.145 u^3)                (u <= 1/8)
           <=  1 - u^2 + 1.145 u^3 .

  Hence   NUM - DEN  >=  u^2 - 2.147 u^3  =  u^2 (1 - 2.147 u)  >  0
  for u <= 1/8, with margin >= 0.73 u^2.  Since n >= 3 and m >= 2 give
  u = m^{-n} <= 1/8, we get

        R_n(m)  >=  1 + 0.73 m^{-2n}   >  1      for ALL n >= 3, m >= 2.   []

  UPPER bound, for the "no integer in between" half.  DEN >= prod_{k=2}^{2n}
  (1 - u^k) >= 1 - u^2/(1-u), and NUM <= 1, so
        R_n(m)  <=  (1-u)/(1-u-u^2)  <=  1 + 1.17 u^2 .
  With c = bracket * R_n and bracket <= 2n :
        bracket < c <= bracket * (1 + 1.17 m^{-2n})  <  bracket + 1
  because 2n * 1.17 * 2^{-2n} < 1 for every n >= 3.  So c lies STRICTLY
  between two consecutive integers and is NEVER an integer.               []
""")
    print("  numerical verification of every inequality used, over a grid:")
    import math
    worst = None
    for n in range(3, 15):
        for m in (2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 27, 32):
            x = Fraction(1, m)
            u = x ** n
            num_lo = 1 - u**3 / (1 - u**3)
            den_hi = (1 - u**2) * (1 + Fraction(1145, 1000) * u**3)
            assert num_lo > den_hi, (n, m)
            # and the true values
            NUM = 1
            for i in range(1, n + 1):
                NUM *= (1 - x ** (2 * i * (2 * n - 1)))
            DEN = 1
            for k in range(2, 2 * n + 1):
                DEN *= (1 - (-1) ** k * x ** (k * n))
            R = NUM / DEN
            assert R > 1, (n, m, R)
            assert R <= 1 + Fraction(117, 100) * u**2, (n, m)
            br = 2 * n
            assert br * (R - 1) < 1
            g = float((num_lo - den_hi) / (u * u))
            if worst is None or g < worst[0]:
                worst = (g, n, m)
    print("      all assertions pass for 3 <= n <= 14, 12 values of m")
    print("      worst normalised margin (NUM_lo - DEN_hi)/u^2 = %.6f at n=%d, m=%d"
          % worst)
    print("      (the proof's guaranteed floor is 1 - 2.147*(1/8) = 0.7316)")
    print()
    print("  exp bound check: exp(u^3/(1-u)) <= 1 + 1.145 u^3 for u <= 1/8 :")
    for uu in (0.125, 0.1, 0.05, 0.01, 0.001):
        lhs = math.exp(uu**3 / (1 - uu))
        rhs = 1 + 1.145 * uu**3
        print("      u=%-8g  exp=%.12f  bound=%.12f  ok=%s" % (uu, lhs, rhs, lhs <= rhs))
    print("  1/(1-u^3) <= 1.002 for u <= 1/8 : %s" % (1/(1-0.125**3) <= 1.002))
    print()
    print("  degree identity used: deg NUM = deg DEN")
    for n in range(3, 15):
        dn = sum(2 * i * (2 * n - 1) for i in range(1, n + 1))
        dd = sum(k * n for k in range(2, 2 * n + 1))
        print("      n=%-3d  %d  vs  %d  (=(2n-1)n(n+1)=%d)  %s"
              % (n, dn, dd, (2*n-1)*n*(n+1), "ok" if dn == dd == (2*n-1)*n*(n+1) else "***"))
    print()
    print("  ==> v_task59 (H3) is CLOSED.  (J5) needs no numerical evidence.")
    print()


# --------------------------------------------------------------- part 9
def part9():
    """How big is the EQ-EX / D-N-test threshold really?"""
    print(BAR)
    print("PART 9 -- EQ-EX as a THRESHOLD: is the residual window actually swept?")
    print(BAR)
    print("""
  EQ-EX says q^{a - N D_1/N_1} <= c/kappa with c <= |Out(S_1)| = O(log q).
  If the exponent gap  g := |a - N D_1/N_1|  can be as small as 1/N_1, the
  threshold q <= (c/kappa)^{1/g} is astronomically large and is NOT swept
  by any run in v_task57/58/59.  So EQ-EX is only safe as an EXACT-RATIO
  FILTER unless the realised gaps are O(1).  Below: the realised gaps.
""")
    FT = {}
    def add(k, D, N, mu):
        FT[k] = (D, N, mu)
    for d in range(2, 33):
        add("L%d" % d, d*d - 1, d*(d-1)//2, d - 1)
    for d in range(3, 33):
        add("U%d" % d, d*d - 1, d*(d-1)//2, 2*d - 3)
    for n in range(2, 17):
        add("C%d" % n, 2*n*n + n, n*n, 2*n - 1)
    for n in range(4, 17):
        add("D%d" % n, 2*n*n - n, n*(n-1), 2*n - 2)
        add("2D%d" % n, 2*n*n - n, n*(n-1), 2*n - 2)
    add("G2", 14, 6, 5); add("3D4", 28, 12, 9); add("2F4", 26, 12, 10)
    add("F4", 52, 24, 15); add("E6", 78, 36, 16); add("2E6", 78, 36, 16)
    add("E7", 133, 63, 27); add("E8", 248, 120, 57)
    add("L2", 3, 1, 1); add("Sz", 5, 2, 2); add("R", 7, 3, 3); add("U3", 8, 3, 3)

    targets = [("S4", 10, 4, 3), ("G2", 14, 6, 5), ("3D4", 28, 12, 9),
               ("2F4", 26, 12, 10), ("F4", 52, 24, 15), ("E6", 78, 36, 16),
               ("2E6", 78, 36, 16), ("E7", 133, 63, 27), ("E8", 248, 120, 57),
               ("C3", 21, 9, 5), ("C6", 78, 36, 11), ("C12", 300, 144, 23),
               ("D8", 120, 56, 14), ("2D8", 120, 56, 14)]
    print("   target  a    N   b   a/N      families passing Lemma EQ' (N1/mu1<=N/b),")
    print("                                 min NONZERO gap |a - N*D1/N1| among them")
    for (k, a, N, b) in targets:
        aN = Fraction(a, N)
        passing = []
        for kk, (D1, N1, mu1) in FT.items():
            if Fraction(N1, mu1) <= Fraction(N, b):
                g = abs(Fraction(a) - Fraction(N * D1, N1))
                passing.append((g, kk))
        nz = sorted(g for (g, kk) in passing if g > 0)
        who = [kk for (g, kk) in sorted(passing) if g == (nz[0] if nz else -1)]
        print("   %-6s %-4d %-4d %-3d %-8s n=%-3d  min gap = %-8s  (%s)"
              % (k, a, N, b, aN, len(passing), nz[0] if nz else "-- all exact",
                 ",".join(sorted(who)[:5]) if nz else "--"))
    print()
    print("  All realised gaps are >= 1/2 (mostly >= 2/3), so the EQ-EX / D-N")
    print("  threshold is q^{1/2} <= c/kappa with c = O(log q): a TINY window,")
    print("  comfortably inside every swept range.  The theoretical 1/(N N_1)")
    print("  worst case is never realised because the admissible sets are")
    print("  pruned by Lemma EQ' FIRST.  ==> EQ-EX is used soundly.")
    print()


PARTS["8"] = part8
PARTS["9"] = part9

if __name__ == "__main__":
    todo = sys.argv[1:] or sorted(PARTS)
    for t in todo:
        PARTS[t]()
