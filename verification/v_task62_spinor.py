#!/usr/bin/env python3
"""
v_task62_spinor.py -- evaluate  (T-BC-RES)  per residue class of odd q.

    Delta(q)  =  p^O7(q)  -  [ p^C6(q) + a(q)*p^C4(q) + C(a(q),3) ]

Every column rule below is a congruence condition on q (they are square-class
conditions on 2, 3, 5, 13 and presence conditions for zeta_9 / sqrt(2)), all of
which were COMPUTED in GAP -- see v_task62_spinor.md sections 2-5 and the
scan outputs.  Hence Delta is periodic in q with modulus

    M = lcm(16, 9, 5, 12, 13) = 9360

(the 16 comes from the degree-6 SL_2(7) column, the 9 from L_2(8), the 5 from
the rank-1 law and 2.J_2, the 12 from the degree-4 2.A_5/2.A_6 and degree-6
U_3(3) columns, the 13 from the two L_2(13) columns).

We enumerate all residues, evaluate Delta, and report where Delta = 0.
Defining-characteristic exceptions (p in {3,5,7,13}) are handled separately
for the finitely many prime powers involved.

Run:  python3 v_task62_spinor.py > v_task62_spinor_py_out.txt
"""

from math import comb


def factorint(n):
    """minimal replacement: {prime: exponent}"""
    f, d = {}, 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


M = 9360          # lcm(16, 9, 5, 12, 13)

# --------------------------------------------------------------------------
# square-class / presence predicates (congruence conditions on q)
# --------------------------------------------------------------------------
sq2   = lambda q: q % 8 in (1, 7)             # 2 is a square in F_q
nsq2  = lambda q: q % 8 in (3, 5)             # 2 is a NON-square
nsq3  = lambda q: q % 12 in (5, 7)            # 3 is a NON-square
sq5   = lambda q: q % 5 in (1, 4)             # 5 is a square  <=> q = +-1 (5)
sq13  = lambda q: q % 13 in (1, 3, 4, 9, 10, 12)
zeta9 = lambda q: q % 9 in (1, 8)             # zeta_9 + zeta_9^-1 in F_q
pm7_16 = lambda q: q % 16 in (7, 9)           # q = +-7 mod 16


# --------------------------------------------------------------------------
# ORTHOGONAL degree-7 Rule-S column sum  p^O7(q)   (q odd, q > 3)
# --------------------------------------------------------------------------
def pO7(q, p):
    c = {}
    c['Omega7(q)']   = 1                      # G itself (4af convention)
    c['G2(q)']       = 2                      # E1, sec.4aa
    c['Sp6(2)']      = 2                      # Rule-S branch 1, sec.4ai
    c['2^3:L3(2)']   = 2                      # v_task62, re-derived
    c['2^3.L3(2)']   = 2
    c['2^6:L3(2)']   = 2
    c['A8']          = 0                      # v_task62 [PROVEN, all odd q]
    c['L3(2)']       = 0                      # v_task62 [PROVEN, all odd q]
    c['U3(3)']       = 0                      # v_task62 [PROVEN, all odd q]
    c['L2(8) Q']     = 0                      # Stab_Out = C_3 [PROVEN]
    c['L2(8) Q(z9)'] = 2 if (zeta9(q) and p != 3) else 0
    c['L2(13)']      = 2 if (sq13(q) and p != 13) else 0
    c['2^6:A7']      = 1 if (q % 8 in (3, 5)) else 0     # E6 + v_task62
    return sum(c.values()), c


# --------------------------------------------------------------------------
# SYMPLECTIC Rule-S column sums
# --------------------------------------------------------------------------
def a_of(q, p):
    """p^C_2(q) = 1 + 2*[SL_2(5) present and Out-unstable]."""
    return 3 if (sq5(q) and p != 5) else 1


def pC4(q, p):
    c = {}
    c['Sp4(q)']   = 1
    c['2.A5']     = 1 if (nsq3(q) and p != 3) else 0
    c['2.A6']     = 1 if (nsq3(q) and p != 3) else 0
    c['Sym^3']    = 1 if (p >= 5 and q != 5) else 0     # multiplier nu^3, nonsq
    c['C6 1920']  = 0                                   # c_4 = 0 (v_task61)
    return sum(c.values()), c


def pC6(q, p):
    c = {}
    c['Sp6(q)']    = 1
    c['2.A5']      = 1 if (nsq2(q) and p != 5) else 0
    c['SL2(7)']    = 2 if (pm7_16(q) and p != 7) else 0
    c['U3(3)']     = 1 if (nsq3(q) and p != 3) else 0
    c['2.L2(13)']  = 2 if (sq13(q) and p != 13) else 0   # Out-unstable, sec.4ai
    c['2.J2']      = 2 if (sq5(q) and p != 5) else 0     # Out-unstable, sec.4ai
    c['2.(A5xA5)'] = 0                                   # C_4 member, killed
    return sum(c.values()), c


def delta(q, p):
    o, oc = pO7(q, p)
    a = a_of(q, p)
    c4, c4c = pC4(q, p)
    c6, c6c = pC6(q, p)
    s = c6 + a * c4 + comb(a, 3)
    return o - s, o, s, a, c4, c6, oc, c4c, c6c


def main():
    print("modulus M =", M)
    prof = {}
    zeros = []
    for r in range(1, M, 2):
        d, o, s, a, c4, c6, *_ = delta(r, 10 ** 9)     # generic characteristic
        prof.setdefault((a, c4, c6, o), []).append(r)
        if d == 0:
            zeros.append(r)
    print("residue classes scanned (odd r mod M):", M // 2)
    print("distinct profiles (a, p^C4, p^C6, p^O7):", len(prof))
    print()
    print(f"{'a':>2} {'pC4':>4} {'pC6':>4} {'symp':>5} {'pO7':>4} "
          f"{'Delta':>6}  {'#classes':>9}   example")
    for key in sorted(prof):
        a, c4, c6, o = key
        s = c6 + a * c4 + comb(a, 3)
        rs = prof[key]
        print(f"{a:2d} {c4:4d} {c6:4d} {s:5d} {o:4d} {o-s:+6d}  "
              f"{len(rs):9d}   q = {rs[0]}")
    print()
    print("### residue classes with Delta = 0:", len(zeros))
    if zeros:
        print("   first 60:", zeros[:60])
        # describe them
        print("   their (q mod 8, q mod 12, q mod 16, q mod 5, q mod 9, "
              "q mod 13) signatures:")
        sig = sorted({(r % 8, r % 12, r % 16, r % 5, r % 9, r % 13)
                      for r in zeros})
        for s0 in sig[:40]:
            print("     ", s0)
        print("   #distinct signatures:", len(sig))

    # ---------------- sensitivity -------------------------------------
    print("\n### SENSITIVITY: perturb one column by +-1 / +-2 and re-check")
    print("    (how robust is 'Delta never 0'?)")
    for shift in (-2, -1, 1, 2):
        bad_o = sum(1 for r in range(1, M, 2)
                    if delta(r, 10 ** 9)[0] + shift == 0)
        print(f"   orthogonal side shifted by {shift:+d}: "
              f"{bad_o:5d} residue classes would have Delta = 0")
    print("   -> the margin is |Delta| >= 1 everywhere, so ANY single column"
          " error of the\n      wrong size in the wrong class destroys the"
          " conclusion; see md sec. 6.")
    mn = min(abs(delta(r, 10 ** 9)[0]) for r in range(1, M, 2))
    print("   min |Delta| over all residue classes =", mn)

    print("\n### defining-characteristic points p in {3,5,7,13}, q < 2000:")
    for q in range(3, 2000, 2):
        f = factorint(q)
        if len(f) != 1:
            continue
        p = list(f)[0]
        if p not in (3, 5, 7, 13):
            continue
        d, o, s, a, c4, c6, *_ = delta(q, p)
        flag = "   <== Delta = 0" if d == 0 else ""
        print(f"  q={q:5d} p={p:3d}  a={a} pC4={c4} pC6={c6} "
              f"symp={s:3d} pO7={o:3d} Delta={d:+3d}{flag}")

    print("\n### small odd prime powers (generic table):")
    print(f"{'q':>5} {'a':>2} {'pC4':>4} {'pC6':>4} {'symp':>5} "
          f"{'pO7':>4} {'Delta':>6}")
    for q in range(5, 220, 2):
        f = factorint(q)
        if len(f) != 1:
            continue
        p = list(f)[0]
        d, o, s, a, c4, c6, *_ = delta(q, p)
        print(f"{q:5d} {a:2d} {c4:4d} {c6:4d} {s:5d} {o:4d} {d:+6d}")


if __name__ == '__main__':
    main()
