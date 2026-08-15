# v_task46_ec.sage -- quantitative feasibility audit for the "uniform-in-c
# effective bound" route on row 2 of Theorem AT.
#
# Row 2: (n-2)(n-1)n = c*(q^2+q+1), c = 6 f1 l*, q = p^f, k = n-1, i.e.
#     C_c :  k^3 - k = c (q^2 + q + 1)          (the object that must be bounded)
# Weierstrass model (v_task44):  E_c : Y^2 = X^3 - 16 c^2 X - 48 c^4,
#     X = 4 c k,  Y = 4 c^2 (2q+1).
#
# IMPORTANT: only integral points of C_c matter -- i.e. integral points of E_c
# subject to the DIVISIBILITY 4c | X, 4c^2 | Y, Y/(4c^2) odd.  (The task's
# observation that the solution is not a generic integral point is correct and
# is honoured here: the audit is run on the divisible sublocus only.)
#
# A uniform-in-c effective bound closes row 2 for all n >= N0 iff there is B(c) with
#   (i)  log|X(P)| <= B(c) for EVERY integral point P of C_c   [correctness]
#   (ii) B(c) <  log(4c(n-1)) for every admissible (c,n), n >= N0  [strength].
# For (ii) only the smallest admissible n at a given c matters.  Proven bounds:
#   (n1) c = 6 f1 l* < 1.13 f1 n <= 2.26 n   (v_task44 2.2)  => n > c/2.26 ; all f>=2
#   (n2) f = 2 sub-row: c <= 3.19 n^(1/3)                    => n > c^3/32.5
# Since every f >= 2 is allowed, the binding requirement is (n1); we print the
# GENEROUS variant n > c/2 (threshold 2 log c + log 2) so the verdicts below are
# conservative, and also the f=2-only threshold 4 log c - 2.093.
#
# Output: v_task46_ec_out.txt

import sys
CMAX = 216

print("="*100)
print("PART 1 -- integral points of C_c : k^3 - k = c(q^2+q+1),  c = 6 f1 l* <= %d" % CMAX)
print("="*100)
print("c    log c   #E_c   #C_c   max log|4ck|  ratio   witness (k,q) of max")
print("-"*100)

rows = []
for c in range(6, CMAX+1, 6):
    E = EllipticCurve([0,0,0,-16*c^2, -48*c^4])
    try:
        pts = E.integral_points()
    except Exception as e:
        print("%-4d  integral_points FAILED (%s)" % (c, e)); sys.stdout.flush(); continue
    good = set()
    for P in pts:
        X, Y = ZZ(P[0]), ZZ(P[1])
        for YY in (Y, -Y):
            if X % (4*c) == 0 and YY % (4*c^2) == 0:
                k = X//(4*c); v = YY//(4*c^2)
                if v % 2 == 1:
                    q = (v-1)//2
                    assert k^3 - k == c*(q^2+q+1), (c,k,q)   # verified by substitution
                    good.add((k,q))
    good = sorted(good)
    if good:
        wk, wq = max(good, key=lambda t: abs(t[0]))
        mx = abs(4*c*wk); lm = float(log(mx))
    else:
        wk = wq = None; lm = 0.0
    lc = float(log(c))
    print("%-4d %-7.3f %-6d %-6d %-13.4f %-7.3f %s"
          % (c, lc, len(pts), len(good), lm, lm/lc, ("(%d,%d)"%(wk,wq)) if good else "-"))
    sys.stdout.flush()
    rows.append((c, lc, len(pts), len(good), lm, wk, wq))

print()
print("="*100)
print("PART 2 -- THE DECISIVE COMPARISON")
print("="*100)
print("c     max log|X_C|   THRESH-1 = 2logc+0.693   verdict1      THRESH-2 = 4logc-2.093   verdict2")
print("-"*100)
n1 = n2 = 0
for (c, lc, ne, ng, lm, wk, wq) in rows:
    t1 = 2*lc + 0.6931
    t2 = 4*lc - 2.0930
    v1 = "IMPOSSIBLE" if lm > t1 else "ok"
    v2 = "IMPOSSIBLE" if lm > t2 else "ok"
    n1 += (lm > t1); n2 += (lm > t2)
    print("%-5d %-14.4f %-24.4f %-13s %-24.4f %s" % (c, lm, t1, v1, t2, v2))
print("-"*100)
print("multipliers at which NO correct B(c) can be strong enough:")
print("   against THRESHOLD-1 (row 2, all f >= 2):  %d / %d" % (n1, len(rows)))
print("   against THRESHOLD-2 (f = 2 sub-row only): %d / %d" % (n2, len(rows)))

print()
print("="*100)
print("PART 3 -- the single human-checkable witness")
print("="*100)
c, k, q = 30, 1994, 16256
lhs = k^3 - k; rhs = c*(q^2+q+1)
print("  c = 30,  (k,q) = (1994, 16256):")
print("    k^3 - k        = %d" % lhs)
print("    30(q^2+q+1)    = %d" % rhs)
print("    equal:", lhs == rhs)
print("    X = 4ck        = %d ,  log X = %.4f" % (4*c*k, float(log(4*c*k))))
print("    THRESHOLD-1(30) = 2 log 30 + 0.693 = %.4f" % (2*float(log(30))+0.6931))
print("    THRESHOLD-2(30) = 4 log 30 - 2.093 = %.4f" % (4*float(log(30))-2.0930))
print("""
  So ANY correct effective bound must satisfy B(30) >= 12.3854, while closing
  row 2 at c = 30 requires B(30) < 7.4955 (all f >= 2) or < 11.5118 (f = 2 only).
  The required statement is FALSE.  No constant chase can repair it.
  (q = 16256 = 2^7 * 127 is not a prime power, so this is not an R1 solution --
   which is precisely the point: an effective bound cannot see the prime-power
   condition, so it must bound THIS point too, and it is already too big.)
""")

print("="*100)
print("PART 4 -- Lang- and Hall-type checks on the hypothetical solution point")
print("="*100)
print("""
log|Delta(E_c)| = log|16(62208 c^8 - 16384 c^6)| ~ 8 log c + 13.8.
The solution point has h(x) = log(4c(n-1)) >= 2 log c by (n1), so
   ĥ(P_sol)/log|Delta|  is bounded BELOW by an absolute positive constant,
of the same order as the values realised by the genuine integral points above.
The solution point is an ORDINARY point of E_c; Lang's conjecture
(ĥ >= C log|Delta|), even granted, is satisfied by it with room to spare.

Hall-type: |Y^2 - X^3| = |16 c^2 X + 48 c^4| ~ 64 c^3 (n-1), which for the
solution point (X ~ 4cn, c <= 3.19 n^(1/3)) is of order X^2 -- not X^(1/2).
Nowhere near a Hall near-miss; the ABC/Hall circle of ideas is mute as well.
""")
