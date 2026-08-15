#!/usr/bin/env python3
"""
v_task48 AUDIT of v_task47 sec.2 "the squeeze", written independently from the
stated hypotheses (NOT from v_task47_ranges.py).

Claim under audit:  for every n >= 1e11 and every live f,
      n-3 < rho_min  and  rho_max < 0.3(n-3)(n-4).

Upstream PROVEN inputs used (as quoted in v_task47 sec.2 / v_task46):
 row2  L_3(q), q=p^f, f>=2, l*>=2 :  q^{(2f-1)/f} >= f n^2 / 8.1   (Q-LB)
                                     q^2 < C(n,3)/(l* f1) <= C(n,3)/2
                                     rho in [ (q+1)/2 , 6f(q+1) ]
 row3  L_5(q), q=p^f, f>=1, l*>=1 :  q^{(4f-1)/f} >= f n(n-2)/3.13 (MASTER)
                                     q^4 < C(n,3)
                                     rho in [ (q^2+1)/2 , 10f(q^2+1) ]
 both  q = p^f >= 2^f, p prime.

Part A: EXACT integer/rational arithmetic (Fraction, unbounded ints), n a power
        of 10 up to 1e40, every live f, no floating point anywhere.
Part B: mpmath at 100 dps for the huge-n mesh (up to 1e(10^6)).
"""
from fractions import Fraction as F
from math import isqrt
import sys

def C3(n): return n*(n-1)*(n-2)//6

def iroot(a, k):
    "floor(a**(1/k)) for ints, exact"
    if a < 0: raise ValueError
    if a == 0: return 0
    x = 1 << ((a.bit_length()+k-1)//k + 1)
    while True:
        y = ((k-1)*x + a//x**(k-1))//k
        if y >= x: break
        x = y
    while (x+1)**k <= a: x += 1
    while x**k > a: x -= 1
    return x

def qmin_row(row, n, f):
    """smallest integer q with the PROVEN lower bound, exact.
       row2: q^(2f-1) >= (f n^2 *10/81)^f ;  row3: q^(4f-1) >= (f n(n-2)*100/313)^f
       also q >= 2^f."""
    if row == 2:
        num, den, e = f*n*n*10, 81, 2*f-1
    else:
        num, den, e = f*n*(n-2)*100, 313, 4*f-1
    # need q^e * den^f >= num^f  -> smallest q
    A = num**f
    B = den**f
    # smallest q with q^e >= A/B  <=> q^e * B >= A
    q = iroot(A//B, e)
    while q**e * B < A: q += 1
    while q >= 1 and (q-1)**e * B >= A: q -= 1
    return max(q, 2**f)

def qmax_row(row, n):
    """largest integer q with the strict upper bound."""
    if row == 2:
        b = C3(n)//2          # q^2 < C(n,3)/2  (l*>=2, f1>=1)
        q = iroot(b, 2)
        while 2*q*q >= C3(n): q -= 1
        return q
    else:
        b = C3(n)
        q = iroot(b, 4)
        while q**4 >= b: q -= 1
        return q

def audit_exact(n, verbose=False):
    out = []
    for row in (2, 3):
        fmin = 2 if row == 2 else 1
        qhi = qmax_row(row, n)
        worst_lo = None; worst_hi = None; nlive = 0
        f = fmin
        while True:
            if 2**f > qhi:      # q >= 2^f impossible
                break
            qlo = qmin_row(row, n, f)
            if qlo > qhi:
                f += 1
                if f > 4*n.bit_length(): break
                continue
            nlive += 1
            k = 1 if row == 2 else 2
            outb = 6*f if row == 2 else 10*f
            rho_min = F(qlo**k + 1, 2)
            rho_max = outb*(qhi**k + 1)
            # need rho_min > n-3   and   rho_max < 0.3(n-3)(n-4)
            lo_ok = rho_min > n-3
            hi_ok = F(rho_max) < F(3*(n-3)*(n-4), 10)
            lo_ratio = F(rho_min, n-3)
            hi_ratio = F(10*rho_max, 3*(n-3)*(n-4))
            if worst_lo is None or lo_ratio < worst_lo[0]: worst_lo = (lo_ratio, f, lo_ok)
            if worst_hi is None or hi_ratio > worst_hi[0]: worst_hi = (hi_ratio, f, hi_ok)
            if not (lo_ok and hi_ok):
                out.append("   *** FAILURE row %d f=%d lo_ok=%s hi_ok=%s" % (row,f,lo_ok,hi_ok))
            f += 1
        out.append("  row %d: live f=%d..  count=%d | worst rho_min/(n-3) = %.6f at f=%s (ok=%s)"
                   " | worst rho_max/(0.3(n-3)(n-4)) = %.6g at f=%s (ok=%s)"
                   % (row, fmin, nlive, float(worst_lo[0]), worst_lo[1], worst_lo[2],
                      float(worst_hi[0]), worst_hi[1], worst_hi[2]))
    return out

print("="*78)
print("PART A -- EXACT integer/rational arithmetic")
print("="*78)
for e in [11,12,13,14,15,16,18,20,25,30,40]:
    n = 10**e
    print("n = 10^%d" % e)
    for l in audit_exact(n): print(l)

# also: the exact margin at the flagged thin point n=1e11, row 2, f=26
n = 10**11
print("\n-- flagged thin point: n=1e11, row 2, f=26 --")
for f in (24,25,26,27,28):
    qlo = qmin_row(2, n, f)
    print("  f=%2d  q_min=%d  rho_min=(q+1)/2=%s  (n-3)=%d  ratio=%.6f  prime-power-adjusted?"
          % (f, qlo, F(qlo+1,2), n-3, float(F(qlo+1,2*(n-3)))))

# ---------------------------------------------------------------------------
print("\n"+"="*78)
print("PART B -- a RIGOROUS all-n replacement for v_task47's finite grid")
print("="*78)
print("""
The grid in v_task47_ranges.py is not a proof (it stops at n=1e(10^6)).
Here is a two-branch argument that is uniform in n, plus its exact check.

LOWER SIDE.
 (i) Uniform-in-n branch.  q = p^f with p >= 2, so q^{1/f} >= 2, hence
       row2:  q^2 = q^{2-1/f} * q^{1/f} >= 2*(f n^2/8.1)  => q >= n*sqrt(2f/8.1)
       row3:  q^4 = q^{4-1/f} * q^{1/f} >= 2*(f n(n-2)/3.13)
                                        => q^2 >= sqrt(2f/3.13)*sqrt(n(n-2))
     So rho_min/(n-3) > q^k/(2n) >= 0.4969*sqrt(f)/2 = 0.2484 sqrt(f)  (row 2)
                                 >= 0.7995*sqrt(f)*sqrt(1-2/n)/2       (row 3).
     Row 2: > 1 for all f >= 17.   Row 3: > 1 for all f >= 7 (n >= 1e11).
 (ii) Small-f branch.  Pure Q-LB/MASTER give
        rho_min/(n-3) >= (f/8.1)^{f/(2f-1)} n^{1/(2f-1)}/2     (row 2)
        rho_min/(n-3) >= (f/3.13)^{2f/(4f-1)} n^{1/(4f-1)}*C   (row 3),
     STRICTLY INCREASING in n at fixed f.  So it suffices to check f<=16 (row 2)
     resp. f<=6 (row 3) at n = 1e11 -- done exactly in PART A.
UPPER SIDE (uniform, all n).
   row2: rho_max <= 6f(q+1) <= 12 f q,  q < sqrt(C(n,3)/2) < n^1.5/sqrt(12),
         f <= log2(q) < 1.5 log2 n  =>  rho_max < 5.2 n^1.5 log2 n.
   row3: rho_max <= 10f(q^2+1) <= 20 f q^2, q^2 < sqrt(C(n,3)) < n^1.5/sqrt(6),
         f <= log2 q < 0.75 log2 n     =>  rho_max < 6.2 n^1.5 log2 n.
   Need < 0.3(n-3)(n-4).  Ratio ~ 21 log2(n)/sqrt(n), decreasing for n >= e^2,
   and at n = 1e11 it is at most 21*36.6/3.16e5 = 2.4e-3 < 1.  QED for all n.
""")
from math import log, sqrt, log2
n0 = 10**11
print("branch (i) row2: 0.2484*sqrt(17) = %.4f  (>1 required)" % (0.2484*sqrt(17)))
print("branch (i) row3: 0.3997*sqrt(7)*sqrt(1-2/1e11) = %.4f" % (0.3997*sqrt(7)))
print("branch (ii) row2, f<=16, worst at n=1e11 (from PART A, exact):")
for f in range(2,17):
    q = qmin_row(2,n0,f); print("    f=%2d ratio=%.5f" % (f, float(F(q+1,2*(n0-3)))))
print("branch (ii) row3, f<=6, worst at n=1e11 (exact):")
for f in range(1,7):
    q = qmin_row(3,n0,f); print("    f=%2d ratio=%.5f" % (f, float(F(q*q+1,2*(n0-3)))))
print("upper side at n=1e11: ratio <= %.3e" % (21*log2(n0)/sqrt(n0)))
