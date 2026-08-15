#!/usr/bin/env python3
"""
v_task47_ranges.py -- the two numeric inequalities of Task 47.  (log-space)

Rows 2 and 3 of Theorem AT.  Standing pinned data (all PROVEN upstream,
v_task45/46):

  R1 equation      l* * f1 * iota1(S*) = C(n,3),   f1 in {1,2}
  row 2  S* = L_3(q), q = p^f, f >= 2, l* >= 2
  row 3  S* = L_5(q), q = p^f, f >= 1, l* >= 1

Task 47 adds one further ABELIAN ind*-value on the O*-orbit, of ratio

  rho = f_x * x / (f1 * iota1),  x/iota1 = q+1   (row 2, X = Z(Syl_p), N_S(X)=B)
                                 x/iota1 = q^2+1 (row 3, X = U_{P_2}, N_S(X)=P_2)

with 1 <= f_x <= |Out(S*)| and 1 <= f1 <= 2, so

  rho_min = (q+1)/2   resp. (q^2+1)/2
  rho_max = |Out|*(q+1) resp. |Out|*(q^2+1),
  |Out(L_3(q))| = 2 f gcd(3,q-1) <= 6f ,  |Out(L_5(q))| <= 10f .

Theorem GAP: I(A_n) contains no value strictly inside (4C(n,4), 6C(n,5)),
i.e. rho must avoid the open interval ( n-3 , 0.3(n-3)(n-4) ).

Checked here with only PROVEN q-bounds:

  row 2 LOWER (Q-LB, v_task46 2.3)  q >= (f n^2/8.1)^{f/(2f-1)}   [n >= 40]
        UPPER  q^2 < iota1 = C(n,3)/(l* f1) <= C(n,3)/2   (l* >= 2, f1 >= 1)
  row 3 LOWER (MASTER, v_task46 2.5)  q^{4-1/f} >= f n(n-2)/3.13
        UPPER  q^4 < iota1 = C(n,3)/(l* f1) <= C(n,3)      (l* >= 1, f1 >= 1)
  both  q = p^f >= 2^f .
"""
from math import log

L2 = log(2.0)

def lC3(ln):                      # log C(n,3), ln = log n
    return 3*ln - log(6.0)        # (n)(n-1)(n-2)/6 <= n^3/6 ; used as UPPER
def lC3lo(ln):                    # a safe LOWER bound for log C(n,3) (n >= 1e10)
    return 3*ln - log(6.0) - 1e-9

def check(row, ln, f):
    """returns (status, log(rho_min/(n-3)), log(rho_max/(0.3(n-3)(n-4))))"""
    if row == 2:
        lq_lo = (f/(2.0*f-1.0)) * (log(f) + 2*ln - log(8.1))
        lq_hi = 0.5*(lC3(ln) - log(2.0))
        lOut  = log(6.0*f)
        k     = 1                        # x/iota1 ~ q^k
    else:
        e = 4.0 - 1.0/f
        lq_lo = (log(f) + 2*ln - log(3.13)) / e
        lq_hi = 0.25*lC3(ln)
        lOut  = log(10.0*f)
        k     = 2
    lq_lo = max(lq_lo, f*L2)             # q = p^f >= 2^f
    if lq_lo > lq_hi:
        return ("empty", None, None)
    # rho_min = (q^k+1)/2 > q^k/2 ; rho_max = |Out|*(q^k+1) < 2|Out| q^k  (q>=2)
    lrho_min = k*lq_lo - log(2.0)
    lrho_max = lOut + k*lq_hi + log(2.0)
    lo_slack = lrho_min - ln                       # want > 0  (rho_min > n-3)
    hi_slack = log(0.3) + 2*ln - 1e-9 - lrho_max   # want > 0
    st = "KILL" if (lo_slack > 0 and hi_slack > 0) else "FAIL"
    return (st, lo_slack, hi_slack)

print("Margins are natural logs; both must be > 0.\n")
bad = 0
for row in (2, 3):
    print("="*76)
    print("ROW %d  (%s)" % (row, "L_3(q), f>=2, l*>=2" if row==2
                                 else "L_5(q), f>=1, l*>=1"))
    for e10 in [11, 12, 15, 20, 30, 60, 120, 300, 1000, 10**4, 10**6]:
        ln = e10*log(10.0)
        wlo, whi, nf, flo, fhi = None, None, 0, None, None
        for f in range((2 if row==2 else 1), 20000):
            st, a, b = check(row, ln, f)
            if st == "empty":
                continue
            nf += 1
            if st == "FAIL":
                bad += 1
                print("   *** FAIL n=1e%d f=%d  lo=%.4g hi=%.4g" % (e10,f,a,b))
            if wlo is None or a < wlo: wlo, flo = a, f
            if whi is None or b < whi: whi, fhi = b, f
        print("  n=1e%-6d live f: %4d   min lo-margin %.4g (f=%s)   "
              "min hi-margin %.4g (f=%s)" % (e10, nf, wlo, flo, whi, fhi))
print("="*76)
print("TOTAL FAILURES:", bad)

print("""
Asymptotic form (the grid is a check, not the proof):

 row 2:  rho_min/(n-3) >= (f n^2/8.1)^{f/(2f-1)}/(2n).  The exponent
         2f/(2f-1) exceeds 1 for every f >= 2, so at fixed f the ratio grows
         like n^{1/(2f-1)}; and since q >= 2^f, only f <= log_2 q <= 1.5 log_2 n
         is live, so the exponent gain n^{1/(3 log_2 n)} is bounded below by a
         constant while the constant factor (f/8.1)^{f/(2f-1)} * sqrt(...) takes
         over: at large f, q^{2-1/f} >= f n^2/8.1 with q^{1/f} = p >= 2 gives
         q >= 0.497 sqrt(f) n, hence rho_min/(n-3) >= 0.248 sqrt(f).
         rho_max/(0.3 n^2) <= 12 f (C(n,3)/2)^{1/2}/(0.3 n^2) = O(f n^{-1/2})
         = O(log n / sqrt n) -> 0.

 row 3:  rho_min/(n-3) >= (f n^2/3.13)^{2/(4-1/f)}/(2n); the exponent
         4f/(4f-1) > 1 always, and at large f the constant (f/3.13)^{1/2} -> oo.
         rho_max/(0.3 n^2) <= 20 f C(n,3)^{1/2}/(0.3 n^2) = O(log n/sqrt n) -> 0.

Both margins are therefore monotone-improving in n past the grid, and the
grid covers 1e11 <= n <= 1e(10^6).
""")
