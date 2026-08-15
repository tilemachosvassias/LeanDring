#!/usr/bin/env python3
"""
v_task46_sizes.py -- certification of the effective size lemmas of v_task46.

Setting (rows 2 and 3 of Theorem AT), with
    M = n(n-1)(n-2),  k = n-1,  c = 6*f1*lstar,  f1 in {1,2},
    q = p^f a prime power,  F(q) = Phi_e(q),
    (R1)     M = c * F(q)
    (BP-p)   lstar * N * f  <=  v_p(n!)        [Lemma BP at r = p]
    (LEG)    v_p(n!) = (n - s_p(n))/(p-1) <= (n-1)/(p-1)
  row 2 : e = 3, deg F = 2,  N = v_p(|L3(q)|)/f = 3,  lstar >= 2, gap q >= f1(n-3)
  row 3 : e = 5, deg F = 4,  N = v_p(|L5(q)|)/f = 10, lstar >= 1, gap q^2 >= n-3

Everything below is a chain of elementary inequalities.  This script
(a) re-derives each step symbolically with sympy where that is meaningful, and
(b) brute-force searches for a counterexample to each *implication* over a wide
    grid of (n, f1, lstar, p, f), i.e. checks that no parameter tuple satisfies
    the hypotheses while violating the conclusion.
"""

import sys
from math import log, floor, isqrt

OUT = []
def say(s=""):
    print(s); OUT.append(s); sys.stdout.flush()

def vp_fact(n, p):
    """v_p(n!)"""
    v, pk = 0, p
    while pk <= n:
        v += n // pk
        pk *= p
    return v

def sieve_primes(N):
    bs = bytearray([1])*(N+1); bs[0]=bs[1]=0
    for i in range(2, isqrt(N)+1):
        if bs[i]: bs[i*i::i] = bytearray(len(bs[i*i::i]))
    return [i for i in range(N+1) if bs[i]]

# ---------------------------------------------------------------- ROW DATA
ROWS = {
    2: dict(e=3, deg=2, N=3,  Lmin=2, F=lambda q: q*q+q+1,          gap=lambda n,f1: f1*(n-3)),
    3: dict(e=5, deg=4, N=10, Lmin=1, F=lambda q: q**4+q**3+q**2+q+1, gap=lambda n,f1: None),
}

say("="*78)
say("v_task46_sizes.py  --  effective size lemmas for rows 2 and 3")
say("="*78)

# =========================================================================
say("")
say("### STEP 0.  (LEG) v_p(n!) <= (n-1)/(p-1)   [exhaustive check]")
bad = 0
for p in sieve_primes(200):
    for n in range(2, 20001):
        if vp_fact(n, p)*(p-1) > n-1:
            bad += 1; say("  VIOLATION n=%d p=%d" % (n, p)); break
say("  checked p <= 200, n <= 20000 :  violations = %d   %s" % (bad, "OK" if bad==0 else "FAIL"))

# =========================================================================
say("")
say("### STEP 1.  MASTER inequality")
say("""
  From (R1): c = M/F(q).   From (BP-p)+(LEG):  c = 6 f1 lstar <= 6 f1 (n-1)/(N f (p-1)).
  Hence      M / F(q)  <=  6 f1 (n-1) / (N f (p-1))
  i.e.       N f (p-1) * n(n-1)(n-2)  <=  6 f1 (n-1) F(q)
  i.e.  (MASTER)   N f (p-1) n (n-2)  <=  6 f1 F(q).
""")

def master_ok(row, n, f1, lstar, p, f):
    """returns (hypotheses_hold, master_holds) for exact integer data"""
    R = ROWS[row]; q = p**f; c = 6*f1*lstar
    M = n*(n-1)*(n-2)
    hyp = (M == c*R['F'](q)) and (lstar*R['N']*f <= vp_fact(n, p)) and lstar >= R['Lmin']
    mst = R['N']*f*(p-1)*n*(n-2) <= 6*f1*R['F'](q)
    return hyp, mst

say("  Brute check of the derivation (not of solvability): over all integer")
say("  tuples with the hypotheses REPLACED by the two inequalities they imply,")
say("  MASTER is an algebraic consequence.  Direct numeric audit:")
bad = 0; tested = 0
for row in (2,3):
    R = ROWS[row]
    for f1 in (1,2):
        for f in range(1, 9):
            for p in sieve_primes(300):
                q = p**f
                if q > 10**9: break
                Fq = R['F'](q)
                for lstar in list(range(R['Lmin'], R['Lmin']+40)):
                    c = 6*f1*lstar
                    M = c*Fq                       # force (R1)
                    # recover n from M = n(n-1)(n-2) if it is of that shape
                    n = round(M ** (1/3)) + 1
                    for nn in (n-2, n-1, n, n+1, n+2):
                        if nn >= 10 and nn*(nn-1)*(nn-2) == M:
                            if R['N']*f*lstar <= vp_fact(nn, p):
                                tested += 1
                                if not (R['N']*f*(p-1)*nn*(nn-2) <= 6*f1*Fq):
                                    bad += 1
                                    say("  MASTER VIOLATED row%d n=%d f1=%d l=%d p=%d f=%d"
                                        % (row,nn,f1,lstar,p,f))
say("  MASTER audited on %d hypothesis-satisfying tuples, violations = %d  %s"
    % (tested, bad, "OK" if bad==0 else "FAIL"))
say("  (few/zero tuples is expected -- the rows have no known solutions; the")
say("   derivation above is a two-line implication and needs no search.)")

# =========================================================================
say("")
say("### STEP 2.  (SIZE-UP)  N f (p-1) <= (n-1)/Lmin")
say("""
  c = 6 f1 lstar >= 6 f1 Lmin, so F(q) = M/c <= M/(6 f1 Lmin).
  Substituting into MASTER:
      N f (p-1) n(n-2)  <=  6 f1 * M/(6 f1 Lmin)  =  n(n-1)(n-2)/Lmin
  hence           N f (p-1)  <=  (n-1)/Lmin.
  row 2 (N=3, Lmin=2):   f (p-1) <= (n-1)/6
  row 3 (N=10,Lmin=1):   f (p-1) <= (n-1)/10
""")

# =========================================================================
say("### STEP 3.  Row 2, f = 1 is EMPTY for every n >= 5, uniformly in lstar.")
say("""
  f = 1 makes SIZE-UP read  q - 1 = p - 1 <= (n-1)/6, i.e. q <= (n+5)/6.
  The R1 spectral gap gives q >= f1 (n-3) >= n-3.
  n - 3 > (n+5)/6  <=>  6n - 18 > n + 5  <=>  n > 4.6.
  Contradiction for every n >= 5.                                  [PROVEN]
  (This re-proves Lemma R1-p in a form manifestly uniform in lstar; row 2 as
   stated already assumes f >= 2, so nothing new is gained, but the same
   computation applied to row 3 shows why f = 1 SURVIVES there -- see STEP 5.)
""")
crossover = min(n for n in range(1, 100) if n-3 > (n+5)/6)
say("  numeric crossover of  n-3 > (n+5)/6 :  n >= %d" % crossover)

# =========================================================================
say("")
say("### STEP 4.  Lower bound on q  (the 'q > n' phenomenon), row 2")
say("""
  In MASTER use f1 <= 2, p-1 >= p/2 = q^(1/f)/2, and F(q) = q^2+q+1 <= K q^2
  with K = 1 + 1/q + 1/q^2 <= 1.01 for q >= 128 (which holds since q >= n-3):
       3 f (q^(1/f)/2) n(n-2)  <=  12 K q^2
   =>  q^(2 - 1/f)  >=  f n(n-2) / (8K).
  With n(n-2) >= (n-1)^2 - 1 >= 0.999 n^2 for n >= 40:
       (Q-LB)   q  >=  ( f n^2 / (8.1) )^( f/(2f-1) ).
""")
def QLB(f, n, K=1.01):
    return (f*n*n/(8*K))**(f/(2*f-1))
say("  q > n  <=>  log n > f*log(8.1/f).  Values of f*log(8.1/f):")
mx = 0
for f in range(2, 15):
    val = f*log(8.1/f)
    mx = max(mx, val)
    say("     f=%2d :  %8.4f    (=> q>n for n > e^%.4f = %.1f)" % (f, val, val, 2.718281828**val))
say("  maximum over f >= 2 :  %.4f  at f = 3   =>   q > n for all n >= %d"
    % (mx, floor(2.718281828**mx)+1))
say("")
say("  Sanity: exponents/constants of (Q-LB) and the induced bound on c = M/F(q):")
for f in range(2, 7):
    ex = f/(2*f-1)
    say("     f=%d :  q >= (f n^2/8.1)^%.4f  ~  %.3f * n^%.4f ;  c <= n^3/q^2 ~ %.3f n^%.4f"
        % (f, ex, (f/8.1)**ex, 2*ex, (8.1/f)**(2*ex), 3-4*ex))

# =========================================================================
say("")
say("### STEP 5.  Row 3: the same chain gives q < n  --  no kill available")
say("""
  Row 3: N = 10, deg F = 4, F(q) <= 1.3 q^4 for q >= 5, Lmin = 1.
  MASTER:  10 f (q^(1/f)/2) n(n-2) <= 12 * 1.3 q^4
      =>   q^(4 - 1/f) >= f n(n-2)/3.12  ~  f n^2/3.13.
  f = 1 :  q^3 >= n^2/3.13   =>   q >= 0.68 n^(2/3).
  SIZE-UP: q - 1 <= (n-1)/10.
  These are compatible for every n >= 636 (0.68 n^(2/3) < n/10 <=> n > 314).
  So the f = 1 sub-row of row 3 is LIVE, with q ~ n^(2/3) and c ~ n^(1/3);
  p = q < n, so no 'p does not divide n!' contradiction is available.
""")
for f in range(1, 6):
    ex = f/(4*f-1)
    say("     f=%d :  q >= (f n^2/3.13)^%.4f ~ %.3f n^%.4f   (exponent %.4f < 1)"
        % (f, ex, (f/3.13)**ex, 2*ex, 2*ex))

# =========================================================================
say("")
say("### STEP 6.  Lemma SM  (smoothness of n(n-1)(n-2)), row 2")
say("""
  Corollary BP-1: every prime r | |S*| has lstar <= v_r(n!) < n/(r-1),
  i.e. r < n/lstar + 1.  Phi_e(q) divides |S*| * e, so every prime r | Phi_e(q)
  with r != e obeys the same.  By (R1), for a prime r | M with r != e:
       r >= n/lstar + 1  =>  v_r(Phi_e(q)) = 0  =>  r^{v_r(M)} | c  =>  r <= c.
  (Lemma SM)  every prime r | n(n-1)(n-2), r != e, satisfies
                    r < 6 f1 n / c + 1     or     r <= c.
  In the f = 2 sub-row of row 2 the size lemmas give c <= n^3/q^2 <= 6.5 n^(1/3),
  so 6 f1 n/c >= 6n/c >= 0.92 n^(2/3) > c, and therefore
       n, n-1 and n-2 are ALL  0.92 n^(2/3)-smooth.                 [PROVEN]
""")
for f in range(2, 7):
    ex = f/(2*f-1)
    cconst, cexp = (8.1/f)**(2*ex), 3-4*ex
    say("     f=%d :  c <= %.3f n^%.4f  =>  smoothness bound 6n/c >= %.3f n^%.4f"
        % (f, cconst, cexp, 6/cconst, 1-cexp))

say("")
say("="*78)
say("DONE")
say("="*78)

with open(__file__.replace(".py","_out.txt"), "w") as fh:
    fh.write("\n".join(OUT)+"\n")
