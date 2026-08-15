#!/usr/bin/env python3
# v_task84 -- adversarial re-derivation of the v_task45 / v_task46 lemmas.
# Exact integer arithmetic where the statement is arithmetic; explicit constant
# chases re-done from scratch where the statement is analytic.
from math import log, exp, isqrt, comb, log2
from fractions import Fraction

# --- minimal replacements for sympy (not installed) ---
def factorint(x):
    x = abs(int(x)); d = {}
    if x <= 1: return d
    p = 2
    while p*p <= x:
        while x % p == 0: d[p] = d.get(p,0)+1; x//=p
        p += 1 if p==2 else 2
    if x > 1: d[x] = d.get(x,0)+1
    return d
def isprime(n):
    n=int(n)
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True
def primerange(a,b): return (n for n in range(max(2,a), b) if isprime(n))
class _S:
    factorint=staticmethod(factorint); isprime=staticmethod(isprime)
    primerange=staticmethod(primerange)
sympy=_S()


def hdr(t): print("\n" + "="*78 + "\n" + t + "\n" + "="*78)

# ---------------------------------------------------------------- Lemma Phi
hdr("Lemma Phi (F1)(F2)(F3), e in {3,5}")
bad = []
for e in (3, 5):
    for q in range(-400, 4001):
        Phi = sum(q**i for i in range(e))
        if Phi == 0: continue
        if Phi % 2 == 0: bad.append(("F1", e, q))
        for r, _ in sympy.factorint(abs(Phi)).items():
            if r != e and r % e != 1: bad.append(("F2", e, q, r))
        v = 0; t = abs(Phi)
        while t % e == 0: t //= e; v += 1
        if v > 1: bad.append(("F3", e, q, v))
print("failures over -400 <= q <= 4000:", bad[:10], "count", len(bad))

# ---------------------------------------------------------------- (SZ)
hdr("(SZ) and the size chase behind Lemmas NC / NC-gen")
def M(n): return n*(n-1)*(n-2)
bad = [n for n in range(10, 200000) if not (Fraction(M(n), (n-3)**2) < 2*(n-2))]
print("M/(n-3)^2 < 2(n-2) for all 10<=n<200000:", bad[:5] or "OK")
bad = [n for n in range(10, 200000) if not (Fraction(M(n), (n-3)**2) < n+4)]
print("M/(n-3)^2 < n+4  :  first n where it holds =",
      min(n for n in range(10, 100) if Fraction(M(n), (n-3)**2) < n+4),
      "; failures for n>=15:", [n for n in bad if n >= 15][:5] or "none")

# ---------------------------------------------------------------- Lemma NC
hdr("Lemma NC, re-derived and stress-tested")
print("step 1: p in {n,n-1,n-2}, n>=12  =>  p >= 10, and p>5>=e :",
      all((n-2) > 5 for n in range(12, 100)))
print("step 2: p > n/2 for p >= n-2 requires n > 4 :", all(n-2 > n/2 for n in range(5, 100)))
print("step 3: v_p(n!) = 1 for n/2 < p <= n  -- exact check n<=3000:")
bad = []
for n in range(5, 3001):
    for p in sympy.primerange(n//2+1, n+1):
        v = 0; t = n
        pk = p
        while pk <= n: v += n//pk; pk *= p
        if v != 1: bad.append((n, p))
print("   failures:", bad[:5] or "none")
print("step 4: p^2 > n for p >= n-2, n >= 12 :  (n-1)(n-4)>0 for n>=5 :",
      all((n-2)**2 > n for n in range(5, 100)))
print("step 5: p | c and 0 < c < 2(n-2) <= 2p  =>  c = p; but 6|c and p prime >3.")
print("   EDGE CASE the audit asked for: is n-2 > n/2 ever violated in range? n>=12 -> no.")
print("   EDGE CASE: does the proof need p != e?  p >= n-2 >= 10 > 5 = max e : OK")
print("   EDGE CASE: c < 2(n-2) <= 2p uses n-2 <= p, true since p >= n-2 : OK")
print("   NOTE: the write-up's Phi_e(q) | |S*|*gcd(e,q-1) step needs p not dividing")
print("   gcd(e,q-1) <= 5, guaranteed by p > 5.  Checked.")

# ---------------------------------------------------------------- (SZ')
hdr("(SZ') constants")
print("row 2 gap q=p^f >= n-3 -> at p=2, f >= log2(n-3); 3f(p-1) >= 3 log2(n-3)")
print("   ell* < n/(3 log2(n-3)) = %.6f * n/ln(n-3)   (claim 0.2310)" % (log(2)/3))
print("   c = 6 f1 ell* <= 12 ell* < %.6f n/ln(n-3)   (claim 2.7726)" % (12*log(2)/3))
print("row 3 gap q^2 >= n-3 -> f >= 0.5 log2(n-3); 10f(p-1) >= 5 log2(n-3)")
print("   ell* < %.6f n/ln(n-3)  (claim 0.1386); c < %.6f n/ln(n-3) (claim 1.6636)"
      % (log(2)/5, 12*log(2)/5))
print("   J(n) row2 = 6/2.7726 = %.4f ln(n-3) - 1  (claim 2.164)" % (6/(12*log(2)/3)))
print("   J(n) row3 = 6/1.6636 = %.4f ln(n-3) - 1  (claim 3.607)" % (6/(12*log(2)/5)))
print("verify minimisation of f(p-1) over p^f >= X is at p=2:")
for X in (10**3, 10**6, 10**9):
    vals = [(p, log(X)/log(p)*(p-1)) for p in (2,3,5,7,11,13)]
    print("   X=%-10s" % X, ["%d:%.2f" % v for v in vals])
print("NC-gen+ side condition p^2 > n, i.e. n > (j+1)^2 with j+1 <= 2.164 ln(n-3):")
bad = [n for n in range(40, 10**6, 7) if n <= (2.164*log(n-3))**2]
print("   n in [40,1e6) violating n > (2.164 ln(n-3))^2 :", bad[:8] or "none")

# ---------------------------------------------------------------- MASTER etc
hdr("MASTER / SIZE-UP / Q-LB / Lemma Q")
print("MASTER: N f (p-1) n(n-2) <= 6 f1 F(q)   [from c=M/F(q) and c<=6f1(n-1)/(Nf(p-1))]")
print("SIZE-UP: N f (p-1) <= (n-1)/L_min")
print("  row2 f=1 consistency: q <= (n+5)/6 vs gap q >= n-3  =>  n >= 5 :",
      all((n+5)/6 < n-3 for n in range(5, 100)))
print("Q-LB constant chase, row 2:")
print("  q^2+q+1 <= 1.01 q^2  <=>  q >= %.3f" % ((1+ (1+4*0.01*1)**0.5)/(2*0.01)))
print("  n(n-2) >= 0.999 n^2  <=>  n >= 2000  (!!) : n=40 gives ratio %.6f"
      % ((40*38)/40**2))
print("  -> the constant 0.999 needs n >= 2000, not n >= 40.  With n>=40 the true")
print("     ratio is 0.95, which changes 8.1 to %.3f" % (8.1*0.999/0.95))
print("crossover: log n > f log(8.1/f); max over f>=2:")
best = max((f*log(8.1/f), f) for f in range(2, 12))
for f in range(2, 10): print("   f=%d : %.4f" % (f, f*log(8.1/f)))
print("   max = %.4f at f=%d  =>  n > %.2f  (claim n>=20)" % (best[0], best[1], exp(best[0])))
print("   with the honest 8.5 in place of 8.1: max = %.4f -> n > %.1f"
      % (max(f*log(8.5/f) for f in range(2,12)), exp(max(f*log(8.5/f) for f in range(2,12)))))

# ---------------------------------------------------------------- Theorem U
hdr("v_task46 Theorem U -- the 1994 witness and the threshold logic")
k, q, c = 1994, 16256, 30
lhs = k**3 - k; rhs = c*(q*q + q + 1)
print("1994^3 - 1994 =", lhs)
print("30*(16256^2+16256+1) =", rhs, "  EQUAL:", lhs == rhs)
print("16256 = 2^7 * 127 :", sympy.factorint(16256), " -> not a prime power")
X = 4*c*k; Y = 4*c*c*(2*q+1)
print("Weierstrass point: X = 4ck =", X, " Y = 4c^2(2q+1) =", Y)
E = lambda x: x**3 - 16*c*c*x - 48*c**4
print("Y^2 - (X^3-16c^2X-48c^4) =", Y*Y - E(X), " (0 means on E_c)")
print("divisibility 4c|X:", X % (4*c) == 0, "  4c^2|Y:", Y % (4*c*c) == 0,
      "  Y/(4c^2) odd:", (Y//(4*c*c)) % 2 == 1)
print("log X = %.4f" % log(X))
print("THRESHOLD-1 (n > c/2)    : 2 log c + log 2 = %.4f" % (2*log(c)+log(2)))
print("THRESHOLD-1 honest (c/2.26): %.4f" % (log(4*c*c/2.26)))
print("THRESHOLD-2 (f=2, n>c^3/32.5): 4 log c - 2.093 = %.4f" % (4*log(c)-2.093))
print()
print("*** THE LOGICAL GAP ***")
print("(ii) is 'B(c) < log(4c(n-1)) for every admissible (c,n) with n >= N0'.")
print("The binding n is n_min(c) = max(N0, c/2.26).  v_task46 silently takes N0")
print("small.  But the row only needs closing ABOVE the scan floor N0 = 1e11.")
for N0 in (1995, 10**4, 10**7, 10**11):
    thr = log(4*c*max(N0, c/2.26))
    print("   N0 = %-12s -> required B(30) < %.4f ; witness forces B(30) >= %.4f -> %s"
          % (N0, thr, log(X), "CONTRADICTION" if log(X) >= thr else "no contradiction"))
print("   break-even: the witness bites only if N0 <= %.0f" % (X/(4*c)+1))
print("   i.e. only if one insists on closing the row from n = 1995 upward.")

# ---------------------------------------------------------------- Theorem W
hdr("Theorem W and Theorem L3_2-gen")
def W(e, x):
    r = 1
    for p, a in sympy.factorint(x).items():
        if p != e and p % e != 1: r *= p**a
    return r
print("(W): W_e(M)=W_e(c) is immediate from M=c*Phi_e(q) and (F2)+(F3).")
print("spot check: for M=n(n-1)(n-2), W_3(M) < 2n happens for what fraction of n?")
cnt = sum(1 for n in range(10, 3000) if W(3, M(n)) < 2*n)
print("   n in [10,3000): %d / 2990 = %.1f%%" % (cnt, 100*cnt/2990))
# L3_2-gen
hdr("Theorem L3_2-gen: v2(c)=2 and odd part of c built from 3 and primes = 1 mod 3")
def dead(c):
    if c % 4 != 0 or c % 8 == 0: return False
    o = c // 4
    while o % 2 == 0: o //= 2
    return all(p == 3 or p % 3 == 1 for p in sympy.factorint(o))
print("c=12 dead:", dead(12), "  c=6 dead:", dead(6), " c=24 dead:", dead(24))
adm = [c for c in range(6, 20001, 6)]
dd = [c for c in adm if dead(c)]
print("dead multipliers c<=20000, c in 6Z: %d of %d = %.2f%%  (claim 286/3333=8.58%%)"
      % (len(dd), len(adm), 100*len(dd)/len(adm)))
# and verify the theorem itself by exhaustive search on the equation
viol = []
for c in dd[:60]:
    for n in range(4, 40000):
        m = M(n)
        if m % c: continue
        t = m//c
        # t = q^2+q+1 ?
        D = 4*t-3
        r = isqrt(D)
        if r*r == D and (r-1) % 2 == 0: viol.append((c, n, (r-1)//2))
print("counterexamples to L3_2-gen among the first 60 dead c, n<40000:", viol or "none")

# ---------------------------------------------------------------- Lemma SM
hdr("Lemma SM / Corollary")
print("r < 6f1 n/c + 1 = n/ell* + 1 since c = 6 f1 ell* : algebraically exact.")
print("Corollary needs 6n/c >= 1.88 n^{2/3} with c <= 3.19 n^{1/3}: 6/3.19 = %.4f" % (6/3.19))
print("and 1.88 n^{2/3} > c for c <= 3.19 n^{1/3}  <=>  n^{1/3} > 1.697 <=> n > 4.9 : OK")
