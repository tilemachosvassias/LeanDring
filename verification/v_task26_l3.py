from math import comb, isqrt
# L3:  iota = q^2+q+1 = C(n,3).   iota-1 = q(q+1), so 6q(q+1) = (n-3)(n^2+2).
# For p != 11, coprimality (gcd(n-3,n^2+2)|11) puts q into ONE factor; q ~ n^1.5 > n-3,
# so q | n^2+2.  Write n^2+2 = q t.  Then 6(q+1) = (n-3)t, and eliminating q:
#        6 n^2 - t^2 n + (3t^2 + 6t + 12) = 0,
# so the discriminant  D(t) = t^4 - 72 t^2 - 144 t - 288  must be a perfect square.
print("squeeze:  (t^2-37)^2 < D(t) < (t^2-36)^2  for t >= 83 ?")
def D(t): return t**4 - 72*t*t - 144*t - 288
bad = [t for t in range(83, 100000) if not ((t*t-37)**2 < D(t) < (t*t-36)**2)]
print("   counterexamples in 83..10^5:", bad[:5], "(none = squeeze holds)")
print("   [(t^2-36)^2 - D(t) = 144t+1584 > 0;  D(t) - (t^2-37)^2 = 2t^2-144t-1657 > 0 iff t >= 83]")
print()
print("finite check t = 1..82:")
sols = []
for t in range(1, 83):
    d = D(t)
    if d < 0: continue
    s = isqrt(d)
    if s*s == d:
        for sign in (1,-1):
            num = t*t + sign*s
            if num % 12: continue
            n = num//12
            if n >= 4 and 6*n*n - t*t*n + (3*t*t+6*t+12) == 0:
                q = (n*n+2)//t if (n*n+2) % t == 0 else None
                sols.append((t, n, q, q*q+q+1 == comb(n,3) if q else False))
print("   D(t) a perfect square at t =", [t for t in range(1,83) if D(t) >= 0 and isqrt(D(t))**2 == D(t)])
print("   integer (t,n) solutions:", sols)
print()
# independent cross-check: direct scan
hits = [n for n in range(4, 2000001) if (lambda K: (lambda d: d>=0 and isqrt(d)**2==d)(4*K-3))(comb(n,3))]
print("direct scan n = 4..2*10^6 with 4*C(n,3)-3 a perfect square:", hits)
for n in hits:
    K = comb(n,3); q = (isqrt(4*K-3)-1)//2
    print(f"    n={n}: q={q}, q^2+q+1={q*q+q+1}, C(n,3)={K}, match={q*q+q+1==K}")
