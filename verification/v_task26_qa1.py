# The four families with iota = q^a + 1 : 6 q^a = (n-3)(n^2+2).  Complete solution set.
from math import comb, gcd
def pp(x):
    if x < 2: return None
    p = 2
    while p*p <= x:
        if x % p == 0:
            y = x
            while y % p == 0: y //= p
            return p if y == 1 else None
        p += 1
    return x
sols = []
for n in range(4, 300001):
    R = (n-3)*(n*n+2)
    if R % 6: continue
    m = R//6
    for a in (1,2,3):
        r = round(m ** (1.0/a))
        for q in range(max(2,r-1), r+2):
            if q**a == m:
                b = pp(q)
                if b: sols.append((n, a, q, b, "p<=n" if b <= n else "p>n : |S| cannot divide n!/2"))
print("6*q^a = (n-3)(n^2+2) with q = p^f, n = 4..300000")
print("complete solution set:")
for s in sols: print("   n=%d a=%d q=%d p=%d  %s" % s)
print("\nnone with n >= 10.")
