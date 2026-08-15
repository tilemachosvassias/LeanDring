from math import comb, gcd, isqrt
import sys
NMAX = 100000
# For each n and each family, solve iota_family(q) = C(n,3) exactly for integer q,
# then test whether q is a prime power p^f with p <= n (else |S| cannot divide n!/2).
def introot(x, k):
    if x < 0: return None
    r = round(x ** (1.0/k))
    for c in range(max(0,r-2), r+3):
        if c**k == x: return c
    return None
def is_pp_smallprime(q, n):
    """is q = p^f with p <= n?"""
    if q < 2: return None
    p = 2
    while p <= min(n, isqrt(q)+1):
        if q % p == 0:
            y = q; f = 0
            while y % p == 0: y //= p; f += 1
            return (p, f) if y == 1 else None
        p += 1
    return None            # remaining prime factor > n (or q prime > n)
def solve(K):
    """candidate q per family with iota(q) = K"""
    out = []
    out.append(("L2", K-1))
    d = 4*K-3                                   # q^2+q+1=K
    s = isqrt(d)
    if s*s == d and (s-1) % 2 == 0: out.append(("L3", (s-1)//2))
    r = introot(K-1,3)
    if r: out.append(("U3", r)); out.append(("Ree", r))
    r = introot(K-1,2)
    if r: out.append(("Sz", r))
    for nm, k in (("S4",3), ("U4",4), ("L4",3), ("G2",5), ("Sp6",5), ("L5",4), ("U5",7)):
        a = round(K ** (1.0/k))
        for q in range(max(2,a-3), a+4):
            v = {"S4": (q*q+1)*(q+1), "U4": (q**3+1)*(q+1), "L4": (q**4-1)//(q-1) if q>1 else 0,
                 "G2": (q**6-1)//(q-1) if q>1 else 0, "Sp6": (q**6-1)//(q-1) if q>1 else 0,
                 "L5": (q**5-1)//(q-1) if q>1 else 0, "U5": (q**5+1)*(q*q+1)}[nm]
            if v == K: out.append((nm, q))
    return out
hits = []
for n in range(9, NMAX+1):
    K = comb(n,3)
    for nm, q in solve(K):
        if q is None or q < 2: continue
        pp = is_pp_smallprime(q, n)
        if pp: hits.append((n, nm, q, pp[0], pp[1]))
print(f"scanned n = 9..{NMAX}")
print(f"solutions of  iota_family(q) = C(n,3)  with q a prime power p^f, p <= n :  {len(hits)}")
for h in hits[:40]: print("   n=%d family=%s q=%d p=%d f=%d" % h)
