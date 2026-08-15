from math import comb, gcd, isqrt
QMAX = 10**7
# sieve primes up to QMAX
sieve = bytearray([1])*(QMAX+1); sieve[0]=sieve[1]=0
for i in range(2, isqrt(QMAX)+1):
    if sieve[i]: sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
primes = [i for i in range(2, QMAX+1) if sieve[i]]
pps = []                      # (q, p, f)
for p in primes:
    q = p; f = 1
    while q <= QMAX:
        pps.append((q, p, f)); f += 1; q *= p
def n_of(I):                  # solve C(n,3) = I
    n = round((6*I)**(1/3)) + 2
    for m in range(max(3, n-4), n+4):
        if comb(m,3) == I: return m
    return None
EQS = [
 ("L2",  lambda q: q+1,              lambda q: q*(q*q-1)//gcd(2,q-1)),
 ("L3",  lambda q: q*q+q+1,          lambda q: q**3*(q**3-1)*(q**2-1)//gcd(3,q-1)),
 ("U3",  lambda q: q**3+1,           lambda q: q**3*(q**3+1)*(q**2-1)//gcd(3,q+1)),
 ("S4",  lambda q: (q*q+1)*(q+1),    lambda q: q**4*(q**4-1)*(q**2-1)//gcd(2,q-1)),
 ("L4",  lambda q: (q**4-1)//(q-1),  lambda q: q**6*(q**4-1)*(q**3-1)*(q**2-1)//gcd(4,q-1)),
 ("U4",  lambda q: (q**3+1)*(q+1),   lambda q: q**6*(q**4-1)*(q**3+1)*(q**2-1)//gcd(4,q+1)),
 ("G2",  lambda q: (q**6-1)//(q-1),  lambda q: q**6*(q**6-1)*(q**2-1)),
 ("Sp6", lambda q: (q**6-1)//(q-1),  lambda q: q**9*(q**6-1)*(q**4-1)*(q**2-1)//gcd(2,q-1)),
 ("Sz",  lambda q: q*q+1,            lambda q: q*q*(q*q+1)*(q-1)),
 ("Ree", lambda q: q**3+1,           lambda q: q**3*(q**3+1)*(q-1)),
 ("L5",  lambda q: (q**5-1)//(q-1),  lambda q: q**10*(q**5-1)*(q**4-1)*(q**3-1)*(q**2-1)//gcd(5,q-1)),
 ("U5",  lambda q: (q**5+1)*(q*q+1), lambda q: q**10*(q**5+1)*(q**4-1)*(q**3+1)*(q**2-1)//gcd(5,q+1)),
]
def vfact(n, p):              # v_p(n!)
    s = 0; pk = p
    while pk <= n: s += n//pk; pk *= p
    return s
def divides_nfact(order, n):
    m = order; 
    for p in primes:
        if p > n: break
        if m % p == 0:
            e = 0
            while m % p == 0: m //= p; e += 1
            if e > vfact(n,p) - (1 if p == 2 else 0): return False
    return m == 1
sols = []
for nm, iof, ordf in EQS:
    for (q,p,f) in pps:
        if nm in ("Sz",) and (p != 2 or f % 2 == 0 or f < 3): continue
        if nm in ("Ree",) and (p != 3 or f % 2 == 0 or f < 3): continue
        if q < 2: continue
        try: I = iof(q)
        except Exception: continue
        if I > comb(200000,3): break
        n = n_of(I)
        if n is None: continue
        if p > n: continue                       # |S| cannot divide n!/2
        sols.append((nm, q, p, f, n, divides_nfact(ordf(q), n)))
print(f"prime powers scanned up to {QMAX}")
print(f"solutions of  iota_family(q) = C(n,3)  with q = p^f, p <= n :  {len(sols)}")
for s in sols: print("   family=%s q=%d (p=%d,f=%d)  n=%d  |S| divides n!/2 ? %s" % s)
