from math import comb, gcd, isqrt
QMAX = 400000
sieve = bytearray([1])*(QMAX+1); sieve[0]=sieve[1]=0
for i in range(2, isqrt(QMAX)+1):
    if sieve[i]: sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
pps = []
for p in range(2, QMAX+1):
    if sieve[p]:
        q = p; f = 1
        while q <= QMAX: pps.append((q,p,f)); f += 1; q *= p
def n_of(I):                      # exact inverse of C(n,3), no cap on n
    if I < 1: return None
    n = int(round((6*I)**(1/3))) + 2
    for m in range(max(3,n-5), n+6):
        c = comb(m,3)
        if c == I: return m
        if c > I: break
    return None
FAM = {"L3":  lambda q: q*q+q+1,
       "S4/L4":lambda q: (q*q+1)*(q+1),
       "U4":  lambda q: (q**3+1)*(q+1),
       "G2/Sp6":lambda q:(q**6-1)//(q-1),
       "L5":  lambda q: (q**5-1)//(q-1),
       "U5":  lambda q: (q**5+1)*(q*q+1)}
hits=[]; cover={}
for nm, f in FAM.items():
    mx = 0
    for (q,p,e) in pps:
        if q < 2: continue
        I = f(q)
        n = n_of(I)
        if n is not None:
            if p <= n: hits.append((nm,q,p,e,n))
        # coverage: largest n such that every solution with that n has q <= QMAX
        mx = max(mx, I)
    cover[nm] = mx
print(f"prime powers q <= {QMAX};  no cap on n")
print("family      max iota reached          => verified for all n up to")
for nm in FAM:
    I = cover[nm]; n = int((6*I)**(1/3))
    print(f"  {nm:<9} {I:<28} n <= {n:,}")
print()
print("solutions iota_F(q) = C(n,3) with q = p^f, p <= n :", hits if hits else "NONE")
