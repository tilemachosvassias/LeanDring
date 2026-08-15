from math import comb, isqrt
QMAX = 6*10**6
sieve = bytearray([1])*(QMAX+1); sieve[0]=sieve[1]=0
for i in range(2, isqrt(QMAX)+1):
    if sieve[i]: sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
def n_of(I):
    n = int(round((6*I)**(1/3))) + 2
    for m in range(max(3,n-5), n+6):
        c = comb(m,3)
        if c == I: return m
        if c > I: break
    return None
hits=[]; mx=0
for p in range(2, QMAX+1):
    if not sieve[p]: continue
    q=p; f=1
    while q <= QMAX:
        I = (q*q+1)*(q+1); mx=max(mx,I)
        n = n_of(I)
        if n is not None and p <= n: hits.append((q,p,f,n))
        f+=1; q*=p
print(f"S4/L4, q <= {QMAX}: max iota = {mx}  => verified for all n <= {int((6*mx)**(1/3)):,}")
print("solutions:", hits if hits else "NONE")
