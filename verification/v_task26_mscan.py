from math import comb, gcd, isqrt
# iota(T) = m * iota(S_i) EXACTLY (m = #S_i-classes fused by T, m | c).
# So separation fails only if  iota(S) = C(n,3)/m  for some small m.  Scan m = 1..8.
QMAX = 300000
sieve = bytearray([1])*(QMAX+1); sieve[0]=sieve[1]=0
for i in range(2, isqrt(QMAX)+1):
    if sieve[i]: sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
pps=[]
for p in range(2,QMAX+1):
    if sieve[p]:
        q=p; f=1
        while q<=QMAX: pps.append((q,p)); f+=1; q*=p
def n_of_times(I, m):        # solve C(n,3) = m*I
    t = m*I
    n = int(round((6*t)**(1/3)))+2
    for x in range(max(3,n-5), n+6):
        c = comb(x,3)
        if c == t: return x
        if c > t: break
    return None
FAM = {"L3":lambda q:q*q+q+1, "S4/L4":lambda q:(q*q+1)*(q+1), "U4":lambda q:(q**3+1)*(q+1),
       "G2/Sp6":lambda q:(q**6-1)//(q-1), "L5":lambda q:(q**5-1)//(q-1),
       "U5":lambda q:(q**5+1)*(q*q+1), "L2":lambda q:q+1, "U3":lambda q:q**3+1,
       "Sz":lambda q:q*q+1, "Ree":lambda q:q**3+1}
hits=[]
for m in range(1,9):
    for nm,f in FAM.items():
        for (q,p) in pps:
            I=f(q)
            n=n_of_times(I,m)
            if n is not None and p<=n: hits.append((m,nm,q,p,n,I,comb(n,3)))
print(f"prime powers q <= {QMAX}, m = 1..8")
print(f"solutions of  m * iota_F(q) = C(n,3)  with q=p^f, p<=n :  {len(hits)}")
for h in sorted(hits): print("   m=%d %s q=%d p=%d n=%d  iota=%d  C(n,3)=%d" % h)
