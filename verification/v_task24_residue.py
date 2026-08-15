from math import factorial, gcd, comb
from itertools import combinations_with_replacement
spor = {}
for line in open("spor2.out"):
    p = line.split()
    if len(p) == 3: spor[p[0]] = (int(p[1]), int(p[2]))
SPOR_OUT = {"M11":1,"M12":2,"M22":2,"M23":1,"M24":1,"J1":1,"J2":2,"J3":2,"HS":2,"McL":2,
            "He":2,"Ru":1,"Suz":2,"Co1":1,"Co2":1,"Co3":1,"Fi22":2,"Fi23":1,"Fi24'":2,
            "HN":2,"Th":1,"ON":2,"Ly":1,"J4":1,"B":1,"M":1}
def primes_upto(n): return [p for p in range(2,n+1) if all(p%r for r in range(2,int(p**.5)+1))]
def iota_alt(m): return {5:5,6:10,7:35,8:15}.get(m, comb(m,3))
# family: order, iota upper bound (minimal parabolic / isotropic-point index), Out, qmin
FAM = [
 ("L2", lambda q:q*(q*q-1)//gcd(2,q-1),                                  lambda q:q+1,
        lambda q,p,f:gcd(2,q-1)*f, 4),
 ("L3", lambda q:q**3*(q**3-1)*(q**2-1)//gcd(3,q-1),                     lambda q:q*q+q+1,
        lambda q,p,f:gcd(3,q-1)*2*f, 2),
 ("U3", lambda q:q**3*(q**3+1)*(q**2-1)//gcd(3,q+1),                     lambda q:q**3+1,
        lambda q,p,f:gcd(3,q+1)*2*f, 3),
 ("S4", lambda q:q**4*(q**4-1)*(q**2-1)//gcd(2,q-1),                     lambda q:(q*q+1)*(q+1),
        lambda q,p,f:f*(2 if p==2 else 1)*gcd(2,q-1), 3),
 ("L4", lambda q:q**6*(q**4-1)*(q**3-1)*(q**2-1)//gcd(4,q-1),            lambda q:(q**4-1)//(q-1),
        lambda q,p,f:gcd(4,q-1)*2*f, 2),
 ("U4", lambda q:q**6*(q**4-1)*(q**3+1)*(q**2-1)//gcd(4,q+1),            lambda q:(q**3+1)*(q+1),
        lambda q,p,f:gcd(4,q+1)*2*f, 2),
 ("G2", lambda q:q**6*(q**6-1)*(q**2-1),                                 lambda q:(q**6-1)//(q-1),
        lambda q,p,f:f*(2 if p==3 else 1), 3),
 ("Sp6",lambda q:q**9*(q**6-1)*(q**4-1)*(q**2-1)//gcd(2,q-1),            lambda q:(q**6-1)//(q-1),
        lambda q,p,f:gcd(2,q-1)*f, 2),
 ("L5", lambda q:q**10*(q**5-1)*(q**4-1)*(q**3-1)*(q**2-1)//gcd(5,q-1),  lambda q:(q**5-1)//(q-1),
        lambda q,p,f:gcd(5,q-1)*2*f, 2),
 ("U5", lambda q:q**10*(q**5+1)*(q**4-1)*(q**3+1)*(q**2-1)//gcd(5,q+1),  lambda q:(q**5+1)*(q*q+1),
        lambda q,p,f:gcd(5,q+1)*2*f, 2),
]
def cands(N, n):
    res = []
    m = 5
    while factorial(m)//2 <= N:
        o = factorial(m)//2
        if o < N and N % o == 0: res.append((f"A{m}", o, iota_alt(m), 4 if m==6 else 2, True))
        m += 1
    for p in primes_upto(n):                      # every prime divisor of |S| divides N, so p <= n
        f = 1; q = p
        while q <= N:
            for nm, of, iof, outf, qmin in FAM:
                if q < qmin: continue
                o = of(q)
                if o < N and o > 1 and N % o == 0:
                    res.append((f"{nm}({q})", o, iof(q), outf(q,p,f), False))
            if p == 2 and f % 2 == 1 and q >= 8:  # Sz(q)
                o = q*q*(q*q+1)*(q-1)
                if o < N and N % o == 0: res.append((f"Sz({q})", o, q*q+1, f, False))
            if p == 3 and f % 2 == 1 and q >= 27: # Ree(q)
                o = q**3*(q**3+1)*(q-1)
                if o < N and N % o == 0: res.append((f"Ree({q})", o, q**3+1, f, False))
            f += 1; q *= p
    for nm,(o,cs) in spor.items():
        if o < N and N % o == 0: res.append((nm, o, cs, SPOR_OUT[nm], False))
    return res
print("  n   C(n,3)  #cand  #bad   surviving all-large-iota factorizations (k<=5, exact Out)")
tot = 0; worst = []
for n in range(5, 101):
    N = factorial(n)//2
    K = comb(n,3) if n >= 9 else iota_alt(n)
    cs = cands(N, n)
    bad = [c for c in cs if not c[4] and c[2] >= K]
    hits = []
    for k in range(1, 6):
        for combo in combinations_with_replacement(bad, k):
            P = 1
            for c in combo: P *= c[1]
            if P > N or N % P: continue
            c0 = N // P
            outp = 1
            for c in combo: outp *= c[3]
            if outp % c0 == 0: hits.append(" * ".join(c[0] for c in combo)+f" * c={c0}")
    tot += len(hits)
    if hits or n % 10 == 0 or n < 12:
        print(f"{n:>3} {K:>8} {len(cs):>6} {len(bad):>5}   " + ("; ".join(hits) if hits else "-- none --"))
print(f"\nTOTAL surviving all-large-iota factorizations, n = 5..100:  {tot}")
