from math import comb
# raise the two weakest coverages: L4 (m=2) and S4/L4 (m=1)
def scan(name, f, QMAX):
    hits=[]; mx=0
    for q in range(2, QMAX+1):
        I=f(q); mx=max(mx,I)
        n=int(round((6*I)**(1/3)))+2
        for x in range(max(3,n-4), n+5):
            c=comb(x,3)
            if c==I: hits.append((q,x))
            if c>I: break
    print(f"{name}: q <= {QMAX:,}  =>  verified for all n <= {int((6*mx)**(1/3)):,}   hits: {hits if hits else 'NONE'}", flush=True)
scan("L4     m=2   2(q^3+q^2+q+1)", lambda q: 2*(q**3+q**2+q+1), 5*10**6)
scan("S4/L4  m=1    q^3+q^2+q+1  ", lambda q: q**3+q**2+q+1,     5*10**6)
scan("L3     m=2   2(q^2+q+1)    ", lambda q: 2*(q*q+q+1),       5*10**7)
