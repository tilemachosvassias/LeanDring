from math import comb, gcd, factorial
def vp(n,p):
    s=0;pk=p
    while pk<=n: s+=n//pk; pk*=p
    return s
def divides(order,n):
    m=order;p=2
    while p<=n and m>1:
        if m%p==0:
            e=0
            while m%p==0: m//=p;e+=1
            if e>vp(n,p)-(1 if p==2 else 0): return False,f"p={p}: needs {p}^{e}, have {p}^{vp(n,p)-(1 if p==2 else 0)}"
        p+=1
    return (m==1), ("prime factor > n" if m>1 else "ok")
ORD = {"L2":lambda q:q*(q*q-1)//gcd(2,q-1), "L3":lambda q:q**3*(q**3-1)*(q**2-1)//gcd(3,q-1),
 "U3":lambda q:q**3*(q**3+1)*(q**2-1)//gcd(3,q+1),
 "S4/L4":lambda q:q**4*(q**4-1)*(q**2-1)//gcd(2,q-1),
 "U4":lambda q:q**6*(q**4-1)*(q**3+1)*(q**2-1)//gcd(4,q+1),
 "G2/Sp6":lambda q:q**6*(q**6-1)*(q**2-1), "L5":lambda q:q**10*(q**5-1)*(q**4-1)*(q**3-1)*(q**2-1)//gcd(5,q-1),
 "U5":lambda q:q**10*(q**5+1)*(q**4-1)*(q**3+1)*(q**2-1)//gcd(5,q+1),
 "Sz":lambda q:q*q*(q*q+1)*(q-1), "Ree":lambda q:q**3*(q**3+1)*(q-1)}
rows=[]
for line in open("mscan.out"):
    line=line.strip()
    if not line.startswith("m="): continue
    parts=line.split()
    m=int(parts[0][2:]); nm=parts[1]; q=int(parts[2][2:]); p=int(parts[3][2:]); n=int(parts[4][2:])
    rows.append((m,nm,q,p,n))
surv=[]
print(f"{len(rows)} numeric solutions; applying |S| divides n!/2\n")
for (m,nm,q,p,n) in sorted(rows):
    # Suzuki/Ree existence conditions
    if nm=="Sz" and not (p==2 and q>=8): reason="Sz(q) needs q=2^odd>=8"; ok=False
    elif nm=="Ree" and not (p==3 and q>=27): reason="Ree(q) needs q=3^odd>=27"; ok=False
    else: ok,reason = divides(ORD[nm](q), n)
    if ok: surv.append((m,nm,q,n)); print(f"   SURVIVES: m={m} {nm}({q}) n={n}")
print(f"\nsurvivors after divisibility + family-existence filter: {len(surv)}")
for s in surv: print("   ", s)
