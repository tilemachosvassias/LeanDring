#!/usr/bin/env python3
"""v_task38_table_checks.py  --  the finite checks of the rewritten conclusion
table of NOTES.md 4at/4au, restated with

  * PAIR invariants (v_task36: a1 = f1*iota1, a2 = f2*iota2, R^p = (f2/f1)R),
  * the prime / non-prime split (v_task32),
  * erratum 1 of 4aw (orbit multiplier l is free -> degree-mismatch kills are
    replaced by Lemma TO-2, the order squeeze),
  * erratum 2 of 4aw (the non-prime kills are SIZE kills, not divisibility).

Branches checked, all with exact integer / Fraction arithmetic:

  (a)  one orbit carries both conductors:      R^p = (n-3)/4
  (b1) two orbits, 3rd value from O*:         R^p = 3(n-3)/4
  (b2) two orbits, 3rd value from O**:        R^p = 3
  (b3) 4th-value sub-branches:                R^p in {4, 4/3}

In every branch the surviving (F,q,Abar,n) must additionally satisfy

  DIV   l = C(n,3)/(f1*iota1) in Z_{>0}          (or C(n,4)/(f1*iota1) in
                                                  branches where O* is the
                                                  iota2-carrying orbit)
  SIZE  |S| > C(n,4)                             (v_task37 Step 1)
  pPART l*f*N <= v_p(n!)                         (|S|_p = q^N)
  ORDER l*log|S| <= log(n!/2)                    (Lemma TO-2)

Output: one line per (family, Abar-type, branch) with the number of survivors.
"""
from fractions import Fraction as F
from math import lgamma, log, isqrt
import sys

QMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 20000

# ---------------- prime powers ----------------
def sieve(n):
    s = [True]*(n+1); s[0]=s[1]=False
    for i in range(2, isqrt(n)+1):
        if s[i]:
            for j in range(i*i, n+1, i): s[j]=False
    return s
S = sieve(QMAX)
PP = []                       # (q, p, f)
for q in range(2, QMAX+1):
    if S[q]: PP.append((q,q,1)); continue
    for p in range(2, isqrt(q)+1):
        if not S[p]: continue
        v, f = p, 1
        while v < q: v*=p; f+=1
        if v == q: PP.append((q,p,f)); break

def vp_fact(n,p):
    v=0; pk=p
    while pk<=n: v+=n//pk; pk*=p
    return v
def C(n,k):
    r=1
    for i in range(k): r=r*(n-i)
    for i in range(1,k+1): r//=i
    return r

# ---------------- family data ----------------
# name -> (iota1(q), |S|(q), N, admissible (f1,f2,R^p) list as a function of q)
def gcd(a,b):
    while b: a,b=b,a%b
    return a

def dat_L3(q,p,f):
    i1=q*q+q+1; i2=(q+1)*i1
    o=q**3*(q**3-1)*(q**2-1)//gcd(3,q-1)
    return i1,i2,o,3,[(1,1),(2,1)]           # Abar without / with graph
def dat_L4(q,p,f):
    i1=(q+1)*(q*q+1); i2=(q*q+1)*(q*q+q+1)
    o=q**6*(q**2-1)*(q**3-1)*(q**4-1)//gcd(4,q-1)
    return i1,i2,o,6,[(1,1),(2,1)]
def dat_L5(q,p,f):
    i1=(q**5-1)//(q-1); i2=(q**5-1)*(q**4-1)//((q-1)*(q**2-1))
    o=q**10*(q**2-1)*(q**3-1)*(q**4-1)*(q**5-1)//gcd(5,q-1)
    return i1,i2,o,10,[(1,1),(2,2)]
def dat_U4(q,p,f):
    if q<3: return None
    i1=(q+1)*(q**3+1); i2=(q*q+1)*(q**3+1)
    o=q**6*(q**2-1)*(q**3+1)*(q**4-1)//gcd(4,q+1)
    return i1,i2,o,6,[(1,1)]
def dat_S4(q,p,f):
    i1=(q+1)*(q*q+1)
    o=q**4*(q**2-1)*(q**4-1)//gcd(2,q-1)
    if p!=2 and f==1:
        if q<5: return None
        return i1, q*q*(q*q+1)//2, o, 4, [(1,1)]
    t=(q-1)//(p-1)                                   # subfield trap, q0=p
    if f==1: return None
    if p==2:  return i1, t*i1, o, 4, [(1,1),(2,2)]
    return i1, t*i1, o, 4, [(1,1),(1,2)]             # (1,2): diagonal present
def dat_Sp6(q,p,f):
    i1=(q**6-1)//(q-1)
    o=q**9*(q**2-1)*(q**4-1)*(q**6-1)//gcd(2,q-1)
    if f==1: return i1,(q+1)*(q*q+1)*(q**3+1),o,9,[(1,1)]
    t=(q-1)//(p-1)
    return i1,t*i1,o,9,[(1,1)] if p==2 else [(1,1),(1,2)]
def dat_U5(q,p,f):
    i1=(q**5+1)*(q*q+1)
    o=q**10*(q**2-1)*(q**3+1)*(q**4-1)*(q**5+1)//gcd(5,q+1)
    if f==1: return i1,q**4*(q**5+1)//(q+1),o,10,[(1,1)]
    t=(q-1)//(p-1)
    return i1,t*i1,o,10,[(1,1)]

FAMS=[("L3",dat_L3),("L4",dat_L4),("L5",dat_L5),("U4",dat_U4),
      ("S4",dat_S4),("Sp6",dat_Sp6),("U5",dat_U5)]

def checks(name,q,p,f,i1,order,N,f1,n,target):
    """target = C(n,3) (O* carries iota) ; returns True if all filters pass."""
    if n<10: return False
    if target % (f1*i1): return False
    l = target//(f1*i1)
    if l<1: return False
    if order <= C(n,4): return False
    if l*f*N > vp_fact(n,p): return False
    if l*log(order) > lgamma(n+1)-log(2): return False
    return (l,)

def run():
    tot=0
    for name,fn in FAMS:
        rows={}
        for (q,p,f) in PP:
            d=fn(q,p,f)
            if d is None: continue
            i1,i2,order,N,pairs=d
            for (f1,f2) in pairs:
                Rp=F(f2*i2, f1*i1)
                key=(name,f1,f2)
                rows.setdefault(key,{"a":[],"b1":[],"b2":[],"b3":[]})
                # (a) R^p = (n-3)/4
                v=4*Rp+3
                if v.denominator==1:
                    n=int(v); r=checks(name,q,p,f,i1,order,N,f1,n,C(n,3))
                    if r: rows[key]["a"].append((q,n,r[0]))
                # (b1) R^p = 3(n-3)/4
                v=4*Rp/3+3
                if v.denominator==1:
                    n=int(v); r=checks(name,q,p,f,i1,order,N,f1,n,C(n,3))
                    if r: rows[key]["b1"].append((q,n,r[0]))
                # (b2)/(b3): n-free ratios; O* here carries C(n,4)
                for tag,val in (("b2",F(3)),("b3",F(4)),("b3",F(4,3))):
                    if Rp!=val: continue
                    # n bounded by Lemma TO-1: |S| > C(n,4)
                    n=10
                    while C(n,4) < order:
                        if C(n,4)%(f1*i1)==0:
                            r=checks(name,q,p,f,i1,order,N,f1,n,C(n,4))
                            if r: rows[key][tag].append((q,n,r[0],str(val)))
                        n+=1
                        if n>3000: break
        for key,br in sorted(rows.items()):
            s=sum(len(v) for v in br.values()); tot+=s
            print("%-4s f1=%d f2=%d : (a)=%d (b1)=%d (b2)=%d (b3)=%d %s"%(
                key[0],key[1],key[2],len(br["a"]),len(br["b1"]),len(br["b2"]),
                len(br["b3"]),
                "" if s==0 else " SURVIVORS "+str(br)))
    print("# q scanned: prime powers <= %d   TOTAL SURVIVORS: %d"%(QMAX,tot))

if __name__=="__main__":
    run()
