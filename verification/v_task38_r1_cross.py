#!/usr/bin/env python3
"""v_task38_r1_cross.py -- independent (q-side) cross-check of the R1 scan.

v_task38_r1_scan.c loops over n and inverts the family shape equations.
This script loops over q and l* instead, so the two searches share no code
path.  Conditions are identical (see the C header):

    GAP  R^p(F,q,f1) > n-3      DIV  l*.f1.iota1 = C(n,3)
    SIZE |S| > C(n,4)           pPART l*.f.N <= v_p(n!)     ORDER  TO-2

Since the gap bounds n above in terms of q, scanning all prime powers
q <= QMAX is complete for every n <= (the per-family coverage printed below).
"""
from fractions import Fraction as F
from math import lgamma, log, isqrt
import sys
QMAX = int(sys.argv[1]) if len(sys.argv)>1 else 3000

def sieve(n):
    s=[True]*(n+1); s[0]=s[1]=False
    for i in range(2,isqrt(n)+1):
        if s[i]:
            for j in range(i*i,n+1,i): s[j]=False
    return s
S=sieve(QMAX); PP=[]
for q in range(2,QMAX+1):
    if S[q]: PP.append((q,q,1)); continue
    for p in range(2,isqrt(q)+1):
        if not S[p]: continue
        v,f=p,1
        while v<q: v*=p; f+=1
        if v==q: PP.append((q,p,f)); break
def vp_fact(n,p):
    v=0;pk=p
    while pk<=n: v+=n//pk; pk*=p
    return v
def C3(n): return n*(n-1)*(n-2)//6
def C4(n): return n*(n-1)*(n-2)*(n-3)//24
def icbrt6(M):
    P=6*M; n=round(P**(1/3))
    for c in range(max(3,n-3),n+4):
        if c*(c-1)*(c-2)==P: return c
    return 0
def g(a,b):
    while b: a,b=b,a%b
    return a

def fam_rows(q,p,f):
    """yield (name, iota1, |S|, N, f1, R^p as Fraction)"""
    if q>=3:
        i1=q*q+q+1; o=q**3*(q**3-1)*(q**2-1)//g(3,q-1)
        yield ("L3",i1,o,3,1,F(q+1)); yield ("L3",i1,o,3,2,F(q+1,2))
    i1=(q+1)*(q*q+1); oL4=q**6*(q**2-1)*(q**3-1)*(q**4-1)//g(4,q-1)
    yield ("L4",i1,oL4,6,1,F(q*q+q+1,q+1)); yield ("L4",i1,oL4,6,2,F(q*q+q+1,2*(q+1)))
    oS4=q**4*(q**2-1)*(q**4-1)//g(2,q-1)
    if p!=2 and f==1 and q>=5: yield ("S4p",i1,oS4,4,1,F(q*q,2*(q+1)))
    if p!=2 and f>=2:          yield ("S4np",i1,oS4,4,1,F(2*(q-1),p-1))
    if p==2 and f>=2:
        yield ("S4e",i1,oS4,4,1,F(q-1)); yield ("S4e",i1,oS4,4,2,F(q-1))
    i1=(q**5-1)//(q-1); o=q**10*(q**2-1)*(q**3-1)*(q**4-1)*(q**5-1)//g(5,q-1)
    yield ("L5",i1,o,10,1,F(q*q+1)); yield ("L5",i1,o,10,2,F(q*q+1))
    if q>=3:
        i1=(q+1)*(q**3+1); o=q**6*(q**2-1)*(q**3+1)*(q**4-1)//g(4,q+1)
        yield ("U4",i1,o,6,1,F(q*q+1,q+1))
    i1=(q**6-1)//(q-1); o=q**9*(q**2-1)*(q**4-1)*(q**6-1)//g(2,q-1)
    yield ("Sp6",i1,o,9,1,F(q**4-1,q**3-1) if f==1 else F(2*(q-1),p-1))
    i1=(q**5+1)*(q*q+1); o=q**10*(q**2-1)*(q**3+1)*(q**4-1)*(q**5+1)//g(5,q+1)
    yield ("U5",i1,o,10,1,F(q**4,(q+1)*(q*q+1)) if f==1 else F(q-1,p-1))

surv=0; cover={}
for (q,p,f) in PP:
    for (name,i1,order,N,f1,Rp) in fam_rows(q,p,f):
        nmax=int(Rp)+3
        while nmax>=3 and F(nmax-3)>=Rp: nmax-=1
        cover[name]=max(cover.get(name,0),nmax)
        if nmax<10: continue
        Cm=C3(nmax); base=f1*i1
        if base>Cm: continue
        l=1
        while l*base<=Cm:
            n=icbrt6(l*base)
            if n>=10 and n<=nmax:
                ok = order>C4(n) and l*f*N<=vp_fact(n,p) and l*log(order)<=lgamma(n+1)-log(2)
                if ok:
                    surv+=1; print("SURVIVOR",name,"q=%d f1=%d l=%d n=%d"%(q,f1,l,n))
            l+=1
print("# q-side R1 cross-check, prime powers q <= %d"%QMAX)
print("# per-family n-coverage (max n whose gap can be met by some q <= QMAX):")
for k in sorted(cover): print("#   %-5s n <= %d"%(k,cover[k]))
print("# SURVIVORS: %d"%surv)
