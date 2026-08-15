#!/usr/bin/env python3
"""v_task38_sporadic.py -- the SPORADIC row of the Theorem-AT input list, in
the TRANSPORTED setting (v_task34 orbit multipliers).

NOTES.md 4aj Debt(B) obs. 1 says "the largest bound in play is Fi24' at
iota <= 4.86e9, i.e. n <~ 3100; for n > 3100 no sporadic can be a large-iota
factor".  That understates the bound: B and M have much larger iota, and the
orbit multiplier l (Lemma TR-1) was not yet available when it was written.
Recomputed here.

Facts used:
  iota_ub(S) = smallest nontrivial conjugacy class size (N(<x>) >= C(x)),
               from v_task24_spor_iota_out.txt (CTblLib, all 26).
  Lemma F     iota(K<=Abar) <= e*iota(S), e = |Out S| <= 2 for sporadics.
  Lemma TO-0  iota(T) <= min P: a twin survives only if EVERY orbit has
               l_O * iota(K<=Abar)_O >= C(n,3).
  Lemma TO-2  l * log|S| <= log(n!/2).
  p-part      l * v_p(|S|) <= v_p(n!) for every prime p.

Part A: exact solutions of  l*m*iota_ub(S) = C(n,3),  m <= |Out S|.
Part B: the largest n for which a sporadic socle factor is possible at all.
"""
from math import lgamma, log
rows=[l.split() for l in open("v_task24_spor_iota_out.txt") if l.strip()]
E={ "M11":1,"M12":2,"M22":2,"M23":1,"M24":1,"J1":1,"J2":2,"J3":2,"HS":2,
    "McL":2,"He":2,"Ru":1,"Suz":2,"Co1":1,"Co2":1,"Co3":1,"Fi22":2,"Fi23":1,
    "Fi24'":2,"HN":2,"Th":1,"ON":2,"Ly":1,"J4":1,"B":1,"M":1 }
def factor(m):
    f={}; d=2
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1; m//=d
        d+=1
    if m>1: f[m]=f.get(m,0)+1
    return f
def vp_fact(n,p):
    v=0; pk=p
    while pk<=n: v+=n//pk; pk*=p
    return v
def solve(P):
    n=round(P**(1/3))
    for c in range(max(3,n-3),n+4):
        if c*(c-1)*(c-2)==P: return c
    return 0
print("=== A. exact solutions of  l*m*iota_ub(S) = C(n,3), with the p-part filter ===")
hits=0
for name,order,iub in rows:
    o=int(order); i=int(iub); e=E[name]; lo=log(o); fo=factor(o)
    for l in range(1,201):
        nb=int((6*l*e*i)**(1/3))+3
        if lgamma(nb+1)-log(2) < l*lo: break
        for m in (1,2):
            if m>e: continue
            n=solve(6*l*m*i)
            if not(n and n>=10): continue
            if lgamma(n+1)-log(2) < l*lo: continue
            bad=[p for p,a in fo.items() if l*a > vp_fact(n,p)]
            tag="KILLED by p-part at p=%s"%bad[0] if bad else "*** LIVE COINCIDENCE ***"
            print("  %-6s l=%-3d m=%d n=%-8d %s"%(name,l,m,n,tag))
            if not bad: hits+=1
print("  live coincidences: %d"%hits)
print()
print("=== B. largest n admitting a sporadic socle factor at all ===")
def pred(n,lo,e,i):
    l=int((lgamma(n+1)-log(2))/lo)
    return l>=1 and l*e*i>=n*(n-1)*(n-2)//6
worst=0; wn=None
for name,order,iub in rows:
    o=int(order); i=int(iub); e=E[name]; lo=log(o)
    n=10; n0=None
    while n<4*10**10:
        if pred(n,lo,e,i): n0=n; break
        n = n+1 if n<400 else int(n*1.02)+1
    if n0 is None: print("  %-6s NONE"%name); continue
    a,b=n0,4*10**10
    while b-a>1:
        mid=(a+b)//2
        if pred(mid,lo,e,i): a=mid
        else: b=mid
    print("  %-6s  possible only for n <= %d"%(name,a))
    if a>worst: worst,wn=a,name
print("  WORST: %s -- no twin of A_n has a sporadic socle factor once n > %d"%(wn,worst))
