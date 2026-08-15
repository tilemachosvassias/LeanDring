from fractions import Fraction
def divisors(n):
    return [d for d in range(1,n+1) if n%d==0]
def phi(n):
    r=n; m=n; p=2
    while p*p<=m:
        if m%p==0:
            while m%p==0: m//=p
            r-=r//p
        p+=1
    if m>1: r-=r//m
    return r
def spec(terms):
    """terms: list of (d, sign) meaning q^d - 1 (sign=-1) or q^d + 1 (sign=+1)"""
    from collections import Counter
    c=Counter()
    for (d,s) in terms:
        if s<0:
            for e in divisors(d): c[e]+=1
        else:
            for e in divisors(2*d):
                if d % e != 0: c[e]+=1
    return c
def rep(c):
    return " ".join("Phi%d^%d"%(e,m) if m>1 else "Phi%d"%e for e,m in sorted(c.items()))

cases = {
 "F4":  ([(12,-1),(8,-1),(6,-1),(2,-1)], 52, 24),
 "E6":  ([(12,-1),(9,-1),(8,-1),(6,-1),(5,-1),(2,-1)], 78, 36),
 "2E6": ([(12,-1),(9,+1),(8,-1),(6,-1),(5,+1),(2,-1)], 78, 36),
 "E7":  ([(18,-1),(14,-1),(12,-1),(10,-1),(8,-1),(6,-1),(2,-1)], 133, 63),
 "E8":  ([(30,-1),(24,-1),(20,-1),(18,-1),(14,-1),(12,-1),(8,-1),(2,-1)], 248, 120),
}
print("family  spectrum                                              M  sum m_e phi(e)  a-N")
for k,(terms,a,N) in cases.items():
    c=spec(terms)
    M=max(m*phi(e) for e,m in c.items())
    s=sum(m*phi(e) for e,m in c.items())
    print("%-5s %-55s %-3d %-4d %-4d %s" % (k, rep(c), M, s, a-N, "ok" if s==a-N else "*** MISMATCH"))
print()
print("Sp/O towers: claim M = n")
for n in range(3,13):
    tC = [(2*i,-1) for i in range(1,n+1)]
    c=spec(tC); M=max(m*phi(e) for e,m in c.items()); s=sum(m*phi(e) for e,m in c.items())
    print("  C%-3d M=%-3d (claim %d) %s  sum=%d a-N=%d %s" % (n,M,n,"ok" if M==n else "***",s,(2*n*n+n)-n*n,"ok" if s==(2*n*n+n)-n*n else "***"))
for n in range(4,13):
    tD = [(n,-1)]+[(2*i,-1) for i in range(1,n)]
    c=spec(tD); M=max(m*phi(e) for e,m in c.items()); s=sum(m*phi(e) for e,m in c.items())
    tE = [(n,+1)]+[(2*i,-1) for i in range(1,n)]
    c2=spec(tE); M2=max(m*phi(e) for e,m in c2.items())
    print("  D%-3d M=%-3d  2D%-3d M=%-3d (claim %d each)  %s" % (n,M,n,M2,n,"ok" if (M<=n and M2<=n) else "*** M>n"))
