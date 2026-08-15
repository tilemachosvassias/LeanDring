from fractions import Fraction
from math import gcd
def S4(q): return q**4*(q**2-1)*(q**4-1)//gcd(2,q-1)
def U4(q): return q**6*(q**2-1)*(q**3+1)*(q**4-1)//gcd(4,q+1)
def G2(q): return q**6*(q**6-1)*(q**2-1)
def D43(q): return q**12*(q**8+q**4+1)*(q**6-1)*(q**2-1)
print("S4(m^3) vs U4(m^2)  [v_task57 5.1: 1 < c < 441/425]")
for m in [2,3,4,5,7,8,9,11,13,16,25,32,64,81]:
    c = Fraction(S4(m**3), U4(m**2))
    cf = Fraction(gcd(4,m*m+1), gcd(2,m-1))*Fraction((m**6-1)**2, (m**4-1)*(m**8-1))
    print("  m=%-4d c=%-24s = %.10f   closed-form match: %s   1<c<441/425: %s"
          % (m, c if len(str(c))<24 else "(big)", float(c), c==cf, 1 < c < Fraction(441,425)))
print()
print("3D4(q) vs G2(q^2)  [v_task57 5.1: c = (q^8+q^4+1)/((q^6+1)(q^2+1)) < 1]")
for q in [2,3,4,5,7,8,9,11,16]:
    c = Fraction(D43(q), G2(q*q))
    cf = Fraction(q**8+q**4+1, (q**6+1)*(q**2+1))
    print("  q=%-4d c=%-16s = %.10f  closed form match: %s  c<1: %s" % (q, c, float(c), c==cf, c<1))
print()
print("v_task57 claims |G2(q^2)| > |3D4(q)| always, i.e. c<1  -> confirmed above")
print()
print("(I1) |E6(m^2)|/|F4(m^3)| and (I2) |E6(q)|/|2F4(q^3)|")
def E6(q): return q**36*(q**12-1)*(q**9-1)*(q**8-1)*(q**6-1)*(q**5-1)*(q**2-1)//gcd(3,q-1)
def E6t(q): return q**36*(q**12-1)*(q**9+1)*(q**8-1)*(q**6-1)*(q**5+1)*(q**2-1)//gcd(3,q+1)
def F4(q): return q**24*(q**12-1)*(q**8-1)*(q**6-1)*(q**2-1)
def F42(q): return q**12*(q**6+1)*(q**4-1)*(q**3+1)*(q-1)
for m in [2,3,4,5,7,8,9,11,13,16,25]:
    c1 = Fraction(E6(m*m), F4(m**3)); c2 = Fraction(E6t(m*m), F4(m**3))
    print("  m=%-4d |E6(m^2)|/|F4(m^3)| = %.12f   |2E6(m^2)|/|F4(m^3)| = %.12f" % (m, float(c1), float(c2)))
for f in [1,3,5,7,9,11]:
    q = 2**f
    if f % 2 == 0: continue
    c1 = Fraction(E6(q), F42(q**3)); c2 = Fraction(E6t(q), F42(q**3))
    print("  q=2^%-3d |E6(q)|/|2F4(q^3)| = %.12f  |2E6(q)|/|2F4(q^3)| = %.12f" % (f,float(c1),float(c2)))
print()
print("(J4) |2D_n(q)|/|D_n(q)|")
def Dn(n,q):
    r=q**(n*(n-1))*(q**n-1)
    for i in range(1,n): r*= q**(2*i)-1
    return r//gcd(4,q**n-1)
def D2n(n,q):
    r=q**(n*(n-1))*(q**n+1)
    for i in range(1,n): r*= q**(2*i)-1
    return r//gcd(4,q**n+1)
for n in [4,5,6,7]:
    for q in [2,3,4,5,7,8,9]:
        c=Fraction(D2n(n,q),Dn(n,q))
        cf=Fraction(gcd(4,q**n-1),gcd(4,q**n+1))*Fraction(q**n+1,q**n-1)
        assert c==cf
        print("  n=%d q=%-3d c=%-16s=%.9f  in (1,2)u(2,3)u(1/2,1): %s  int>=2: %s"
              %(n,q,c,float(c), (1<c<2) or (2<c<3) or (Fraction(1,2)<c<1), c.denominator==1 and c>=2))
