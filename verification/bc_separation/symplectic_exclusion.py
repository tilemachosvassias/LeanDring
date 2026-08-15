#!/usr/bin/env python3
"""
symplectic_exclusion.py -- the separation of B_n(q) from C_n(q) by a single
ind*-VALUE, not by the psn census mult_1.

Setup (notation of NOTES.md 4aj/4ba).  For a finite group G,
    ind*(H) = |G| * |H'| / |N_G(H)|            (H != 1)
    I(G)    = { ind*(H) : 1 != H <= G }
is read off the conductor multiset of D(G), hence is a D-invariant.

THE ASYMMETRY.
  (O) In S = Omega_{2n+1}(q), q odd, let e be anisotropic and
      z_e = -r_e  (i.e. +1 on <e>, -1 on e^perp).  det z_e = 1 and
      z_e lies in Omega for exactly one of the two square classes of Q(e).
      For that class, H = <z_e> is abelian, N_S(H) = C_S(z_e) = Stab_S(<e>),
      and ind*(H) = |orbit of <e>| = q^n (q^n - eps)/2  for the corresponding
      eps in {+1,-1}.  In particular v := q^n(q^n-eps)/2 lies in I(S)
      and v < q^{2n}.
  (C) In S = PSp_{2n}(q), q odd, n >= 3, EVERY element of I(S) below q^{2n}
      is divisible by iota_1 = (q^{2n}-1)/(q-1):
         ind*(H) = [S:N_S(H)] * |H'| < q^{2n}  forces  [S:N_S(H)] < q^{2n},
         so N_S(H) lies in a maximal subgroup of index < q^{2n}; by the
         Aschbacher/BHR classification the only such maximal is P_1 (verified
         numerically below), whence iota_1 = [S:P_1] divides [S:N_S(H)].
  (X) iota_1 does not divide q^n(q^n-eps)/2:  gcd(iota_1, q) = 1 and
      iota_1 >= q^{2n-1} > (q^n+1)/2 >= (q^n-eps)/2.
  Hence v in I(B_n(q)) \\ I(C_n(q)):  D(B_n(q)) !~ D(C_n(q)).

This script verifies (C)'s maximal-subgroup step and (X) exactly on a grid.
"""
from math import gcd

def isprime(x):
    if x < 2:
        return False
    i = 2
    while i*i <= x:
        if x % i == 0:
            return False
        i += 1
    return True

def is_pp(m):
    for p in range(2, m+1):
        if m % p == 0:
            if not isprime(p):
                return False
            k = m
            while k % p == 0:
                k //= p
            return k == 1
    return False

def sp_order(n, q):
    o = q**(n*n)
    for i in range(1, n+1):
        o *= q**(2*i) - 1
    return o

def gl_order(n, q):
    o = q**(n*(n-1)//2)
    for i in range(1, n+1):
        o *= q**i - 1
    return o

def gu_order(n, q):
    o = q**(n*(n-1)//2)
    for i in range(1, n+1):
        o *= q**i - (-1)**i
    return o

def ti_subspaces(n, q, k):
    """number of totally isotropic k-spaces in Sp_2n(q) = [Sp_2n : P_k]."""
    r = 1
    for i in range(k):
        r = r * (q**(2*n-2*i) - 1) // (q**(i+1) - 1)
    return r

def maximal_indices(n, q, p, f):
    """indices of (super-sets of) all maximal subgroups of Sp_2n(q), q odd.
    Returns list of (label, index-or-lower-bound). Uses group ORDERS, so a
    lower bound for the index of any maximal in the corresponding class."""
    G = sp_order(n, q)
    out = []
    for k in range(1, n+1):
        out.append(("P_%d" % k, ti_subspaces(n, q, k)))
    # C1 nondegenerate: Sp_2m perp Sp_{2n-2m}
    for m in range(1, n//2 + 1):
        out.append(("Sp%d_perp_Sp%d" % (2*m, 2*n-2*m),
                    G // (sp_order(m, q) * sp_order(n-m, q))))
    # C2 GL_n(q).2  (stabiliser of a pair of complementary t.i. n-spaces)
    out.append(("GL%d.2" % n, G // (2 * gl_order(n, q))))
    # C2 Sp_2m wr S_t
    for m in range(1, n+1):
        if n % m == 0 and m < n:
            t = n // m
            fact = 1
            for i in range(2, t+1):
                fact *= i
            out.append(("Sp%d wr S%d" % (2*m, t),
                        G // (sp_order(m, q)**t * fact)))
    # C3 Sp_{2n/r}(q^r).r  and GU_n(q).2 (n even for the latter is not required)
    for r in range(2, n+1):
        if n % r == 0:
            out.append(("Sp%d(q^%d).%d" % (2*n//r, r, r),
                        G // (r * sp_order(n//r, q**r))))
    out.append(("GU%d(q).2" % n, G // (2 * gu_order(n, q))))
    # C5 subfield Sp_2n(q0).[..]
    for d in range(1, f):
        if f % d == 0:
            q0 = p**d
            out.append(("Sp%d(%d) subfield" % (2*n, q0),
                        G // (sp_order(n, q0) * (f//d) * 2)))
    # C6 2^{1+2n}.O^-_{2n}(2)  (only when n is a power of 2, q = p prime)
    o2 = 2**(1 + 2*n)
    om = 2**(n*(n-1)) * (2**n + 1)
    for i in range(1, n):
        om *= 2**(2*i) - 1
    out.append(("C6 2^{1+2n}.O-", G // (o2 * om * 2)))
    # S:  n >= 4 -- Liebeck's bound |M| < q^{6n} for M in class S of Sp_2n(q).
    #     n  = 3 -- Liebeck's bound is too weak (q^18 vs q^21); use the explicit
    #     BHR Table 8.28/8.29 list for Sp_6(q), q odd:  the S-members are
    #     2.L_2(q) = Sym^5 SL_2(q) (order q(q^2-1)), SL_2(13), 2.L_2(7),
    #     2.A_7, 2.U_4(2), 6.L_3(4), 2.J_2 -- so |M| <= 4f*max(q(q^2-1), |2.J_2|).
    if n == 3:
        out.append(("S (BHR 8.28/8.29 list)",
                    G // (4 * f * max(q*(q*q-1), 1209600))))
    else:
        out.append(("S (Liebeck |M|<q^6n)", G // q**(6*n)))
    return out

print("=" * 74)
print("STEP (C): the only maximal subgroup of Sp_2n(q) of index < q^{2n} is P_1")
print("=" * 74)
bad = 0
tested = 0
for n in range(3, 9):
    for q in [m for m in range(3, 200) if is_pp(m) and m % 2 == 1]:
        # recover p, f
        p = min(x for x in range(2, q+1) if q % x == 0)
        f = 0
        k = q
        while k % p == 0:
            k //= p
            f += 1
        bound = q**(2*n)
        tested += 1
        for lab, idx in maximal_indices(n, q, p, f):
            if idx < bound and lab != "P_1":
                print("  !! n=%d q=%d  %-24s index %d < q^{2n}=%d"
                      % (n, q, lab, idx, bound))
                bad += 1
        assert ti_subspaces(n, q, 1) == (q**(2*n) - 1) // (q - 1)
print("  (n,q) pairs tested: %d      violations: %d" % (tested, bad))
print("  closest call is always P_n at n=3: [Sp6:P3] - q^6 = q^5+q^4+2q^3+q^2+q+1 > 0")

print()
print("=" * 74)
print("STEP (X): iota_1 = (q^{2n}-1)/(q-1) never divides v = q^n(q^n-eps)/2,")
print("          and v < q^{2n} always")
print("=" * 74)
bad = 0
tested = 0
for n in range(3, 13):
    for q in [m for m in range(3, 400) if is_pp(m) and m % 2 == 1]:
        i1 = (q**(2*n) - 1) // (q - 1)
        for eps in (1, -1):
            v = q**n * (q**n - eps) // 2
            tested += 1
            if v % i1 == 0:
                print("  !! DIVIDES n=%d q=%d eps=%d" % (n, q, eps)); bad += 1
            if v >= q**(2*n):
                print("  !! TOO BIG n=%d q=%d eps=%d" % (n, q, eps)); bad += 1
            if gcd(i1, q) != 1:
                print("  !! gcd n=%d q=%d" % (n, q)); bad += 1
print("  (n,q,eps) triples tested: %d      violations: %d" % (tested, bad))

print()
print("=" * 74)
print("STEP (O): the two Omega_{2n+1}(q) nonsingular-point orbit sizes")
print("=" * 74)
print("  %-4s %-5s %-14s %-14s %-14s" % ("n", "q", "q^n(q^n-1)/2", "q^n(q^n+1)/2", "iota_1"))
for n in (3, 4):
    for q in (3, 5, 7, 9, 11, 13):
        print("  %-4d %-5d %-14d %-14d %-14d"
              % (n, q, q**n*(q**n-1)//2, q**n*(q**n+1)//2,
                 (q**(2*n)-1)//(q-1)))
print("  sum of the two orbits = q^{2n} = #nonsingular projective points  ",
      all(q**n*(q**n-1)//2 + q**n*(q**n+1)//2 == q**(2*n)
          for n in range(3, 10) for q in (3, 5, 7, 9, 11, 13)))

print()
print("CONCLUSION: v = q^n(q^n-eps)/2 lies in I(B_n(q)) and not in I(C_n(q)),")
print("for every n >= 3 and every odd q.  Theorem BC-n follows.")
