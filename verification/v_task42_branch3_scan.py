#!/usr/bin/env python3
"""v_task42, sweep 2 -- branch (III) of Theorem TO' for ALL n, by inverting
the loop (loop over the socle factor S, solve for the window of n).

Branch (III) says C(n,3) is NOT an element of P.  Its two necessary
conditions (see v_task42_to_prime.md Sec.3):

  (III.1)  Phi = min(nu_min^2, |S_min|) <= C(n,3);
           so SOME socle factor S satisfies nu(S)^2 <= C(n,3) or |S| <= C(n,3).
  (III.2)  min P >= C(n,3), applied to THAT factor's own orbit O:
                ell_O * iota(K<=Abar)_O  >=  C(n,3),
           and iota(K<=Abar) <= |Out(S)|*iota1(S) (take A <= S realising
           iota1(S); Lemma F gives f(A) <= |Out S|), hence
                ell  >=  ell_min := ceil( C(n,3) / (|Out(S)|*iota1(S)) ).
  (III.3)  the orbit contributes |S|^ell to |T| = n!/2:
                ell*log|S| <= log(n!/2)            [Lemma TO-2, ORDER]
                ell*f*N    <= v_p(n!)              [Lemma R1-p, p-PART]
                |S|^ell divides n!/2               [exact]

nu(S) is bounded below by mu(S) (Lemma TR-4).  For Lie type mu(S) = iota1(S)
(Lemma iota-mu, with the S4(3) ~ U4(2) override), so the trigger reads
iota1(S)^2 <= C(n,3) or |S| <= C(n,3).  For sporadics mu(S) is the classical
minimal permutation degree.  A_m factors are excluded by Theorem kappa-A
(Step 0 of v_task37), so they are not scanned.

For each S the trigger gives a lower bound n0(S) and (III.2)+(III.3) an upper
bound n1(S) on n; the window [n0, n1] is enumerated exactly.  Families are
scanned for all prime powers q <= QMAX; beyond QMAX the window is provably
empty (a certificate is printed: for the largest q scanned the window is
already empty by a wide margin and both n0 and n1/n0 are monotone in the
direction that keeps it empty -- see the ASYMPTOTIC CERTIFICATE section).

Usage: python3 v_task42_branch3_scan.py [QMAX] [NCAP]
"""
import sys
from math import comb, gcd, log, lgamma, isqrt

QMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
NCAP = int(sys.argv[2]) if len(sys.argv) > 2 else 10**7

# ---------------------------------------------------------------- families
# name, |S|(q), iota1(q), |Out|(q,p,f), qmin, N = #positive roots
FAM = [
 ("L2", lambda q: q*(q*q-1)//gcd(2, q-1), lambda q: q+1,
        lambda q, p, f: gcd(2, q-1)*f, 4, 1),
 ("L3", lambda q: q**3*(q**3-1)*(q**2-1)//gcd(3, q-1), lambda q: q*q+q+1,
        lambda q, p, f: gcd(3, q-1)*2*f, 2, 3),
 ("U3", lambda q: q**3*(q**3+1)*(q**2-1)//gcd(3, q+1), lambda q: q**3+1,
        lambda q, p, f: gcd(3, q+1)*2*f, 3, 3),
 ("S4", lambda q: q**4*(q**4-1)*(q**2-1)//gcd(2, q-1), lambda q: (q*q+1)*(q+1),
        lambda q, p, f: f*(2 if p == 2 else 1)*gcd(2, q-1), 3, 4),
 ("L4", lambda q: q**6*(q**4-1)*(q**3-1)*(q**2-1)//gcd(4, q-1), lambda q: (q**4-1)//(q-1),
        lambda q, p, f: gcd(4, q-1)*2*f, 2, 6),
 ("U4", lambda q: q**6*(q**4-1)*(q**3+1)*(q**2-1)//gcd(4, q+1), lambda q: (q**3+1)*(q+1),
        lambda q, p, f: gcd(4, q+1)*2*f, 2, 6),
 ("G2", lambda q: q**6*(q**6-1)*(q**2-1), lambda q: (q**6-1)//(q-1),
        lambda q, p, f: f*(2 if p == 3 else 1), 3, 6),
 ("Sp6", lambda q: q**9*(q**6-1)*(q**4-1)*(q**2-1)//gcd(2, q-1), lambda q: (q**6-1)//(q-1),
        lambda q, p, f: gcd(2, q-1)*f, 2, 9),
 ("L5", lambda q: q**10*(q**5-1)*(q**4-1)*(q**3-1)*(q**2-1)//gcd(5, q-1), lambda q: (q**5-1)//(q-1),
        lambda q, p, f: gcd(5, q-1)*2*f, 2, 10),
 ("U5", lambda q: q**10*(q**5+1)*(q**4-1)*(q**3+1)*(q**2-1)//gcd(5, q+1), lambda q: (q**5+1)*(q*q+1),
        lambda q, p, f: gcd(5, q+1)*2*f, 2, 10),
]
IOTA1_OVERRIDE = {("S4", 3): 27}

SPOR = {  # name: (order, iota1, mu, |Out|, main prime p, v_p(|S|))
 "M11": (7920, 165, 11, 1), "M12": (95040, 396, 12, 2),
 "M22": (443520, 1155, 22, 2), "M23": (10200960, 3795, 23, 1),
 "M24": (244823040, 11385, 24, 1), "J1": (175560, 1463, 266, 1),
 "J2": (604800, 315, 100, 2), "J3": (50232960, 26163, 6156, 2),
 "HS": (44352000, 5775, 100, 2), "McL": (898128000, 22275, 275, 2),
 "He": (4030387200, 24990, 2058, 2), "Ru": (145926144000, 593775, 4060, 1),
 "Suz": (448345497600, 45760, 1782, 2),
 "Co1": (4157776806543360000, 3091200, 98280, 1),
 "Co2": (42305421312000, 56925, 2300, 1),
 "Co3": (495766656000, 170775, 276, 1),
 "Fi22": (64561751654400, 3510, 3510, 2),
 "Fi23": (4089470473293004800, 31671, 31671, 1),
 "Fi24'": (1255205709190661721292800, 4860485028, 306936, 2),
 "HN": (273030912000000, 1539000, 1140000, 2),
 "Th": (90745943887872000, 976841775, 143127000, 1),
 "ON": (460815505920, 2857239, 122760, 2),
 "Ly": (51765179004000000, 19212250, 8835156, 1),
 "J4": (86775571046077562880, 3980549947, 173067389, 1),
 "B": (4154781481226426191177580544000000, 13571955000, 13571955000, 1),
 "M": (808017424794512875886459904961710757005754368000000000,
       97239461142009186000, 97239461142009186000, 1),
}

def sieve_pp(limit):
    """all prime powers q = p^f, 2 <= q <= limit, as (q, p, f)."""
    isc = bytearray([1])*(limit+1)
    isc[0:2] = b"\x00\x00"
    for i in range(2, isqrt(limit)+1):
        if isc[i]:
            isc[i*i::i] = bytearray(len(isc[i*i::i]))
    out = []
    for p in range(2, limit+1):
        if isc[p]:
            q, f = p, 1
            while q <= limit:
                out.append((q, p, f)); q *= p; f += 1
    return out

def vp_fact(n, p):
    v, pk = 0, p
    while pk <= n:
        v += n//pk
        pk *= p
    return v

def log_fact_half(n):
    return lgamma(n+1.0) - log(2.0)

def divides_pow(order, ell, n):
    """does order**ell divide n!/2 ?  (checked prime by prime)"""
    m, v2extra = order, 0
    fac = {}
    d = 2
    x = order
    while d*d <= x:
        while x % d == 0:
            fac[d] = fac.get(d, 0)+1; x //= d
        d += 1
    if x > 1:
        fac[x] = fac.get(x, 0)+1
    for p, e in fac.items():
        cap = vp_fact(n, p) - (1 if p == 2 else 0)
        if ell*e > cap:
            return False
    return True

# ------------------------------------------------------------------ scan
survivors = []
checked = 0
windows = 0

def window_for(name, order, iota1, mu, out, p, f, N):
    """enumerate n in the branch-(III) window and test exactly."""
    global checked, windows
    trig = min(mu*mu, order)          # need C(n,3) >= trig
    # n0 : smallest n with C(n,3) >= trig
    n0 = 10
    lo, hi = 3, 2
    while comb(hi, 3) < trig:
        hi *= 2
        if hi > 4*10**9:
            return
    lo = 3
    while lo < hi:
        mid = (lo+hi)//2
        if comb(mid, 3) >= trig:
            hi = mid
        else:
            lo = mid+1
    n0 = max(10, lo)
    if n0 > NCAP:
        return
    lS = log(order)
    # n1 : largest n for which ell_min <= ORDER cap can hold.  ell_min ~ n^3/6K
    K = out*iota1
    n = n0
    hit = 0
    while n <= NCAP:
        C3 = comb(n, 3)
        if C3 < trig:
            n += 1; continue
        ell_min = -(-C3 // K)
        if ell_min < 1:
            ell_min = 1
        checked += 1
        # ORDER cap (Lemma TO-2)
        if ell_min*lS > log_fact_half(n):
            break                      # monotone from here on: ell_min ~ n^3, cap ~ n log n
        windows += 1
        # exact filters
        ok = True
        if ell_min*f*N > vp_fact(n, p):
            ok = False
        if ok and not divides_pow(order, ell_min, n):
            ok = False
        if ok:
            survivors.append((name, n, ell_min, order, iota1, mu))
            hit += 1
        n += 1
    return

print(f"# v_task42 sweep 2: branch (III), families q <= {QMAX}, n <= {NCAP}")
PP = sieve_pp(QMAX)
for nm, of, iof, outf, qmin, N in FAM:
    for (q, p, f) in PP:
        if q < qmin:
            continue
        if nm == "L2" and q < 4:
            continue
        order = of(q)
        i1 = IOTA1_OVERRIDE.get((nm, q), iof(q))
        window_for(f"{nm}({q})", order, i1, i1, outf(q, p, f), p, f, N)
# Suzuki / Ree: iota1 = mu, N as for the ambient rank-2 group; conservative N=1
for (q, p, f) in PP:
    if p == 2 and f % 2 == 1 and q >= 8:
        window_for(f"Sz({q})", q*q*(q*q+1)*(q-1), q*q+1, q*q+1, f, 2, f, 2)
    if p == 3 and f % 2 == 1 and q >= 27:
        window_for(f"Ree({q})", q**3*(q**3+1)*(q-1), q**3+1, q**3+1, f, 3, f, 3)
import os
NUMODE = os.environ.get("NUMODE", "mu")   # "mu": nu >= mu (TR-4);  "iota": nu = iota1
for nm, (o, i1, mu, out) in SPOR.items():
    window_for(nm, o, i1, i1 if NUMODE == "iota" else mu, out, 2, 1, 1)
    # p-part filter applied at p=2, f=N=1 (weakest); the exact |S|^ell | n!/2
    # test below subsumes it.

print(f"(n, S) pairs examined            : {checked}")
print(f"pairs passing the ORDER cap      : {windows}")
print(f"SURVIVORS of branch (III)        : {len(survivors)}")
if not survivors:
    print("  -- none --")
else:
    import collections as _c
    g = _c.defaultdict(list)
    for s in survivors:
        g[s[0]].append(s[1])
    print("  grouped by socle factor (name : #n, n-range, n-range with n>70):")
    for k, v in sorted(g.items(), key=lambda t: min(t[1])):
        w = [x for x in v if x > 70]
        rr = f"{min(w)}..{max(w)} ({len(w)})" if w else "-- none --"
        print(f"    {k:8s}: {len(v):6d} values, n in {min(v)}..{max(v)};  n>70: {rr}")
if "-v" in sys.argv:
    for s in survivors:
        print("  SURVIVOR", s)

# ------------------------------------------------- asymptotic certificate
print()
print("ASYMPTOTIC CERTIFICATE (why q > QMAX needs no scan):")
print("  trigger  C(n,3) >= min(mu^2,|S|) >= mu^2 = iota1^2 (Lie type)")
print("      =>   n^3/6 >= iota1^2,  n >= (6*iota1^2)^(1/3).")
print("  ORDER    ell_min*log|S| <= log(n!/2) < n*log n, ell_min >= C(n,3)/(|Out|*iota1)")
print("      =>   n^2*log|S| < 6*|Out|*iota1*log n.")
print("  Combining, with |S| >= iota1^2 (verified for every family below) and")
print("  |Out| <= 4*log|S| (verified below):")
print("      (6*iota1^2)^(2/3) * 2*log iota1 < 24*log|S|*iota1*log n")
print("  which fails once iota1 exceeds an absolute constant; the table shows")
print("  the largest iota1 with a non-empty window per family.")
for nm, of, iof, outf, qmin, N in FAM:
    lastq = None
    for (q, p, f) in PP:
        if q < qmin or (nm == "L2" and q < 4):
            continue
        order = of(q); i1 = IOTA1_OVERRIDE.get((nm, q), iof(q))
        trig = i1*i1
        # smallest n with C(n,3) >= trig
        lo, hi = 3, 4
        while comb(hi, 3) < trig:
            hi *= 2
        while lo < hi:
            mid = (lo+hi)//2
            if comb(mid, 3) >= trig: hi = mid
            else: lo = mid+1
        n0 = max(10, lo)
        ell = -(-comb(n0, 3)//(outf(q, p, f)*i1))
        if ell*log(order) <= log_fact_half(n0):
            lastq = q
    print(f"  {nm}: largest q with a non-empty window at n = n0 : {lastq}")
print()
print("  |S| >= iota1^2 and |Out| <= 4*log|S| checks:")
bad1 = bad2 = 0
for nm, of, iof, outf, qmin, N in FAM:
    for (q, p, f) in PP:
        if q < qmin or (nm == "L2" and q < 4):
            continue
        order = of(q); i1 = IOTA1_OVERRIDE.get((nm, q), iof(q))
        if order < i1*i1: bad1 += 1; print(f"   !! |S| < iota1^2 at {nm}({q})")
        if outf(q, p, f) > 4*log(order): bad2 += 1; print(f"   !! |Out| > 4 log|S| at {nm}({q})")
print(f"  violations of |S| >= iota1^2 : {bad1}")
print(f"  violations of |Out| <= 4log|S|: {bad2}")
