#!/usr/bin/env python3
"""v_task27: the group-theoretic bypass of the Sec.4ap arithmetic residue.

Two questions, both about factorizations  n!/2 = c * prod |S_i|  with
S_i simple and c dividing prod |Out(S_i)| (the necessary shape of a
Fitting-free T with |T| = |A_n|, socle prod S_i, T/Soc -> Out(Soc)):

  (A)  CRITERION-AT FAILURES.  Sec.4am verified "c * min_i iota(S_i) <
       C(n,3) for every admissible factorization, n <= 70" -- but its
       candidate table (v_task24_residue.py) carries only ten Lie families
       (L2 L3 U3 S4 L4 U4 G2 Sp6 L5 U5) plus Sz, Ree, alternating and
       sporadic.  Every OMITTED CFSG family is higher-rank or exceptional,
       i.e. LARGE iota -- and large iota is exactly what a failure needs.
       So the verification was complete only relative to that table.
       Here every remaining CFSG family is added, each with iota_ub = INF
       (maximally conservative: it is always counted as dangerous), and
       the search is rerun.

  (B)  THE BYPASS CONJECTURE.  Theorem kappa-A (Sec.4aj) already separates,
       for ALL n, every twin whose socle has an alternating factor.  So if
         (*)  every admissible factorization of n!/2 has an alternating
              socle factor,
       then Theorem AT holds for all n and the eight residual curves of
       Sec.4ap never have to be solved.  (*) is tested here directly.

Conservative choices throughout (all of them ADD candidates / ADD hits,
never remove them): iota_ub = INF for every family not in the exact table;
generous |Out|; all integer q, filtered by "order divides n!/2".
"""
import sys
from math import factorial, gcd, comb

INF = float('inf')

def primes_upto(n):
    return [p for p in range(2, n + 1)
            if all(p % r for r in range(2, int(p ** .5) + 1))]

def iota_alt(m):
    return {5: 5, 6: 10, 7: 35, 8: 15}.get(m, comb(m, 3))

def prod(xs):
    r = 1
    for x in xs:
        r *= x
    return r

# ---------------------------------------------------------------------------
# (1) the ten families with EXACT iota, verbatim from v_task24_residue.py
#     entry: name, |S|, iota_ub, |Out| (generous)
# ---------------------------------------------------------------------------
FAM_EXACT = [
 ("L2",  lambda q: q*(q*q-1)//gcd(2,q-1),                                lambda q: q+1,
         lambda q,p,f: gcd(2,q-1)*f, 4),
 ("L3",  lambda q: q**3*(q**3-1)*(q**2-1)//gcd(3,q-1),                   lambda q: q*q+q+1,
         lambda q,p,f: gcd(3,q-1)*2*f, 2),
 ("U3",  lambda q: q**3*(q**3+1)*(q**2-1)//gcd(3,q+1),                   lambda q: q**3+1,
         lambda q,p,f: gcd(3,q+1)*2*f, 3),
 ("S4",  lambda q: q**4*(q**4-1)*(q**2-1)//gcd(2,q-1),                   lambda q: (q*q+1)*(q+1),
         lambda q,p,f: f*(2 if p==2 else 1)*gcd(2,q-1), 3),
 ("L4",  lambda q: q**6*(q**4-1)*(q**3-1)*(q**2-1)//gcd(4,q-1),          lambda q: (q**4-1)//(q-1),
         lambda q,p,f: gcd(4,q-1)*2*f, 2),
 ("U4",  lambda q: q**6*(q**4-1)*(q**3+1)*(q**2-1)//gcd(4,q+1),          lambda q: (q**3+1)*(q+1),
         lambda q,p,f: gcd(4,q+1)*2*f, 2),
 ("G2",  lambda q: q**6*(q**6-1)*(q**2-1),                               lambda q: (q**6-1)//(q-1),
         lambda q,p,f: f*(2 if p==3 else 1), 3),
 ("Sp6", lambda q: q**9*(q**6-1)*(q**4-1)*(q**2-1)//gcd(2,q-1),          lambda q: (q**6-1)//(q-1),
         lambda q,p,f: gcd(2,q-1)*f, 2),
 ("L5",  lambda q: q**10*(q**5-1)*(q**4-1)*(q**3-1)*(q**2-1)//gcd(5,q-1),lambda q: (q**5-1)//(q-1),
         lambda q,p,f: gcd(5,q-1)*2*f, 2),
 ("U5",  lambda q: q**10*(q**5+1)*(q**4-1)*(q**3+1)*(q**2-1)//gcd(5,q+1),lambda q: (q**5+1)*(q*q+1),
         lambda q,p,f: gcd(5,q+1)*2*f, 2),
]

# ---------------------------------------------------------------------------
# (2) every REMAINING CFSG family, iota_ub = INF (always "dangerous")
# ---------------------------------------------------------------------------
def classical_extra(q, N):
    """(name, order) for the classical families omitted by v_task24."""
    out = []
    d = 6                                                # L_d, U_d, d >= 6
    while True:
        oL = q**(d*(d-1)//2) * prod(q**i - 1 for i in range(2, d+1)) // gcd(d, q-1)
        if oL > N and d > 6:
            break
        if oL <= N:
            out.append((f"L{d}({q})", oL))
        oU = q**(d*(d-1)//2) * prod(q**i - (-1)**i for i in range(2, d+1)) // gcd(d, q+1)
        if oU <= N:
            out.append((f"U{d}({q})", oU))
        if oL > N and oU > N:
            break
        d += 1
        if d > 40:
            break
    m = 4                                                # Sp_2m / Omega_2m+1, m >= 4
    while True:
        o = q**(m*m) * prod(q**(2*i) - 1 for i in range(1, m+1)) // gcd(2, q-1)
        if o > N:
            break
        out.append((f"Sp{2*m}({q})", o))                 # = |Omega_{2m+1}(q)|
        m += 1
        if m > 40:
            break
    m = 4                                                # Omega^eps_2m, m >= 4
    while True:
        base = q**(m*(m-1)) * prod(q**(2*i) - 1 for i in range(1, m))
        op = base * (q**m - 1) // gcd(4, q**m - 1)
        om = base * (q**m + 1) // gcd(4, q**m + 1)
        if op > N and om > N:
            break
        if op <= N:
            out.append((f"O+{2*m}({q})", op))
        if om <= N:
            out.append((f"O-{2*m}({q})", om))
        m += 1
        if m > 40:
            break
    return out

def exceptional_extra(q, p, f, N):
    out = []
    o3D4 = q**12*(q**8+q**4+1)*(q**6-1)*(q**2-1)
    if o3D4 <= N: out.append((f"3D4({q})", o3D4))
    oF4 = q**24*(q**12-1)*(q**8-1)*(q**6-1)*(q**2-1)
    if oF4 <= N: out.append((f"F4({q})", oF4))
    oE6 = q**36*(q**12-1)*(q**9-1)*(q**8-1)*(q**6-1)*(q**5-1)*(q**2-1)//gcd(3,q-1)
    if oE6 <= N: out.append((f"E6({q})", oE6))
    o2E6 = q**36*(q**12-1)*(q**9+1)*(q**8-1)*(q**6-1)*(q**5+1)*(q**2-1)//gcd(3,q+1)
    if o2E6 <= N: out.append((f"2E6({q})", o2E6))
    oE7 = q**63*prod(q**k-1 for k in (18,14,12,10,8,6,2))//gcd(2,q-1)
    if oE7 <= N: out.append((f"E7({q})", oE7))
    oE8 = q**120*prod(q**k-1 for k in (30,24,20,18,14,12,8,2))
    if oE8 <= N: out.append((f"E8({q})", oE8))
    if p == 2 and f % 2 == 1 and q >= 8:                 # 2F4(q), q = 2^odd >= 8
        o = q**12*(q**6+1)*(q**4-1)*(q**3+1)*(q-1)
        if o <= N: out.append((f"2F4({q})", o))
    return out

# ATLAS orders, hardcoded (spor2.out is not in the repo).  iota_ub = INF.
SPOR = {
 "M11":7920, "M12":95040, "M22":443520, "M23":10200960, "M24":244823040,
 "J1":175560, "J2":604800, "J3":50232960, "J4":86775571046077562880,
 "HS":44352000, "McL":898128000, "He":4030387200, "Ru":145926144000,
 "Suz":448345497600, "Co1":4157776806543360000, "Co2":42305421312000,
 "Co3":495766656000, "Fi22":64561751654400, "Fi23":4089470473293004800,
 "Fi24'":1255205709190661721292800, "HN":273030912000000,
 "Th":90745943887872000, "ON":460815505920, "Ly":51765179004000000,
 "B":4154781481226426191177580544000000,
 "M":808017424794512875886459904961710757005754368000000000,
 "Tits":17971200,
}
SPOR_OUT = {"M11":1,"M12":2,"M22":2,"M23":1,"M24":1,"J1":1,"J2":2,"J3":2,"HS":2,
            "McL":2,"He":2,"Ru":1,"Suz":2,"Co1":1,"Co2":1,"Co3":1,"Fi22":2,
            "Fi23":1,"Fi24'":2,"HN":2,"Th":1,"ON":2,"Ly":1,"J4":1,"B":1,"M":1,
            "Tits":2}

GENEROUS_OUT = 48          # >= |Out(S)| for every extra family in range

def cands(N, n):
    """(name, |S|, iota_ub, |Out|, is_alternating) for every simple S with
    |S| a proper divisor of N = n!/2."""
    res = []
    m = 5
    while factorial(m)//2 <= N:
        o = factorial(m)//2
        if o < N and N % o == 0:
            res.append((f"A{m}", o, iota_alt(m), 4 if m == 6 else 2, True))
        m += 1
    for p in primes_upto(n):     # every prime divisor of |S| divides N, so p <= n
        f, q = 1, p
        while q <= N:
            for nm, of, iof, outf, qmin in FAM_EXACT:
                if q < qmin: continue
                o = of(q)
                if 1 < o < N and N % o == 0:
                    res.append((f"{nm}({q})", o, iof(q), outf(q, p, f), False))
            if p == 2 and f % 2 == 1 and q >= 8:
                o = q*q*(q*q+1)*(q-1)
                if o < N and N % o == 0: res.append((f"Sz({q})", o, q*q+1, f, False))
            if p == 3 and f % 2 == 1 and q >= 27:
                o = q**3*(q**3+1)*(q-1)
                if o < N and N % o == 0: res.append((f"Ree({q})", o, q**3+1, f, False))
            for nm, o in classical_extra(q, N) + exceptional_extra(q, p, f, N):
                if 1 < o < N and N % o == 0:
                    res.append((nm, o, INF, GENEROUS_OUT, False))
            f += 1; q *= p
    for nm, o in SPOR.items():
        if o < N and N % o == 0:
            res.append((nm, o, INF, SPOR_OUT[nm], False))
    # de-duplicate by (name)
    seen, uniq = set(), []
    for c in res:
        if c[0] not in seen:
            seen.add(c[0]); uniq.append(c)
    return uniq

def search(N, pool, KMAX, need_alt_free=False, K=None):
    """all multisets from `pool` whose product divides N with N/prod | prod Out."""
    hits = []
    pool = sorted(pool, key=lambda t: -t[1])
    L = len(pool)
    stack = [(0, N, [], 1)]
    while stack:
        i, rem, chosen, outp = stack.pop()
        if chosen and outp % rem == 0:
            if K is None or rem * min(x[2] for x in chosen) >= K:
                hits.append((tuple(x[0] for x in chosen), rem))
        if len(chosen) >= KMAX:
            continue
        for j in range(i, L):
            o = pool[j][1]
            if o <= rem and rem % o == 0:
                stack.append((j, rem//o, chosen + [pool[j]], outp*pool[j][3]))
    return hits

if __name__ == "__main__":
    mode  = sys.argv[1] if len(sys.argv) > 1 else "A"
    NMAX  = int(sys.argv[2]) if len(sys.argv) > 2 else 70
    KMAX  = int(sys.argv[3]) if len(sys.argv) > 3 else 5
    print(f"mode {mode}, n = 5..{NMAX}, at most {KMAX} socle factors\n")
    if mode == "A":
        print("(A) Criterion-AT failures: factorizations in which EVERY factor has")
        print("    iota_ub >= C(n,3)/c, over the FULL CFSG candidate table.\n")
        print(f"{'n':>4} {'C(n,3)':>9} {'#cand':>6} {'#large-iota':>11}  failures")
        tot = 0
        for n in range(5, NMAX + 1):
            N = factorial(n)//2
            K = comb(n, 3) if n >= 9 else iota_alt(n)
            cs = cands(N, n)
            bad = [c for c in cs if not c[4] and c[2] >= K]
            hits = search(N, bad, KMAX, K=K)
            tot += len(hits)
            if hits or n % 10 == 0 or n < 12:
                s = "; ".join(" * ".join(h[0]) + f" * c={h[1]}" for h in hits[:6])
                print(f"{n:>4} {K:>9} {len(cs):>6} {len(bad):>11}  {s if hits else '-- none --'}")
        print(f"\nTOTAL Criterion-AT failures, n = 5..{NMAX}: {tot}")
    else:
        print("(B) admissible factorizations with NO alternating socle factor.\n")
        print(f"{'n':>4} {'#cand':>6} {'#adm':>6} {'#alt-free':>10}  witnesses")
        tot = totaf = 0
        for n in range(5, NMAX + 1):
            N = factorial(n)//2
            cs = cands(N, n)
            hits = search(N, cs, KMAX)
            altnames = {c[0] for c in cs if c[4]}
            af = [h for h in hits if not (set(h[0]) & altnames)]
            tot += len(hits); totaf += len(af)
            s = "; ".join(" * ".join(h[0]) + f" * c={h[1]}" for h in af[:6])
            print(f"{n:>4} {len(cs):>6} {len(hits):>6} {len(af):>10}  {s if af else '--'}",
                  flush=True)
        print(f"\nTOTAL admissible factorizations n = 5..{NMAX}: {tot}")
        print(f"TOTAL with no alternating socle factor:        {totaf}")
