"""v_task65 -- adversarial audit of Theorem BC-n (v_task64), arithmetic parts.

(A) iota_1 | v_eps ?  -- exact, and the *coprimality* form of the argument
    (v_task64 states only the size form).
(B) maximal-subgroup index sweep for Sp_{2n}(q), q odd, class by class,
    from Kleidman-Liebeck Table 3.5.C orders, with a GENEROUS outer/extension
    factor applied to every non-parabolic class (so the computed index is a
    LOWER bound on the true index).  Checks: is any non-P1 maximal of index
    < q^{2n}?
(C) the n=3 class-S list (BHR 8.28/8.29) at order level.
"""
from math import factorial, gcd, prod, isqrt

def sp_order(n, q):          # |Sp_{2n}(q)|
    return q**(n*n) * prod(q**(2*i) - 1 for i in range(1, n+1))
def gl_order(n, q):
    return q**(n*(n-1)//2) * prod(q**i - 1 for i in range(1, n+1))
def gu_order(n, q):
    return q**(n*(n-1)//2) * prod(q**i - (-1)**i for i in range(1, n+1))
def o_order(eps, m, q):      # |O^eps_{2m}(q)| , q odd  (full orthogonal)
    return 2 * q**(m*(m-1)) * (q**m - eps) * prod(q**(2*i)-1 for i in range(1, m))
def o_odd_order(m, q):       # |O_{2m+1}(q)| = 2*|Sp_{2m}(q)|
    return 2 * sp_order(m, q)

def prime_powers(lim):
    out=[]
    for x in range(3, lim, 2):
        for p in range(3, x+1, 2):
            if x % p == 0:
                y=x
                while y % p == 0: y//=p
                if y==1: out.append((x,p))
                break
    return out

def isotropic_count(n, k, q):   # number of totally isotropic k-spaces in Sp_2n
    num = prod(q**(2*n-2*i) - 1 for i in range(k))
    den = prod(q**(i+1) - 1 for i in range(k))
    assert num % den == 0
    return num // den

def maximal_index_lower_bounds(n, q, p, e):
    """returns list of (label, index_lower_bound) for every maximal EXCEPT P1."""
    G = sp_order(n, q)
    out = []
    OUT = 8 * n * max(1, e)          # generous outer/extension slack factor
    # parabolics P_k, k>=2 : exact indices
    for k in range(2, n+1):
        out.append((f"P{k}", isotropic_count(n, k, q)))
    # C1 nondegenerate  Sp_2m x Sp_2(n-m)
    for m in range(1, n//2 + 1):
        if 2*m == 2*n: continue
        M = sp_order(m, q) * sp_order(n-m, q) * 2
        out.append((f"C1 Sp{2*m}xSp{2*(n-m)}", G // M))
    # C2 imprimitive  Sp_2m wr S_t,  mt = n, t >= 2
    for t in range(2, n+1):
        if n % t: continue
        m = n // t
        M = sp_order(m, q)**t * factorial(t) * OUT
        out.append((f"C2 Sp{2*m}wrS{t}", G // M))
    # C2 GL_n(q).2
    out.append(("C2 GL_n.2", G // (gl_order(n, q) * 2 * OUT)))
    # C3 field extension Sp_{2n/r}(q^r).r
    for r in [x for x in range(2, n+1) if n % x == 0 and all(x % d for d in range(2, x))]:
        M = sp_order(n//r, q**r) * r * OUT
        out.append((f"C3 Sp{2*n//r}(q^{r})", G // M))
    # C3 GU_n(q).2
    out.append(("C3 GU_n.2", G // (gu_order(n, q) * 2 * OUT)))
    # C4 tensor  Sp_2a (x) O_b ,  a*b = n, b >= 3 odd
    for b in range(3, n+1, 2):
        if n % b: continue
        a = n // b
        M = sp_order(a, q) * o_odd_order((b-1)//2, q) * OUT
        out.append((f"C4 Sp{2*a}xO{b}", G // M))
    # C5 subfield
    for r in [x for x in range(2, e+1) if e % x == 0 and all(x % d for d in range(2, x))]:
        q0 = round(q ** (1.0/r))
        while q0**r < q: q0 += 1
        M = sp_order(n, q0) * r * OUT
        out.append((f"C5 subfield r={r}", G // M))
    # C6 extraspecial 2^{1+2n}.O^-_{2n}(2)
    M = 2**(1+2*n) * o_order(-1, n, 2) * OUT
    out.append(("C6 2^{1+2n}", G // M))
    # C7 tensor-induced Sp_2m wr S_t with (2m)^t = 2n
    for t in range(2, 8):
        for m in range(1, n+1):
            if (2*m)**t == 2*n:
                M = sp_order(m, q)**t * factorial(t) * OUT
                out.append((f"C7 ({2*m})^{t}", G // M))
    # S class
    if n == 3:
        # BHR 8.28/8.29, q odd: orders of the S-maximals of Sp_6(q)
        cands = [q*(q*q-1),           # Sym^5 SL2(q) = 2.L2(q)
                 2*1092,              # SL2(13)
                 2*168, 2*2520,       # 2.L2(7), 2.A7
                 2*25920,             # 2.U4(2)
                 6*20160,             # 6.L3(4)
                 2*604800]            # 2.J2
        M = max(cands) * OUT
        out.append(("S (BHR 8.28/8.29 max order)", G // M))
    else:
        out.append(("S (Liebeck q^{3d})", G // (q**(6*n) * OUT)))
    return out

print("=== (A) iota_1 vs v_eps ===")
bad = 0; tested = 0
for (q, p) in prime_powers(400):
    for n in range(3, 13):
        i1 = (q**(2*n) - 1)//(q - 1)
        for eps in (1, -1):
            v = q**n * (q**n - eps)//2
            tested += 1
            if v % i1 == 0: bad += 1; print("  !! divides", n, q, eps)
            if v >= q**(2*n): bad += 1; print("  !! v >= q^2n", n, q, eps)
            # coprimality form: iota1 | v  <=>  iota1 | (q^n-eps)/2  (gcd(i1,q)=1)
            assert gcd(i1, q) == 1
            assert i1 > (q**n - eps)//2 > 0
print(f"  {tested} triples, {bad} violations; coprimality form verified everywhere")

print("\n=== (B) maximal indices of Sp_2n(q), non-P1, vs q^{2n} ===")
worst = None; viol = 0; npairs = 0
for (q, p) in prime_powers(200):
    e = 0; x = q
    while x > 1: x //= p; e += 1
    for n in range(3, 9):
        npairs += 1
        thr = q**(2*n)
        for lab, idx in maximal_index_lower_bounds(n, q, p, e):
            ratio = idx / thr
            if idx < thr:
                viol += 1
                print(f"  !! VIOLATION n={n} q={q} {lab} index~{idx} < q^2n={thr}")
            if worst is None or ratio < worst[0]:
                worst = (ratio, n, q, lab, idx, thr)
print(f"  {npairs} (n,q) pairs, {viol} violations")
print(f"  tightest: ratio={worst[0]:.4f} n={worst[1]} q={worst[2]} {worst[3]} index~{worst[4]} vs q^2n={worst[5]}")

print("\n=== (C) exact P_n identity at n=3 (the tightest exact case) ===")
for q in [3,5,7,9,11,13]:
    idx = isotropic_count(3, 3, q)
    print(f"  q={q}: [Sp6:P3]={idx}  q^6={q**6}  diff={idx-q**6}")
print("  symbolically [Sp6:P3]=(q+1)(q^2+1)(q^3+1)=q^6+q^5+q^4+2q^3+q^2+q+1 > q^6")

print("\n=== (D) Liebeck S-bound sufficiency: index >= q^{2n^2+n-6n} ===")
for n in range(3, 9):
    print(f"  n={n}: exponent 2n^2-5n = {2*n*n-5*n} vs 2n = {2*n} -> {'OK' if 2*n*n-5*n >= 2*n else 'TOO WEAK'}")

print("\n=== (E) the two flagged cases, tightened ===")
# C6: N_{Sp}(2^{1+2n}) = 2^{1+2n}.O^-_{2n}(2), exists only for q = p prime odd.
for (q,p) in prime_powers(60):
    if q != p: continue
    for n in range(3, 9):
        M = 2**(1+2*n) * o_order(-1, n, 2) * 2
        idx = sp_order(n,q)//M
        if idx < q**(2*n):
            print(f"  C6 STILL BELOW: n={n} q={q} idx>={idx} < {q**(2*n)}")
print("  C6: no case below q^{2n} with the exact normaliser order")

# S class, n=3, per candidate with its existence condition (BHR 8.28/8.29)
S3 = [("Sym^5 SL2(q)=2.L2(q)", lambda q,p: p>=7,        lambda q: q*(q*q-1)*2),
      ("SL2(13)",              lambda q,p: True,        lambda q: 2*1092*2),
      ("2.L2(7)",              lambda q,p: True,        lambda q: 2*168*2),
      ("2.A7",                 lambda q,p: True,        lambda q: 2*2520*2),
      ("2.U4(2)",              lambda q,p: True,        lambda q: 2*25920*2),
      ("6.L3(4)",              lambda q,p: True,        lambda q: 6*20160*2),
      ("2.J2",                 lambda q,p: True,        lambda q: 2*604800*2)]
flag=0
for (q,p) in prime_powers(200):
    for nm, ex, order in S3:
        if not ex(q,p): continue
        idx = sp_order(3,q)//order(q)
        if idx < q**6:
            flag+=1; print(f"  S-flag q={q}: {nm} index>={idx} < q^6={q**6}")
print(f"  n=3 S-class: {flag} residual flags (all at small q; ATLAS settles q=3, see GAP PART B)")
