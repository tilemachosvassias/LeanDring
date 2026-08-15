#!/usr/bin/env python3
"""Rational-point census on the two remaining genus-1 curves of NOTES Sec.4ap.

    C_c :  m^3 - m = c*(q^3+q^2+q+1),   c = 6  (S4/L4, m=1)
                                        c = 12 (L4,    m=2)

For q = a/b in lowest terms, put w = m*b; then w is an ALGEBRAIC INTEGER
root of the monic integer polynomial

    w^3 - b^2 w - c*(a^3 + a^2 b + a b^2 + b^3) = 0,

so w is an ordinary integer and rational points are found by an exact
integer-root test.  Small-height census => a lower bound on the rank and a
first look at the torsion.
"""
from math import gcd

def int_roots(b2, C):
    """integer roots of w^3 - b2*w - C."""
    out = []
    # |w| <= |b2|+|C|+1 is crude; use cube-root bracket instead
    lo = -(abs(C) ** (1 / 3) + abs(b2) ** 0.5 + 2)
    hi = -lo
    # divisors of C (w | C when C != 0, since w(w^2-b2) = C)
    cand = set()
    if C == 0:
        cand.update([0])
        s = int(round(abs(b2) ** 0.5))
        for t in (s - 1, s, s + 1):
            if t * t == b2:
                cand.update([t, -t])
    else:
        n = abs(C)
        d = 1
        while d * d <= n:
            if n % d == 0:
                cand.update([d, -d, n // d, -(n // d)])
            d += 1
    for w in cand:
        if lo - 1 <= w <= hi + 1 and w ** 3 - b2 * w - C == 0:
            out.append(w)
    return sorted(out)

for c in (6, 12):
    print(f"\n=== c = {c}:  m^3 - m = {c}(q^3+q^2+q+1) ===")
    pts = []
    H = 80
    for b in range(1, H + 1):
        for a in range(-H, H + 1):
            if gcd(abs(a), b) != 1:
                continue
            C = c * (a ** 3 + a * a * b + a * b * b + b ** 3)
            for w in int_roots(b * b, C):
                if w % b == 0 or b == 1:
                    q = f"{a}" if b == 1 else f"{a}/{b}"
                    m = w / b
                    pts.append((abs(a) + b, q, w, b))
                else:
                    pts.append((abs(a) + b, f"{a}/{b}", w, b))
    seen = set()
    for h, q, w, b in sorted(pts):
        key = (q, w, b)
        if key in seen:
            continue
        seen.add(key)
        m = f"{w}" if w % b == 0 else f"{w}/{b}"
        print(f"   q = {q:>10s}   m = {m:>12s}   (m = w/b, w = {w}, b = {b})")
    print(f"   total rational points of height <= {H}: {len(seen)}")
