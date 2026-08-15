#!/usr/bin/env python3
"""Genus of the eight residual curves of NOTES.md Sec.4ao.

Each residual equation  m * iota_F(q) = C(n,3)  normalises to

        k^3 - k  =  c * f(q),        c = 6*m,   k = n-1,

a curve C_f of degree 3 over the q-line.  Riemann-Hurwitz:

  * finite branch points: the fibre m^3 - m - c f(a) degenerates exactly
    when its discriminant  4 - 27 c^2 f(a)^2  vanishes -- 2*deg(f) points,
    each carrying ONE simple ramification (e=2) provided the roots are
    simple, i.e. provided  Res(f', 27c^2 f^2 - 4) != 0.  That resultant is
    computed here exactly, in integers.
  * over q = infinity: m^3 ~ c q^d, so gcd(3,d)=1 gives one totally
    ramified place (contributes 2) and 3 | d gives three unramified places
    (contributes 0; c is never a cube here).

  =>   2g - 2 = -6 + 2d + (0 if 3|d else 2).

No CAS required: exact integer resultant via the Sylvester determinant
(fraction-free Gaussian elimination on Fraction entries).
"""
from fractions import Fraction

def polymul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return r

def deriv(a):                      # a = [c0, c1, ...] ascending
    return [i * a[i] for i in range(1, len(a))] or [0]

def resultant(a, b):
    """Res(a,b) via the Sylvester matrix determinant. Ascending coeff lists."""
    m, n = len(a) - 1, len(b) - 1
    N = m + n
    M = [[Fraction(0)] * N for _ in range(N)]
    for i in range(n):                       # n rows of a
        for j, c in enumerate(reversed(a)):
            M[i][i + j] = Fraction(c)
    for i in range(m):                       # m rows of b
        for j, c in enumerate(reversed(b)):
            M[n + i][i + j] = Fraction(c)
    det, sign = Fraction(1), 1
    for col in range(N):
        piv = next((r for r in range(col, N) if M[r][col] != 0), None)
        if piv is None:
            return Fraction(0)
        if piv != col:
            M[col], M[piv] = M[piv], M[col]
            sign = -sign
        det *= M[col][col]
        inv = M[col][col]
        for r in range(col + 1, N):
            if M[r][col]:
                fac = M[r][col] / inv
                for cc in range(col, N):
                    M[r][cc] -= fac * M[col][cc]
    return sign * det

# f given as ascending coefficient lists; c = 6*mult
EQS = [
    ("S4/L4  m=1", [1, 1, 1, 1],          6),   # q^3+q^2+q+1
    ("U4     m=1", [1, 1, 0, 1, 1],       6),   # q^4+q^3+q+1
    ("L5     m=1", [1, 1, 1, 1, 1],       6),   # q^4+...+1
    ("G2/Sp6 m=1", [1, 1, 1, 1, 1, 1],    6),   # q^5+...+1
    ("U5     m=1", [1, 0, 1, 0, 0, 1, 0, 1], 6),# q^7+q^5+q^2+1
    ("L3     m=2", [1, 1, 1],            12),   # 2(q^2+q+1)
    ("L4     m=2", [1, 1, 1, 1],         12),   # 2(q^3+q^2+q+1)
    ("L5     m=2", [1, 1, 1, 1, 1],      12),   # 2(q^4+...+1)
]

print(f"{'equation':14s} {'deg f':>5s} {'2d branch pts simple?':>22s} "
      f"{'inf':>5s} {'genus':>6s}")
print("-" * 60)
for name, f, c in EQS:
    d = len(f) - 1
    disc = [-4] + [0] * (2 * d)                 # 27 c^2 f^2 - 4
    ff = polymul(f, f)
    for i, x in enumerate(ff):
        disc[i] += 27 * c * c * x
    R = resultant(deriv(f), disc)
    simple = (R != 0)
    inf = 0 if d % 3 == 0 else 2
    g = (-6 + 2 * d + inf + 2) // 2
    print(f"{name:14s} {d:5d} {str(simple) + '  (Res=' + str(R) + ')':>22s} "
          f"{inf:5d} {g:6d}")
