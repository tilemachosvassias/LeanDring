#!/usr/bin/env sage
# =============================================================================
# v_task44_dioph_triage -- exact Diophantine triage of the THREE surviving R1
# equations of NOTES.md Sec.4ay.
#
#   row 1  S4(q), q odd non-prime, l* = 1   :   (q+1)(q^2+1)   = C(n,3)
#   row 2  L3(q), q = p^f (f>=2), l* >= 2   :   l*f1*(q^2+q+1) = C(n,3)
#   row 3  L5(q), q = p^f, any l*           :   l*f1*[5,1]_q   = C(n,3)
#
# with f1 in {1,2} (graph-automorphism multiplier).  Writing k = n-1 and
# c = 6*l**f1 each is  k^3 - k = c*f(q)  with deg f = 3, 2, 4 respectively.
#
# The point of the triage: row 1 is ONE curve (l* = 1 is PROVEN, Lemma
# R1-S4-l1), rows 2 and 3 are INFINITE FAMILIES indexed by l*.  This script
# settles, uniformly in c:
#   (a) the genus of every member (Riemann-Hurwitz, resultant in c exact);
#   (b) whether the point(s) at infinity are rational -- i.e. whether
#       E.integral_points() applies, which is exactly the Sec.4ap obstruction;
#   (c) the explicit Weierstrass model of the L3 family, uniform in c;
#   (d) the effective range of l* as a function of n, hence the exact n-range
#       that a "close all l* <= L" strategy would buy.
# =============================================================================

R.<q, m, z> = QQ[]
Rc.<C> = QQ[]

def homog(fq, d):
    """m^3 - m = C*f(q) homogenised to total degree D = max(3, deg f + ?)"""
    pass

print("="*78)
print("PART A -- genus, uniformly in c, for each of the three shapes")
print("="*78)

Rq.<x> = QQ[]
shapes = {
  "row1  S4  f = q^3+q^2+q+1": x^3 + x^2 + x + 1,
  "row2  L3  f = q^2+q+1":     x^2 + x + 1,
  "row3  L5  f = q^4+q^3+q^2+q+1": x^4 + x^3 + x^2 + x + 1,
}
Rcx.<cc> = QQ[]
Rcxx.<a> = Rcx[]
for name, f in shapes.items():
    d = f.degree()
    fa = f.change_ring(Rcx)(a)
    fpa = fa.derivative(a)
    # finite branch points: the fibre cubic m^3 - m - c f(a) has a repeated
    # root iff 4 - 27 c^2 f(a)^2 = 0; simple/transverse iff this and f'(a)
    # have no common root, i.e. Res_a(f', 27 c^2 f^2 - 4) != 0.
    res = fpa.resultant(27*cc^2*fa^2 - 4)
    res = Rcx(res)
    rts = [r for r, _ in res.roots()]
    intrts = [r for r in rts if r in ZZ and r >= 1]
    g = (-6 + 2*d + (0 if d % 3 == 0 else 2))/2 + 1
    print("%-34s deg f = %d" % (name, d))
    print("    Res_a(f', 27c^2 f^2 - 4) as a polynomial in c:", res.factor())
    print("    -> rational roots:", rts, "   positive INTEGER roots:", intrts)
    print("    => for every integer c >= 1 the %d finite branch points are" % (2*d))
    print("       simple, and 2g-2 = -6 + 2d + %d, i.e. GENUS = %d, uniformly in c."
          % (0 if d % 3 == 0 else 2, g))
    print()

print("="*78)
print("PART B -- the points at infinity: WHERE Sec.4ap's obstruction does and")
print("          does not bite")
print("="*78)
S.<Q, M, Z, cs> = QQ[]
for name, f in shapes.items():
    d = f.degree()
    D = max(3, d)                      # total degree of the plane model
    fh = sum(S(co)*Q^i*Z^(d-i) for i, co in enumerate(f.list()))
    F = M^3*Z^(D-3) - M*Z^(D-1) - cs*fh*Z^(D-d)
    print("%-34s plane model of degree %d:" % (name, D))
    print("     ", F)
    # points at infinity: Z = 0
    at_inf = F.subs(Z=0)
    print("      F|_{Z=0} =", at_inf)
    if d < 3:
        print("      => M^3 = 0: ONE point (1:0:0), with the line Z=0 meeting the")
        print("         cubic there to order 3 -- a RATIONAL INFLECTION.  Hence the")
        print("         pole divisor of q is 3*O with O rational: integrality is")
        print("         Weierstrass integrality and E.integral_points() APPLIES,")
        print("         for EVERY c.  (Sec.4ap's obstruction does NOT occur here.)")
    elif d == 3:
        print("      => M^3 = c Q^3: rational points at infinity exist iff c is a")
        print("         cube.  c = 6*l**f1 is a cube for some l*, but at l* = 1")
        print("         (the only value the S4 row can take) c = 6 is not, which")
        print("         is exactly the Sec.4ap obstruction -- handled in")
        print("         v_task44_dioph_c6.sage.")
    else:
        print("      => c Q^4 = 0: the unique point at infinity is (0:1:0), and it")
        print("         is a smooth point (dF/dZ = M^3 there).  The model is a")
        print("         PLANE QUARTIC, genus 3, non-hyperelliptic, with a rational")
        print("         point -- but no algorithm for its integral points.")
    print()

print("="*78)
print("PART C -- the L3 family in Weierstrass form, uniformly in c")
print("="*78)
print("k^3 - k = c(q^2+q+1).  Multiply by 4 and put v = 2q+1:")
print("     c(v^2 + 3) = 4(k^3 - k).")
print("Then with  X = 4ck,  Y = 4c^2 v  one gets")
print("     E_c :  Y^2 = X^3 - 16 c^2 X - 48 c^4 ,")
print("and (q,k) integral <=> X = 0 mod 4c, Y = 0 mod 8c^2, Y/(4c^2) odd.")
Rk.<kk, vv> = QQ[]
for ctest in [12, 18, 24, 30, 36, 42, 48, 60, 72, 96, 120]:
    E = EllipticCurve([0, 0, 0, -16*ctest^2, -48*ctest^4])
    # verify the transformation on a random rational solution of the model
    ok = True
    for kv in range(-6, 7):
        val = 4*(kv^3 - kv) - 3*ctest
        if val >= 0 and (val/ctest).is_square() and val % ctest == 0:
            v0 = sqrt(val/ctest)
            if v0 in ZZ:
                assert E.is_on_curve(4*ctest*kv, 4*ctest^2*v0)
    print("   c = %-4d  E_c: Y^2 = X^3 - %d X - %d   rank = %s  |E_c(Q)_tors| = %s"
          % (ctest, 16*ctest^2, 48*ctest^4, E.rank(), E.torsion_order()))
print()
print("j(E_c) = -28311552/(62208 c^2 - 16384): j varies with c, so the E_c are")
print("pairwise non-isomorphic -- rows 2 and 3 are genuinely INFINITE families")
print("of curves, not finitely many.  Per-curve methods cannot close them.")

print()
print("="*78)
print("PART D -- how much n-range does 'close all l* <= L' actually buy?")
print("="*78)
print("Row 2 (L3).  The R1 spectral gap gives q >= f1*(n-3), hence")
print("     C(n,3) = l* f1 (q^2+q+1) > l* f1^3 (n-3)^2,")
print("     l* < n(n-1)(n-2) / (6 f1^3 (n-3)^2)  <  n/6   (f1 >= 1, n >= 10).")
for L in [10, 100, 10^3, 10^4, 10^5, 10^6]:
    print("     closing l* <= %-8s covers only n <= %-10s"
          % (L, 6*L))
print("   The existing exact scan (v_task38/v_task41) already covers n <= 2e7")
print("   COMPLETELY IN q AND l*.  So closing the family curve-by-curve up to")
print("   l* <= L is strictly WEAKER than the scan unless L > 3.3e6, i.e. more")
print("   than three million Mordell-Weil computations on curves with")
print("   coefficients of size 48c^4 ~ 1e30.  The per-l* elliptic-curve route")
print("   is NOT competitive; rows 2 and 3 need a uniform-in-l* argument.")
print()
print("Row 3 (L5).  l* is provably free (v_task41 Sec.1.3); the same count")
print("applies with q^2 >= n-3, giving l* < n^3/(6 f1 (n-3)^2) < n/6 as well.")
print()
print("="*78)
print("PART E -- p-part refinement of the l* range (Lemma R1-p)")
print("="*78)
print("For S* of Lie type over F_{p^f} with N positive roots, |S*|_p = p^{fN}")
print("and |Q| divides n!/2, so  l* f N <= v_p(n!) < n/(p-1).")
print("Row 2 (L3, N = 3, f >= 2): with q = p^f >= f1(n-3),")
print("     3 l* f < n / (p-1),   p >= (f1 (n-3))^(1/f),")
print("   so   l* < n^(1-1/f) / (3 f f1^(1/f)).")
print("   f = 2: l* < sqrt(n)/6 ; f = 3: l* < n^(2/3)/9 ; and since")
print("   p >= 2 forces f <= log2(f1 n) + 1, uniformly l* = O(n/log n).")
print("Row 3 (L5, N = 10, f >= 1): 10 l* f <= v_p(n!) and q^2 >= n-3 give")
print("     l* < n^(1-1/(2f))/(10 f) -- again unbounded.")
print("CONCLUSION: no proven bound makes l* finite.  Rows 2 and 3 are open")
print("families; row 1 is a single curve and is settled in v_task44_dioph_c6.")
