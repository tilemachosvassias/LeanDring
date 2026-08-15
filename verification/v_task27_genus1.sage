#!/usr/bin/env sage
# ============================================================================
# THE TWO SURVIVING GENUS-1 EQUATIONS  (NOTES.md Sec.4ap)   -- VERDICT: Sage
# CANNOT CLOSE THEM EITHER, and this file proves why.
#
#   C_c :  m^3 - m = c*(q^3 + q^2 + q + 1),   m = n-1
#          c = 6   <->   S4/L4, mult 1 :  q^3+q^2+q+1     = C(n,3)
#          c = 12  <->   L4,    mult 2 : 2(q^3+q^2+q+1)   = C(n,3)
#
# The line at infinity meets C_c where m^3 = c q^3, and c is not a cube, so
# the three points at infinity are one Galois orbit: C_c has NO rational
# point at infinity.  Hence q and m have pole divisor D of degree 3 with no
# rational point in its support, and "q, m integral" is integrality relative
# to D -- whereas E.integral_points() computes integrality relative to 3*O
# for a RATIONAL point O.  The two notions coincide iff C_c has a rational
# INFLECTION point I (then D ~ 3I and the Weierstrass map is linear).
#
# I is an inflection  <=>  3*[I-O] = [D - 3O] =: kappa  in E(Q) = Pic^0(C).
# kappa is computed from any collinear rational triple (all triples must give
# the same class -- checked below over every line through two known rational
# points), and the test "kappa in 3E(Q)" is decided exactly by
# division_points(3).
#
# RESULT (both curves):  rank 3 (proof=True), trivial torsion, kappa NOT in
# 3E(Q)  =>  no rational inflection  =>  integral_points()/S_integral_points()
# do not apply.  Sec.4ao's "one IntegralPoints call each" fails for these two
# as well, for a different reason than for the five higher-genus curves.
# ============================================================================

P.<X, Y, Z> = QQ[]

KNOWN = {
  6:  [(-1,-1), (-1,1), (0,2), (1,3), (-3,-5), (-8,-14), (QQ(-6)/7, QQ(10)/7),
       (QQ(3)/11, QQ(24)/11), (QQ(-9)/7, QQ(-13)/7), (QQ(11)/7, QQ(27)/7)],
  12: [(-1,-1), (-1,1), (-2,-4), (QQ(1)/5, QQ(13)/5), (QQ(-6)/13, QQ(28)/13),
       (QQ(11)/13, QQ(45)/13)],
}
INTEGRAL_KNOWN = {6:  [(-8,-14), (-3,-5), (-1,-1), (-1,0), (-1,1), (0,2), (1,3)],
                  12: [(-2,-4), (-1,-1), (-1,0), (-1,1)]}

R.<t> = QQ[]

for c in [6, 12]:
    print("=" * 74)
    print(f"C_{c}:  m^3 - m = {c}(q^3+q^2+q+1)")
    F = Y^3 - Y*Z^2 - c*(X^3 + X^2*Z + X*Z^2 + Z^3)
    C = Curve(F)
    print("  smooth:", C.is_smooth(), "  genus:", C.genus())
    print("  rational points at infinity (m^3 = c q^3):",
          (t^3 - c).roots(), "  -- none, as advertised")

    # origin O = (-1,0); EllipticCurve_from_cubic blows this point down
    phi = EllipticCurve_from_cubic(F, [-1, 0, 1], morphism=True)
    E, D = phi.codomain(), phi.domain()
    Emin = E.minimal_model()
    iso = E.isomorphism_to(Emin)

    def im(q, m):
        if (q, m) == (-1, 0):
            return Emin(0)
        return iso(phi(D([q, m, 1])))

    print("  minimal model :", Emin)
    print("  conductor     :", Emin.conductor())
    print("  torsion       :", Emin.torsion_subgroup().order())
    print("  rank          :", Emin.rank(proof=True), "(proved)")
    print("  generators    :", Emin.gens())

    # --- the hyperplane class kappa, from every collinear rational triple ---
    classes = []
    K = KNOWN[c]
    for i in range(len(K)):
        for j in range(i + 1, len(K)):
            (q1, m1), (q2, m2) = K[i], K[j]
            if q1 == q2:
                continue
            a = (m2 - m1) / (q2 - q1)
            b = m1 - a * q1
            g = (a*t + b)^3 - (a*t + b) - c*(t^3 + t^2 + t + 1)
            rts = [r for r, _ in g.roots()]
            if len(rts) == 3:                      # fully rational triple
                classes.append(sum((im(r, a*r + b) for r in rts), Emin(0)))
    assert classes and len(set(classes)) == 1, "hyperplane class not well defined"
    kappa = classes[0]
    print(f"  {len(classes)} collinear rational triples, all giving ONE class:")
    print("  kappa = [D - 3O] =", kappa)

    dp = kappa.division_points(3)
    print("  kappa in 3E(Q) :", dp, " => rational inflection exists:", bool(dp))
    assert not dp
    print("  ==> integrality is relative to a degree-3 divisor with no rational")
    print("      point in its support; integral_points() does NOT apply.")

    print("  known integral points (all have q <= 1, none a prime power):")
    for (q0, m0) in INTEGRAL_KNOWN[c]:
        assert m0^3 - m0 == c*(q0^3 + q0^2 + q0 + 1)
        print(f"      (q, m) = ({q0}, {m0})   ->  n = {m0 + 1}")

print("=" * 74)
print("What would be needed: elliptic logarithms relative to a degree-3 divisor")
print("(Bilu-style), over a rank-3 Mordell-Weil lattice.  Not in Sage, not in")
print("Magma.  See NOTES.md Sec.4ap for the group-theoretic bypass taken instead.")
