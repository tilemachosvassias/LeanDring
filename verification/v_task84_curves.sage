### v_task84 -- ADVERSARIAL RE-DERIVATION of v_task44's genus-1 closures.
###   C_c :  m^3 - m = c*(q^3+q^2+q+1),   c = 6 (row 1 of R1) and c = 12.
### Nothing from v_task44 is used as input: the Weierstrass model, the q-map,
### the constants of (I) and (II), and the LLL/CVP reduction are all
### re-derived here.  The write-up's numbers are only compared at the end.

import sys, itertools

prec = 400
RF = RealField(prec)

def banner(t):
    print("\n" + "="*78 + "\n" + t + "\n" + "="*78); sys.stdout.flush()

# ------------------------------------------------- exact CVP (LLL + Fincke-Pohst)
def exact_cvp2(Bmat, yvec):
    Bl = Bmat.LLL()
    n  = Bl.nrows()
    G  = Bl.gram_schmidt()[0]
    nG = [G[i]*G[i] for i in range(n)]
    mu = [[ (Bl[i]*G[j])/nG[j] for j in range(n)] for i in range(n)]
    y  = vector(QQ, yvec)
    t = y; coeffs = [0]*n
    for i in range(n-1, -1, -1):
        ci = QQ((t*G[i])/nG[i]).round(); coeffs[i] = ci; t = t - ci*Bl[i]
    v0 = sum((coeffs[i]*Bl[i] for i in range(n)), vector(ZZ, [0]*n))
    d2 = (y - v0)*(y - v0)
    ycoef = [ (y*G[i])/nG[i] for i in range(n) ]
    sol = [0]*n; best = [d2]
    def rec(i, partial):
        if i < 0:
            if partial < best[0]: best[0] = partial
            return
        centre = ycoef[i] - sum(sol[j]*mu[j][i] for j in range(i+1, n))
        rem = best[0] - partial
        if rem <= 0: return
        t = QQ(rem/nG[i]); a = t.numerator(); b = t.denominator()
        rad = QQ(ZZ(a*b).isqrt() + 1)/QQ(b)          # exact upper bound for sqrt(t)
        lo = (centre - rad).floor(); hi = (centre + rad).ceil()
        for v in range(lo, hi+1):
            d = QQ(v) - centre; add = d*d*nG[i]
            if partial + add < best[0]:
                sol[i] = v; rec(i-1, partial+add)
        sol[i] = 0
    rec(n-1, QQ(0))
    return best[0]

# ------------------------------------------------------------------------ main
def run(c, claimed_pts, claimed_N):
    banner("C_%d :  m^3 - m = %d*(q^3+q^2+q+1)" % (c, c))

    # ---------------- (1) independent cubic -> Weierstrass with both maps
    R = PolynomialRing(QQ, ['qv','mv','zv']); qv, mv, zv = R.gens()
    F = mv^3 - mv*zv^2 - c*(qv^3 + qv^2*zv + qv*zv^2 + zv^3)
    assert F(-1, 0, 1) == 0
    phi  = EllipticCurve_from_cubic(F, [-1, 0, 1], morphism=True)
    Eraw = phi.codomain(); E = Eraw.minimal_model()
    isoM = E.isomorphism_to(Eraw); u, r0, s0, t0 = isoM.tuple()
    print("[1] independent minimal model :", E)
    print("    disc =", E.discriminant(), "  <0 :", E.discriminant() < 0)
    print("    conductor =", E.conductor(), "  torsion =", E.torsion_order())

    # ---------------- (2) rank / gens / saturation / heights
    rk = E.rank(proof=True); gens = E.gens(proof=True)
    print("[2] rank(proof=True) =", rk, "   gens =", gens)
    print("    saturation index of gens =", E.saturation(list(gens))[1])
    H = E.height_pairing_matrix(gens)
    lam = RF(min(RR(e) for e in H.eigenvalues()))
    cps = RF(E.CPS_height_bound()); silv = RF(E.silverman_height_bound())
    print("    lambda_min =", RR(lam))
    print("    CPS  bound (h <= hhat + B) :", RR(cps), "  <-- WRONG DIRECTION for (I)")
    print("    Silv bound (|h - hhat|<=B) :", RR(silv), "  <-- the usable one")

    # ---------------- (3) x as a function of (q,m); coefficient norms
    pp = phi.defining_polynomials()
    numX = u^2*pp[0] + r0*pp[2]; denX = pp[2]
    g = gcd(numX, denX); numX = numX//g; denX = denX//g
    L = lcm([QQ(cf).denominator() for p in (numX, denX) for cf in p.coefficients()])
    numX = numX*L; denX = denX*L
    gg = gcd([ZZ(cf) for p in (numX, denX) for cf in p.coefficients()])
    numX = numX/gg; denX = denX/gg
    dg = max(numX.degree(), denX.degree())
    S  = max(sum(abs(ZZ(t)) for t in numX.coefficients()),
             sum(abs(ZZ(t)) for t in denX.coefficients()))
    print("[3] x_E = A/B with A =", numX, "   B =", denX)
    print("    degree =", dg, "   S = max 1-norm =", S)

    # ---------------- (4) the q- and m-maps on E
    Sr = PolynomialRing(QQ, ['X','Y','Z']); X, Y, Z = Sr.gens()
    psi_p = phi.inverse().defining_polynomials()
    xr = (X - r0*Z)/u^2; yr = (Y - s0*(X - r0*Z) - t0*Z)/u^3
    qn = psi_p[0](xr, yr, Z); mn = psi_p[1](xr, yr, Z); qd = psi_p[2](xr, yr, Z)
    dd = lcm([QQ(cf).denominator() for p in (qn, mn, qd) for cf in p.coefficients()])
    qn, mn, qd = qn*dd, mn*dd, qd*dd
    g2 = gcd(gcd(qn, qd), mn); qn, mn, qd = qn//g2, mn//g2, qd//g2
    gg2 = gcd([ZZ(cf) for p in (qn, mn, qd) for cf in p.coefficients()])
    qn, mn, qd = qn/gg2, mn/gg2, qd/gg2
    print("[4] q = (%s) / (%s)" % (qn, qd))
    print("    m = (%s) / (%s)" % (mn, qd))
    def qm_of(P):
        if P.is_zero(): return (QQ(-1), QQ(0))   # the base point of the construction
        X0, Y0, Z0 = P[0], P[1], P[2]
        d = qd(X0, Y0, Z0)
        if d == 0: return None
        return (qn(X0, Y0, Z0)/d, mn(X0, Y0, Z0)/d)
    print("    image of O =", qm_of(E(0)))
    print("    claimed points, checked on the equation AND through the map:")
    for (q0, m0) in claimed_pts:
        assert m0^3 - m0 == c*(q0^3+q0^2+q0+1), (q0, m0)
        dv = denX(q0, m0, 1)
        if dv == 0:
            hit = E(0) if qm_of(E(0)) == (q0, m0) else None
            xv = 'infinity (base point -> O)'
        else:
            xv = numX(q0, m0, 1)/dv
            hit = None
            for yv in E.lift_x(xv, all=True):
                if qm_of(yv) == (q0, m0): hit = yv
        print("      (q,m)=(%s,%s)  ->  x=%s  ->  P=%s" % (q0, m0, xv, hit))
        assert hit is not None

    # ---------------- (5) inequality (I), own constants
    alpha = RF((RF(5)/2*c)^(RF(1)/3))     # |m| <= alpha|q| for |q|>=2
    C1 = dg*RF(log(alpha)) + RF(log(S)) + silv
    print("[5] (I):  hhat(P) <= %d*log|q| + C1  with alpha = %s, C1 = %s"
          % (dg, RR(alpha), RR(C1)))

    # ---------------- (6) real pole of q, kappa, Q0
    PL = E.period_lattice(); om = RF(PL.real_period(prec=prec))
    print("[6] real period omega =", RR(om))
    def pt(zz):
        P = PL.elliptic_exponential(RF(zz))
        return (RF(P[0]), RF(P[1]))
    def q_at(zz):
        try:
            x, y = pt(zz)
        except Exception:
            return None
        d = qd(x, y, RF(1))
        if d == 0: return None
        return qn(x, y, RF(1))/d
    Ng = 40000
    inv = []
    for k in range(Ng):
        v = q_at(om*k/Ng)
        inv.append(RF(1)/v if (v is not None and v != 0) else RF(0))
    poles = []
    for i in range(Ng):
        a, b = inv[i], inv[(i+1) % Ng]
        if a*b < 0 and abs(a) < RF('0.05') and abs(b) < RF('0.05'):
            lo, hi = om*i/Ng, om*(i+1)/Ng
            fa = a
            for _ in range(400):
                mid = (lo+hi)/2
                vm = q_at(mid); fm = RF(1)/vm if (vm is not None and vm != 0) else RF(0)
                if fa*fm < 0: hi = mid
                else: lo = mid; fa = fm
            poles.append((lo+hi)/2)
    print("    real poles of q on E(R):", [RR(p) for p in poles])
    assert len(poles) == 1
    zinf = poles[0]
    print("    z(P_inf) =", RR(zinf), "   P_inf ~", [RR(v) for v in pt(zinf)])

    eps = RF('0.01'); kappa = RF(0); K = 60000
    for j in range(1, K+1):
        for sg in (1, -1):
            dz = sg*eps*j/K
            v = q_at(zinf+dz)
            if v is None or v == 0: continue
            kappa = max(kappa, abs(dz)*abs(v))
    kappa = kappa*RF('1.05')
    Q0 = RF(0); M = 60000
    for j in range(M+1):
        v = q_at(zinf + eps + (om - 2*eps)*j/M)
        if v is None: continue
        Q0 = max(Q0, abs(v))
    Q0 = Q0*RF('1.05')
    print("    own kappa =", RR(kappa), "   own Q0 =", RR(Q0))

    # ---------------- (7) elliptic logs of the generators
    def red(z): return z - om*RF(z/om).floor()
    zg = [red(RF(PL.elliptic_logarithm(G, prec=prec).real())) for G in gens]
    print("[7] z(G_i) =", [RR(z) for z in zg])
    T = gens[0] + 2*gens[1] - gens[2]
    zt = red(RF(PL.elliptic_logarithm(T, prec=prec).real()))
    e = red(zt - (zg[0]+2*zg[1]-zg[2]))
    print("    homomorphism check, residual =", RR(min(e, om-e)))

    # ---------------- (8) own LLL / exact-CVP reduction loop
    def step(Bnd):
        C = ZZ(ceil(RF(4*Bnd)^5))
        a = [ZZ((C*z).round()) for z in zg] + [ZZ((C*om).round())]
        Bm = matrix(ZZ, 4, 4)
        for i in range(3): Bm[i, i] = 1
        for i in range(4): Bm[3, i] = a[i]
        Bm = Bm.transpose()
        yv = vector(ZZ, [0, 0, 0, ZZ((C*zinf).round())])
        d2 = exact_cvp2(Bm, yv)
        new = 0
        for Nn in range(0, min(Bnd, 10^6)+1):
            lq = QQ(d2) - 3*Nn^2
            if lq <= 0: new = Nn; continue
            lhs = RF(lq).sqrt() - (3*Nn + 3) - 1
            rhs = RF(C)*kappa*exp(C1 - dg*lam*Nn^2/2) if dg == 2 else \
                  RF(C)*kappa*exp(C1 - lam*Nn^2)
            if lhs <= rhs: new = Nn
        return C, d2, new
    print("[8] reduction loop (own LLL + exact CVP):")
    finals = {}
    for B0 in [10^60, 10^100, 10^200]:
        Bnd = B0
        for it in range(10):
            C, d2, nb = step(Bnd)
            print("     start %-8s d = %-22s -> new bound %s"
                  % (("1e%d" % B0.ndigits()), RR(RF(QQ(d2)).sqrt()), nb))
            if nb >= Bnd: break
            Bnd = nb
            if Bnd <= 1: break
        finals[B0] = Bnd
        print("     REDUCED BOUND from start %s : N <= %s" % (B0, Bnd))
    Nfinal = max(finals.values())

    # |q| >= Q0 is automatic once ...
    Nq0 = RR(sqrt((dg*log(Q0) + C1)/lam)) if dg == 2 else RR(sqrt((log(Q0)+C1)/lam))
    print("[9] (II) applies (|q| >= Q0) as soon as N >", Nq0)

    # ---------------- (10) enumeration
    Nen = max(Nfinal, ceil(Nq0)) + 2
    print("[10] enumerating all P = sum n_i G_i with |n_i| <=", Nen)
    found = set()
    rO = qm_of(E(0))
    if rO is not None and rO[0] in ZZ and rO[1] in ZZ:
        found.add((ZZ(rO[0]), ZZ(rO[1])))
    for n in itertools.product(range(-Nen, Nen+1), repeat=3):
        if n == (0,0,0): continue
        P = n[0]*gens[0] + n[1]*gens[1] + n[2]*gens[2]
        if P.is_zero(): continue
        r = qm_of(P)
        if r is None: continue
        if r[0] in ZZ and r[1] in ZZ:
            found.add((ZZ(r[0]), ZZ(r[1])))
    small = set()
    for q0 in range(-ceil(Q0)-3, ceil(Q0)+4):
        rhs = c*(q0^3+q0^2+q0+1)
        for m0 in range(-400, 401):
            if m0^3 - m0 == rhs: small.add((q0, m0))
    allp = sorted(found | small)
    print("     from enumeration :", sorted(found))
    print("     |q| <= Q0 sweep  :", sorted(small))
    print("     TOTAL            :", allp)
    print("     v_task44 claims  :", sorted(claimed_pts))
    print("     MATCH :", allp == sorted([tuple(p) for p in claimed_pts]))

    # ---------------- (11) brute-force control
    bf = set()
    for q0 in range(-2*10^6, 2*10^6):
        rhs = c*(q0^3+q0^2+q0+1)
        s = ZZ(rhs).sign(); a = ZZ(abs(rhs))
        m0 = s*ZZ(round(RR(a)^(RR(1)/3)))
        for d in range(-2, 3):
            if (m0+d)^3 - (m0+d) == rhs: bf.add((q0, m0+d))
    print("[11] brute force |q| < 2e6:", sorted(bf), " subset of closed list:",
          bf <= set(allp))
    return allp

run(6,  [(-8,-14), (-3,-5), (-1,-1), (-1,0), (-1,1), (0,2), (1,3)], 8)
run(12, [(-2,-4), (-1,-1), (-1,0), (-1,1)], 6)
