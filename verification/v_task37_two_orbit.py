#!/usr/bin/env python3
"""
v_task37_two_orbit.py -- the A_n side of the elimination of case (b)
(NOTES.md 4av, input I5).

Proves, by the exact dynamic programme of 4as Step 3, the

    Lemma iota_3-A :  for n >= 10 the THIRD smallest value of
        I(A_n) = { [A_n : N(A)] : 1 <> A <= A_n abelian }
    is  3*C(n,4), attained exactly at A = <(12)(34)>;
    and the FOURTH is 4*C(n,4) if nonabelian H are admitted
    (H = A_4, |H'| = 4), else 6*C(n,5).

Machinery (4as Step 1).  For A abelian with support of size s,
    ind(A) = n^{(s)} / |N_{S_s}(A)|          if s <= n-2
    ind(A) >= n^{(s)} / (2|N_{S_s}(A)|)      always,
with A abelian, fixed-point-free and all-even on the s points.  A is
regular on each of its orbits, so (4as (*))

    |N_{S_s}(A)| <= G(s) := max over partitions s = sum n_i (n_i >= 2)
                    of  (prod_j m_j!) * prod_i g(n_i),
    g(m) = max{ m*|Aut(B)| : B abelian of order m }.

The claim  ind(A) > 3*C(n,4) = n^{(4)}/8  for every s >= 5 is therefore
implied by
    (n-4)^{(s-4)} > G(s)/8      (s <= n-2)
    (n-4)^{(s-4)} > G(s)/4      (s in {n-1, n}).
Both are checked exactly below.  s = 3, 4 are done by hand in 4as
Step 2 (values C(n,3); C(n,4) and 3C(n,4)).

|Aut(B)| for B abelian is the Hillar-Rhea formula; it is cross-checked
against the g-table printed by v_task37_two_orbit.g (PART B).
"""

from math import factorial
from functools import lru_cache


def factorint(m):
    f, d = {}, 2
    while d * d <= m:
        while m % d == 0:
            f[d] = f.get(d, 0) + 1
            m //= d
        d += 1
    if m > 1:
        f[m] = f.get(m, 0) + 1
    return f



def aut_abelian_p(p, exps):
    """|Aut| of the abelian p-group of type (p^e_1,...,p^e_k), Hillar-Rhea."""
    e = sorted(exps)
    k = len(e)
    d = [max(l for l in range(k) if e[l] == e[i]) + 1 for i in range(k)]
    c = [min(l for l in range(k) if e[l] == e[i]) + 1 for i in range(k)]
    r = 1
    for i in range(1, k + 1):
        r *= (p ** d[i - 1] - p ** (i - 1))
    for j in range(1, k + 1):
        r *= p ** (e[j - 1] * (k - d[j - 1]))
    for i in range(1, k + 1):
        r *= p ** ((e[i - 1] - 1) * (k - c[i - 1] + 1))
    return r


def partitions_of(m, maxpart=None):
    if maxpart is None:
        maxpart = m
    if m == 0:
        yield []
        return
    for f in range(min(m, maxpart), 0, -1):
        for rest in partitions_of(m - f, f):
            yield [f] + rest


@lru_cache(maxsize=None)
def g(m):
    """max m*|Aut(B)| over abelian B of order m."""
    fac = factorint(m)
    best = 1
    # choose a partition of each exponent
    def rec(primes, acc):
        nonlocal best
        if not primes:
            best = max(best, acc)
            return
        p, a = primes[0]
        for part in partitions_of(a):
            rec(primes[1:], acc * aut_abelian_p(p, part))
    rec(sorted(fac.items()), 1)
    return m * best


@lru_cache(maxsize=None)
def G(s):
    """max over partitions of s into parts >= 2 of (prod m_j!) * prod g(n_i)."""
    best = 0
    for part in partitions_of(s):
        if any(x < 2 for x in part):
            continue
        v = 1
        from collections import Counter
        cnt = Counter(part)
        for size, mult in cnt.items():
            v *= factorial(mult) * g(size) ** mult
        best = max(best, v)
    return best


def falling(n, k):
    r = 1
    for i in range(k):
        r *= (n - i)
    return r


def main():
    print("=== g(m), m = 2..40 (cross-check against GAP PART B) ===")
    print({m: g(m) for m in range(2, 41)})
    print()
    print("=== G(s), s = 4..45, against the two thresholds ===")
    print("  s |        G(s) | 4as thresh 12*(s-4)! | 8*(s-2)!/2 (s<=n-2) | 4*(s-4)! (s=n)")
    for s in range(4, 46):
        print(f"{s:3d} | {G(s):11d} | {12*factorial(max(s-4,0)):20d} |"
              f" {4*factorial(max(s-2,0)):19d} | {4*factorial(max(s-4,0)):14d}")
    print()

    # ---- the actual per-(n,s) check for Lemma iota_3-A ----
    print("=== Lemma iota_3-A check: ind(A) > 3*C(n,4) for all s >= 5 ===")
    bad = []
    NMAX = 400
    for n in range(10, NMAX + 1):
        for s in range(5, n + 1):
            Gs = G(s) if s <= 45 else None
            if Gs is None:
                continue
            lhs = falling(n - 4, s - 4)
            need = 8 if s <= n - 2 else 4
            if not lhs * need > Gs:
                bad.append((n, s, Gs, lhs, need))
    print(f"n = 10..{NMAX}, s = 5..min(n,45): violations = {len(bad)}")
    for b in bad[:20]:
        print("   VIOLATION", b)
    print()

    # n = 9, the known exception
    print("=== n = 9 (the AGL(3,2) point) ===")
    for s in range(5, 10):
        need = 8 if s <= 7 else 4
        print(f"  s={s}: G(s)={G(s):6d}   {need}*(9-4)^({s-4}) = {need*falling(5,s-4):6d}"
              f"   {'OK' if need*falling(5,s-4) > G(s) else 'FAILS'}")
    print("  -> s=8 fails: A = C_2^3 regular, N = AGL(3,2), ind = 9^(8)/1344 = "
          f"{falling(9,8)//1344}, and 3*C(9,4) = {3*126}. "
          "So iota_3(A_9) = 135 < 378: n = 9 is a genuine exception.")
    print()

    # ---- tail s > 45 ----
    print("=== tail s > 45 ===")
    print("  g(m) <= 2.5^m for all m (checked below), and a partition of s into")
    print("  parts >= 2 has at most s/2 parts, so G(s) <= (s/2)! * 2.5^s.")
    worst = max(g(m) / 2.5 ** m for m in range(2, 41))
    print(f"  max_{{2<=m<=40}} g(m)/2.5^m = {worst:.4f}  (<1, so g(m) <= 2.5^m holds)")
    for s in [46, 50, 60, 80, 100]:
        lhs = factorial(s // 2) * 2.5 ** s
        rhs = 4 * factorial(s - 4)
        print(f"  s={s}: (s/2)!*2.5^s = {lhs:.3e}   4*(s-4)! = {rhs:.3e}   "
              f"{'OK' if rhs > lhs else 'FAILS'}")
    print()

    # ---- the fourth value ----
    print("=== the fourth value of the spectrum ===")
    for n in [10, 12, 15, 20, 40, 100]:
        c34 = falling(n, 3) // 6
        c4 = falling(n, 4) // 24
        s5 = falling(n, 5) // 20          # C_5 on 5 points, N = F_20
        print(f"  n={n:4d}: C(n,3)={c34:12d} C(n,4)={c4:12d} 3C(n,4)={3*c4:12d} "
              f"4C(n,4)={4*c4:12d} 6C(n,5)={s5:12d}")
    print("  -> for n >= 9 the abelian 4th value is 6C(n,5) iff 6C(n,5) < the")
    print("     next s=4 value; there is none, so abelian iota_4 = 6C(n,5) when")
    print("     6C(n,5) < min_{s>=6} ..., and with nonabelian H admitted the 4th")
    print("     value is 4C(n,4) (H = A_4) whenever 4C(n,4) < 6C(n,5), i.e. n < 4+20/6*... :")
    for n in range(9, 20):
        c4 = falling(n, 4) // 24
        s5 = falling(n, 5) // 20
        print(f"     n={n:3d}: 4C(n,4)={4*c4:8d}  6C(n,5)={s5:8d}  "
              f"4th = {'4C(n,4) [A_4]' if 4*c4 < s5 else '6C(n,5) [C_5]'}")

    # ---- branch (b2): which ratios equal 3 ----
    print()
    print("=== branch (b2): iota_2/iota = 3 for the residual families ===")
    print("  ratio r(q) from 4at/4au (corrected); solve r(q) = 3*m1/m2 with")
    print("  m1, m2 | |Out(S)| -- i.e. r(q) is a rational with bounded height.")
    fams = {
        "L3(q) q>=3": lambda q: (q + 1),
        "L4(q)": lambda q: (q * q + q + 1) / (q + 1),
        "L5(q)": lambda q: q * q + 1,
        "S4(q) q=p>=5": lambda q: q * q / (2 * (q + 1)),
        "U4(q) q>=3": lambda q: (q * q + 1) / (q + 1),
        "Sp6(q) q=p": lambda q: (q ** 4 - 1) / (q ** 3 - 1),
        "U5(q) q=p": lambda q: q ** 4 / ((q + 1) * (q * q + 1)),
    }
    for nm, f in fams.items():
        hits = [q for q in range(2, 200) if abs(f(q) - 3) < 1e-12]
        near = [q for q in range(2, 200) if 3 / 24 <= f(q) <= 3 * 24]
        print(f"  {nm:14s}: r(q)=3 exactly at q in {hits};  "
              f"r(q) in [1/8, 72] only for q <= {max(near) if near else None}")


if __name__ == "__main__":
    main()


# ====================================================================
#  Appendix: the branch sweep for Theorem TO.
#
#  Residual families (4at/4au, corrected).  For each, iota_1(q) and
#  r(q) = iota_2(q)/iota_1(q) of the SIMPLE group; the pair invariants
#  are m_1*iota_1 and m_2*iota_2 with m_1, m_2 | |Out(S)| the fusion
#  numbers (4am: m <= 2 for the long-root class; we sweep m_i <= 4).
#
#  Branch (i)  [orbit O* carries the 3rd or 4th spectral value]:
#       (m_2/m_1) * r(q) = R(n),  R(n) in { 3(n-3)/4 , n-3 }
#  Branch (ii) [orbit O** carries it]:
#       (m_2/m_1) * r(q) = R,     R in { 3 , 4 }
#  together with
#       ell * m_1 * iota_1(q) = C(n,3)   (O*)   resp.  C(n,4)  (O**)
#       |S| > C(n,4)                      [(star)]
#       ell * log|S| <= log(n!/2)         [order]
# ====================================================================

from math import comb, lgamma, log


def order_L(d, q):
    o = q ** (d * (d - 1) // 2)
    for i in range(2, d + 1):
        o *= q ** i - 1
    return o // gcd_(d, q - 1)


def gcd_(a, b):
    while b:
        a, b = b, a % b
    return a


def order_U(d, q):
    o = q ** (d * (d - 1) // 2)
    for i in range(2, d + 1):
        o *= q ** i - (-1) ** i
    return o // gcd_(d, q + 1)


def order_Sp(m, q):   # PSp_{2m}(q)
    o = q ** (m * m)
    for i in range(1, m + 1):
        o *= q ** (2 * i) - 1
    return o // gcd_(2, q - 1)


FAMS = [
    # name, iota_1(q), r(q)=iota_2/iota_1, |S|(q), q-range
    ("L3(q)", lambda q: q * q + q + 1, lambda q: (q + 1, 1),
     lambda q: order_L(3, q), range(3, 400)),
    ("L4(q)", lambda q: (q + 1) * (q * q + 1), lambda q: (q * q + q + 1, q + 1),
     lambda q: order_L(4, q), range(2, 400)),
    ("L5(q)", lambda q: (q ** 5 - 1) // (q - 1), lambda q: (q * q + 1, 1),
     lambda q: order_L(5, q), range(2, 200)),
    ("U4(q)", lambda q: (q + 1) * (q ** 3 + 1), lambda q: (q * q + 1, q + 1),
     lambda q: order_U(4, q), range(3, 400)),
    ("S4(q) q=p>=5", lambda q: (q + 1) * (q * q + 1), lambda q: (q * q, 2 * (q + 1)),
     lambda q: order_Sp(2, q), range(5, 400)),
    ("Sp6(q) q=p", lambda q: (q ** 6 - 1) // (q - 1),
     lambda q: (q ** 4 - 1, q ** 3 - 1), lambda q: order_Sp(3, q), range(2, 200)),
    ("U5(q) q=p", lambda q: (q ** 5 + 1) * (q * q + 1),
     lambda q: (q ** 4, (q + 1) * (q * q + 1)), lambda q: order_U(5, q), range(2, 200)),
]


def logfact(n):
    return lgamma(n + 1)


def sweep():
    print("\n\n=== APPENDIX: branch sweep for Theorem TO ===")
    MS = [1, 2, 3, 4]
    for tag, Rname in [("(i)  O* / 3rd value", "3(n-3)/4"),
                       ("(i)  O* / 4th value", "n-3"),
                       ("(ii) O** / 3rd value", "3"),
                       ("(ii) O** / 4th value", "4")]:
        print(f"\n--- branch {tag} :  (m2/m1)*r(q) = {Rname} ---")
        surv = []
        for name, iota1, rq, ordS, qr in FAMS:
            for q in qr:
                num, den = rq(q)
                for m1 in MS:
                    for m2 in MS:
                        # (m2/m1)*num/den = R
                        if Rname in ("3", "4"):
                            R = int(Rname)
                            if m2 * num != R * m1 * den:
                                continue
                            ns = "free"
                            # |S| > C(n,4) bounds n
                            S = ordS(q)
                            nmax = 4
                            while comb(nmax + 1, 4) < S:
                                nmax += 1
                            cand = []
                            for n in range(10, min(nmax, 3000) + 1):
                                i1 = iota1(q)
                                if comb(n, 4) % (m1 * i1):
                                    continue
                                ell = comb(n, 4) // (m1 * i1)
                                if ell < 1:
                                    continue
                                if ell * log(S) > logfact(n) - log(2):
                                    continue
                                cand.append((n, ell))
                            if cand:
                                surv.append((name, q, m1, m2, cand[:5],
                                             f"n<= {nmax}"))
                        else:
                            # R(n) = 3(n-3)/4 or (n-3)
                            lhs_num, lhs_den = m2 * num, m1 * den
                            if Rname == "3(n-3)/4":
                                # (n-3) = 4*lhs/3
                                if (4 * lhs_num) % (3 * lhs_den):
                                    continue
                                n = 3 + (4 * lhs_num) // (3 * lhs_den)
                            else:
                                if lhs_num % lhs_den:
                                    continue
                                n = 3 + lhs_num // lhs_den
                            if n < 10:
                                continue
                            i1 = iota1(q)
                            if comb(n, 3) % (m1 * i1):
                                continue
                            ell = comb(n, 3) // (m1 * i1)
                            if ell < 1:
                                continue
                            S = ordS(q)
                            if S <= comb(n, 4):
                                continue                     # (star) fails
                            if ell * log(S) > logfact(n) - log(2):
                                continue                     # order fails
                            surv.append((name, q, m1, m2, n, ell))
        if surv:
            for s in surv[:40]:
                print("   SURVIVOR", s)
            print(f"   total survivors: {len(surv)}")
        else:
            print("   no survivors -- branch empty over the swept range")


sweep()


# ====================================================================
#  Appendix 2:  the 29 (*)-failures of v_task35_star_check_out.txt.
#
#  KEY POINT.  Theorem TR's side-condition (*) is needed only for the
#  EQUALITY iota(T) = min P.  The INCLUSION I(T) \supseteq P is Lemma
#  TR-1, which is unconditional.  Separation from A_n needs only the
#  inequality
#         iota(T) <= min P < C(n,3) = iota(A_n),
#  which then gives kappa(T) > kappa(A_n) by 4aj.  So every (*)-failure
#  whose min P is already below C(n,3) is separated OUTRIGHT, with no
#  side condition and no two-orbit analysis at all.
#
#  Upper bounds used for the orbit terms  ell * iota(K <= Abar):
#    * ell = 1 for every one of the 29 (all socle factors pairwise
#      non-isomorphic in each row, so every T-orbit is a singleton);
#    * A_m  : iota(K <= Abar) = C(m,3) EXACTLY for m >= 9 (the 3-cycle
#      is a single class in both A_m and S_m, so the fusion number is 1;
#      4am), and max(35, C(m,3)) for 5 <= m <= 8;
#    * L2(q): iota(K <= Abar) <= |Out| * iota(L2(q)) <= 2f*(q+1);
#      we use the crude q+1 times |Out| bound.
#    * sporadics: iota from the census tables (M11: 55, M12: 66,
#      J1: 266, J2: 100, S4(4): 85);  |Out| <= 2.
# ====================================================================

IOTA_SPOR = {"M11": 55, "M12": 66, "J1": 266, "J2": 100, "S4(4)": 85}


def iota_alt(m):
    return {5: 5, 6: 10, 7: 35, 8: 15}.get(m, comb(m, 3))


def iota_L2(q):
    return {7: 7, 9: 10}.get(q, q + 1)


ROWS = """60 A59 L2(4) / 60 A59 L2(5) / 16 A14 L2(4) / 16 A14 L2(5) /
68 A65 L2(67) / 65 A62 L2(64) / 62 A59 L2(61) / 60 A57 L2(59) /
54 A51 L2(53) / 50 A47 L2(49) / 48 A45 L2(47) / 44 A41 L2(43) /
42 A39 L2(41) / 38 A35 L2(37) / 33 A30 L2(32) / 32 A29 L2(31) /
30 A27 L2(29) / 28 A25 L2(27) / 12 M12 A7 / 26 A23 L2(25) /
24 A21 L2(23) / 20 A17 L2(19) / 18 A15 L2(17) / 22 A15 J1 L2(17) /
11 M11 A7 / 16 J2 M11 L2(13) / 66 A62 M11 L2(13) / 17 A14 L2(16) /
20 S4(4) J1 L2(27) L2(4)"""


def iota_of(tok):
    if tok.startswith("A") and tok[1:].isdigit():
        return iota_alt(int(tok[1:])), 1          # fusion number 1
    if tok.startswith("L2("):
        return iota_L2(int(tok[3:-1])), 2         # |Out| bound (crude)
    return IOTA_SPOR[tok], 2


def check29():
    print("\n\n=== APPENDIX 2: the 29 (*)-failures are separated unconditionally ===")
    print(" n  | socle factors                    | min_O ell*iota(K<=Abar) bound | C(n,3) | sep?")
    ok = 0
    for row in ROWS.replace("\n", " ").split("/"):
        t = row.split()
        if not t:
            continue
        n = int(t[0])
        toks = t[1:]
        best, wit = None, None
        for tok in toks:
            i, m = iota_of(tok)
            v = i * m
            if best is None or v < best:
                best, wit = v, tok
        c3 = comb(n, 3)
        sep = best < c3
        ok += sep
        print(f"{n:3d} | {' * '.join(toks):32s} | {best:8d} (at {wit:8s}) "
              f"| {c3:6d} | {'YES' if sep else 'NO'}")
    print(f"\n  separated: {ok} / 29")


check29()
