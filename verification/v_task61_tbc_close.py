#!/usr/bin/env python3
"""
v_task61_tbc_close.py -- the PSN-GF bookkeeping for T-BC, made checkable.

By Theorem PSN-GF (NOTES.md Even, section 4af), for odd q and under (PAR),

    mult_1(PSp_{2n}(q)) = [x^{2n}] prod_{d even} (1 + x^d)^{p_d(q)}

so for n = 3,  mult_1(PSp_6(q)) = p_6 + p_2*p_4 + C(p_2, 3).

By Lemma GLUE (v_task61_tbc_close.md, section 3) the orthogonal
perp-decomposable layers vanish, so

    mult_1(Omega_7(q)) = p^O_7(q)   (plus p=3 parabolic artifacts).

This script evaluates both sides from the Rule-S column data recomputed in
v_task61_tbc_close.g and the exact primitive counts of v_task61_p4.g, and
prints the resulting bounds per residue class.  Nothing here is a proof;
it is the arithmetic of the bounds, isolated so that it can be rechecked.
"""

from itertools import combinations
from math import comb


def a(q, is_five_power):
    """rank-1 law: p^C_2(q) = p^O_3(q) = 1 + 2*[5 | q^2-1, q not a 5-power]"""
    return 3 if ((q * q - 1) % 5 == 0 and not is_five_power) else 1


def mult1_sp6(p2, p4, p6):
    return p6 + p2 * p4 + comb(p2, 3)


# --- Rule-S columns, symplectic (v_task61_tbc_close.g, section A) -----------
# branch 1 (Out-orbit 2) contributes exactly 2; branch 2 contributes 0 or 1.
def p4_bounds(q, sq5):
    """(lower, upper) for p^C_4(q).  Columns: Sp_4(q); 2.A_5 (Q, branch 2);
    2.A_6 two chars (Q, branch 2); Sym^3 SL_2(q) (defining char, <=1);
    C_6 member (computed 0 at q = 5, 7)."""
    lo = 1 + 1 + 1                      # Sp_4, 2.A_5, 2.A_6  (computed q=5,7)
    hi = 1 + 1 + 2 + 1 + 1              # + second 2.A_6 char, Sym^3, C_6
    return lo, hi


def p6_bounds(q, sq5, sq13, sqm2):
    """(lower, upper) for p^C_6(q).  Columns from the degree-6 table."""
    lo = 1 + 2 * sq5                    # Sp_6(q); 2.J_2 branch 1
    hi = (1              # Sp_6(q)
          + 1            # 2.A_5   (Q, branch 2)
          + 1            # U_3(3)  (Q, branch 2)
          + 2 * sq5      # 2.J_2   (Q(sqrt5), branch 1)
          + 2 * sq13     # 2.L_2(13) (Q(sqrt13), branch 1)
          + 1 * sqm2     # SL_2(7) (Q(sqrt-2), branch 2)
          + 2)           # Sym^5 SL_2(q), defining characteristic
    return lo, hi


# --- the orthogonal side ----------------------------------------------------
P_O7_PROVEN_LOWER = 11      # 1 (Omega_7) + 8 (Sp_6(2) tree) + 2 (G_2(q))
P_O7_EXTRA_COLUMNS = 5      # A_8, U_3(3), L_3(2), L_2(8), 2^6:A_7 -- each
                            # 0, 1 or 2 depending on an UNCOMPUTED spinor
                            # square class.  Upper bound 2 each.


def report(q, is_five_power, sq5, sq13, sqm2):
    p2 = a(q, is_five_power)
    p4lo, p4hi = p4_bounds(q, sq5)
    p6lo, p6hi = p6_bounds(q, sq5, sq13, sqm2)
    slo = mult1_sp6(p2, p4lo, p6lo)
    shi = mult1_sp6(p2, p4hi, p6hi)
    olo = P_O7_PROVEN_LOWER
    ohi = P_O7_PROVEN_LOWER + 2 * P_O7_EXTRA_COLUMNS
    verdict = ("Omega wins" if olo > shi else
               "Sp wins" if slo > ohi else
               "UNDECIDED by present bounds")
    print(f"q={q:>3}  a={p2}  Sp in [{slo:>2},{shi:>2}]   "
          f"Omega in [{olo:>2},{ohi:>2}]   -> {verdict}")


if __name__ == "__main__":
    print(__doc__)
    print("Legend: sq5 = [q = +-1 mod 5], sq13 = [13 a square mod q],")
    print("        sqm2 = [q = 1,3 mod 8]\n")
    for q in [5, 7, 9, 11, 13, 17, 19, 23, 25, 27, 29, 31]:
        is5 = (q in (5, 25))
        sq5 = 1 if ((q * q - 1) % 5 == 0 and not is5) else 0
        # 13 a square mod q: quadratic residue test on the prime part
        p = q
        while p % 2 == 0:
            p //= 2
        sq13 = 1 if pow(13, (q - 1) // 2, q) == 1 else 0 if q % 13 else 1
        sqm2 = 1 if q % 8 in (1, 3) else 0
        report(q, is5, sq5, sq13, sqm2)
    print("\nConclusion: with the proven inputs alone, EVERY residue class is")
    print("undecided, and for a = 3 the symplectic LOWER bound (13) already")
    print("exceeds the orthogonal PROVEN lower bound (11).  The decisive")
    print("missing input is the degree-7 spinor-norm square-class table.")
