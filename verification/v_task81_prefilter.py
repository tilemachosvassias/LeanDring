#!/usr/bin/env python3
"""
v_task81_prefilter.py -- independent reproduction of v_task50 §3.2's orbit-floor
prefilter table ("proper factors surviving") for all 27 sporadic targets.

The iota upper bounds are all self-derived (see iota_ub below); the only
imported datum is the v_task39 sporadic iota table, which was independently
re-verified in GAP by v_task81_iota.g.
"""
import re
import sys
from math import comb

sys.path.insert(0, __file__.rsplit('/', 1)[0])
import v_task81_census as V

SPORIOTA = V.IOTA_TARGET


def iota_ub(name, order):
    """VALID upper bounds for iota_ab(S), all self-derived:
       (a) |S| / |S|_p  for every p          (witness A = Z(Syl_p), N_S(A) >= Syl_p)
       (b) C(m,3) for A_m                    (witness <(123)>)
       (c) minimal parabolic index for Lie   (Borel-Tits, N_S(Z(U_P)) = P)
       (d) the v_task39 sporadic table (independently reconfirmed in GAP)."""
    cands = [order // p ** e for p, e in V.factorise(order).items()]
    if name in SPORIOTA:
        cands.append(SPORIOTA[name])
    if name.startswith("A") and name[1:].isdigit():
        cands.append(comb(int(name[1:]), 3))
    m = re.match(r"^L(\d+)\((\d+)\)$", name)
    if m:
        n, q = int(m.group(1)), int(m.group(2))
        cands.append((q ** n - 1) // (q - 1))
    m = re.match(r"^U(\d+)\((\d+)\)$", name)
    if m:
        n, q = int(m.group(1)), int(m.group(2))
        cands.append((q ** n - (-1) ** n) * (q ** (n - 1) - (-1) ** (n - 1))
                     // (q * q - 1))
    m = re.match(r"^S(\d+)\((\d+)\)$", name)
    if m:
        n, q = int(m.group(1)) // 2, int(m.group(2))
        cands.append((q ** (2 * n) - 1) // (q - 1))
    m = re.match(r"^O(\d+)\((\d+)\)$", name)
    if m:
        n, q = (int(m.group(1)) - 1) // 2, int(m.group(2))
        cands.append((q ** (2 * n) - 1) // (q - 1))
    m = re.match(r"^O(\d+)([+-])\((\d+)\)$", name)
    if m:
        n, s, q = int(m.group(1)) // 2, m.group(2), int(m.group(3))
        cands.append(((q ** (n - 1) + 1) * (q ** n - 1) // (q - 1)) if s == '+'
                     else ((q ** (n - 1) - 1) * (q ** n + 1) // (q - 1)))
    m = re.match(r"^G2\((\d+)\)$", name)
    if m:
        q = int(m.group(1))
        cands.append((q ** 6 - 1) // (q - 1))
    m = re.match(r"^Sz\((\d+)\)$", name)
    if m:
        cands.append(int(m.group(1)) ** 2 + 1)
    m = re.match(r"^R\((\d+)\)$", name)
    if m:
        cands.append(int(m.group(1)) ** 3 + 1)
    m = re.match(r"^3D4\((\d+)\)$", name)
    if m:
        q = int(m.group(1))
        cands.append((q ** 8 + q ** 4 + 1) * (q + 1))
    m = re.match(r"^F4\((\d+)\)$", name)
    if m:
        q = int(m.group(1))
        cands.append((q ** 12 - 1) * (q ** 4 + 1) // (q - 1))
    m = re.match(r"^2E6\((\d+)\)$", name)
    if m:
        q = int(m.group(1))
        cands.append((q ** 9 + 1) * (q ** 8 + q ** 4 + 1) // (q + 1))
    return min(cands)


def main():
    print("SHARP prefilter (independent iota upper bounds) -- reproducing")
    print("v_task50 §3.2 column 'proper factors surviving the orbit floor':")
    print()
    for nm in ["M11", "M12", "M22", "M23", "M24", "J1", "J2", "J3", "J4",
               "HS", "McL", "He", "Ru", "Suz", "ON", "Co1", "Co2", "Co3",
               "Fi22", "Fi23", "Fi24'", "HN", "Ly", "Th", "B", "M",
               "2F4(2)'"]:
        N = V.SPORADIC[nm]
        iotaS = V.IOTA_TARGET[nm]
        qcap, primes = V.divisor_cap(N)
        divs = [(a, o, ou) for (a, o, ou) in
                V.all_simple_upto(N, qmax=qcap, allowed_primes=primes)
                if N % o == 0]
        surv = []
        for (a, o, ou) in divs:
            if a == nm:
                continue
            iu = iota_ub(a, o)
            l = 1
            while l * ou * iu < iotaS:
                l += 1
                if o ** l > N:
                    break
            if o ** l <= N and l * ou * iu >= iotaS:
                surv.append((a, l))
        print("  %-8s iota=%-22d divisors=%-4d survivors: %s"
              % (nm, iotaS, len(divs), surv or "NONE"))
        sys.stdout.flush()


if __name__ == "__main__":
    main()
