#!/usr/bin/env python3
"""
v_task45_cdead.py --- the L3_2 valuation kill, generalised to an arbitrary
multiplier c, for the two open R1 rows.

Both open rows of R1 have the shape

    n(n-1)(n-2)  =  c * F(q),      c = 6 f1 l*,      F = Phi_3 or Phi_5,

with F(q) = q^2+q+1 (row 2, L_3) or q^4+q^3+q^2+q+1 (row 3, L_5).

Facts used (all elementary, proved in v_task45_ellstar.md):
  (F1) F(q) is ODD for every integer q.
  (F2) every prime r | Phi_e(q) satisfies r = e or r == 1 (mod e), e in {3,5}.
  (F3) v_e(Phi_e(q)) <= 1.

Consequences, for M = n(n-1)(n-2):
  (C1) v_2(M) = v_2(c)                     [from (F1)]
  (C2) W_e(M) divides c, where W_e(x) = prod_{r prime, r != e, r != 1 mod e}
       r^{v_r(x)}                          [from (F2)]
  (C3) for X in {n,n-1,n-2} with e ł X:  X == W_e(X)  (mod e).

The script decides, for each c, whether (C1)+(C2)+(C3) are simultaneously
satisfiable.  If not, the equation has NO solution for ANY n: c is DEAD,
unconditionally and for every n.

Positive control: c = 12 must come out DEAD in row 2 (that is Theorem L3_2).
Negative control: c = 6 must come out ALIVE in row 2 (Sec 4ao needed a
quartic squeeze there, so no valuation obstruction can exist).
"""

import sys
from math import gcd


def v2(x):
    k = 0
    while x % 2 == 0:
        x //= 2
        k += 1
    return k


def divisors(c):
    ds = []
    d = 1
    while d * d <= c:
        if c % d == 0:
            ds.append(d)
            if d != c // d:
                ds.append(c // d)
        d += 1
    return sorted(ds)


def two_adic_patterns(V):
    """All possible (v2(n), v2(n-1), v2(n-2)) with v2(M) = V.

    n odd : (0, V, 0), needs V >= 1.
    n even: n-1 odd; n and n-2 are consecutive even numbers so exactly one
            has v2 = 1 and the other has v2 >= 2.  Hence {v2(n),v2(n-2)}
            = {1, V-1} with V-1 >= 2, i.e. V >= 3.
    """
    pats = []
    if V >= 1:
        pats.append((0, V, 0))
    if V >= 3:
        pats.append((1, 0, V - 1))
        pats.append((V - 1, 0, 1))
    return pats


def alive(c, e):
    """Is the system (C1)+(C2)+(C3) satisfiable for this c and modulus e?

    Returns None if dead, else a witness (n mod e, 2-adic pattern, g-triple).
    """
    V = v2(c)
    ds = [d for d in divisors(c) if d % e != 0]      # g's are coprime to e
    by_v2 = {}
    for d in ds:
        by_v2.setdefault(v2(d), []).append(d)
    for pat in two_adic_patterns(V):
        for r in range(e):                            # r = n mod e
            res = [(r - i) % e for i in range(3)]      # residues of n,n-1,n-2
            cands = []
            ok = True
            for i in range(3):
                lst = []
                for g in by_v2.get(pat[i], []):
                    if res[i] == 0 or g % e == res[i]:
                        lst.append(g)
                if not lst:
                    ok = False
                    break
                cands.append(lst)
            if not ok:
                continue
            for g0 in cands[0]:
                for g1 in cands[1]:
                    if c % (g0 * g1) != 0:
                        continue
                    for g2 in cands[2]:
                        p = g0 * g1 * g2
                        if c % p == 0:
                            return (r, pat, (g0, g1, g2))
    return None


def report(e, label, cmax):
    dead = []
    tot = 0
    for c in range(6, cmax + 1, 6):
        tot += 1
        if alive(c, e) is None:
            dead.append(c)
    print(f"--- {label}: modulus e = {e}, c = 6,12,...,{cmax} ---")
    print(f"    multipliers tested : {tot}")
    print(f"    provably DEAD      : {len(dead)}   ({100.0*len(dead)/tot:.2f} %)")
    print(f"    first 40 dead c    : {dead[:40]}")
    return set(dead)


if __name__ == "__main__":
    cmax = int(sys.argv[1]) if len(sys.argv) > 1 else 3000

    print("== controls ==")
    print("row 2, c = 12 (Theorem L3_2):", "DEAD" if alive(12, 3) is None else "ALIVE  <-- BUG")
    print("row 2, c =  6 (Sec 4ao squeeze needed):", "ALIVE" if alive(6, 3) else "DEAD  <-- BUG")
    w = alive(6, 5)
    print("row 3, c =  6 witness (n mod 5, v2-pattern, g-triple):", w)
    print()

    d3 = report(3, "ROW 2  (L_3, F = q^2+q+1)", cmax)
    print()
    d5 = report(5, "ROW 3  (L_5, F = q^4+q^3+q^2+q+1)", cmax)
    print()

    # Characterisation claimed in the write-up for row 2:
    #   c is dead  <=>  v_2(c) = 2  and every odd prime factor of c is
    #                   3 or == 1 (mod 3).
    def claim3(c):
        if v2(c) != 2:
            return False
        m = c >> 2
        r = 2
        while r * r <= m:
            if m % r == 0:
                if r != 3 and r % 3 != 1:
                    return False
                while m % r == 0:
                    m //= r
            r += 1
        return m == 1 or m == 3 or m % 3 == 1

    bad = [c for c in range(6, cmax + 1, 6) if (c in d3) != claim3(c)]
    print("row 2 closed-form characterisation  v_2(c)=2 & odd part 3-or-1mod3 :",
          "CONFIRMED on all tested c" if not bad else f"FAILS at {bad[:10]}")

    # density of dead multipliers in row 3, by v_2(c)
    from collections import Counter
    cnt = Counter()
    tot = Counter()
    for c in range(6, cmax + 1, 6):
        tot[v2(c)] += 1
        if c in d5:
            cnt[v2(c)] += 1
    print("row 3 dead-fraction by v_2(c):",
          {k: f"{cnt[k]}/{tot[k]}" for k in sorted(tot)})
