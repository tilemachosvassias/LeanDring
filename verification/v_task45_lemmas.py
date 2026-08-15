#!/usr/bin/env python3
"""
v_task45_lemmas.py --- numerical certification of the elementary inequalities
and valuation facts used in v_task45_ellstar.md.

Nothing here is a proof by itself; each item is the finite/asymptotic check
attached to a hand proof in the write-up.
"""
import math

FAIL = []


def chk(name, ok, extra=""):
    print(f"[{'OK ' if ok else 'FAIL'}] {name} {extra}")
    if not ok:
        FAIL.append(name)


# ---------------------------------------------------------------- (F1)-(F3)
def Phi(e, q):
    return sum(q ** i for i in range(e))


ok = all(Phi(3, q) % 2 == 1 and Phi(5, q) % 2 == 1 for q in range(-50, 2000))
chk("(F1) Phi_3(q), Phi_5(q) odd for all integers q", ok)


def primes_up_to(N):
    s = bytearray([1]) * (N + 1)
    s[0] = s[1] = 0
    for i in range(2, int(N ** .5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(N + 1) if s[i]]


P = primes_up_to(100000)


def factor(n):
    d = {}
    for p in P:
        if p * p > n:
            break
        while n % p == 0:
            n //= p
            d[p] = d.get(p, 0) + 1
    if n > 1:
        d[n] = d.get(n, 0) + 1
    return d


bad2 = bad3 = bad5 = None
for e in (3, 5):
    for q in range(2, 700):
        for r, v in factor(Phi(e, q)).items():
            if r != e and r % e != 1:
                bad3 = (e, q, r)
            if r == e and v > 1:
                bad5 = (e, q, v)
chk("(F2) every prime of Phi_e(q) is e or == 1 mod e   (e=3,5, q<=700)", bad3 is None, str(bad3 or ""))
chk("(F3) v_e(Phi_e(q)) <= 1                            (e=3,5, q<=700)", bad5 is None, str(bad5 or ""))


# ------------------------------------------------- Lemma NC size inequality
# claim:  n(n-1)(n-2)/(n-3)^2  <  2(n-2)   for all n >= 10
bad = [n for n in range(10, 2000) if n * (n - 1) * (n - 2) / (n - 3) ** 2 >= 2 * (n - 2)]
chk("Lemma NC ineq  M/(n-3)^2 < 2(n-2) for n >= 10 (checked n<=2000; "
    "equivalent to n^2-11n+18>0, true for all n>=10)", not bad, str(bad[:5]))

# f1 = 2 refinement:  M/(4(n-3)^2) < n-2   for all n >= 10
bad = [n for n in range(10, 2000) if n * (n - 1) * (n - 2) / (4 * (n - 3) ** 2) >= (n - 2)]
chk("Lemma NC ineq (f1=2)  M/(4(n-3)^2) < n-2 for n >= 10", not bad, str(bad[:5]))


# ------------------------------------------------------ Lemma L-bound on l*
# l* = M / (6 f1 Phi_3(q)) with q >= f1(n-3).  Claim: l* < n/6 + 3 (f1=1)
# and l* < n/48 + 1 (f1=2), for all n >= 10.
bad = []
for n in range(10, 200000):
    M = n * (n - 1) * (n - 2)
    for f1 in (1, 2):
        q = f1 * (n - 3)
        lmax = M / (6 * f1 * (q * q + q + 1))
        bound = n / 6 + 3 if f1 == 1 else n / 48 + 1
        if lmax > bound:
            bad.append((n, f1, lmax, bound))
chk("Lemma L-bound  l* < n/6 + 3 (f1=1),  l* < n/48 + 1 (f1=2), n <= 2*10^5",
    not bad, str(bad[:3]))


# --------------------------------- Theorem L3_2-gen: sufficient condition
# c dead  <=  v_2(c) = 2 and every odd prime factor of c is 3 or == 1 mod 3.
def v2(x):
    k = 0
    while x % 2 == 0:
        x //= 2
        k += 1
    return k


def dead_c(c):
    if v2(c) != 2:
        return False
    for r in factor(c >> 2):
        if r != 3 and r % 3 != 1:
            return False
    return True


dead = [c for c in range(6, 4001, 6) if dead_c(c)]
print(f"\nrow-2 multipliers c <= 4000 killed by Theorem L3_2-gen: {len(dead)}")
print("  ", dead[:25], "...")

# exhaustive confirmation on a window: no (n,q) with q>=2 solves
# k^3-k = c*Phi_3(q) for any dead c, for all n <= 3*10^5
viol = []
for n in range(3, 300001):
    M = n * (n - 1) * (n - 2)
    for c in dead:
        if M % c:
            continue
        Y = 4 * (M // c) - 3
        if Y < 1:
            continue
        s0 = math.isqrt(Y)
        if s0 * s0 == Y and s0 % 2 == 1 and (s0 - 1) // 2 >= 2:
            viol.append((c, n, (s0 - 1) // 2))
chk("Theorem L3_2-gen: no solution for ANY of the %d dead c <= 4000, all "
    "n <= 3*10^5" % len(dead), not viol, str(viol[:5]))


# ------------------------------- Lemma NC: density of n it kills on its own
def is_prime(n):
    if n < 2:
        return False
    for p in P:
        if p * p > n:
            break
        if n % p == 0:
            return n == p
    return True


X = 200000
killed = sum(1 for n in range(10, X + 1)
             if any(is_prime(n - i) for i in range(3)))
print(f"\nLemma NC alone kills {killed}/{X-9} = {100.0*killed/(X-9):.2f} % of n <= {X} "
      f"(asymptotically ~3/log n -> 0): it is a structural constraint, NOT a "
      f"density-1 kill.")

# NC-gen with j <= 5
killed2 = 0
for n in range(10, X + 1):
    hit = False
    for i in range(3):
        m = n - i
        for j in range(1, 5):
            if m % j == 0 and is_prime(m // j) and m // j > n / (j + 1):
                hit = True
                break
        if hit:
            break
    if hit:
        killed2 += 1
print(f"Lemma NC-gen (j <= 4, needs l* >= 5) kills {100.0*killed2/(X-9):.2f} % of n <= {X}")

print("\nFAILURES:", FAIL if FAIL else "none")


# ------------------------------------------------- Lemma NC-gen+ (sharpened)
# p-part filter (v_task38 filter (4), PROVEN):  l* f N <= v_p(n!) < n/(p-1),
# with q = p^f >= n-3 (row 2, N=3) resp. q^2 >= n-3 (row 3, N=10).
# => l* < n ln p / (N' (p-1) ln(n-3)) maximised at p = 2.
import math as _m
print()
for row, N, expo in ((2, 3, 1), (3, 10, 2)):
    best = 0.0
    for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]:
        best = max(best, expo * _m.log(p) / (N * (p - 1)))
    print(f"row {row}: l* < {best:.4f} * n/ln(n-3)   (max over p at p=2)")
    print(f"        c = 6 f1 l* < {12*best:.4f} * n/ln(n-3)")
    print(f"        NC-gen+ valid for j <= {6/(12*best):.4f}*ln(n-3) - 1")

Xs = [10**5, 10**7, 10**11]
for X in Xs:
    J2 = max(1, int(2.1645 * _m.log(X - 3)) - 1)
    J3 = max(1, int(3.6067 * _m.log(X - 3)) - 1)
    print(f"n ~ {X:.0e}:  row-2 j-range = 1..{J2},  row-3 j-range = 1..{J3}")

# measured density of the NC-gen+ kill at n <= 2*10^5 with the j-range
# available there (row 2: j <= 24, row 3: j <= 42)
X = 200000
for label, J in (("row 2", 24), ("row 3", 42)):
    killed = 0
    for n in range(10, X + 1):
        hit = False
        for i in range(3):
            m = n - i
            for j in range(1, J + 1):
                if m % j == 0 and is_prime(m // j) and m // j > n / (j + 1):
                    hit = True
                    break
            if hit:
                break
        if hit:
            killed += 1
    print(f"Lemma NC-gen+ ({label}, j <= {J}, needs l* > j) kills "
          f"{100.0*killed/(X-9):.2f} % of n <= {X}")
