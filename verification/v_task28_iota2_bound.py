#!/usr/bin/env python3
"""NOTES.md Sec.4as, Step 3(b): the normalizer bound for large support.

For A <= S_s abelian, no fixed points, orbits O_1..O_t of sizes n_1..n_t,
    |N_{S_s}(A)|  <=  (prod_j m_j!) * prod_i |Hol(A|_{O_i})|
                  <=  (prod_j m_j!) * prod_i g(n_i)                    (*)
with m_j the number of orbits of each size and
    g(m) = max{ m*|Aut(A)| : A abelian of order m }   [GAP, hol.g].

Theorem needs:  G(s) := max over partitions of s into parts >= 2 of the
right-hand side of (*)  satisfies  G(s) <= 12*(s-4)!  for all s >= 10.
This script evaluates G(s) exactly by dynamic programming.
"""
from math import factorial

G_HOL = {2:2, 3:6, 4:24, 5:20, 6:12, 7:42, 8:1344, 9:432, 10:40, 11:110,
         12:144, 13:156, 14:84, 15:120, 16:322560, 17:272, 18:864, 19:342,
         20:480, 21:252, 22:220, 23:506, 24:8064, 25:12000, 26:312,
         27:303264, 28:1008, 29:812, 30:240, 31:930, 32:319979520, 33:660,
         34:544, 35:840, 36:10368, 37:1332, 38:684, 39:936, 40:26880}
SMAX = max(G_HOL)

def G(s):
    """max over partitions of s into parts >= 2 of (prod m_j!) prod g(n_i)."""
    # dp[part][remaining] = best using parts >= `part`
    from functools import lru_cache
    @lru_cache(maxsize=None)
    def best(part, rem):
        if rem == 0:
            return 1
        if part > rem:
            return 0
        b = best(part + 1, rem)                    # use no orbit of size `part`
        k, w = 1, G_HOL[part]
        while k * part <= rem:
            cand = factorial(k) * w * best(part + 1, rem - k * part)
            if cand > b:
                b = cand
            k += 1; w *= G_HOL[part]
        return b
    return best(2, s)

print(f"{'s':>4} {'G(s)':>22} {'12*(s-4)!':>26}  ok   worst-case shape")
allok = True
for s in range(5, SMAX + 1):
    g, thr = G(s), 12 * factorial(s - 4)
    ok = g <= thr
    if s >= 10 and not ok:
        allok = False
    print(f"{s:>4} {g:>22} {thr:>26}  {'OK' if ok else 'FAIL'}"
          f"{'' if s >= 10 else '   (s<10: handled at n=9 instead)'}")
print(f"\nG(s) <= 12*(s-4)! for all 10 <= s <= {SMAX}: {allok}")
print("For s > 40:  G(s) <= (s/2)! * 2.5^s  (since g(m) <= 2.5^m and there are")
print("at most s/2 orbits), and (s-4)!/(s/2)! >= (s/2)^(s/2-4) > 2.5^s/12 for")
print("s >= 24, so the bound holds a fortiori.")
