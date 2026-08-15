#!/usr/bin/env python3
"""
v_task63_delta.py -- ADVERSARIAL re-derivation of Delta(q) for (T-BC-RES).

Independent of v_task62_spinor.py: the column rules are re-entered from the
mathematics (see v_task63_bc3_audit.md), and the SUBFIELD (Aschbacher C_5)
columns -- omitted by v_task62 on both sides -- are put back.

    Delta(q) = p^O7(q) - [ p^C6(q) + a(q)*p^C4(q) + C(a(q),3) ]

Because the subfield columns depend on the FACTORISATION r of q = p^r and not
on a residue class, the scan is over (p mod M, r) rather than q mod M.
"""
from math import comb

M = 9360                                   # lcm(16,9,5,12,13)

sq2  = lambda q: q % 8 in (1, 7)
nsq2 = lambda q: q % 8 in (3, 5)
nsq3 = lambda q: q % 12 in (5, 7)          # 3 a non-square (q odd)
sq5  = lambda q: q % 5 in (1, 4)
sq13 = lambda q: q % 13 in (1, 3, 4, 9, 10, 12)
z9   = lambda q: q % 9 in (1, 8)
pm716= lambda q: q % 16 in (7, 9)


def divisors(r):
    return [d for d in range(1, r + 1) if r % d == 0]


# ---------------------------------------------------------------- subfields
def subfield_data(p, r):
    """proper subfields F_{p^d} of F_{p^r}."""
    props = [d for d in divisors(r) if d < r]
    # G_2(q_0) is psn in Omega_7(q) for EVERY subfield (incl. q_0 = q):
    #   no diagonal aut, field auts not linearly realised -> N_{SO_7}(G_2(q_0))
    #   = G_2(q_0) <= Omega_7, Stab_Out(chi) = 1 -> 2 classes.
    nG2 = len(divisors(r))                       # includes d = r
    # Omega_7 / Sp_6 / Sp_4 / SL_2 subfield copies are psn iff the index r/d
    # is ODD (else the diagonal/spinor coset element becomes a square).
    odd = [d for d in props if (r // d) % 2 == 1]
    nOm = len(odd)                               # Omega_7(q_0): 1 class each
    nSp = len(odd)                               # Sp_6(q_0), Sp_4(q_0)
    nSL = len([d for d in odd if p ** d > 3])    # SL_2(3) is not perfect
    return nG2, nOm, nSp, nSL


# ---------------------------------------------------------------- columns
def pO7(p, r, subfields=True):
    q = p ** r
    nG2, nOm, _, _ = subfield_data(p, r)
    c = {}
    c['Omega7(q)'] = 1
    c['G2 tower'] = 2 * (nG2 if subfields else 1)
    c['Sp6(2)'] = 2
    c['2^3:L3(2)'] = 2
    c['2^3.L3(2)'] = 2
    c['2^6:L3(2)'] = 2
    c['A8'] = 0
    c['L3(2)'] = 0
    c['U3(3)'] = 0
    c['L2(8) Q'] = 0
    c['L2(8) Q(z9)'] = 2 if (z9(q) and p != 3) else 0
    c['L2(13)'] = 2 if (sq13(q) and p != 13) else 0
    c['2^6:A7'] = 1 if nsq2(q) else 0
    c['Omega7 subfields'] = nOm if subfields else 0
    return sum(c.values()), c


def a_of(p, r, subfields=True):
    q = p ** r
    _, _, _, nSL = subfield_data(p, r)
    base = 1 if q > 3 else 0                 # SL_2(3) not perfect
    base += 2 if (sq5(q) and p != 5) else 0
    return base + (nSL if subfields else 0)


def pC4(p, r, subfields=True):
    q = p ** r
    _, _, nSp, _ = subfield_data(p, r)
    c = {}
    c['Sp4(q)'] = 1
    c['2.A5'] = 1 if (nsq3(q) and p != 3) else 0
    c['2.A6'] = 1 if (nsq3(q) and p != 3) else 0
    c['Sym^3'] = 1 if (p >= 5 and q != 5) else 0
    c['Sp4 subfields'] = nSp if subfields else 0
    return sum(c.values()), c


def pC6(p, r, subfields=True):
    q = p ** r
    _, _, nSp, _ = subfield_data(p, r)
    c = {}
    c['Sp6(q)'] = 1
    c['2.A5'] = 1 if (nsq2(q) and p != 5) else 0
    c['SL2(7)'] = 2 if (pm716(q) and p != 7) else 0
    c['U3(3)'] = 1 if (nsq3(q) and p != 3) else 0
    c['2.L2(13)'] = 2 if (sq13(q) and p != 13) else 0
    c['2.J2'] = 2 if (sq5(q) and p != 5) else 0
    c['Sp6 subfields'] = nSp if subfields else 0
    return sum(c.values()), c


def delta(p, r, subfields=True):
    o, _ = pO7(p, r, subfields)
    a = a_of(p, r, subfields)
    c4, _ = pC4(p, r, subfields)
    c6, _ = pC6(p, r, subfields)
    s = c6 + a * c4 + comb(a, 3)
    return o - s, o, s, a, c4, c6


def main():
    # ---- (A) reproduce v_task62 (r = 1 only, no subfields) ----------------
    print("=== (A) r = 1, no subfield columns: reproduce v_task62 ===")
    zeros, vals = [], set()
    for res in range(1, M, 2):
        d, *_ = delta(res, 1, subfields=False)     # 'p' used only mod M here
        vals.add(d)
        if d == 0:
            zeros.append(res)
    print("  Delta values:", sorted(vals))
    print("  zero classes:", len(zeros), " min|Delta| =",
          min(abs(v) for v in vals))

    # ---- (B) r = 1 with subfields (none) ---------------------------------
    # ---- (C) full scan over (p mod M, r) ---------------------------------
    print("\n=== (C) subfield columns REINSTATED: scan r = 1..12 ===")
    print("  (residue = p mod 9360; q = p^r; a residue is admissible for")
    print("   r > 1 only if some prime is congruent to it -- we scan all)")
    hits = {}
    for r in range(1, 13):
        z, mn, seen = [], 99, set()
        for res in range(1, M, 2):
            if res % 3 == 0 or res % 5 == 0 or res % 13 == 0:
                continue                      # not coprime -> handled below
            q = pow(res, r, M)
            # emulate: build a fake p whose residue is res
            d, o, s, a, c4, c6 = delta_res(res, r)
            seen.add(d)
            mn = min(mn, abs(d))
            if d == 0:
                z.append(res)
        hits[r] = (len(z), mn, sorted(seen))
        print(f"  r={r:2d}: zero classes = {len(z):5d}, min|Delta| = {mn}, "
              f"values {sorted(seen)}")
        if z:
            print(f"        first tie residues p = {z[:12]}")

    # ---- (D) defining characteristic p in {3,5,7,13} ---------------------
    print("\n=== (D) defining characteristic, p in {3,5,7,13}, r = 1..12 ===")
    for p in (3, 5, 7, 13):
        for r in range(1, 13):
            d, o, s, a, c4, c6 = delta(p, r)
            flag = "   <== TIE" if d == 0 else ""
            print(f"  q={p}^{r:<2} a={a} pC4={c4} pC6={c6} symp={s:3d} "
                  f"pO7={o:3d} Delta={d:+3d}{flag}")

    # ---- (E) explicit small prime powers ---------------------------------
    print("\n=== (E) explicit q = p^r, p<60, r<=8 ===")
    print(f"{'q':>14} {'p':>4} {'r':>2} {'a':>2} {'pC4':>4} {'pC6':>4} "
          f"{'symp':>5} {'pO7':>4} {'Delta':>6}")
    ties = []
    for p in [x for x in range(3, 200) if all(x % k for k in range(2, x))]:
        for r in range(1, 9):
            if p ** r > 10 ** 14:
                break
            d, o, s, a, c4, c6 = delta(p, r)
            if d == 0:
                ties.append((p, r))
            if p < 60 and r <= 8:
                print(f"{p**r:14d} {p:4d} {r:2d} {a:2d} {c4:4d} {c6:4d} "
                      f"{s:5d} {o:4d} {d:+6d}"
                      + ("   <== TIE" if d == 0 else ""))
    print("\n  TIES among p<200, r<=8:", ties if ties else "NONE")


def delta_res(res, r):
    """Delta for a hypothetical prime p = res (mod M) with q = p^r.
    Congruence predicates need q mod M = res^r mod M; the subfield count
    needs only r and whether p^d > 3 (true for all p >= 5, and for p=3,d>=2).
    We take the conservative/generic case p >= 5."""
    q = pow(res, r, M) or M
    props = [d for d in divisors(r) if d < r]
    nG2 = len(divisors(r))
    odd = [d for d in props if (r // d) % 2 == 1]
    nOm = nSp = nSL = len(odd)
    o = (1 + 2 * nG2 + 2 + 2 + 2 + 2
         + (2 if z9(q) else 0)
         + (2 if sq13(q) else 0)
         + (1 if nsq2(q) else 0)
         + nOm)
    a = 1 + (2 if sq5(q) else 0) + nSL
    c4 = 1 + (2 if nsq3(q) else 0) + 1 + nSp
    c6 = (1 + (1 if nsq2(q) else 0) + (2 if pm716(q) else 0)
          + (1 if nsq3(q) else 0) + (2 if sq13(q) else 0)
          + (2 if sq5(q) else 0) + nSp)
    s = c6 + a * c4 + comb(a, 3)
    return o - s, o, s, a, c4, c6


if __name__ == '__main__':
    main()


# ==========================================================================
# v_task63 STAGE 2: also reinstate the DEFINING-CHARACTERISTIC S-columns
#   Sym^3 SL_2(q_0) < Sp_4(q)   (p>=5, present in v_task62 for q_0 = q only)
#   Sym^5 SL_2(q_0) < Sp_6(q)   (p>=7, MISSING ENTIRELY from v_task62)
#   Sym^6 SL_2(q_0) < Omega_7(q)(p>=7, contributes 0 -- machine-verified)
# each psn iff [F_q : F_{q_0}] is ODD  (multiplier nu^k, k odd, nonsquare).
# ==========================================================================
def delta2(p, r, subfields=True, sym5=True):
    q = p ** r
    props = [d for d in divisors(r) if d < r]
    odd_all = [d for d in divisors(r) if (r // d) % 2 == 1]      # incl. d=r
    odd_pr = [d for d in props if (r // d) % 2 == 1]
    nG2 = len(divisors(r)) if subfields else 1
    nOm = nSp = len(odd_pr) if subfields else 0
    nSL = len([d for d in odd_pr if p ** d > 3]) if subfields else 0

    o = (1 + 2 * nG2 + 8
         + (2 if (z9(q) and p != 3) else 0)
         + (2 if (sq13(q) and p != 13) else 0)
         + (1 if nsq2(q) else 0)
         + nOm)                                   # Sym^6 column = 0
    a = (1 if q > 3 else 0) + (2 if (sq5(q) and p != 5) else 0) + nSL
    nsym3 = len([d for d in (odd_all if subfields else [r])
                 if p >= 5 and p ** d != 5])
    c4 = (1 + (2 if (nsq3(q) and p != 3) else 0) + nsym3 + nSp)
    nsym5 = len([d for d in (odd_all if subfields else [r])
                 if p >= 7]) if sym5 else 0
    c6 = (1 + (1 if (nsq2(q) and p != 5) else 0)
          + (2 if (pm716(q) and p != 7) else 0)
          + (1 if (nsq3(q) and p != 3) else 0)
          + (2 if (sq13(q) and p != 13) else 0)
          + (2 if (sq5(q) and p != 5) else 0)
          + nsym5 + nSp)
    s = c6 + a * c4 + comb(a, 3)
    return o - s, o, s, a, c4, c6


def stage2():
    primes = [x for x in range(3, 4000)
              if all(x % k for k in range(2, int(x ** .5) + 1))]
    print("\n\n=== STAGE 2: Sym^5 column reinstated (p^C6 += 1 for p >= 7) ===")
    for lbl, kw in [("v62 columns + Sym^5 only (no subfields)",
                     dict(subfields=False, sym5=True)),
                    ("v62 columns + subfields only",
                     dict(subfields=True, sym5=False)),
                    ("FULL: subfields + Sym^k",
                     dict(subfields=True, sym5=True))]:
        ties, mn = [], 99
        for p in primes:
            for r in range(1, 13):
                if p ** r > 10 ** 30:
                    break
                d = delta2(p, r, **kw)[0]
                mn = min(mn, abs(d))
                if d == 0:
                    ties.append(p ** r)
        ties.sort()
        print(f"\n  [{lbl}]")
        print(f"    min|Delta| = {mn};  ties: {len(ties)}")
        print("    first 25 tie q:", ties[:25])
    print("\n  --- FULL model, small q table ---")
    print(f"{'q':>10} {'p':>5} {'r':>2} {'a':>2} {'pC4':>4} {'pC6':>4} "
          f"{'symp':>5} {'pO7':>4} {'Delta':>6}")
    for p in primes[:20]:
        for r in range(1, 4):
            if p ** r > 10 ** 7:
                break
            d, o, s, a, c4, c6 = delta2(p, r)
            print(f"{p**r:10d} {p:5d} {r:2d} {a:2d} {c4:4d} {c6:4d} {s:5d} "
                  f"{o:4d} {d:+6d}" + ("   <== TIE" if d == 0 else ""))


stage2()
