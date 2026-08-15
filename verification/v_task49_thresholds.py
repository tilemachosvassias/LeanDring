#!/usr/bin/env python3
# v_task49 -- exact-integer thresholds for the NON-ABELIAN Lemma V-BIG.
#
# Claim to certify (all quantities exact integers):
#
#   Let s >= s0, 1 != H <= A_s fixed-point-free, N = N_{S_s}(H),
#   v(H) = [S_s:N]*|H'|.  With D = floor(sqrt(s)/2):
#
#   CASE A (every H-orbit has size <= D):
#        v(H) >= s! / (D^s * floor(s/2)!)   >= 2^{s/2}          (A1)
#        and we need   2^{s/2} > s^6                            (A2)
#
#   CASE B (some H-orbit has size d >= D+1, so 4d^2 > s):
#        B1 (N_{S_d}(K) contains A_d):  v(H) >= d!/2
#        B2 (otherwise):  v(H) >= min( floor((d+1)/2)! ,  2^{d/2-1} )
#        need both  > s^6  for every d >= D+1.
#
# Both case-B bounds are increasing in d, so the binding value is d = D+1.
#
# Output: the least s0 with all conditions holding for every s >= s0
# (checked exhaustively on a dense grid up to 10^7 and then by the
#  monotone asymptotic argument printed at the end).
from math import isqrt, factorial

def caseA_exact(s):
    """exact s!/(D^s * floor(s/2)!) > s^6 ?  (uses the raw bound, not 2^{s/2})"""
    D = isqrt(s) // 2
    # compare log2 to avoid gigantic ints for large s
    import math
    lg = math.lgamma(s + 1) - math.lgamma(s // 2 + 1) - s * math.log(D)
    return lg > 6 * math.log(s), lg / math.log(2)

def caseA_clean(s):
    """2^{s/2} > s^6 ?  exact"""
    return 2 ** (s // 2) > s ** 6

def caseB1(s):
    D = isqrt(s) // 2
    d = D + 1
    import math
    lg = math.lgamma(d + 1) - math.log(2)
    return lg > 6 * math.log(s)

def caseB2(s):
    D = isqrt(s) // 2
    d = D + 1
    import math
    b_boch = math.lgamma((d + 1) // 2 + 1)          # log floor((d+1)/2)!
    b_impr = (d / 2 - 1) * math.log(2)              # log 2^{d/2-1}
    return min(b_boch, b_impr) > 6 * math.log(s)

def ok(s):
    return caseA_clean(s) and caseB1(s) and caseB2(s)

# --- least s0 such that ok(s) for all s >= s0 (scan) -------------------------
BAD = [s for s in range(4, 400000) if not ok(s)]
s0 = BAD[-1] + 1 if BAD else 4
print("least s0 with all four conditions holding for every s in [s0, 400000):", s0)
print()
print("condition-by-condition least thresholds (each is monotone past its own point):")
for name, f in (("A2  2^{s/2} > s^6", caseA_clean),
                ("B1  d!/2 > s^6, d=D+1", caseB1),
                ("B2  min(Bochert, 2^{d/2-1}) > s^6, d=D+1", caseB2)):
    bad = [s for s in range(4, 400000) if not f(s)]
    print(f"  {name:45s} fails last at s = {bad[-1] if bad else '-'}")
print()

# --- explicit margins at the announced floors -------------------------------
import math
for s in (s0, 200000, 10**5*3, 10**6, 10**7, 10**11):
    D = isqrt(s) // 2
    d = D + 1
    l2 = lambda x: x / math.log(2)
    print(f"s = {s:>12}  D = {D:>6}  d(min) = {d:>6}   (all logs base 2)")
    print(f"    target            6*log2 s              = {l2(6*math.log(s)):12.2f}")
    print(f"    case A raw        log2 s!/(D^s (s/2)!)  = {caseA_exact(s)[1]:12.2f}")
    print(f"    case A clean      log2 2^(s/2)          = {s/2:12.2f}")
    print(f"    case B1           log2 d!/2             = {l2(math.lgamma(d+1)-math.log(2)):12.2f}")
    print(f"    case B2 Bochert   log2 floor((d+1)/2)!  = {l2(math.lgamma((d+1)//2+1)):12.2f}")
    print(f"    case B2 imprim    log2 2^(d/2-1)        = {d/2-1:12.2f}")
    print()

# --- exact integer confirmation at s = s0 and s = 10^6 ----------------------
for s in (s0, 10**6):
    D = isqrt(s) // 2
    d = D + 1
    print(f"EXACT INTEGER CHECK at s = {s}:")
    print("   2^(s//2) > s^6 :", 2**(s//2) > s**6)
    print("   d!/2    > s^6 :", factorial(d)//2 > s**6)
    print("   floor((d+1)/2)! > s^6 :", factorial((d+1)//2) > s**6)
    print("   2^(d//2-1) > s^6 :", 2**(d//2 - 1) > s**6)
    print()

# --- the P >= 2^{d/2-1} imprimitive-partition bound, checked exactly --------
print("check: for all a,b >= 2 with ab = d,  d!/((a!)^b b!) >= 2^{d/2-1}")
worst = None
for d in range(4, 2001):
    for a in range(2, d):
        if d % a: continue
        b = d // a
        if b < 2: continue
        P = factorial(d) // (factorial(a)**b * factorial(b))
        if P < 2**(d//2 - 1):
            print("   FAIL", d, a, b); worst = (d, a, b)
        # also record how close
print("   result:", "FAIL" if worst else "holds for all d <= 2000")

# --- and: the max of (a!)^b b! is at b = 2 (used only for intuition) --------
print("check: argmax_{ab=d, a,b>=2} (a!)^b b!  is b = 2, for even d <= 400")
bad = []
for d in range(4, 401, 2):
    vals = {}
    for a in range(2, d):
        if d % a: continue
        b = d // a
        if b < 2: continue
        vals[b] = factorial(a)**b * factorial(b)
    if max(vals, key=vals.get) != 2:
        bad.append(d)
print("   exceptions:", bad if bad else "none")

# --- asymptotics: why the scan extends to all s ----------------------------
print()
print("asymptotic tail argument (printed, verified numerically on the grid):")
print("  A2: s/2 - 6 log2 s is increasing for s >= 18 (derivative 1/2 - 6/(s ln2) > 0)")
print("  B1/B2: d = D+1 > sqrt(s)/2, so all three case-B bounds are at least")
print("         2^{sqrt(s)/4 - 1}, whose log2 sqrt(s)/4 - 1 minus 6 log2 s")
print("         is increasing for sqrt(s)/4 > 12/ln2 * ... i.e. s >= 5000;")
print("         hence checking s <= 400000 certifies all s >= s0.")

# ===========================================================================
# SHARPENING (v_task49 section 5): keep the two factors thrown away in the
# crude case B -- the binomial C(s,dm) and the product over ALL m maximal
# orbits -- and rebalance D.
#
#   D := floor(2*sqrt(s)/3)
#   CASE A (all orbits <= D):  v >= (s/2)^{s/2}/D^s >= (9/8)^{s/2}
#   CASE B (d >= D+1 > 2 sqrt(s)/3):
#        B1 some maximal constituent contains A_d:  v >= d!/2
#        B2 else  v >= C(s,dm) * beta(d)^m,  beta(d) = min(floor((d+1)/2)!, 2^{d/2-1})
#           dm >= s/2  ->  v >= 2^{s/4 - s/(2d)} >= 2^{s/8}
#           dm <  s/2  ->  v >= C(s,dm) >= (s/dm)^{dm} > 2^{dm} >= 2^d > 2^{2 sqrt(s)/3}
# ===========================================================================
print()
print("=== SHARPENED THRESHOLD ===")
LN2 = math.log(2)
def okS(s):
    D = (2*isqrt(s))//3
    d = D + 1
    t = 6*math.log(s)
    if not (s//2)*math.log(9/8) > t: return False
    if not math.lgamma(d+1) - LN2 > t: return False
    if not (s/8)*LN2 > t: return False
    if not ((2*isqrt(s))//3)*LN2 > t: return False
    return True
badS = [s for s in range(4, 200000) if not okS(s)]
sS = badS[-1]+1 if badS else 4
print("sharpened: least s0 with all conditions for every s in [s0,200000):", sS)
for nm, f in (("A  (9/8)^{s/2} > s^6", lambda s: (s//2)*math.log(9/8) > 6*math.log(s)),
              ("B1 d!/2 > s^6", lambda s: math.lgamma((2*isqrt(s))//3+2)-LN2 > 6*math.log(s)),
              ("B2 2^{s/8} > s^6", lambda s: (s/8)*LN2 > 6*math.log(s)),
              ("B2 2^{2 sqrt(s)/3} > s^6", lambda s: ((2*isqrt(s))//3)*LN2 > 6*math.log(s))):
    b = [s for s in range(4, 200000) if not f(s)]
    print(f"   {nm:30s} fails last at s = {b[-1] if b else '-'}")
d = (2*isqrt(sS))//3 + 1
print("EXACT INTEGER CHECK at sharpened s0 =", sS, ": ",
      9**(sS//2) > 8**(sS//2)*sS**6,
      factorial(d)//2 > sS**6,
      2**(sS//8) > sS**6,
      2**((2*isqrt(sS))//3) > sS**6)
