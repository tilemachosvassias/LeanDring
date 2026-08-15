#!/usr/bin/env python3
# v_task84 -- adversarial re-derivation of v_task49's numeric thresholds.
# Every comparison is done in EXACT integer arithmetic (no logs, no floats)
# by clearing halves:  2^{s/2} > s^6   <=>   2^s > s^12,  etc.
from math import isqrt, comb, factorial
import sys

def D_crude(s):   return isqrt(s)//2          # floor(sqrt(s)/2)
def D_sharp(s):   return (2*isqrt(s*1))//3 if False else isqrt(4*s)//3

# floor(2 sqrt(s)/3):  2 sqrt(s) = sqrt(4s)  so floor(sqrt(4s)/3) is NOT the same
# as floor(2 sqrt(s)/3) in general -- do it exactly:
def floor_2sqrt_over_3(s):
    # largest k with 3k <= 2 sqrt(s)  <=>  9k^2 <= 4s
    k = isqrt(4*s)//3
    while 9*(k+1)**2 <= 4*s: k += 1
    while 9*k*k > 4*s: k -= 1
    return k

def floor_sqrt_over_2(s):
    k = isqrt(s)//2
    while 4*(k+1)**2 <= s: k += 1
    while 4*k*k > s: k -= 1
    return k

print("="*78); print("PART 1 -- the crude split, D = floor(sqrt(s)/2), d = D+1"); print("="*78)

# sanity on the floor functions
for s in [4,5,8,9,15,16,17,24,25,178083,178084,15875,15876]:
    import math
    assert floor_sqrt_over_2(s) == math.floor(math.sqrt(s)/2), s
    assert floor_2sqrt_over_3(s) == math.floor(2*math.sqrt(s)/3), s
print("floor helpers agree with float reference on spot values: OK")

def caseA_ok(s):        # 2^{s/2} > s^6   <=>  2^s > s^12
    return 2**s > s**12
def B1_ok(s):
    d = floor_sqrt_over_2(s)+1
    return factorial(d)//2 > s**6 if factorial(d) % 2 == 0 else factorial(d) > 2*s**6
def B2_ok(s):
    d = floor_sqrt_over_2(s)+1
    # min( floor((d+1)/2)! , 2^{d/2-1} ) > s^6 ; clear halves: 2^{d-2} > s^12
    a = factorial((d+1)//2)
    return (a > s**6) and (2**(d-2) > s**12)
def B2_parts(s):
    d = floor_sqrt_over_2(s)+1
    return (factorial((d+1)//2) > s**6, 2**(d-2) > s**12)

lastA = lastB1 = lastB2 = None
for s in range(4, 400001):
    if not caseA_ok(s): lastA = s
    if not B1_ok(s):    lastB1 = s
    if not B2_ok(s):    lastB2 = s
print("last s (<400000) at which  2^{s/2} > s^6   FAILS  :", lastA,  " (v_task49 says 75)")
print("last s (<400000) at which  d!/2   > s^6    FAILS  :", lastB1, " (v_task49 says 1763)")
print("last s (<400000) at which  B2 min > s^6    FAILS  :", lastB2, " (v_task49 says 178083)")
s0 = max(lastA, lastB1, lastB2)+1
print("=> crude s0 =", s0, "  (v_task49 says 178084)")
print("which of the two B2 branches binds at s = %d: primitive-ok=%s imprimitive-ok=%s"
      % (s0, *B2_parts(s0)))
print("at s = s0-1 = %d: primitive-ok=%s imprimitive-ok=%s" % (s0-1, *B2_parts(s0-1)))
d0 = floor_sqrt_over_2(s0)+1
print("at s0: D =", floor_sqrt_over_2(s0), " d =", d0,
      " 2^{d/2-1} =", 2**((d0-2)//2) if (d0-2)%2==0 else "half-int",
      " s0^6 =", s0**6)
print("Bochert branch value floor((d+1)/2)! at s0 has", len(str(factorial((d0+1)//2))), "digits;",
      "imprimitive 2^{d/2-1} has", len(str(2**((d0-2)//2))), "digits")
print("=> the PRIMITIVE (Bochert) branch is never the binding one for d >= 7:")
for d in range(5, 40):
    prim = factorial((d+1)//2); imp2 = 2**(d-2)          # =(2^{d/2-1})^2
    print("   d=%2d  floor((d+1)/2)! = %-12d  2^{d/2-1}^2 = %-12d  min is %s"
          % (d, prim, imp2, "imprimitive" if imp2 < prim**2 else "PRIMITIVE"))
    if d > 12: break

print()
print("="*78); print("PART 2 -- the sharpened split, D = floor(2 sqrt(s)/3)"); print("="*78)
def sA_ok(s):    # (9/8)^{s/2} > s^6  <=>  9^s > 8^s * s^12
    return 9**s > 8**s * s**12
def sB1_ok(s):
    d = floor_2sqrt_over_3(s)+1
    return factorial(d) > 2*s**6
def sB2a_ok(s):  # 2^{s/8} > s^6  <=> 2^s > s^48
    return 2**s > s**48
def sB2b_ok(s):  # 2^{floor(2 sqrt s/3)} > s^6
    return 2**floor_2sqrt_over_3(s) > s**6
lasts = [None]*4
for s in range(4, 20001):
    if not sA_ok(s):   lasts[0] = s
    if not sB1_ok(s):  lasts[1] = s
    if not sB2a_ok(s): lasts[2] = s
    if not sB2b_ok(s): lasts[3] = s
print("last failures: (9/8)^{s/2}>s^6 :", lasts[0], "(claim 661)")
print("               d!/2>s^6        :", lasts[1], "(claim 840)")
print("               2^{s/8}>s^6     :", lasts[2], "(claim 417)")
print("               2^{D}>s^6       :", lasts[3], "(claim 15875)")
print("=> sharpened s0 =", max(x for x in lasts if x)+1, " (claim 15876)")

print()
print("="*78); print("PART 3 -- the elementary inequalities behind case A"); print("="*78)
# s!/(D^s * floor(s/2)!) >= 2^{s/2}, exactly, for the crude D
bad = []
for s in range(4, 3001):
    D = floor_sqrt_over_2(s)
    if D < 2: continue
    lhs2 = factorial(s)**2                      # square both sides to clear 2^{s/2}
    rhs2 = (D**s * factorial(s//2))**2 * 2**s
    if lhs2 < rhs2: bad.append(s)
print("s!/(D^s*floor(s/2)!) >= 2^{s/2} exact-check for 4<=s<=3000, failures:", bad)
# and the sharpened form  s!/(D'^s floor(s/2)!) >= (9/8)^{s/2}
bad = []
for s in range(4, 3001):
    D = floor_2sqrt_over_3(s)
    if D < 2: continue
    if factorial(s)**2 * 8**s < (D**s*factorial(s//2))**2 * 9**s: bad.append(s)
print("s!/(D'^s*floor(s/2)!) >= (9/8)^{s/2} exact-check for 4<=s<=3000, failures:", bad)

print()
print("="*78); print("PART 4 -- the imprimitive partition bound"); print("="*78)
worst = None; bad = []
for d in range(4, 2001):
    for a in range(2, d):
        if d % a: continue
        b = d//a
        if b < 2: continue
        P = factorial(d)//(factorial(a)**b * factorial(b))
        # P >= 2^{d/2-1}  <=> P^2 >= 2^{d-2}
        if P*P < 2**(d-2): bad.append((d,a,b))
        # also check the intermediate claim P >= 2^{(a-1)(b-1)}
        if P < 2**((a-1)*(b-1)): bad.append(("mid",d,a,b))
        # and (a-1)(b-1) >= d/2 - 1  <=>  2(a-1)(b-1) >= d-2
        if 2*(a-1)*(b-1) < d-2: bad.append(("exp",d,a,b))
print("d!/((a!)^b b!) >= 2^{d/2-1}, >= 2^{(a-1)(b-1)}, and (a-1)(b-1) >= d/2-1")
print("   checked for all d <= 2000 and all factorisations: failures =", bad)
# the per-factor step C(2a-1,a-1) >= 2^{a-1}
bad = [a for a in range(2, 500) if comb(2*a-1, a-1) < 2**(a-1)]
print("C(2a-1,a-1) >= 2^{a-1} for 2<=a<500: failures =", bad)

print()
print("="*78); print("PART 5 -- monotonicity beyond the scanned range"); print("="*78)
# crude: need  d/2-1 > 6 log2 s  with d = floor(sqrt(s)/2)+1, i.e. sqrt(s)/4 - 1 > 6 log2 s
import math
def gcrude(s): return math.sqrt(s)/4 - 1 - 6*math.log2(s)
print("g(s)=sqrt(s)/4-1-6log2(s):  g(178084)=%.3f  g(4e5)=%.3f  g(1e6)=%.3f  g(1e12)=%.3f"
      % (gcrude(178084), gcrude(4e5), gcrude(1e6), gcrude(1e12)))
print("g'(s)=1/(8 sqrt s)-6/(s ln2) > 0  <=>  sqrt(s) > 48/ln2 = %.2f, i.e. s > %.0f"
      % (48/math.log(2), (48/math.log(2))**2))
print("   (v_task49 states the crossover as sqrt(s) > 69.3, i.e. s > 4800 -- checked:",
      abs(48/math.log(2) - 69.25) < 0.1, ")")
print("h(s)=s/2-6log2(s): increasing for s>=18? h'(s)=1/2-6/(s ln2)>0 <=> s>17.3 :",
      0.5 - 6/(18*math.log(2)) > 0)
# sharpened: 2^{floor(2 sqrt s/3)} > s^6 needs 2 sqrt(s)/3 - 1 > 6 log2 s
def gsharp(s): return 2*math.sqrt(s)/3 - 1 - 6*math.log2(s)
print("sharp g(15876)=%.3f  g(2e4)=%.3f  g(1e12)=%.3f ; g' > 0 <=> sqrt(s) > %.2f"
      % (gsharp(15876), gsharp(2e4), gsharp(1e12), 3*6/(math.log(2))/1*1/ (2/3) /6 ))
print("   sharp derivative: 1/(3 sqrt s) - 6/(s ln2) > 0 <=> sqrt(s) > 18/ln2 = %.2f (s > %.0f)"
      % (18/math.log(2), (18/math.log(2))**2))

print()
print("="*78); print("PART 6 -- Corollary GAP-FREE arithmetic"); print("="*78)
print("C(n,6) > 6 C(n,5)  <=>  n-5 > 36  <=>  n > 41 :",
      all(comb(n,6) > 6*comb(n,5) for n in range(42, 300)),
      " and fails at n=41:", comb(41,6) > 6*comb(41,5))
print("6C(n,5) < s^6/2 for n <= s+5, s >= 4 :",
      all(6*comb(s+5,5) < s**6/2 for s in range(4, 2000)))
print("s0+5 =", 178084+5, " (v_task49's n0 = 178089); sharpened n0 =", 15876+5)
