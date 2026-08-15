import sys, time
exec(open("residue5.py").read().split("NMAX = 300")[0])
from math import factorial, comb
NMAX = int(sys.argv[1]); KMAX = int(sys.argv[2])
fails = []; totfac = 0; t0 = time.time()
for n in range(5, NMAX+1):
    N = factorial(n)//2
    K = comb(n,3) if n >= 9 else iota_alt(n)
    cs = sorted(cands(N, n), key=lambda t: -t[1])
    L = len(cs)
    stack = [(0, N, [], 1)]
    while stack:
        i, rem, chosen, outp = stack.pop()
        if chosen and outp % rem == 0:
            totfac += 1
            mn = min(x[2] for x in chosen)
            if rem * mn >= K:
                fails.append((n, " * ".join(x[0] for x in chosen), rem, mn, K))
        if len(chosen) >= KMAX: continue
        for j in range(i, L):
            o = cs[j][1]
            if o <= rem and rem % o == 0:
                stack.append((j, rem//o, chosen+[cs[j]], outp*cs[j][3]))
    if n % 10 == 0:
        print(f"  n={n}: cands={L} cumulative_factorizations={totfac} uncovered={len(fails)}  [{time.time()-t0:.0f}s]", flush=True)
print(f"\nk<={KMAX}, n=5..{NMAX}: admissible factorizations examined = {totfac}")
print(f"factorizations NOT covered by  c*min_iota_ub < C(n,3):  {len(fails)}")
for t in fails[:30]: print("   n=%d  %s  c=%d  min_iota_ub=%d  C(n,3)=%d" % t)
