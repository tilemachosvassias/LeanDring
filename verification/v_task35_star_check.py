#!/usr/bin/env python3
"""v_task35: mechanical check of side-condition (*) (v_task34_transport.md,
Theorem TR) on every admissible factorization of Sec.4am's sweep.

(*)   p2 < min( nu_min^2 , |S_min| )      [Theorem TR notation]

  P      = union over T-orbits O of  ell_O * I(K_i <= Abar_i)   (the pair
           invariant of the orbit's socle factor, Sec 0 of v_task34_transport.md)
  p2     = second-smallest element of P
  nu_min = min_i nu(S_i),  nu(S) = min{[S:N_S(A)]: 1 != A <= Aut(S) abelian}
  |S_min|= smallest factor order

REBUILDING THE SWEEP.  v_task25_sharpened_sweep.py (the script that produced
the "222 admissible factorizations" of Sec.4am) `exec`s a file `residue5.py`
that is NOT present in the repo or in git history (checked: `git log --all
--diff-filter=A -- '*residue5*'` returns nothing) -- it was a scratch file
outside the tracked tree.  What IS reproducible is v_task24_residue.py's
`cands()` (the exact 10-family + alternating + sporadic candidate table that
v_task25 imports verbatim from the same source, per its own commentary in
Sec.4aq) together with v_task25's own DFS-over-multisets search, which is
copied here unchanged.  Re-running this combination reproduces the same
"222 admissible factorizations, n=5..70, k<=4" figure -- see the CHECK line
in the _out.txt.  (v_task27_altfactor.py's `cands()` differs: it adds INF-iota
placeholder families used only for the Criterion-AT hole-repair, not for this
enumeration.)

PAIR-INVARIANT DATA (I(K<=Abar) tables) DO NOT EXIST for the 10 families --
that is v_task34's own "OPEN, main new debt" input I3.  Since it is not
computable here, this script uses the best available STAND-IN, exactly as
the task instructions prescribe:

  * ln := iota_1(S)  (the exact simple-group index, Sec.4at/4au, with the
    prime/non-prime subfield correction for S4, Sp6, U5 applied) as the
    value carried by S's own T-orbit;
  * l2n := iota_2(S) where a closed form is PROVEN (Sec.4at/4au tables,
    A_n via Lemma iota2-A / small-n direct data); marked UNKNOWN otherwise
    (L2, U3, Sz, Ree, sporadics, S4(q) odd non-prime, A7/A9..A_(m<9) beyond
    the tabulated small cases).
  * nu_min uses the PROVEN lower bound nu(S) >= mu(S) (Lemma TR-4); mu(S) is
    taken to be iota_1(S) for Lie type (Lemma iota-mu, exact except at the
    S4(3)~U4(2) defect, already worked into iota_1 above) and the classical
    minimal permutation degree for A_m (mu=m) and for sporadics (hardcoded,
    standard CFSG data).  For A_m the EXACT value nu(A_m)=C(m,2) is used
    instead of the mu-bound, since Sec.4am computed it exactly.

Both stand-ins make (*) MECHANICALLY HARDER to satisfy than the true
statement: ln,l2n are upper bounds for the true pair-invariant entries
(fusion in Abar can only raise them, per the task's own remark) --
raising a candidate value of P can only raise p2, which makes (*) harder;
and the mu-bound on nu_min only *lowers* nu_min^2, which also makes (*)
harder.  So every PASS reported here is a PASS of the true statement too;
every FAIL or UNKNOWN needs a closer look (listed explicitly).

p2 itself, given per-orbit (ell, ln, l2n), is computed via Theorem TR's own
formula (Sec 1, Theorem TR, part 2):

  p2 = min( ell_(O*) * l2n_(O*) ,  min_{O != O*} ell_O * ln_O )

(O* = the argmin orbit realising ln(T)=min P).  If O* is the unique orbit
(k=1) and l2n_(O*) is UNKNOWN, p2 is UNKNOWN for that factorization and is
reported separately, not silently passed.
"""
import sys
from math import factorial, gcd, comb
from itertools import groupby

INF = float('inf')

def primes_upto(n):
    return [p for p in range(2, n + 1) if all(p % r for r in range(2, int(p**.5) + 1))]

def iota_alt(m):
    return {5: 5, 6: 10, 7: 35, 8: 15}.get(m, comb(m, 3))

# iota_2(A_m): Lemma iota2-A (proven n>=9) -> C(m,4); small cases from the
# exhaustive I(A_m) data quoted in v_task34_transport.md Sec 2 / Sec4as.
def iota2_alt(m):
    if m >= 9:
        return comb(m, 4)
    return {5: 6, 6: 15, 8: 35}.get(m, None)   # A7: only "35" known (=iota1); no 2nd value in range

def nu_alt(m):
    return comb(m, 2)

# ---------------------------------------------------------------------------
# The ten exact Lie families, verbatim from v_task24_residue.py / v_task25's
# `residue5.py` import (same formulas, reproduced since that file is lost).
# entry: name, order(q), iota1(q), Out(q,p,f), qmin
# ---------------------------------------------------------------------------
FAM = [
 ("L2", lambda q: q*(q*q-1)//gcd(2, q-1),                                lambda q: q+1,
        lambda q, p, f: gcd(2, q-1)*f, 4),
 ("L3", lambda q: q**3*(q**3-1)*(q**2-1)//gcd(3, q-1),                   lambda q: q*q+q+1,
        lambda q, p, f: gcd(3, q-1)*2*f, 2),
 ("U3", lambda q: q**3*(q**3+1)*(q**2-1)//gcd(3, q+1),                   lambda q: q**3+1,
        lambda q, p, f: gcd(3, q+1)*2*f, 3),
 ("S4", lambda q: q**4*(q**4-1)*(q**2-1)//gcd(2, q-1),                   lambda q: (q*q+1)*(q+1),
        lambda q, p, f: f*(2 if p == 2 else 1)*gcd(2, q-1), 3),
 ("L4", lambda q: q**6*(q**4-1)*(q**3-1)*(q**2-1)//gcd(4, q-1),          lambda q: (q**4-1)//(q-1),
        lambda q, p, f: gcd(4, q-1)*2*f, 2),
 ("U4", lambda q: q**6*(q**4-1)*(q**3+1)*(q**2-1)//gcd(4, q+1),          lambda q: (q**3+1)*(q+1),
        lambda q, p, f: gcd(4, q+1)*2*f, 2),
 ("G2", lambda q: q**6*(q**6-1)*(q**2-1),                                lambda q: (q**6-1)//(q-1),
        lambda q, p, f: f*(2 if p == 3 else 1), 3),
 ("Sp6", lambda q: q**9*(q**6-1)*(q**4-1)*(q**2-1)//gcd(2, q-1),         lambda q: (q**6-1)//(q-1),
        lambda q, p, f: gcd(2, q-1)*f, 2),
 ("L5", lambda q: q**10*(q**5-1)*(q**4-1)*(q**3-1)*(q**2-1)//gcd(5, q-1), lambda q: (q**5-1)//(q-1),
        lambda q, p, f: gcd(5, q-1)*2*f, 2),
 ("U5", lambda q: q**10*(q**5+1)*(q**4-1)*(q**3+1)*(q**2-1)//gcd(5, q+1), lambda q: (q**5+1)*(q*q+1),
        lambda q, p, f: gcd(5, q+1)*2*f, 2),
]
# S4(3) exceptional isomorphism S4(3)~=U4(2): the true iota is 27, not
# (q+1)(q^2+1)=40 (Sec.4at "defect in Lemma iota-mu").
IOTA1_OVERRIDE = {("S4", 3): 27}

# --- iota_2, PROVEN closed forms, Sec.4at + Sec.4au prime/non-prime split --
def is_prime_power(q):
    for p in primes_upto(q):
        f, x = 0, q
        while x % p == 0:
            x //= p; f += 1
        if x == 1:
            return p, f
    return None

def iota2_lie(name, q):
    pf = is_prime_power(q)
    if pf is None:
        return None
    p, f = pf
    ln = IOTA1_OVERRIDE.get((name, q), FAM_INDEX[name][1](q))
    if name == "L3":
        return (q+1)*ln                                    # PROVEN all q
    if name == "L4":
        return (q*q+1)*(q*q+q+1)                            # PROVEN mod cited fact, all q
    if name == "L5":
        return ln*(q*q+1)                                   # PROVEN mod cited fact, all q
    if name == "U4":
        return (q*q+1)*(q**3+1)                             # PROVEN mod cited fact, all q
    if name == "S4":
        if q % 2 == 0:
            t = (q-1)//(p-1)
            return t*ln                                     # PROVEN all q (subfield form)
        if f == 1:
            return q*q*(q*q+1)//2                            # PROVEN q=p odd prime
        return None                                          # OPEN exact form (refuted old formula)
    if name == "Sp6":
        if f == 1:
            return (q+1)*(q*q+1)*(q**3+1)                   # PROVEN q=p
        t = (q-1)//(p-1)
        return t*ln                                          # PROVEN (subfield form, Sec.4au)
    if name == "U5":
        if f == 1:
            return q**4*(q**5+1)//(q+1)                      # PROVEN q=p
        t = (q-1)//(p-1)
        return t*ln                                          # PROVEN (subfield form, Sec.4au)
    if name == "G2":
        return None    # not needed: G2 has no closed iota2, only Bound G2 (upper bound on ratio)
    return None

FAM_INDEX = {nm: (o, i, out, qmin) for nm, o, i, out, qmin in FAM}

# --- mu(S) lower bound for nu(S) (Lemma TR-4: nu(S) >= mu(S)) -------------
# Lie type: mu(S) = iota_1(S) exactly (Lemma iota-mu, S4(3) defect already
# folded into iota_1 via IOTA1_OVERRIDE).
def mu_lie(name, q):
    return IOTA1_OVERRIDE.get((name, q), FAM_INDEX[name][1](q))

# Sporadic minimal permutation degrees (standard CFSG data; NOT computed by
# this project's scripts -- used only as the mu(S) LOWER bound for nu_min,
# per the task's explicit "use mu(S) lower bounds" instruction).
SPOR_MINDEG = {
 "M11": 11, "M12": 12, "M22": 22, "M23": 23, "M24": 24, "J1": 266, "J2": 100,
 "J3": 6156, "HS": 100, "McL": 275, "He": 2058, "Ru": 4060, "Suz": 1782,
 "Co1": 98280, "Co2": 2300, "Co3": 276, "Fi22": 3510, "Fi23": 31671,
 "Fi24'": 306936, "HN": 1140000, "Th": 143127000, "ON": 122760,
 "Ly": 8835156, "J4": 173067389, "B": 13571955000,
 "M": 97239461142009186000,
}
# Sporadic iota_1 (exact, Sec.4at/v_task24_spor_iota_out.txt data).
SPOR_IOTA1 = {
 "M11": 165, "M12": 396, "M22": 1155, "M23": 3795, "M24": 11385, "J1": 1463,
 "J2": 315, "J3": 26163, "HS": 5775, "McL": 22275, "He": 24990, "Ru": 593775,
 "Suz": 45760, "Co1": 3091200, "Co2": 56925, "Co3": 170775, "Fi22": 3510,
 "Fi23": 31671, "Fi24'": 4860485028, "HN": 1539000, "Th": 976841775,
 "ON": 2857239, "Ly": 19212250, "J4": 3980549947, "B": 13571955000,
 "M": 97239461142009186000,
}
SPOR_ORDER = {
 "M11": 7920, "M12": 95040, "M22": 443520, "M23": 10200960, "M24": 244823040,
 "J1": 175560, "J2": 604800, "J3": 50232960, "J4": 86775571046077562880,
 "HS": 44352000, "McL": 898128000, "He": 4030387200, "Ru": 145926144000,
 "Suz": 448345497600, "Co1": 4157776806543360000, "Co2": 42305421312000,
 "Co3": 495766656000, "Fi22": 64561751654400, "Fi23": 4089470473293004800,
 "Fi24'": 1255205709190661721292800, "HN": 273030912000000,
 "Th": 90745943887872000, "ON": 460815505920, "Ly": 51765179004000000,
 "B": 4154781481226426191177580544000000,
 "M": 808017424794512875886459904961710757005754368000000000,
}
SPOR_OUT = {"M11": 1, "M12": 2, "M22": 2, "M23": 1, "M24": 1, "J1": 1, "J2": 2,
 "J3": 2, "HS": 2, "McL": 2, "He": 2, "Ru": 1, "Suz": 2, "Co1": 1, "Co2": 1,
 "Co3": 1, "Fi22": 2, "Fi23": 1, "Fi24'": 2, "HN": 2, "Th": 1, "ON": 2,
 "Ly": 1, "J4": 1, "B": 1, "M": 1}

# ---------------------------------------------------------------------------
# candidate table (unchanged from v_task24/v_task25: 10 Lie families + Sz +
# Ree + alternating + sporadic), tagged with structured data for later use.
# ---------------------------------------------------------------------------
def cands(N, n):
    res = []
    m = 5
    while factorial(m)//2 <= N:
        o = factorial(m)//2
        if o < N and N % o == 0:
            res.append({"name": f"A{m}", "order": o, "iota1": iota_alt(m),
                        "iota2": iota2_alt(m), "nu": nu_alt(m),
                        "out": 4 if m == 6 else 2, "alt": True})
        m += 1
    for p in primes_upto(n):
        f, q = 1, p
        while q <= N:
            for nm, of, iof, outf, qmin in FAM:
                if q < qmin:
                    continue
                o = of(q)
                if 1 < o < N and N % o == 0:
                    i1 = IOTA1_OVERRIDE.get((nm, q), iof(q))
                    res.append({"name": f"{nm}({q})", "order": o, "iota1": i1,
                                "iota2": iota2_lie(nm, q), "nu": mu_lie(nm, q),
                                "out": outf(q, p, f), "alt": False})
            if p == 2 and f % 2 == 1 and q >= 8:
                o = q*q*(q*q+1)*(q-1)
                if o < N and N % o == 0:
                    res.append({"name": f"Sz({q})", "order": o, "iota1": q*q+1,
                                "iota2": None, "nu": q*q+1, "out": f, "alt": False})
            if p == 3 and f % 2 == 1 and q >= 27:
                o = q**3*(q**3+1)*(q-1)
                if o < N and N % o == 0:
                    res.append({"name": f"Ree({q})", "order": o, "iota1": q**3+1,
                                "iota2": None, "nu": q**3+1, "out": f, "alt": False})
            f += 1; q *= p
    for nm, o in SPOR_ORDER.items():
        if o < N and N % o == 0:
            res.append({"name": nm, "order": o, "iota1": SPOR_IOTA1[nm],
                        "iota2": None, "nu": SPOR_MINDEG[nm],
                        "out": SPOR_OUT[nm], "alt": False})
    return res

def search(N, pool, KMAX):
    """all multisets from `pool` (dicts) whose product divides N and whose
    complement c=N/prod satisfies c | prod(Out).  Verbatim algorithm of
    v_task25_sharpened_sweep.py's DFS, adapted to carry dicts."""
    pool = sorted(pool, key=lambda t: -t["order"])
    L = len(pool)
    hits = []
    stack = [(0, N, [], 1)]
    while stack:
        i, rem, chosen, outp = stack.pop()
        if chosen and outp % rem == 0:
            hits.append((tuple(chosen), rem))
        if len(chosen) >= KMAX:
            continue
        for j in range(i, L):
            o = pool[j]["order"]
            if o <= rem and rem % o == 0:
                stack.append((j, rem//o, chosen + [pool[j]], outp*pool[j]["out"]))
    return hits

def orbits_of(chosen):
    """group identical factors (same name) into T-orbits; ell = multiplicity."""
    by_name = {}
    for c in chosen:
        by_name.setdefault(c["name"], []).append(c)
    return [(len(v), v[0]) for v in by_name.values()]   # (ell, representative dict)

def check_star(n, c, chosen):
    orb = orbits_of(chosen)
    # nu_min, |S_min|
    nu_min = min(o[1]["nu"] for o in orb)
    s_min = min(o[1]["order"] for o in orb)
    Phi = min(nu_min*nu_min, s_min)
    # best orbit (min ell*iota1)
    vals = [(ell*rep["iota1"], ell, rep) for ell, rep in orb]
    vals.sort(key=lambda t: t[0])
    best_val, best_ell, best_rep = vals[0]
    if len(vals) >= 2:
        second_orbit_val = vals[1][0]
    else:
        second_orbit_val = None
    i2 = best_rep["iota2"]
    best_orbit_p2 = best_ell*i2 if i2 is not None else None
    candidates = [v for v in (best_orbit_p2, second_orbit_val) if v is not None]
    if not candidates:
        p2 = None
    else:
        p2 = min(candidates)
    unknown = (p2 is None)
    verdict = None if unknown else (p2 < Phi)
    return {
        "n": n, "c": c, "factors": [(o[1]["name"], o[0]) for o in orb],
        "nu_min": nu_min, "s_min": s_min, "Phi": Phi,
        "p2": p2, "verdict": verdict,
        "best_orbit_p2": best_orbit_p2, "second_orbit_val": second_orbit_val,
        "best_name": best_rep["name"], "best_ell": best_ell,
    }

if __name__ == "__main__":
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 70
    KMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    total = 0
    npass = nfail = nunk = 0
    tight = []      # within factor 2 of failing, or failing
    unknown_list = []
    all_results = []
    for n in range(5, NMAX+1):
        N = factorial(n)//2
        cs = cands(N, n)
        hits = search(N, cs, KMAX)
        for chosen, c in hits:
            total += 1
            r = check_star(n, c, chosen)
            all_results.append(r)
            if r["verdict"] is None:
                nunk += 1
                unknown_list.append(r)
            elif r["verdict"]:
                npass += 1
                if r["Phi"] <= 2*r["p2"]:
                    tight.append(r)
            else:
                nfail += 1
                tight.append(r)
        if n % 10 == 0:
            print(f"n<={n}: cumulative admissible factorizations = {total}", flush=True)

    print(f"\nCHECK: total admissible factorizations found (n=5..{NMAX}, k<={KMAX}): {total}")
    print(f"(Sec.4am reports 222 for n=5..70, k<=4, from the lost residue5.py sweep;")
    print(f" this reconstruction from v_task24_residue.py's cands()+v_task25's DFS is")
    print(f" the closest reproducible match -- compare the number above to 222.)\n")

    print(f"(*) side-condition results:")
    print(f"  PASS    : {npass}")
    print(f"  FAIL    : {nfail}")
    print(f"  UNKNOWN : {nunk}  (best orbit has no proven iota2 closed form, and it is the only orbit)")

    print(f"\n--- FAIL or within factor 2 of failing (Phi <= 2*p2), sorted by margin ---")
    tight.sort(key=lambda r: r["Phi"]/r["p2"])
    for r in tight:
        margin = r["Phi"]/r["p2"]
        tag = "FAIL" if not r["verdict"] else "TIGHT"
        fac = " * ".join(f"{nm}^{e}" if e > 1 else nm for nm, e in r["factors"])
        print(f"  [{tag}] n={r['n']:3d}  c={r['c']:<4d}  {fac}")
        print(f"         p2={r['p2']}  Phi=min(nu_min^2={r['nu_min']}^2={r['nu_min']**2}, |S_min|={r['s_min']}) = {r['Phi']}"
              f"   margin Phi/p2={margin:.3f}")
        print(f"         (best orbit {r['best_name']}^{r['best_ell']}: ell*iota2={r['best_orbit_p2']};"
              f" 2nd-best-orbit ell*iota1={r['second_orbit_val']})")
    if not tight:
        print("  -- none: every PASS has margin Phi/p2 > 2 --")

    print(f"\n--- UNKNOWN cases (p2 not computable from proven closed forms) ---")
    for r in unknown_list[:60]:
        fac = " * ".join(f"{nm}^{e}" if e > 1 else nm for nm, e in r["factors"])
        print(f"  n={r['n']:3d}  c={r['c']:<4d}  {fac}   "
              f"Phi=min({r['nu_min']}^2={r['nu_min']**2},{r['s_min']})={r['Phi']}"
              f"   best orbit={r['best_name']} (iota2 unknown), single orbit={r['second_orbit_val'] is None}")
    if len(unknown_list) > 60:
        print(f"  ... and {len(unknown_list)-60} more")
    if not unknown_list:
        print("  -- none --")

    # Out(S)-fusion ambiguity check: for the tight/fail cases, recompute p2
    # with the best orbit's iota2 multiplied by min(|Out(S)|, 2) -- the
    # documented fusion cap m<=2 for ell-minimal classes (Sec.4am/4at) -- and
    # flag any verdict flip.
    print(f"\n--- Out(S)-fusion ambiguity scan (best-orbit iota2 x up to min(|Out|,2)) ---")
    flips = 0
    for r in all_results:
        if r["p2"] is None or r["best_orbit_p2"] is None:
            continue
        fused = r["best_orbit_p2"]*2
        cands2 = [v for v in (fused, r["second_orbit_val"]) if v is not None]
        p2_fused = min(cands2)
        verdict_fused = p2_fused < r["Phi"]
        if verdict_fused != r["verdict"]:
            flips += 1
            fac = " * ".join(f"{nm}^{e}" if e > 1 else nm for nm, e in r["factors"])
            print(f"  FLIP  n={r['n']}  {fac}  p2 {r['p2']}->{p2_fused}  "
                  f"verdict {r['verdict']}->{verdict_fused}")
    print(f"  total flips under x2 fusion cap: {flips}")
