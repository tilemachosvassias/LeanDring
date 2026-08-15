#!/usr/bin/env python3
"""v_task40: mechanical check of side-condition (*3) (v_task37_two_orbit.md
line 175-176, needed for Theorem TO's trichotomy per v_task38 P6) on every
admissible factorization of Sec.4am's sweep -- the same 222 factorizations
v_task35_star_check.py swept for (*).

(*3)  p4 < Phi      [v_task37_two_orbit.md:175-176, v_task38 (H3)/finding P6]

  "the extension of (*) to the third and fourth values (p4 < Phi)" -- i.e.
  p4 is the 4TH-smallest element of P (not the 3rd; the name "(*3)" is a
  label, not an index -- confirmed by grep: v_task37:175-176 spells out
  "p4 < Phi" explicitly, and v_task38:201-215/475 states Theorem TO needs
  the "three (four) smallest" values of I(T) identified with P, i.e. up to
  the 4th).  P, Phi, nu_min are exactly as in v_task34_transport.md /
  v_task35_star_check.py; see that script's docstring for their definitions
  and the (*) case (p2 < Phi).

RECONSTRUCTING THE 222 FACTORIZATIONS.  Identical to v_task35: residue5.py
(the original sweep script) is lost; this file copies v_task35's cands()/
search()/orbits_of() machinery verbatim (same source: v_task24_residue.py's
candidate table + v_task25_sharpened_sweep.py's DFS) to reproduce the same
"222 admissible factorizations, n=5..70, k<=4" figure.  See v_task35's
CHECK line for the same caveat.

EXTRA DATA NEEDED BEYOND v_task35: the 3rd/4th pair-invariant values
ι3, ι4 per orbit.

  * For alternating factors A_m (Lemma ι3-A, v_task37_two_orbit.md Sec.1,
    lines 57-130), PROVEN for m >= 10:
        iota3(A_m) = 3*C(m,4)   iota4(A_m) = 4*C(m,4)
    m = 9 is an explicit exception: iota3(A_9) = 135 (v_task37:67,98,381);
    iota4(A_9) is NOT proven (no closed form quoted) -- treated as UNKNOWN.
    m = 5,6,7,8: no iota3/iota4 closed form or tabulated value exists in
    this project's record (v_task35's iota2_alt only tabulates iota2 for
    m=5,6,8, and does not go further) -- treated as UNKNOWN for all of
    m in {5,6,7,8}.
  * For every non-alternating family (the 10 Lie families, Sz, Ree, the
    sporadics), NO proven iota3/iota4 closed form exists anywhere in this
    project (only iota1 always, iota2 sometimes -- v_task35's iota2_lie).
    So these orbits contribute only iota1 (and iota2 where known) as KNOWN
    candidate values to P; their iota3/iota4 are UNKNOWN.

CONSERVATIVE p4 CONVENTION (mirrors v_task35's honest-UNKNOWN discipline
for p2).  Build the multiset of ALL KNOWN candidate values in P:
  for each orbit O=(ell,rep):  ell*iota1  (always known)
                                ell*iota2  (if rep's iota2 is proven)
                                ell*iota3, ell*iota4  (only for A_m, per above)
If this KNOWN multiset has >= 4 elements, let p4_upper = its 4th-smallest.
This is a legitimate (mechanically hardest-to-satisfy) UPPER bound for the
true p4 PROVIDED no orbit could smuggle in an undiscovered value smaller
than p4_upper: since fusion in Abar can only raise a true pair-invariant
value above its stand-in (v_task35's own observation), any UNKNOWN slot in
orbit O is only guaranteed to be >= ell*iota1(O) (its 1st, always-known,
value; an unknown iota2/iota3/iota4 of that orbit is provably >= its own
iota1 slot, since pair-invariant spectra are increasing by definition).  So
we check: for every orbit O whose KNOWN candidates were NOT all already
used among the 4 chosen smallest, and whose ell*iota1(O) < p4_upper, does O
have an unknown iota2/iota3/iota4 that could still be < p4_upper?  If yes,
p4 is UNKNOWN for that factorization (an undiscovered value could displace
the 4th-smallest known value downward, making (*3) look like it fails, or
could be small enough itself to need inclusion -- either way we cannot
certify p4_upper as valid).  If no such orbit exists, p4_upper is a valid
conservative p4: PASS (p4_upper < Phi) is a genuine PASS of the true
statement (raising a candidate can only raise p4, so a passing upper bound
means p4_true <= p4_upper < Phi, wait -- p4 is a specific rank statistic,
not monotone in an unbounded way under a single value increasing; see the
implementation note in check_star3() for the precise argument actually
used, which follows v_task35's p2 argument by orbit-count induction).

Concretely, exactly as v_task35 did for p2: an UNKNOWN candidate slot in
orbit O can only be *replaced by nothing smaller than* ell*iota1(O) (the
true pair-invariant spectrum is non-decreasing, so any later term is >=
the first).  So when deciding p4, we only need to worry about orbits O
whose ell*iota1(O) is small enough to still be "in contention" for a top-4
spot once its own definitely-known contributions are accounted for.  The
per-factorization logic in check_star3() below makes this precise.
"""
import sys
from math import factorial, comb

# ---------------------------------------------------------------------------
# Verbatim reuse of v_task35_star_check.py's reconstruction machinery.
# ---------------------------------------------------------------------------
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from v_task35_star_check import (
    cands, search, orbits_of, iota_alt, iota2_alt, nu_alt,
    iota2_lie, mu_lie, FAM_INDEX, IOTA1_OVERRIDE, SPOR_IOTA1, SPOR_MINDEG,
    SPOR_ORDER, SPOR_OUT,
)

# --- iota3, iota4 for A_m: Lemma iota3-A (v_task37_two_orbit.md Sec.1) ----
def iota3_alt(m):
    if m >= 10:
        return 3*comb(m, 4)
    if m == 9:
        return 135
    return None   # m=5..8: UNKNOWN (untabulated)

def iota4_alt(m):
    if m >= 10:
        return 4*comb(m, 4)
    return None   # m=9: not proven (no closed form quoted); m=5..8: UNKNOWN


def orbit_known_values(ell, rep):
    """All KNOWN candidate values ell*iota_k contributed by this orbit,
    in increasing order, per the data availability documented above."""
    vals = [ell*rep["iota1"]]
    i2 = rep["iota2"]
    if i2 is not None:
        vals.append(ell*i2)
    if rep.get("alt"):
        m = int(rep["name"][1:])
        i3 = iota3_alt(m)
        if i3 is not None:
            vals.append(ell*i3)
        i4 = iota4_alt(m)
        if i4 is not None:
            vals.append(ell*i4)
    return vals


def check_star3(n, c, chosen):
    orb = orbits_of(chosen)
    nu_min = min(o[1]["nu"] for o in orb)
    s_min = min(o[1]["order"] for o in orb)
    Phi = min(nu_min*nu_min, s_min)

    per_orbit = [(ell, rep, orbit_known_values(ell, rep)) for ell, rep in orb]

    # all known candidate values, tagged with owning orbit index
    known = []
    for idx, (ell, rep, vals) in enumerate(per_orbit):
        for v in vals:
            known.append((v, idx))
    known.sort(key=lambda t: t[0])

    if len(known) < 4:
        return {"n": n, "c": c, "factors": [(o[1]["name"], o[0]) for o in orb],
                "nu_min": nu_min, "s_min": s_min, "Phi": Phi,
                "p4": None, "verdict": None, "reason": "fewer than 4 known candidate values"}

    p4_upper = known[3][0]

    # soundness check: any orbit NOT fully accounted among the top 4, with
    # ell*iota1 < p4_upper, and an UNKNOWN higher slot -> could smuggle in
    # an undiscovered value < p4_upper -> mark whole thing UNKNOWN.
    unsound = False
    for idx, (ell, rep, vals) in enumerate(per_orbit):
        base = ell*rep["iota1"]
        if base >= p4_upper:
            continue
        # does this orbit have an unknown deeper slot that could be
        # smaller than p4_upper?  It has one iff its known-value count is
        # smaller than what a fully-charted spectrum would offer, i.e. if
        # any of iota2/iota3/iota4 is None for this orbit's family.
        i2 = rep["iota2"]
        has_unknown = i2 is None
        if not has_unknown and rep.get("alt"):
            m = int(rep["name"][1:])
            has_unknown = (iota3_alt(m) is None) or (iota4_alt(m) is None)
        elif not has_unknown and not rep.get("alt"):
            has_unknown = True   # non-alt families never have proven iota3/iota4
        if has_unknown:
            unsound = True
            break

    if unsound:
        return {"n": n, "c": c, "factors": [(o[1]["name"], o[0]) for o in orb],
                "nu_min": nu_min, "s_min": s_min, "Phi": Phi,
                "p4": None, "verdict": None,
                "reason": "an orbit with ell*iota1 < p4_upper has an unproven deeper slot"}

    verdict = p4_upper < Phi
    return {"n": n, "c": c, "factors": [(o[1]["name"], o[0]) for o in orb],
            "nu_min": nu_min, "s_min": s_min, "Phi": Phi,
            "p4": p4_upper, "verdict": verdict, "reason": None,
            "known_top4": [v for v, _ in known[:4]]}


if __name__ == "__main__":
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 70
    KMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    total = 0
    npass = nfail = nunk = 0
    fails = []
    unknown_list = []
    all_results = []
    for n in range(5, NMAX+1):
        N = factorial(n)//2
        cs = cands(N, n)
        hits = search(N, cs, KMAX)
        for chosen, c in hits:
            total += 1
            r = check_star3(n, c, chosen)
            all_results.append(r)
            if r["verdict"] is None:
                nunk += 1
                unknown_list.append(r)
            elif r["verdict"]:
                npass += 1
            else:
                nfail += 1
                fails.append(r)
        if n % 10 == 0:
            print(f"n<={n}: cumulative admissible factorizations = {total}", flush=True)

    print(f"\nCHECK: total admissible factorizations found (n=5..{NMAX}, k<={KMAX}): {total}")
    print(f"(v_task35 reproduces 222 for n=5..70, k<=4 from the same reconstruction; "
          f"compare the number above to 222.)\n")

    print(f"(*3) side-condition results (p4 < Phi):")
    print(f"  PASS    : {npass}")
    print(f"  FAIL    : {nfail}")
    print(f"  UNKNOWN : {nunk}")

    print(f"\n--- FAIL cases (p4_upper < Phi is FALSE, i.e. p4_upper >= Phi), full list ---")
    fails.sort(key=lambda r: r["n"])
    for r in fails:
        fac = " * ".join(f"{nm}^{e}" if e > 1 else nm for nm, e in r["factors"])
        print(f"  [FAIL] n={r['n']:3d}  c={r['c']:<4d}  {fac}")
        print(f"         p4={r['p4']}  Phi=min(nu_min^2={r['nu_min']}^2={r['nu_min']**2}, "
              f"|S_min|={r['s_min']}) = {r['Phi']}   known top4={r['known_top4']}")
    if not fails:
        print("  -- none --")

    print(f"\n--- UNKNOWN cases (p4 not certifiable from proven closed forms) ---")
    for r in unknown_list[:80]:
        fac = " * ".join(f"{nm}^{e}" if e > 1 else nm for nm, e in r["factors"])
        print(f"  n={r['n']:3d}  c={r['c']:<4d}  {fac}   reason: {r['reason']}")
    if len(unknown_list) > 80:
        print(f"  ... and {len(unknown_list)-80} more")
    if not unknown_list:
        print("  -- none --")

    # ------------------------------------------------------------------
    # Failure-shape classification: same shape v_task35 found for (*) --
    # "large A_{n-k} paired with small L2(q)"?
    # ------------------------------------------------------------------
    print(f"\n--- Failure shape classification ---")
    for r in fails:
        names = [nm for nm, e in r["factors"]]
        has_big_alt = any(nm.startswith("A") and nm[1:].isdigit() and int(nm[1:]) >= r["n"] - 4
                           for nm in names)
        has_small_l2 = any(nm.startswith("L2(") for nm in names)
        shape = "large A_{n-k} x small L2(q)" if (has_big_alt and has_small_l2) else "OTHER"
        fac = " * ".join(f"{nm}^{e}" if e > 1 else nm for nm, e in r["factors"])
        print(f"  n={r['n']:3d}  {fac:<30s}  shape: {shape}")

    # ------------------------------------------------------------------
    # TO-0-style rescue check: for every (*3) FAIL, is it already killed
    # by Theorem kappa-A / Theorem TO Step 0 (contains an A_m factor with
    # m <= n-2, i.e. the "large A_{n-k}" already excludes case (b) outright
    # -- (*3) failing there is MOOT), or does min P < C(n,3) by orders of
    # magnitude (the same unconditional Lemma TO-0 argument that rescued
    # the 29 (*) failures for SEPARATION, even if not for the trichotomy)?
    # ------------------------------------------------------------------
    print(f"\n--- TO-0 rescue check for (*3) FAIL cases: min P vs C(n,3) ---")
    for r in fails:
        n = r["n"]
        Cn3 = comb(n, 3)
        # min P = ell*iota1 of the best orbit = the smallest known top-4 value
        min_P = r["known_top4"][0]
        names = [nm for nm, e in r["factors"]]
        step0_dead = any(nm.startswith("A") and nm[1:].isdigit() and int(nm[1:]) <= n - 2
                          for nm in names)
        fac = " * ".join(f"{nm}^{e}" if e > 1 else nm for nm, e in r["factors"])
        margin = Cn3/min_P if min_P else float('inf')
        verdict_txt = "Step-0 MOOT (contains A_m, m<=n-2)" if step0_dead else \
                      ("TO-0 rescued: min P << C(n,3)" if min_P < Cn3 else "min P >= C(n,3): genuinely open")
        print(f"  n={n:3d}  {fac:<30s}  min_P={min_P:<12d}  C(n,3)={Cn3:<14d}  "
              f"margin C(n,3)/minP={margin:10.2f}   -> {verdict_txt}")
    if not fails:
        print("  -- none (no (*3) FAIL cases to check) --")
