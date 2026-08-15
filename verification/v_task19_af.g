#!/usr/bin/env gap -q
# v_task19: Theorem AF (per-n), NOTES.md Even/NOTES.md sec 4u.
#
# TARGET AF: for n >= 5, every Fitting-free group of order n!/2 is simple.
# This script settles the per-n arithmetic half of AF (NOTES sec 4u,
# "Per-n decision procedure") for n = 9..40: does N := n!/2 admit a
# factorization N = |S1|*...*|Sk|*c (k<=3, each Si nonabelian simple,
# c a plausible Out-part), EXCLUDING the trivial k=1, S1=A_n (order N),
# c=1 case?  A NO_FACTORIZATION verdict for a given n, combined with the
# sec 4l/4t simple-vs-simple rigidity closure, extends full D-rigidity to
# that A_n unconditionally (SR1-style, sec 4l).
#
# ENGINE: this is v_task18_bm.g's exact, N-specific valuation-bounded
# candidate generator (GenerateCandidatesForN / BuildOrderTable /
# CheckSR1), COPIED VERBATIM below (self-contained, same house style as
# v_task18's own copy from v_task15), with two adaptations:
#
#  (A) SYMMETRY-GENEROUS c-bound.  v_task18's CDiv used c | (Out1*Out2*...)
#      only.  When repeated isomorphic factors occur (Si = Sj as a chosen
#      order value), the permutation part of Aut(socle) also contributes a
#      k!-style wreath factor (Out(S x S) = Out(S) wr C2 has an EXTRA
#      factor 2 beyond Out(S)^2, from swapping the two copies).  Per the
#      task brief ("allow c | ... times the permutation part when
#      isomorphic factors repeat -- allow generously"), CDiv is replaced by
#      AllowedC(c, outProd, symFactor), symFactor = (multiplicities)! for
#      the chosen order-tuple (1 if all k factors have distinct orders, 2
#      if exactly two coincide, k! if all k coincide).  This makes the
#      admitted-c test MORE permissive than v_task18's, biasing against a
#      false NO_FACTORIZATION verdict -- i.e. any FACTORIZATION_EXISTS
#      hit under the tighter v_task18 rule is still a hit here, and this
#      run additionally catches repeated-factor cases v_task18 would have
#      missed.
#
#  (B) FIELD-AUTOMORPHISM EDGE CASE (NOTES sec 4u (iii)).  The forced-
#      prime argument "every prime p in (n/2,n] divides Pi|Si|*Pi|Out(Si)|"
#      has a gap: a forced prime P can enter through the FIELD-AUTOMORPHISM
#      part of Out, not the socle itself -- Out(L2(2^P)) = C_P when P is
#      itself the field-extension degree.  GenerateCandidatesForN's main
#      loop does NOT produce this (it only varies f up to v_p(N)/E for
#      BASE prime p); a dedicated FieldAutomorphismCheck function is added
#      that, for each forced prime P, tries L2(r^P) for every prime r | N,
#      r <> P, subject to the necessary valuation budget f=P <= v_r(N),
#      and exact-divides-tests the resulting order against N.  Per sec 4u,
#      this is expected to fail for every (P,r) pair tested (2-adic/r-adic
#      budget kills it) -- printed explicitly per n, not just asserted.
#
# FAMILY SCOPE (unchanged from v_task18): A_n (m = 5 .. largest prime
# factor of N -- an exact, non-arbitrary sub-bound of the task's "m =
# 5..40" that excludes only m for which m!/2 provably cannot divide N,
# per v_task18's own justification), L2(q), L3(q), U3(q), S4(q)=Sp4(q),
# L4(q), U4(q), G2(q), Sz(q), Ree(q)=^2G2(q), Sp6(q), L5(q), U5(q), plus
# the 24 non-B/M-scope sporadics (ATLAS Out orders, orders fetched live
# via CTblLib as a correctness gate).  NOT covered (same honesty standard
# as v_task15/v_task18): PSL/PSU(n,q) n>=6, PSp(2n,q) n>=4, orthogonal
# groups, exceptional E6/E7/E8/F4/^3D4/^2F4(q).
#
# CONTROLS: n=8 (order 20160) must rediscover the CFSG-order-theorem
# coincidence L3(4) (order 20160 = |A8|, k=1, c=1, S <> A8) -- the ONE
# known exception to "the only simple of order n!/2 is A_n", confirming
# the engine can find such coincidences when they exist.  n=9,10 are
# printed as full M11-style negative-sanity controls (complete per-
# forced-prime candidate lists + full near-miss log), expected
# NO_FACTORIZATION as stated in sec 4u.
#
# Run: gap -q -o 8g < v_task19_af.g > v_task19_out.txt   (exit 0 expected)

LoadPackage("ctbllib");;

# =======================================================================
# Formula spot-checks (already validated in v_task15/v_task18; repeated
# here cheaply for self-containedness).
# =======================================================================
Print("=== Formula spot-checks (must all be OK) ===\n");
CheckEq := function(label, got, expected)
    if got = expected then
        Print("  OK   ", label, " = ", got, "\n");
    else
        Print("  FAIL ", label, " : got ", got, ", expected ", expected, "\n");
    fi;
end;;
CheckEq("|A5|", Factorial(5)/2, 60);
CheckEq("|L2(7)| (formula)", 7*(7^2-1)/GcdInt(2,7-1), 168);
CheckEq("|L3(4)| (formula)", 4^3*(4^3-1)*(4^2-1)/GcdInt(3,4-1), 20160);
CheckEq("|PSL(5,2)| (formula)", 2^10*(2^2-1)*(2^3-1)*(2^4-1)*(2^5-1)/GcdInt(5,2-1), 9999360);
CheckEq("|Sz(8)| (formula)", 8^2*(8^2+1)*(8-1), 29120);
CheckEq("|Sp6(2)| (formula)", 2^9*(2^2-1)*(2^4-1)*(2^6-1)/GcdInt(2,2-1), 1451520);
CheckEq("|Ree(27)|=|^2G2(27)| (formula)", 27^3*(27^3+1)*(27-1), 10073444472);
Print("\n");

# =======================================================================
# ENGINE (copied verbatim from v_task18_bm.g, sporadics memoized).
# =======================================================================
gSporadicCache := fail;;
SporadicExtra := function()
    local ct, data, r, cands;
    if gSporadicCache <> fail then return gSporadicCache; fi;
    data := [
        rec(name:="M11", out:=1), rec(name:="M12", out:=2),
        rec(name:="M22", out:=2), rec(name:="M23", out:=1),
        rec(name:="M24", out:=1), rec(name:="J1", out:=1),
        rec(name:="J2", out:=2), rec(name:="J3", out:=2),
        rec(name:="J4", out:=1), rec(name:="HS", out:=2),
        rec(name:="McL", out:=2), rec(name:="He", out:=2),
        rec(name:="Ru", out:=1), rec(name:="Suz", out:=2),
        rec(name:="ON", out:=2), rec(name:="Co3", out:=1),
        rec(name:="Co2", out:=1), rec(name:="Co1", out:=1),
        rec(name:="Fi22", out:=2), rec(name:="Fi23", out:=1),
        rec(name:="Fi24'", out:=2), rec(name:="HN", out:=2),
        rec(name:="Ly", out:=1), rec(name:="Th", out:=1),
        rec(name:="B", out:=1), rec(name:="M", out:=1)
    ];
    cands := [];
    for r in data do
        ct := CharacterTable(r.name);
        if ct = fail then
            Print("WARNING: could not load CharacterTable(\"", r.name, "\")\n");
        else
            Add(cands, rec(order:=Size(ct), out:=r.out, name:=r.name));
        fi;
    od;
    gSporadicCache := cands;
    return cands;
end;;

GenerateCandidatesForN := function(N)
    local cands, add, primePow, pf, p, vp, n, ord, q, f, maxf,
          familyList, fam, largestPrime, sp;
    cands := [];
    add := function(theOrd, theOut, theName)
        Add(cands, rec(order := theOrd, out := theOut, name := theName));
    end;

    primePow := Collected(Factors(N));
    largestPrime := Maximum(List(primePow, x -> x[1]));

    # A_n, m = 5 .. largest prime of N (exact bound: m!/2 for m beyond
    # that introduces a prime > largestPrime(N), so N mod (m!/2) <> 0).
    for n in [5 .. largestPrime] do
        ord := Factorial(n) / 2;
        if n = 6 then
            add(ord, 4, Concatenation("A", String(n)));
        else
            add(ord, 2, Concatenation("A", String(n)));
        fi;
    od;

    familyList := [
      rec(tag:="L2", E:=1, minQ:=4, base:="any", fOdd:=false,
          ordf:=function(q) return q*(q^2-1)/GcdInt(2,q-1); end,
          outf:=function(q,f) return GcdInt(2,q-1)*f; end),
      rec(tag:="L3", E:=3, minQ:=2, base:="any", fOdd:=false,
          ordf:=function(q) return q^3*(q^3-1)*(q^2-1)/GcdInt(3,q-1); end,
          outf:=function(q,f) return GcdInt(3,q-1)*f*2; end),
      rec(tag:="U3", E:=3, minQ:=3, base:="any", fOdd:=false,
          ordf:=function(q) return q^3*(q^3+1)*(q^2-1)/GcdInt(3,q+1); end,
          outf:=function(q,f) return GcdInt(3,q+1)*f*2; end),
      rec(tag:="S4", E:=4, minQ:=3, base:="any", fOdd:=false,
          ordf:=function(q) return q^4*(q^4-1)*(q^2-1)/GcdInt(2,q-1); end,
          outf:=function(q,f) return 2*f; end),
      rec(tag:="L4", E:=6, minQ:=2, base:="any", fOdd:=false,
          ordf:=function(q) return q^6*(q^4-1)*(q^3-1)*(q^2-1)/GcdInt(4,q-1); end,
          outf:=function(q,f) return GcdInt(4,q-1)*f*2; end),
      rec(tag:="U4", E:=6, minQ:=2, base:="any", fOdd:=false,
          ordf:=function(q) return q^6*(q^4-1)*(q^3+1)*(q^2-1)/GcdInt(4,q+1); end,
          outf:=function(q,f) return GcdInt(4,q+1)*f*2; end),
      rec(tag:="G2", E:=6, minQ:=3, base:="any", fOdd:=false,
          ordf:=function(q) return q^6*(q^6-1)*(q^2-1); end,
          outf:=function(q,f) return f; end),
      rec(tag:="Sz", E:=2, minQ:=8, base:=2, fOdd:=true,
          ordf:=function(q) return q^2*(q^2+1)*(q-1); end,
          outf:=function(q,f) return f; end),
      rec(tag:="Ree", E:=3, minQ:=27, base:=3, fOdd:=true,
          ordf:=function(q) return q^3*(q^3+1)*(q-1); end,
          outf:=function(q,f) return f; end),
      rec(tag:="Sp6", E:=9, minQ:=2, base:="any", fOdd:=false,
          ordf:=function(q) return q^9*(q^2-1)*(q^4-1)*(q^6-1)/GcdInt(2,q-1); end,
          outf:=function(q,f)
              if q mod 2 = 0 then return f; else return 2*f; fi;
          end),
      rec(tag:="L5", E:=10, minQ:=2, base:="any", fOdd:=false,
          ordf:=function(q) return q^10*(q^2-1)*(q^3-1)*(q^4-1)*(q^5-1)/GcdInt(5,q-1); end,
          outf:=function(q,f) return GcdInt(5,q-1)*f*2; end),
      rec(tag:="U5", E:=10, minQ:=2, base:="any", fOdd:=false,
          ordf:=function(q) return q^10*(q^2-1)*(q^3+1)*(q^4-1)*(q^5+1)/GcdInt(5,q+1); end,
          outf:=function(q,f) return GcdInt(5,q+1)*f*2; end),
    ];

    for pf in primePow do
        p := pf[1]; vp := pf[2];
        for fam in familyList do
            if fam.base <> "any" and fam.base <> p then continue; fi;
            maxf := QuoInt(vp, fam.E);
            if maxf < 1 then continue; fi;
            f := 1;
            while f <= maxf do
                if (not fam.fOdd) or (f >= 3 and f mod 2 = 1) then
                    q := p^f;
                    if q >= fam.minQ then
                        ord := fam.ordf(q);
                        add(ord, fam.outf(q,f), Concatenation(fam.tag,"(",String(q),")"));
                    fi;
                fi;
                f := f + 1;
            od;
        od;
    od;

    for sp in SporadicExtra() do
        if sp.order < N then
            Add(cands, sp);
        fi;
    od;

    return cands;
end;;

BuildOrderTable := function(cands)
    local byOrder, c, entry, orders;
    byOrder := rec();
    for c in cands do
        entry := String(c.order);
        if not IsBound(byOrder.(entry)) then
            byOrder.(entry) := [];
        fi;
        if not ForAny(byOrder.(entry), r -> r.out = c.out and r.name = c.name) then
            Add(byOrder.(entry), rec(out := c.out, name := c.name));
        fi;
    od;
    orders := Set(List(cands, c -> c.order));
    return rec(orders := orders, byOrder := byOrder);
end;;

OutOptionsForOrder := function(table, d)
    return table.byOrder.(String(d));
end;;

# (A) symmetry-generous divisibility test: c is admitted iff it divides
# outProd * symFactor, symFactor = k! for the multiplicity pattern of the
# chosen order-tuple (see header). Strictly more permissive than plain
# CDiv (symFactor=1 reproduces v_task18's rule exactly).
AllowedC := function(c, outProd, symFactor)
    if c = 0 then return false; fi;
    return (outProd * symFactor) mod c = 0;
end;;

CheckSR1 := function(N, table, logNearMisses)
    local simpleInN, d, d1, d2, d3, c, out1, out2, out3, o1, o2, o3,
          nearMisses, i, j, l, n, prod, sym;

    simpleInN := Filtered(table.orders, d -> d < N and N mod d = 0);
    nearMisses := [];

    # k=1 (symFactor=1 always; a single factor has no repeats)
    for d in simpleInN do
        c := N / d;
        if c > 1 then
            out1 := OutOptionsForOrder(table, d);
            if ForAny(out1, r -> AllowedC(c, r.out, 1)) then
                return rec(verdict := "FACTORIZATION_EXISTS", k := 1,
                    factors := [d], c := c, simpleInN := simpleInN,
                    detail := Concatenation(First(out1, r -> AllowedC(c, r.out, 1)).name,
                        " * ", String(c), "  [Out=", String(First(out1, r -> AllowedC(c, r.out, 1)).out),
                        ", symFactor=1]"));
            elif logNearMisses then
                Add(nearMisses, rec(k := 1, factors := [d],
                    names := List(out1, r -> r.name), outs := List(out1, r -> r.out), c := c));
            fi;
        fi;
    od;

    n := Length(simpleInN);
    for i in [1 .. n] do
        for j in [i .. n] do
            d1 := simpleInN[i]; d2 := simpleInN[j];
            prod := d1 * d2;
            if N mod prod = 0 then
                c := N / prod;
                out1 := OutOptionsForOrder(table, d1);
                out2 := OutOptionsForOrder(table, d2);
                sym := 1; if i = j then sym := 2; fi;
                for o1 in out1 do
                    for o2 in out2 do
                        if AllowedC(c, o1.out * o2.out, sym) then
                            return rec(verdict := "FACTORIZATION_EXISTS", k := 2,
                                factors := [d1, d2], c := c, simpleInN := simpleInN,
                                detail := Concatenation(o1.name, " * ", o2.name, " * ", String(c),
                                    "  [Out=", String(o1.out), ",", String(o2.out),
                                    ", symFactor=", String(sym), "]"));
                        fi;
                    od;
                od;
            fi;
        od;
    od;

    for i in [1 .. n] do
        for j in [i .. n] do
            d1 := simpleInN[i]; d2 := simpleInN[j];
            if N mod (d1 * d2) <> 0 then continue; fi;
            for l in [j .. n] do
                d3 := simpleInN[l];
                prod := d1 * d2 * d3;
                if N mod prod = 0 then
                    c := N / prod;
                    out1 := OutOptionsForOrder(table, d1);
                    out2 := OutOptionsForOrder(table, d2);
                    out3 := OutOptionsForOrder(table, d3);
                    if i = j and j = l then sym := 6;
                    elif i = j or j = l then sym := 2;
                    else sym := 1; fi;
                    for o1 in out1 do
                        for o2 in out2 do
                            for o3 in out3 do
                                if AllowedC(c, o1.out * o2.out * o3.out, sym) then
                                    return rec(verdict := "FACTORIZATION_EXISTS", k := 3,
                                        factors := [d1, d2, d3], c := c, simpleInN := simpleInN,
                                        detail := Concatenation(o1.name, " * ", o2.name, " * ", o3.name,
                                            " * ", String(c), "  [Out=", String(o1.out), ",",
                                            String(o2.out), ",", String(o3.out),
                                            ", symFactor=", String(sym), "]"));
                                fi;
                            od;
                        od;
                    od;
                fi;
            od;
        od;
    od;

    return rec(verdict := "NO_FACTORIZATION", simpleInN := simpleInN, nearMisses := nearMisses);
end;;

# =======================================================================
# NEW for v_task19: forced-prime bookkeeping, order-coincidence check,
# field-automorphism edge case.
# =======================================================================

# Primes p with n/2 < p <= n (the "forced slots": exactly one factor of
# p in n!, hence in N=n!/2, since 2p > n rules out a second multiple).
ForcedPrimesOf := function(n)
    return Filtered([QuoInt(n,2)+1 .. n], IsPrimeInt);
end;;

# Cross-check: each forced prime really has v_p(N) = 1.
VerifyForcedPrimesValuation1 := function(N, forced)
    local primePow, p, entry, ok;
    primePow := Collected(Factors(N));
    ok := true;
    for p in forced do
        entry := First(primePow, x -> x[1] = p);
        if entry = fail or entry[2] <> 1 then
            Print("  ANOMALY: forced prime ", p, " has v_p(N) <> 1 (", entry, ")\n");
            ok := false;
        fi;
    od;
    return ok;
end;;

# Per forced prime: which candidates (order | N, order < N, p | order)
# exist in the covered family scope.
ForcedPrimeReport := function(N, forced, cands)
    local p, matching, c;
    for p in forced do
        matching := Filtered(cands, c -> c.order < N and N mod c.order = 0 and c.order mod p = 0);
        Print("  forced prime ", p, ": ", Length(matching), " candidate(s):\n");
        for c in matching do
            Print("      ", c.name, "  order=", c.order, "  Out=", c.out,
                  "  (", p, "-valuation of order = ",
                  Length(Filtered(Factors(c.order), x -> x = p)), ")\n");
        od;
    od;
end;;

# Order-coincidence check: candidates (any family, incl. A_m for m<>n)
# whose order is EXACTLY N, other than A_n itself. This is the n=8
# control target (L3(4)) and, per CFSG, expected empty for n=9..40.
OrderCoincidenceCheck := function(N, cands, nName)
    local hits, c, selfName, seen;
    selfName := Concatenation("A", String(nName));
    hits := [];
    seen := [];
    for c in cands do
        if c.order = N and c.name <> selfName and not (c.name in seen) then
            Add(hits, c);
            Add(seen, c.name);
        fi;
    od;
    return hits;
end;;

# (B) Field-automorphism edge case: for forced prime P, try L2(r^P) for
# every prime r | N, r <> P, subject to the necessary valuation budget
# f=P <= v_r(N) (order of L2(q) has EXACT r-valuation f, since q-1,q+1
# coprime to r). Prints every (P,r) attempt and its outcome.
FieldAutomorphismCheck := function(N, forced)
    local primePow, P, entry, r, vr, q, ord, divides, anyHit, hits;
    primePow := Collected(Factors(N));
    hits := [];
    for P in forced do
        Print("  forced prime ", P, ":\n");
        anyHit := false;
        for entry in primePow do
            r := entry[1]; vr := entry[2];
            if r = P then continue; fi;
            if P > vr then
                Print("    r=", r, ": SKIP (budget fails: need f=", P,
                      " <= v_", r, "(N)=", vr, ")\n");
                continue;
            fi;
            q := r^P;
            ord := q*(q^2-1)/GcdInt(2,q-1);
            divides := (N mod ord = 0);
            if divides then
                Print("    r=", r, ": q=", r, "^", P, ", L2(q) order divides N -- HIT\n");
                Add(hits, rec(P:=P, r:=r, q:=q, ord:=ord));
                anyHit := true;
            else
                Print("    r=", r, ": q=", r, "^", P,
                      " (", Length(String(q)), " digits), L2(q) order does NOT divide N -- rejected\n");
            fi;
        od;
        if not anyHit then
            Print("    -> no field-automorphism L2(r^", P, ") candidate divides N.\n");
        fi;
    od;
    return hits;
end;;

# =======================================================================
# CONTROL: n=8, must rediscover the L3(4) coincidence.
# =======================================================================
Print("=== CONTROL: n=8 (|A8|=20160) must rediscover the L3(4) coincidence ===\n");
N8 := Factorial(8)/2;;
Print("N8 = ", N8, "\n");
cands8 := GenerateCandidatesForN(N8);;
Print("total candidates generated: ", Length(cands8), "\n");
coin8 := OrderCoincidenceCheck(N8, cands8, 8);;
Print("Order-N coincidences (name <> A8): ", Length(coin8), "\n");
for c in coin8 do
    Print("  ", c.name, "  order=", c.order, "  Out=", c.out, "\n");
od;
if Length(coin8) > 0 and ForAny(coin8, c -> c.name = "L3(4)") then
    Print("CONTROL PASSED: L3(4) coincidence rediscovered.\n");
else
    Print("CONTROL FAILED: L3(4) coincidence NOT found.\n");
fi;
table8 := BuildOrderTable(cands8);;
res8 := CheckSR1(N8, table8, false);;
Print("(informational, not part of AF range) standard k<=3 verdict for n=8: ", res8.verdict, "\n");
if res8.verdict = "FACTORIZATION_EXISTS" then
    Print("  detail: ", res8.detail, "\n");
fi;
Print("\n");

# =======================================================================
# MAIN SWEEP: n = 9 .. 40.
# =======================================================================
results := [];;
for n in [9 .. 40] do
    Print("=========================================================\n");
    Print("=== n = ", n, " ===\n");
    N := Factorial(n) / 2;;
    Print("N = |A", n, "| = n!/2 = ", N, "\n");
    Print("Factors(N) = ", Collected(Factors(N)), "\n");

    forced := ForcedPrimesOf(n);;
    Print("Forced primes in (n/2, n] = ", forced, "\n");
    VerifyForcedPrimesValuation1(N, forced);;

    cands := GenerateCandidatesForN(N);;
    Print("total candidates generated (incl. sporadics): ", Length(cands), "\n");
    table := BuildOrderTable(cands);;
    Print("distinct order values: ", Length(table.orders), "\n");

    Print("--- Forced-prime candidate report ---\n");
    ForcedPrimeReport(N, forced, cands);

    Print("--- Field-automorphism edge case (sec 4u (iii)) ---\n");
    faHits := FieldAutomorphismCheck(N, forced);;
    if Length(faHits) > 0 then
        Print("  ANOMALY: ", Length(faHits), " field-automorphism hit(s) found -- see above.\n");
    fi;

    Print("--- Order-N coincidence check (name <> A", n, ") ---\n");
    coin := OrderCoincidenceCheck(N, cands, n);;
    Print("  hits: ", Length(coin), "\n");
    for c in coin do
        Print("    ", c.name, "  order=", c.order, "  Out=", c.out, "\n");
    od;

    logNear := (n = 9 or n = 10);
    Print("--- CheckSR1 (k<=3, symmetry-generous) ---\n");
    res := CheckSR1(N, table, logNear);;
    Print("  candidates dividing N (< N, in-scope): ", Length(res.simpleInN), "\n");
    if logNear then
        Print("  full in-scope divisor list: ", res.simpleInN, "\n");
    fi;
    Print("  VERDICT (n=", n, "): ", res.verdict, "\n");
    if res.verdict = "FACTORIZATION_EXISTS" then
        Print("  witness: ", res.detail, "\n");
    elif logNear then
        Print("  near-miss log (k=1, all divisors with c>1, none admits AllowedC):\n");
        for nm in res.nearMisses do
            Print("    d=", nm.factors[1], "  c=", nm.c, "  candidates=", nm.names,
                  "  Outs=", nm.outs, "\n");
        od;
    fi;

    detailStr := "";
    if res.verdict = "FACTORIZATION_EXISTS" then
        detailStr := res.detail;
    fi;
    Add(results, rec(n := n, N := N, verdict := res.verdict,
        detail := detailStr,
        coincidences := coin, faHits := faHits, forced := forced));
    Print("\n");
od;

# =======================================================================
# FINAL SUMMARY
# =======================================================================
Print("=========================================================\n");
Print("=== FINAL SUMMARY: n = 9..40 ===\n");
for r in results do
    if r.verdict = "FACTORIZATION_EXISTS" then
        Print("  n=", r.n, ": FACTORIZATION  ", r.detail, "\n");
    else
        Print("  n=", r.n, ": NO_FACTORIZATION\n");
    fi;
    if Length(r.coincidences) > 0 then
        Print("      order-N coincidence(s): ", List(r.coincidences, c -> c.name), "\n");
    fi;
    if Length(r.faHits) > 0 then
        Print("      field-automorphism hit(s): ", r.faHits, "\n");
    fi;
od;

Print("\n=== COVERAGE STATEMENT ===\n");
Print("Family scope (exact, N-specific bounds, NOT a magnitude truncation):\n");
Print("A_m (m=5..largest prime of N), L2(q), L3(q), U3(q), S4(q)=Sp4(q),\n");
Print("L4(q), U4(q), G2(q), Sz(q), Ree(q)=^2G2(q), Sp6(q), L5(q), U5(q),\n");
Print("plus the 24 non-B/M sporadics (order fetched via CTblLib) plus B, M.\n");
Print("Within this scope, candidate generation for each n is EXHAUSTIVE:\n");
Print("for each prime p | N with valuation v_p(N), every family member\n");
Print("whose defining field q=p^f could possibly divide N (f<=v_p(N)/E, E\n");
Print("fixed per family) was generated and exactly divisibility-tested; no\n");
Print("q was skipped by an arbitrary magnitude cutoff. The c-bound uses a\n");
Print("symmetry-generous divisibility test (Out-product times k! for\n");
Print("repeated-order tuples), strictly more permissive than v_task18's.\n");
Print("The field-automorphism edge case (forced prime entering via a\n");
Print("field-extension degree rather than the base prime, sec 4u (iii)) is\n");
Print("checked explicitly per forced prime against L2(r^P) for every prime\n");
Print("r|N, r<>P, within the necessary valuation budget.\n");
Print("NOT covered (any n): PSL/PSU(n,q) n>=6, PSp(2n,q) n>=4,\n");
Print("orthogonal O(2n+1,q)/O^+-(2n,q), exceptional E6/E7/E8/F4/^3D4/^2F4(q).\n");
Print("A NO_FACTORIZATION verdict is therefore exact relative to the\n");
Print("13-family + sporadic scope above, not a certified CFSG-exhaustive\n");
Print("sweep against every remaining simple-group family.\n");

quit;
