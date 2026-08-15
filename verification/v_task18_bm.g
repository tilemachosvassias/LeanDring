#!/usr/bin/env gap -q
# v_task18: SR1 arithmetic check for the Baby Monster (B) and the Monster
# (M) -- the two sporadics left INCONCLUSIVE by v_task15 because their
# orders (~4.15e33, ~8.08e53) exceed v_task15's global candidate-generation
# bound of 2*10^24.
#
# STRATEGY (per NOTES.md Even/NOTES.md addressed by this task): instead of
# generating candidate simple-group orders up to a fixed global magnitude
# bound (infeasible for B, M), generate them EXACTLY using N's OWN prime
# factorization.  For a Lie-type family with defining field size q = p^f
# (p prime, f>=1), the order formula always contains a term q^E for some
# fixed small integer E depending on the family (E=1 for L2, E=3 for
# L3/U3, E=4 for S4=Sp4, E=6 for L4/U4/G2, etc.), and since q-1, q+1,
# q^2-1, ... are all coprime to p, the p-adic valuation of |family(q)|
# is EXACTLY E*f.  For |family(q)| to divide N, we therefore need
#     E*f <= v_p(N)     (v_p(N) = p-adic valuation of N)
# which gives an EXACT, non-arbitrary bound on f for each prime p dividing
# N -- not a truncation.  Looping p over N's own (small, ~11-15 element)
# prime set and f over this exact bound is cheap (a few hundred candidates
# total), and every candidate is then given a final exact big-integer
# divisibility test (N mod order = 0) via GAP's native bignums -- no
# hand-verified smoothness argument is relied on for correctness, only
# for motivating *why* the search is bounded the way it is.
#
# This makes the resulting NO_FACTORIZATION / FACTORIZATION verdict for
# B and M, restricted to the family scope below, EXHAUSTIVE (not merely
# bounded) for those families -- an improvement on v_task15's coverage
# note, which had to rely on an a priori magnitude bound.
#
# Family scope: the 8 families from v_task15 (A_n, L2(q), L3(q), U3(q),
# S4(q)=Sp4(q), L4(q), U4(q), G2(q)) PLUS 5 bonus families added here
# specifically to widen the net for the large primes 31,47 (B) and
# 41,59,71 (M): Sz(q) [Suzuki, q=2^f f odd], Ree(q) [^2G2(q), q=3^f f
# odd], Sp6(q), PSL5(q), PSU5(q).  Plus the 24 non-B/M sporadics as
# discrete extra candidates (hardcoded ATLAS orders/Out).
#
# NOT covered (stated honestly, same spirit as v_task15's coverage note):
# PSL/PSU(n,q) n>=6, PSp(2n,q) n>=4, orthogonal O(2n+1,q)/O^+-(2n,q),
# exceptional E6/E7/E8/F4/^3D4/^2F4(q).  A "candidates found: NONE" per
# large prime, restricted to the covered families, is not by itself a
# certified CFSG-exhaustive claim -- see the final coverage statement.

# ---------------------------------------------------------------------
# Formula spot-checks (bonus families), must all be OK before trusting
# them below.  (Core 8-family formulas were already spot-checked in
# v_task15_sporadic.g; not repeated here.)
# ---------------------------------------------------------------------
Print("=== Bonus-family formula spot-checks (must all be OK) ===\n");
CheckEq := function(label, got, expected)
    if got = expected then
        Print("  OK   ", label, " = ", got, "\n");
    else
        Print("  FAIL ", label, " : got ", got, ", expected ", expected, "\n");
    fi;
end;;
CheckEq("|PSL(5,2)| (formula)", 2^10*(2^2-1)*(2^3-1)*(2^4-1)*(2^5-1)/GcdInt(5,2-1), 9999360);
CheckEq("|Sz(8)| (formula)", 8^2*(8^2+1)*(8-1), 29120);
CheckEq("|Sp6(2)| (formula)", 2^9*(2^2-1)*(2^4-1)*(2^6-1)/GcdInt(2,2-1), 1451520);
CheckEq("|Ree(27)|=|^2G2(27)| (formula)", 27^3*(27^3+1)*(27-1), 10073444472);
Print("\n");

# ---------------------------------------------------------------------
# 24 non-B/M sporadic orders + ATLAS-standard Out orders, hardcoded
# (added as discrete extra candidates; cheap, finite list).
# ---------------------------------------------------------------------
SporadicExtra := function()
    local ct, data, r, cands;
    # rec(name, out) ; order fetched live via CTblLib for correctness
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
        rec(name:="Ly", out:=1), rec(name:="Th", out:=1)
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
    return cands;
end;;

# ---------------------------------------------------------------------
# GenerateCandidatesForN(N): exact (non-truncated) candidate generation
# using N's own prime factorization, across the 13-family scope, plus
# the 24 sporadic extras.
# ---------------------------------------------------------------------
GenerateCandidatesForN := function(N)
    local cands, add, primePow, pf, p, vp, n, ord, q, f, maxf,
          familyList, fam, largestPrime, sp;
    cands := [];
    add := function(theOrd, theOut, theName)
        Add(cands, rec(order := theOrd, out := theOut, name := theName));
    end;

    primePow := Collected(Factors(N));
    largestPrime := Maximum(List(primePow, x -> x[1]));

    # A_n, n = 5 .. largest prime of N (n! introduces a prime > largestPrime
    # for n beyond that, guaranteeing N mod (n!/2) <> 0).
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
        Add(cands, sp);
    od;

    return cands;
end;;

# ---------------------------------------------------------------------
# BuildOrderTable / CheckSR1: same machinery as v_task15_sporadic.g,
# unchanged (copied verbatim so this file is self-contained).
# ---------------------------------------------------------------------
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

CDiv := function(c, outProd)
    if c = 0 then return false; fi;
    return outProd mod c = 0;
end;;

CheckSR1 := function(N, table, logNearMisses)
    local simpleInN, d, d1, d2, d3, c, out1, out2, out3, o1, o2, o3,
          nearMisses, i, j, l, n, prod;

    simpleInN := Filtered(table.orders, d -> d < N and N mod d = 0);
    nearMisses := [];

    for d in simpleInN do
        c := N / d;
        if c > 1 then
            out1 := OutOptionsForOrder(table, d);
            if ForAny(out1, r -> CDiv(c, r.out)) then
                return rec(verdict := "FACTORIZATION_EXISTS", k := 1,
                    factors := [d], c := c, simpleInN := simpleInN,
                    detail := Concatenation(First(out1, r -> CDiv(c, r.out)).name,
                        " * ", String(c), "  [Out=", String(First(out1, r -> CDiv(c, r.out)).out), "]"));
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
                for o1 in out1 do
                    for o2 in out2 do
                        if CDiv(c, o1.out * o2.out) then
                            return rec(verdict := "FACTORIZATION_EXISTS", k := 2,
                                factors := [d1, d2], c := c, simpleInN := simpleInN,
                                detail := Concatenation(o1.name, " * ", o2.name, " * ", String(c),
                                    "  [Out=", String(o1.out), ",", String(o2.out), "]"));
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
                    for o1 in out1 do
                        for o2 in out2 do
                            for o3 in out3 do
                                if CDiv(c, o1.out * o2.out * o3.out) then
                                    return rec(verdict := "FACTORIZATION_EXISTS", k := 3,
                                        factors := [d1, d2, d3], c := c, simpleInN := simpleInN,
                                        detail := Concatenation(o1.name, " * ", o2.name, " * ", o3.name,
                                            " * ", String(c), "  [Out=", String(o1.out), ",",
                                            String(o2.out), ",", String(o3.out), "]"));
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

# ---------------------------------------------------------------------
# Per-large-prime candidate report: which generated candidates (from
# the covered families) have order dividing N AND divisible by p.
# ---------------------------------------------------------------------
LargePrimeReport := function(N, largePrimes, cands, label)
    local p, matching, c;
    Print("\n--- Large-prime coverage check for ", label, " ---\n");
    for p in largePrimes do
        matching := Filtered(cands, c -> c.order < N and N mod c.order = 0 and c.order mod p = 0);
        # dedup by (order,name)
        Print("  prime ", p, ": ", Length(matching), " candidate(s) with order | N and ", p, " | order:\n");
        for c in matching do
            Print("      ", c.name, "  order=", c.order, "  Out=", c.out,
                  "  (", p, "-valuation of order = ",
                  Length(Filtered(Factors(c.order), x -> x = p)), ")\n");
        od;
    od;
end;;

# ---------------------------------------------------------------------
# Out-smoothness check: over ALL candidates dividing N (from the covered
# families), is any Out value divisible by one of N's own large
# (valuation-1) primes?  Confirms the "Out too smooth to carry a large
# prime" claim on the ACTUAL generated data, not just asserted.
# ---------------------------------------------------------------------
OutSmoothnessCheck := function(N, cands, valuation1Primes)
    local divisors, c, bad, p;
    divisors := Filtered(cands, c -> c.order < N and N mod c.order = 0);
    bad := [];
    for c in divisors do
        for p in valuation1Primes do
            if c.out mod p = 0 then
                Add(bad, rec(name:=c.name, out:=c.out, p:=p));
            fi;
        od;
    od;
    Print("  Candidates dividing N (covered families): ", Length(divisors), "\n");
    if Length(bad) = 0 then
        Print("  Out-smoothness CONFIRMED: no candidate's Out is divisible by any\n");
        Print("  valuation-1 prime of N (checked primes: ", valuation1Primes, ").\n");
    else
        Print("  ANOMALY: the following candidates have Out divisible by a large prime:\n");
        for c in bad do
            Print("    ", c.name, " Out=", c.out, " divisible by ", c.p, "\n");
        od;
    fi;
end;;

# =======================================================================
# CONTROLS
# =======================================================================
Print("=== v_task18: SR1 arithmetic check for B and M ===\n");
Print("(Using N-specific exact candidate generation; see header comment.)\n\n");

Print("=== POSITIVE CONTROL: J2 (|J2|=604800) should rediscover A5*A7*4 ===\n");
j2cands := GenerateCandidatesForN(604800);;
j2table := BuildOrderTable(j2cands);;
j2res := CheckSR1(604800, j2table, false);;
Print("J2 verdict: ", j2res.verdict, "\n");
if j2res.verdict = "FACTORIZATION_EXISTS" then
    Print("  detail: ", j2res.detail, "\n");
fi;
Print("\n");

Print("=== NEGATIVE CONTROL: M11 (|M11|=7920) should give NO_FACTORIZATION ===\n");
m11cands := GenerateCandidatesForN(7920);;
m11table := BuildOrderTable(m11cands);;
m11res := CheckSR1(7920, m11table, true);;
Print("M11 verdict: ", m11res.verdict, "\n");
Print("  candidates dividing 7920: ", m11res.simpleInN, "\n");
Print("\n");

# =======================================================================
# MAIN: B and M
# =======================================================================
LoadPackage("ctbllib");;
bOrder := Size(CharacterTable("B"));;
mOrder := Size(CharacterTable("M"));;

Print("=== |B| = ", bOrder, " ===\n");
Print("Factors(|B|) = ", Collected(Factors(bOrder)), "\n");
bValuation1Primes := List(Filtered(Collected(Factors(bOrder)), x -> x[2]=1), x -> x[1]);;
Print("Valuation-1 primes of |B|: ", bValuation1Primes, "\n");
bLargePrimes := [31, 47];;
Print("Task-specified 'large primes' for B: ", bLargePrimes, "\n\n");

Print("=== |M| = ", mOrder, " ===\n");
Print("Factors(|M|) = ", Collected(Factors(mOrder)), "\n");
mValuation1Primes := List(Filtered(Collected(Factors(mOrder)), x -> x[2]=1), x -> x[1]);;
Print("Valuation-1 primes of |M|: ", mValuation1Primes, "\n");
mLargePrimes := [41, 59, 71];;
Print("Task-specified 'large primes' for M: ", mLargePrimes, "\n\n");

Print("Generating candidates for B (exact, N-specific bounds)...\n");
bCands := GenerateCandidatesForN(bOrder);;
Print("  total raw candidates generated (incl. sporadics): ", Length(bCands), "\n");
bTable := BuildOrderTable(bCands);;
Print("  distinct order values: ", Length(bTable.orders), "\n");

Print("Generating candidates for M (exact, N-specific bounds)...\n");
mCands := GenerateCandidatesForN(mOrder);;
Print("  total raw candidates generated (incl. sporadics): ", Length(mCands), "\n");
mTable := BuildOrderTable(mCands);;
Print("  distinct order values: ", Length(mTable.orders), "\n\n");

Print("=== Out-smoothness check (B) ===\n");
OutSmoothnessCheck(bOrder, bCands, bValuation1Primes);
Print("\n=== Out-smoothness check (M) ===\n");
OutSmoothnessCheck(mOrder, mCands, mValuation1Primes);

LargePrimeReport(bOrder, bValuation1Primes, bCands, "B (all valuation-1 primes)");
LargePrimeReport(mOrder, mValuation1Primes, mCands, "M (all valuation-1 primes)");

Print("\n=== Full SR1 candidate list dividing |B| (k=1 divisors only) ===\n");
bSimple := Filtered(bTable.orders, d -> d < bOrder and bOrder mod d = 0);;
Print("Count: ", Length(bSimple), "\n");
for d in bSimple do
    Print("  order ", d, ": ", List(OutOptionsForOrder(bTable,d), r->Concatenation(r.name," (Out=",String(r.out),")")), "\n");
od;

Print("\n=== Full SR1 candidate list dividing |M| (k=1 divisors only) ===\n");
mSimple := Filtered(mTable.orders, d -> d < mOrder and mOrder mod d = 0);;
Print("Count: ", Length(mSimple), "\n");
for d in mSimple do
    Print("  order ", d, ": ", List(OutOptionsForOrder(mTable,d), r->Concatenation(r.name," (Out=",String(r.out),")")), "\n");
od;

Print("\n=== Running full CheckSR1 (k<=3) for B ===\n");
bResult := CheckSR1(bOrder, bTable, false);;
Print("B VERDICT: ", bResult.verdict, "\n");
if bResult.verdict = "FACTORIZATION_EXISTS" then
    Print("  detail: ", bResult.detail, "\n");
fi;

Print("\n=== Running full CheckSR1 (k<=3) for M ===\n");
mResult := CheckSR1(mOrder, mTable, false);;
Print("M VERDICT: ", mResult.verdict, "\n");
if mResult.verdict = "FACTORIZATION_EXISTS" then
    Print("  detail: ", mResult.detail, "\n");
fi;

Print("\n=== COVERAGE STATEMENT ===\n");
Print("Family scope (exact, N-specific bounds, NOT a magnitude truncation):\n");
Print("A_n (n=5..largest prime of N), L2(q), L3(q), U3(q), S4(q)=Sp4(q),\n");
Print("L4(q), U4(q), G2(q), Sz(q), Ree(q)=^2G2(q), Sp6(q), L5(q), U5(q),\n");
Print("plus the 24 non-B/M sporadics.\n");
Print("Within this scope, candidate generation for B and M is EXHAUSTIVE:\n");
Print("for each prime p | N with valuation v_p(N), every family member whose\n");
Print("defining field q=p^f could possibly divide N (f <= v_p(N)/E, E fixed\n");
Print("per family) was generated and exactly divisibility-tested; no q was\n");
Print("skipped by an arbitrary magnitude cutoff.\n");
Print("NOT covered (any order): PSL/PSU(n,q) n>=6, PSp(2n,q) n>=4,\n");
Print("orthogonal O(2n+1,q)/O^+-(2n,q), exceptional E6/E7/E8/F4/^3D4/^2F4(q).\n");
Print("A NO_FACTORIZATION / 'candidates: NONE' verdict is therefore exact\n");
Print("relative to the 13-family + sporadic scope above, but not a\n");
Print("certified CFSG-exhaustive sweep against every remaining simple-group\n");
Print("family (Suzuki/Ree beyond the simplest, higher orthogonal/unitary/\n");
Print("linear rank, and all exceptional Lie types).\n");

quit;
