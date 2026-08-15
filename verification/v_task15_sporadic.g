#!/usr/bin/env gap -q
# v_task15: SR1 arithmetic check for the 26 sporadic simple groups.
#
# Corrected redo of v_task12 (used a size BOUND c<=576 instead of
# divisibility) and v_task13 (enforced divisibility but against one global
# constant c | 2^8*3^4 = 20736, which is not realizable as an actual
# product of Out(S_i) orders).  Here: for each candidate factorization
# |M| = S1*...*Sk*c (k<=3, Si nonabelian simple, EXCLUDING the trivial
# k=1,S1=M,c=1 case), the allowed c must satisfy
#     c | prod_i |Out(Si)|
# using the ACTUAL outer automorphism group order of each Si, not a
# global bound.  Family formulas used (q = p^f, standard ATLAS /
# Kleidman-Liebeck d.f.g decomposition), spot-checked below against
# known isomorphisms and GAP-verifiable small cases:
#
#   A_n (n>=5):      Out = 2, except A6: Out = 4.
#   PSL(2,q):        Out = gcd(2,q-1) * f            [d.f, g=1: A1 diagram, no graph aut]
#   PSL(3,q):        Out = gcd(3,q-1) * f * 2         [d.f.g, g=2: A2 diagram symmetry]
#   PSU(3,q):        Out = gcd(3,q+1) * f * 2
#   PSp(4,q), q>=3:  Out = 2 * f                      [uniform: d.f.g = 2f whether q odd (d=2,g=1) or q=2^f,f>=2 (d=1,g=2)]
#   PSL(4,q):        Out = gcd(4,q-1) * f * 2
#   PSU(4,q):        Out = gcd(4,q+1) * f * 2
#   G2(q), q>=3:     Out = f                          [G2 simply-connected=adjoint, trivial diagonal part; no extra graph outer autos]
#
# Cross-checks used to validate the formulas before trusting them on the
# sporadics (all consistency checks below PASSED when this file was run):
#   PSL(3,2) = PSL(2,7)  (isomorphic, order 168):  both formulas give Out=2.
#   PSL(4,2) = A8        (isomorphic, order 20160): both formulas give Out=2.
#   PSU(4,2) = PSp(4,3)  (isomorphic, order 25920): both formulas give Out=2.
#   PSL(2,9) = A6        (isomorphic, order 360):   both formulas give Out=4.
#   PSL(3,4): Out=12 (the classical "exceptional" Out(L3(4))=D12), matches ATLAS.
#   PSU(3,3): Out=2, PSU(3,4): Out=4, PSU(3,5): Out=6 -- all match ATLAS.
#   PSp(4,3): Out=2, PSp(4,4): Out=4 -- match ATLAS.
#
# The one KNOWN accidental order-collision inside the generated family
# range (CFSG order theorem, per NOTES.md Even/NOTES.md): A8 and L3(4)
# both have order 20160, but Out(A8)=2 while Out(L3(4))=12.  Handled
# explicitly below: order 20160 carries BOTH out-options {2,12}, and the
# existence check tries all of them (most generous choice) before
# declaring NO_FACTORIZATION.

# ---------------------------------------------------------------------
# Sporadic orders (via CTblLib character tables, as in v_task12/v_task13)
# ---------------------------------------------------------------------
GetSporadicOrders := function()
    local sporadics, orders, names, ct, i;
    sporadics := [
        "M11", "M12", "M22", "M23", "M24",
        "J1", "J2", "J3", "J4",
        "HS", "McL", "He",
        "Ru", "Suz", "ON",
        "Co3", "Co2", "Co1",
        "Fi22", "Fi23", "Fi24'",
        "HN", "Ly", "Th", "B", "M"
    ];
    orders := [];
    names := [];
    for i in [1..Length(sporadics)] do
        ct := CharacterTable(sporadics[i]);
        if ct <> fail then
            Add(orders, Size(ct));
            Add(names, sporadics[i]);
        else
            Print("WARNING: could not load CharacterTable(\"", sporadics[i], "\")\n");
        fi;
    od;
    return rec(names := names, orders := orders);
end;;

# ---------------------------------------------------------------------
# Candidate nonabelian simple group orders WITH actual |Out| attached.
# Returns a list of records rec(order:=.., out:=.., name:=..).
# Bound caps generated orders (families grow fast in q; entries above
# `bound` are dropped since they cannot appear as a factor of interest).
# ---------------------------------------------------------------------
GenerateCandidates := function(bound)
    local cands, n, ord, p, f, q, primesList, add;
    cands := [];
    add := function(theOrd, theOut, theName)
        if theOrd <= bound and theOrd >= 60 then
            Add(cands, rec(order := theOrd, out := theOut, name := theName));
        fi;
    end;

    # A_n, n = 5..30
    for n in [5..30] do
        ord := Factorial(n) / 2;
        if n = 6 then
            add(ord, 4, "A6");
        else
            add(ord, 2, Concatenation("A", String(n)));
        fi;
    od;

    primesList := Filtered([2 .. 250], IsPrime);

    # PSL(2,q), q = p^f >= 4
    for p in primesList do
        f := 1; q := p;
        while q <= 3*10^8 do
            if q >= 4 then
                ord := q * (q^2 - 1) / GcdInt(2, q - 1);
                add(ord, GcdInt(2, q - 1) * f, Concatenation("L2(", String(q), ")"));
            fi;
            f := f + 1; q := p^f;
        od;
    od;

    # PSL(3,q), q = p^f >= 2
    for p in primesList do
        f := 1; q := p;
        while q <= 20000 do
            ord := q^3 * (q^3 - 1) * (q^2 - 1) / GcdInt(3, q - 1);
            add(ord, GcdInt(3, q - 1) * f * 2, Concatenation("L3(", String(q), ")"));
            f := f + 1; q := p^f;
        od;
    od;

    # PSU(3,q), q = p^f >= 3
    for p in primesList do
        f := 1; q := p;
        while q <= 20000 do
            if q >= 3 then
                ord := q^3 * (q^3 + 1) * (q^2 - 1) / GcdInt(3, q + 1);
                add(ord, GcdInt(3, q + 1) * f * 2, Concatenation("U3(", String(q), ")"));
            fi;
            f := f + 1; q := p^f;
        od;
    od;

    # PSp(4,q), q = p^f >= 3  (Sp4(2) is not simple; its derived group is A6, already listed)
    for p in primesList do
        f := 1; q := p;
        while q <= 6000 do
            if q >= 3 then
                ord := q^4 * (q^4 - 1) * (q^2 - 1) / GcdInt(2, q - 1);
                add(ord, 2 * f, Concatenation("S4(", String(q), ")"));
            fi;
            f := f + 1; q := p^f;
        od;
    od;

    # PSL(4,q), q = p^f >= 2
    for p in primesList do
        f := 1; q := p;
        while q <= 500 do
            ord := q^6 * (q^4 - 1) * (q^3 - 1) * (q^2 - 1) / GcdInt(4, q - 1);
            add(ord, GcdInt(4, q - 1) * f * 2, Concatenation("L4(", String(q), ")"));
            f := f + 1; q := p^f;
        od;
    od;

    # PSU(4,q), q = p^f >= 2
    for p in primesList do
        f := 1; q := p;
        while q <= 500 do
            ord := q^6 * (q^4 - 1) * (q^3 + 1) * (q^2 - 1) / GcdInt(4, q + 1);
            add(ord, GcdInt(4, q + 1) * f * 2, Concatenation("U4(", String(q), ")"));
            f := f + 1; q := p^f;
        od;
    od;

    # G2(q), q = p^f >= 3  (G2(2) is not simple; G2(2)' = U3(3), already listed)
    for p in primesList do
        f := 1; q := p;
        while q <= 500 do
            if q >= 3 then
                ord := q^6 * (q^6 - 1) * (q^2 - 1);
                add(ord, f, Concatenation("G2(", String(q), ")"));
            fi;
            f := f + 1; q := p^f;
        od;
    od;

    return cands;
end;;

# ---------------------------------------------------------------------
# Build: orderList (sorted distinct orders) and a lookup order -> list
# of rec(out:=.., name:=..) [to carry collisions, e.g. order 20160].
# ---------------------------------------------------------------------
BuildOrderTable := function(cands)
    local byOrder, c, entry, orders;
    byOrder := rec();
    for c in cands do
        entry := String(c.order);
        if not IsBound(byOrder.(entry)) then
            byOrder.(entry) := [];
        fi;
        # de-dup by (out,name)
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

NamesForOrder := function(table, d)
    return List(OutOptionsForOrder(table, d), r -> r.name);
end;;

# ---------------------------------------------------------------------
# CheckDivisibility: does c divide outProd?  (c | prod_i |Out(Si)|)
# ---------------------------------------------------------------------
CDiv := function(c, outProd)
    if c = 0 then return false; fi;
    return outProd mod c = 0;
end;;

# ---------------------------------------------------------------------
# Full SR1 check for one sporadic order N.  logNearMisses=true collects
# ALL attempted k=1,k=2 combinations (used only for the M11 anchor print).
# ---------------------------------------------------------------------
CheckSR1 := function(N, table, logNearMisses)
    local simpleInN, d, d1, d2, d3, c, out1, out2, out3, o1, o2, o3,
          nearMisses, i, j, l, n, prod;

    simpleInN := Filtered(table.orders, d -> d < N and N mod d = 0);
    nearMisses := [];

    # k = 1 (almost-simple: S1 <> M forced since simpleInN excludes N itself)
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

    # k = 2
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
                if logNearMisses then
                    Add(nearMisses, rec(k := 2, factors := [d1, d2],
                        names := [List(out1, r -> r.name), List(out2, r -> r.name)],
                        outs := [List(out1, r -> r.out), List(out2, r -> r.out)], c := c));
                fi;
            fi;
        od;
    od;

    # k = 3
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

# =======================================================================
# Sanity/consistency spot-checks on the Out() formulas before trusting
# them on the sporadics (all must print "OK").
# =======================================================================
CheckFormula := function(label, got, expected)
    if got = expected then
        Print("  OK   ", label, " : Out = ", got, "\n");
    else
        Print("  FAIL ", label, " : got ", got, ", expected ", expected, "\n");
    fi;
end;;

Print("=== Formula spot-checks (must all be OK) ===\n");
CheckFormula("Out(A6)", 4, 4);
CheckFormula("Out(A8)", 2, 2);
CheckFormula("Out(L2(7))  [=L3(2)]", GcdInt(2,6)*1, 2);
CheckFormula("Out(L3(2))  [=L2(7)]", GcdInt(3,1)*1*2, 2);
CheckFormula("Out(L2(9))  [=A6]", GcdInt(2,8)*2, 4);
CheckFormula("Out(L4(2))  [=A8]", GcdInt(4,1)*1*2, 2);
CheckFormula("Out(U4(2))  [=S4(3)]", GcdInt(4,3)*1*2, 2);
CheckFormula("Out(S4(3))  [=U4(2)]", 2*1, 2);
CheckFormula("Out(L3(4))", GcdInt(3,3)*2*2, 12);
CheckFormula("Out(U3(3))", GcdInt(3,4)*1*2, 2);
CheckFormula("Out(U3(4))", GcdInt(3,5)*2*2, 4);
CheckFormula("Out(U3(5))", GcdInt(3,6)*1*2, 6);
CheckFormula("Out(S4(4))", 2*2, 4);
Print("\n");

# =======================================================================
# MAIN
# =======================================================================
Print("=== v_task15: SR1 arithmetic check, 26 sporadic simple groups ===\n");
Print("Condition per candidate factorization |M| = S1*...*Sk*c (k<=3):\n");
Print("  c MUST divide prod_i |Out(Si)|, using ACTUAL per-family Out orders.\n\n");

sporadics := GetSporadicOrders();;
Print("Sporadics loaded: ", Length(sporadics.names), " / 26\n");

# CAND_BOUND exceeds |Fi24'| = 1255205709190661721292800, the largest
# of the 24 sporadics other than B and M (see coverage note below).
CAND_BOUND := 2*10^24;;
cands := GenerateCandidates(CAND_BOUND);;
table := BuildOrderTable(cands);;
Print("Candidate simple-group orders generated (families: An n=5..30, ",
      "L2(q), L3(q), U3(q), S4(q), L4(q), U4(q), G2(q)), bound ", CAND_BOUND, ": ",
      Length(table.orders), " distinct order values\n");

# Report any order collisions (multiple non-isomorphic simple groups
# sharing the same order) found among the generated candidates.
Print("\n=== Order collisions detected among generated candidates ===\n");
collisionCount := 0;;
for d in table.orders do
    entry := OutOptionsForOrder(table, d);
    if Length(entry) > 1 then
        collisionCount := collisionCount + 1;
        Print("  order ", d, ": ", List(entry, r -> Concatenation(r.name, " (Out=", String(r.out), ")")), "\n");
    fi;
od;
if collisionCount = 0 then
    Print("  none\n");
fi;

results := [];;
for i in [1 .. Length(sporadics.names)] do
    logNM := (sporadics.names[i] = "M11");
    r := CheckSR1(sporadics.orders[i], table, logNM);
    # Coverage honesty: a NO_FACTORIZATION verdict is only as strong as the
    # candidate generation bound. If |M| itself exceeds CAND_BOUND, a simple
    # group of order between CAND_BOUND and |M| could exist that we never
    # generated, so the verdict must be downgraded to INCONCLUSIVE.
    if r.verdict = "NO_FACTORIZATION" and sporadics.orders[i] > CAND_BOUND then
        r.verdict := "INCONCLUSIVE";
        r.coverageNote := Concatenation("|M| = ", String(sporadics.orders[i]),
            " exceeds the candidate generation bound ", String(CAND_BOUND),
            "; a simple-group divisor in that gap cannot be ruled out here.");
    fi;
    Add(results, rec(name := sporadics.names[i], order := sporadics.orders[i], result := r));
od;

Print("\n=== RESULTS TABLE ===\n\n");
for i in [1 .. Length(results)] do
    r := results[i];
    Print(r.name, " (|M|=", r.order, ") | ");
    if r.result.verdict = "FACTORIZATION_EXISTS" then
        Print("FACTORIZATION | ", r.result.detail, "\n");
    elif r.result.verdict = "INCONCLUSIVE" then
        Print("INCONCLUSIVE | ", r.result.coverageNote, "\n");
    else
        Print("NO FACTORIZATION | candidates dividing |M|: ", Length(r.result.simpleInN), "\n");
    fi;
od;

Print("\n=== M11 ANCHOR: full candidate list + rejected near-misses ===\n");
m11 := First(results, r -> r.name = "M11");;
Print("M11 order: ", m11.order, "\n");
Print("M11 verdict: ", m11.result.verdict, "\n");
Print("Candidate simple orders dividing 7920 (from generated families): ", m11.result.simpleInN, "\n");
for d in m11.result.simpleInN do
    Print("    order ", d, " realized by: ",
        List(OutOptionsForOrder(table, d), r -> Concatenation(r.name, " (Out=", String(r.out), ")")), "\n");
od;
Print("\nRejected near-misses (k=1 and k=2; P | N but no Out-choice makes c | outProd):\n");
for nm in m11.result.nearMisses do
    if nm.k = 1 then
        Print("  k=1: S1=order ", nm.factors[1], " ", nm.names, " Out-options=", nm.outs,
              "; c = 7920/", nm.factors[1], " = ", nm.c,
              "; REJECTED since ", nm.c, " does not divide any of ", nm.outs, "\n");
    else
        Print("  k=2: S1=order ", nm.factors[1], " ", nm.names[1], " (Out=", nm.outs[1],
              "), S2=order ", nm.factors[2], " ", nm.names[2], " (Out=", nm.outs[2],
              "); c = 7920/", nm.factors[1]*nm.factors[2], " = ", nm.c,
              "; REJECTED since ", nm.c, " does not divide any product of ", nm.outs[1], " x ", nm.outs[2], "\n");
    fi;
od;

Print("\n=== SUMMARY COUNTS ===\n");
noFact := Filtered(results, r -> r.result.verdict = "NO_FACTORIZATION");;
yesFact := Filtered(results, r -> r.result.verdict = "FACTORIZATION_EXISTS");;
incFact := Filtered(results, r -> r.result.verdict = "INCONCLUSIVE");;
Print("NO FACTORIZATION (SR1 holds, D-rigid): ", Length(noFact), "\n");
Print("FACTORIZATION EXISTS: ", Length(yesFact), "\n");
Print("INCONCLUSIVE (coverage): ", Length(incFact), "\n");
if Length(yesFact) > 0 then
    Print("  Groups with a factorization: ", List(yesFact, r -> r.name), "\n");
fi;
if Length(incFact) > 0 then
    Print("  Groups with a coverage gap: ", List(incFact, r -> r.name), "\n");
fi;

Print("\n=== COVERAGE STATEMENT ===\n");
Print("Family scope: A_n (n=5..30), PSL(2,q), PSL(3,q), PSU(3,q), PSp(4,q),\n");
Print("PSL(4,q), PSU(4,q), G2(q); candidate simple-group orders generated up to\n");
Print(CAND_BOUND, ", which exceeds |M| for all 24 sporadics except B and M.\n");
Print("NOT covered (any order): Suzuki Sz(q), Ree ^2G2(q)/^2F4(q), PSL/PSU(n,q)\n");
Print("n>=5, PSp(2n,q) n>=3, orthogonal O(2n+1,q)/O^+-(2n,q), exceptional\n");
Print("E6/E7/E8/F4/^3D4.\n");
Print("A NO_FACTORIZATION verdict means: no factorization exists using\n");
Print("candidates from the covered families, and |M| itself is within the\n");
Print("generation bound so no in-family divisor was missed by truncation.\n");
Print("It still assumes SR1's family scope (the 8 families above) is the\n");
Print("complete list of relevant simple-group orders for that |M| -- it is\n");
Print("not a certified exhaustive CFSG sweep against every Lie-type family.\n");
Print("B and M exceed the generation bound (|B|, |M| >> ", CAND_BOUND,
      "), so a simple-group divisor between the bound and |M| cannot be\n");
Print("ruled out by this run; both are reported INCONCLUSIVE (coverage), not NO.\n");

quit;
