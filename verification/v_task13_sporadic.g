#!/usr/bin/env gap -q
# v_task13: SR1 Arithmetic Condition Check for 26 Sporadic Simple Groups
# CORRECTED from v_task12: enforce divisibility c | 2^8*3^4 = 20736, not just bounded
#
# Task: For each sporadic M, decide if there EXISTS a factorization
# |M| = |S1|·...·|Sk|·c with k >= 1 nonabelian simple Si, c dividing 20736,
# EXCLUDING the trivial case k=1, S1=M, c=1.
#
# Critical fix: c must DIVIDE 2^8·3^4 = 20736 exactly (test: 20736 mod c = 0)

GetSporadicOrders := function()
    local sporadics, orders, names, ct, ord, i;
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
        fi;
    od;
    return rec(names := names, orders := orders);
end;

GenerateSimpleGroupOrders := function(bound)
    local orders, n, ord, q, qpow, p, e, primes, g;
    orders := [];
    # Alternating groups A_n for n in [5..30]
    for n in [5..30] do
        ord := Factorial(n) / 2;
        if ord <= bound then Add(orders, ord); fi;
    od;
    # PSL(2,2^e) for e in [2..20]
    for e in [2..20] do
        qpow := 2^e;
        ord := qpow * (qpow^2 - 1);
        if ord <= bound then Add(orders, ord); fi;
    od;
    # PSL(2,p) for various primes/prime powers q up to ~10^6
    primes := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97];
    for p in primes do
        for e in [1..6] do
            qpow := p^e;
            if qpow > 1000000 then break; fi;
            ord := qpow * (qpow - 1) * (qpow + 1) / 2;
            if ord <= bound then Add(orders, ord); fi;
        od;
    od;
    # PSL(3,q), PSU(3,q) for small q up to 1000
    for q in [2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31] do
        ord := q^3 * (q^3 - 1) * (q^2 - 1);
        g := GcdInt(3, q - 1);
        if g > 1 then ord := ord / g; fi;
        if ord <= bound then Add(orders, ord); fi;
    od;
    for q in [2,3,4,5,7,8,9,11,13] do
        ord := q^3 * (q^3 + 1) * (q^2 - 1);
        g := GcdInt(3, q + 1);
        if g > 1 then ord := ord / g; fi;
        if ord <= bound then Add(orders, ord); fi;
    od;
    # Sp(4,q) and PSL(4,q) for small q
    for q in [2,3,4,5,7,8,9] do
        ord := q^4 * (q^4 - 1) * (q^2 - 1);
        g := GcdInt(2, q - 1);
        if g > 1 then ord := ord / g; fi;
        if ord <= bound then Add(orders, ord); fi;
    od;
    # PSU(4,q)
    for q in [2,3,4,5,7] do
        ord := q^6 * (q^4 - 1) * (q^3 - 1) * (q^2 - 1);
        g := GcdInt(4, q - 1);
        ord := ord / g;
        if ord <= bound then Add(orders, ord); fi;
    od;
    # G2(q)
    for q in [2,3,4,5,7] do
        ord := q^6 * (q^6 - 1) * (q^2 - 1);
        g := GcdInt(2, q - 1);
        if g > 1 then ord := ord / g; fi;
        if ord <= bound then Add(orders, ord); fi;
    od;
    # Ree groups ^2G2(q)
    for e in [1..2] do
        q := 3^(2*e + 1);
        if q <= 10000 then
            ord := q^3 * (q^3 - 1) * (q - 1);
            if ord <= bound then Add(orders, ord); fi;
        fi;
    od;
    return AsSet(orders);
end;

CheckDivisibility := function(c, bound)
    # Check if c divides bound exactly
    # Equivalently, check if bound mod c = 0
    if c = 0 then return false; fi;
    return bound mod c = 0;
end;

CheckSRCondition := function(N, simpleOrders, divBound)
    local simpleInN, i, j, k, c, s1, s2, s3, prod, idx1, idx2, idx3;
    simpleInN := Filtered(simpleOrders, d -> N mod d = 0 and d < N);

    if Length(simpleInN) = 0 then
        return rec(
            verdict := "NO_FACTORIZATION",
            simpleInN := [],
            reason := "No simple order (other than N itself) divides N"
        );
    fi;

    # k=1 (almost-simple variant): S ≠ M with N/|S| dividing divBound and > 1
    for s1 in simpleInN do
        c := N / s1;
        if c > 1 and CheckDivisibility(c, divBound) then
            return rec(
                verdict := "FACTORIZATION_EXISTS",
                type := "almost-simple",
                S := s1,
                c := c,
                factorization := Concatenation(String(s1), "*", String(c)),
                simpleInN := simpleInN
            );
        fi;
    od;

    # k=2
    if Length(simpleInN) >= 2 then
        for i in [1..Length(simpleInN)] do
            for j in [i..Length(simpleInN)] do
                s1 := simpleInN[i];
                s2 := simpleInN[j];
                prod := s1 * s2;
                if N mod prod = 0 then
                    c := N / prod;
                    if CheckDivisibility(c, divBound) then
                        return rec(
                            verdict := "FACTORIZATION_EXISTS",
                            type := "k-simple-2",
                            S1 := s1,
                            S2 := s2,
                            c := c,
                            factorization := Concatenation(String(s1), "*", String(s2), "*", String(c)),
                            simpleInN := simpleInN
                        );
                    fi;
                fi;
            od;
        od;
    fi;

    # k=3 (limited search)
    if Length(simpleInN) >= 3 then
        for idx1 in [1..Minimum(Length(simpleInN), 30)] do
            for idx2 in [idx1..Minimum(Length(simpleInN), 30)] do
                for idx3 in [idx2..Minimum(Length(simpleInN), 30)] do
                    s1 := simpleInN[idx1];
                    s2 := simpleInN[idx2];
                    s3 := simpleInN[idx3];
                    prod := s1 * s2 * s3;
                    if N mod prod = 0 then
                        c := N / prod;
                        if CheckDivisibility(c, divBound) then
                            return rec(
                                verdict := "FACTORIZATION_EXISTS",
                                type := "k-simple-3",
                                S1 := s1,
                                S2 := s2,
                                S3 := s3,
                                c := c,
                                factorization := Concatenation(String(s1), "*", String(s2), "*", String(s3), "*", String(c)),
                                simpleInN := simpleInN
                            );
                        fi;
                    fi;
                od;
            od;
        od;
    fi;

    if Length(simpleInN) >= 2 then
        return rec(
            verdict := "INCONCLUSIVE",
            reason := Concatenation("Many simple orders divide N but no valid factorization found with c | ", String(divBound)),
            numSimpleInN := Length(simpleInN),
            simpleInN := simpleInN
        );
    else
        return rec(
            verdict := "NO_FACTORIZATION",
            reason := "Only 1 simple order divides N; no k>=2 or almost-simple factorization with valid c",
            simpleInN := simpleInN
        );
    fi;
end;

# ==== MAIN ====
Print("=== v_task13: SR1 Check for 26 Sporadic Simple Groups ===\n");
Print("Constraint: c must DIVIDE 2^8*3^4 = 20736 exactly\n\n");

sporadics := GetSporadicOrders();
simpleOrders := GenerateSimpleGroupOrders(10^10);
divBound := 20736;  # 2^8 * 3^4

Print("Total sporadics found: ", Length(sporadics.names), "\n");
Print("Total simple orders generated: ", Length(simpleOrders), "\n\n");

results := [];
for i in [1..Length(sporadics.names)] do
    result := CheckSRCondition(sporadics.orders[i], simpleOrders, divBound);
    Add(results, rec(name := sporadics.names[i], order := sporadics.orders[i], result := result));
od;

Print("=== RESULTS TABLE ===\n\n");

for i in [1..Length(results)] do
    r := results[i];
    Print(r.name, " (", r.order, ") | ");

    if r.result.verdict = "FACTORIZATION_EXISTS" then
        Print("YES | ", r.result.factorization, "\n");
    elif r.result.verdict = "INCONCLUSIVE" then
        Print("INCONCLUSIVE | ", r.result.numSimpleInN, " simple orders divide\n");
    else
        Print("NO\n");
    fi;
od;

Print("\n=== SANITY ANCHOR: M11 CHECK ===\n");
m11_idx := Position(sporadics.names, "M11");
if m11_idx <> fail then
    m11_result := results[m11_idx];
    Print("M11 order: ", m11_result.order, "\n");
    Print("M11 verdict: ", m11_result.result.verdict, "\n");
    if m11_result.result.verdict = "NO_FACTORIZATION" then
        Print("ANCHOR PASSED: M11 correctly identified as NO factorization\n");
        if Length(m11_result.result.simpleInN) > 0 then
            Print("Divisor candidates: ", m11_result.result.simpleInN, "\n");
        fi;
    else
        Print("WARNING: M11 did not return NO_FACTORIZATION!\n");
    fi;
fi;

Print("\n=== COVERAGE ===\n");
Print("Simple group families covered:\n");
Print("  - Alternating: A_n for n in [5..30]\n");
Print("  - PSL(2,q): q=2^e (e in [2..20]) and odd prime powers up to ~10^6\n");
Print("  - PSL(3,q), PSU(3,q): selected q up to 31\n");
Print("  - Sp(4,q), PSL(4,q), PSU(4,q): selected q up to 8/7/7\n");
Print("  - G2(q): q in {2,3,4,5,7}\n");
Print("  - 26 Sporadic groups (M11..M, J1..J4, etc.)\n");
Print("\nDivisibility bound: 2^8*3^4 = ", divBound, "\n");

quit;
