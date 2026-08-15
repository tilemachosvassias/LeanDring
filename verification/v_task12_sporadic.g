#!/usr/bin/env gap -q
# SR1 Arithmetic Condition Check for 26 Sporadic Simple Groups
# Task: Determine if each sporadic order N can be written as:
# (A) |S1| * |S2| * ... * |Sk| * c where k>=2, Si nonabelian simple, c|2^6*3^2
# (B) Almost-simple: |S| * c where S nonabelian simple, c>1, c|2^6*3^2

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
    for n in [5..25] do
        ord := Factorial(n) / 2;
        if ord <= bound then Add(orders, ord); fi;
    od;
    for e in [2..20] do
        qpow := 2^e;
        ord := qpow * (qpow^2 - 1);
        if ord <= bound then Add(orders, ord); fi;
    od;
    primes := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97];
    for p in primes do
        for e in [1..6] do
            qpow := p^e;
            if qpow > 1000000 then break; fi;
            ord := qpow * (qpow - 1) * (qpow + 1) / 2;
            if ord <= bound then Add(orders, ord); fi;
        od;
    od;
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
    for q in [2,3,4,5,7,8,9] do
        ord := q^4 * (q^4 - 1) * (q^2 - 1);
        g := GcdInt(2, q - 1);
        if g > 1 then ord := ord / g; fi;
        if ord <= bound then Add(orders, ord); fi;
    od;
    for q in [2,3,4,5,7] do
        ord := q^6 * (q^4 - 1) * (q^3 - 1) * (q^2 - 1);
        g := GcdInt(4, q - 1);
        ord := ord / g;
        if ord <= bound then Add(orders, ord); fi;
    od;
    for q in [2,3,4,5,7] do
        ord := q^6 * (q^6 - 1) * (q^2 - 1);
        g := GcdInt(2, q - 1);
        if g > 1 then ord := ord / g; fi;
        if ord <= bound then Add(orders, ord); fi;
    od;
    for e in [1..2] do
        q := 3^(2*e + 1);
        if q <= 10000 then
            ord := q^3 * (q^3 - 1) * (q - 1);
            if ord <= bound then Add(orders, ord); fi;
        fi;
    od;
    return AsSet(orders);
end;

CheckSRCondition := function(N, simpleOrders, maxAuto)
    local simpleInN, i, j, k, c, s1, s2, s3, prod;
    simpleInN := Filtered(simpleOrders, d -> N mod d = 0);

    if Length(simpleInN) = 0 then
        return rec(
            verdict := "NO_FACTORIZATION",
            simpleInN := [],
            reason := "No simple order divides N"
        );
    fi;

    for s1 in simpleInN do
        if s1 < N then
            c := N / s1;
            if c > 1 and c <= maxAuto then
                return rec(
                    verdict := "FACTORIZATION_EXISTS",
                    type := "almost-simple",
                    S := s1,
                    c := c,
                    simpleInN := simpleInN
                );
            fi;
        fi;
    od;

    if Length(simpleInN) >= 2 then
        for i in [1..Length(simpleInN)] do
            for j in [i..Length(simpleInN)] do
                s1 := simpleInN[i];
                s2 := simpleInN[j];
                prod := s1 * s2;
                if N mod prod = 0 then
                    c := N / prod;
                    if c <= maxAuto then
                        return rec(
                            verdict := "FACTORIZATION_EXISTS",
                            type := "k-simple-2",
                            S1 := s1,
                            S2 := s2,
                            c := c,
                            simpleInN := simpleInN
                        );
                    fi;
                fi;
            od;
        od;

        if Length(simpleInN) >= 3 then
            for i in [1..Minimum(Length(simpleInN), 20)] do
                for j in [i..Minimum(Length(simpleInN), 20)] do
                    for k in [j..Minimum(Length(simpleInN), 20)] do
                        s1 := simpleInN[i];
                        s2 := simpleInN[j];
                        s3 := simpleInN[k];
                        prod := s1 * s2 * s3;
                        if N mod prod = 0 then
                            c := N / prod;
                            if c <= maxAuto then
                                return rec(
                                    verdict := "FACTORIZATION_EXISTS",
                                    type := "k-simple-3",
                                    S1 := s1,
                                    S2 := s2,
                                    S3 := s3,
                                    c := c,
                                    simpleInN := simpleInN
                                );
                            fi;
                        fi;
                    od;
                od;
            od;
        fi;
    fi;

    if Length(simpleInN) >= 2 then
        return rec(
            verdict := "INCONCLUSIVE",
            reason := "Many simple orders divide N but no valid factorization found with c<=576",
            numSimpleInN := Length(simpleInN),
            simpleInN := simpleInN
        );
    else
        return rec(
            verdict := "NO_FACTORIZATION",
            reason := "Only 1 simple order divides N; no k>=2 or almost-simple factorization possible",
            simpleInN := simpleInN
        );
    fi;
end;

# Main
Print("=== SR1 Check: Sporadics ===\n\n");
sporadics := GetSporadicOrders();
simpleOrders := GenerateSimpleGroupOrders(10^10);
maxAuto := 576;

results := [];
for i in [1..Length(sporadics.names)] do
    result := CheckSRCondition(sporadics.orders[i], simpleOrders, maxAuto);
    Add(results, rec(name := sporadics.names[i], order := sporadics.orders[i], result := result));
od;

Print("Sporadic | Order | Verdict | Details\n");
Print("---------|-------|---------|--------\n");

for i in [1..Length(results)] do
    r := results[i];
    Print(r.name, " | ", r.order, " | ");

    if r.result.verdict = "FACTORIZATION_EXISTS" then
        Print("YES");
        if r.result.type = "almost-simple" then
            Print(" | S*c: ", r.result.S, "*", r.result.c);
        elif r.result.type = "k-simple-2" then
            Print(" | k=2: ", r.result.S1, "*", r.result.S2, "*", r.result.c);
        else
            Print(" | k=3: ", r.result.S1, "*", r.result.S2, "*", r.result.S3, "*", r.result.c);
        fi;
    elif r.result.verdict = "INCONCLUSIVE" then
        Print("INCONCLUSIVE | ", r.result.numSimpleInN, " simple orders divide N");
    else
        Print("NO | (", r.result.reason, ")");
    fi;
    Print("\n");
od;

Print("\n=== SIMPLE GROUP FAMILIES COVERED ===\n");
Print("1. Alternating groups: A_n for n in [5,25]\n");
Print("2. PSL(2,q): q=2^m for m in [2,20]; odd prime powers up to ~10^6\n");
Print("3. PSL(3,q), PSU(3,q), Sp(4,q): selected q up to 31\n");
Print("4. PSL(4,q): q in {2,3,4,5,7}\n");
Print("5. G2(q): q in {2,3,4,5,7}\n");
Print("6. Ree groups ^2G2(q): q in {27, 243}\n");
Print("\nTotal: ", Length(simpleOrders), " simple orders up to 10^10\n");

quit;
