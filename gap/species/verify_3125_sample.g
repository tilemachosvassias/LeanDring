# verify_3125_sample.g
#
# Bounded independent checks using the current dring_sieve_standalone.g
# implementation.  For each Satz-5.1 group this computes only the leading
# 70 x 70 table and checks Lemma A on the first 14 [H,1] species.  It does not
# launch the full 2724 x 2724 table computation.
#
# Run from the project root:
#   gap -q gap/species/verify_3125_sample.g

Read("gap/lib/dring_sieve_standalone.g");

PartialSpeciesTableD3125 := function(G, k)
    local cls, basis, T, i, j, s, b, conjH, g, tot, elG, pos;
    cls := SpeciesClassesD(G);
    basis := BasisClassesD(G);
    if Length(cls) <> Length(basis) then
        Error("species/basis count mismatch");
    fi;
    elG := Elements(G);
    T := [];
    for i in [1..k] do
        s := cls[i];
        conjH := List(elG, g -> s.H ^ g);
        T[i] := [];
        for j in [1..k] do
            b := basis[j];
            tot := 0;
            for g in [1..Length(elG)] do
                if IsSubset(b.K, conjH[g]) then
                    pos := Position(b.elK, s.h ^ elG[g]);
                    tot := tot + b.vals[pos];
                fi;
            od;
            tot := tot / Size(b.K);
            if not IsCycInt(tot) then
                Error("non-integral species value");
            fi;
            T[i][j] := tot;
        od;
    od;
    return rec(cls := cls, basis := basis, table := T);
end;

CheckTrivialConductors3125 := function(G, data, maxHidx)
    local T, cls, n, TT, out, i, rhs, sol, check, r, c, nlat, ngrp;
    T := data.table;
    cls := data.cls;
    n := Length(T);
    TT := TransposedMat(T);
    out := [];
    for i in [1..n] do
        if cls[i].Hidx > maxHidx or Order(cls[i].q) <> 1 then
            continue;
        fi;
        rhs := List([1..n], r -> 0);
        rhs[i] := 1;
        sol := SolutionMat(TT, rhs);
        if sol = fail then
            Error("leading system has no solution at row ", i);
        fi;
        check := List([1..n], r ->
            Sum([1..n], c -> T[r][c] * sol[c]));
        if check <> rhs then
            Error("solution verification failed at row ", i);
        fi;
        if not ForAll(sol, IsRat) then
            Error("non-rational coefficient at trivial species ", i);
        fi;
        nlat := Lcm(List(sol, DenominatorRat));
        ngrp := Size(Normalizer(G, cls[i].H)) / Size(cls[i].Hp);
        Add(out, [i, cls[i].Hidx, Size(cls[i].H), nlat, ngrp,
                  nlat = ngrp]);
    od;
    return out;
end;

RunBounded3125 := function(id)
    local G, cls, basis, data, checks, tm;
    tm := Runtime();
    G := SmallGroup(3125, id);
    cls := SpeciesClassesD(G);
    basis := BasisClassesD(G);
    Print("G", id, " species=", Length(cls), " basis=", Length(basis),
          " square=", Length(cls) = Length(basis), "\n");
    data := PartialSpeciesTableD3125(G, 70);
    checks := CheckTrivialConductors3125(G, data, 14);
    Print("G", id, " conductor_coverage=", Length(checks), "/",
          Length(ConjugacyClassesSubgroups(G)),
          " all_pass=", ForAll(checks, x -> x[6]),
          " ms=", Runtime() - tm, "\n");
    Print("G", id, " conductor_details=", checks, "\n");
end;

RunBounded3125(68);
RunBounded3125(69);

