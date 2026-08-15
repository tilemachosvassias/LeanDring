HypergroupData := function(A, W)
    local orbs, n, i, j, k, x, y, S, tally, z, pos, A_elms;
    
    A_elms := Elements(A);
    orbs := ShallowCopy(OrbitsDomain(W, A_elms, OnPoints));
    n := Length(orbs);
    Sort(orbs, function(a,b) return Length(a) < Length(b); end);
    
    S := [];
    for i in [1..n] do
        S[i] := [];
        for j in [1..n] do
            tally := List([1..n], x -> 0);
            for x in orbs[i] do
                for y in orbs[j] do
                    z := x * y;
                    pos := PositionProperty(orbs, o -> z in o);
                    tally[pos] := tally[pos] + 1;
                od;
            od;
            S[i][j] := List([1..n], k -> tally[k] / Length(orbs[k]));
        od;
    od;
    
    return [List(orbs, Length), S];
end;

RunG2 := function()
    local order, A, AutA, ccW, W, hd, i;
    Print("data = [\n");
    for order in [1..32] do
        for A in AllSmallGroups(order, IsAbelian, true) do
            AutA := AutomorphismGroup(A);
            ccW := ConjugacyClassesSubgroups(AutA);
            for i in [1..Length(ccW)] do
                W := Representative(ccW[i]);
                hd := HypergroupData(A, W);
                Print("  {'A_id': ", IdGroup(A), ", 'W_size': ", Size(W), 
                      ", 'W_class': ", i, ", 'orb_sizes': ", hd[1], 
                      ", 'S': ", hd[2], "},\n");
            od;
        od;
    od;
    Print("]\n");
end;

RunG2();
quit;
