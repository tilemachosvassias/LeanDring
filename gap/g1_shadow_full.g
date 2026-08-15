ShadowData := function(G)
    local cc, n, i, j, K, N, chars, orbits, sigs, dc, D, int_K, int_idx, dc_data, rep, invs, get_inv, inv_map, cand, k;
    
    cc := ConjugacyClassesSubgroups(G);
    n := Length(cc);
    
    get_inv := H -> [ Size(H), AbelianInvariants(H), Size(Normalizer(G, H)) ];
    
    sigs := [];
    invs := [];
    inv_map := []; # map invariant -> list of class indices
    
    for i in [1..n] do
        Print("Computing invariants for class ", i, "/", n, "\n");
        K := Representative(cc[i]);
        N := Normalizer(G, K);
        chars := LinearCharacters(K);
        orbits := List(OrbitsDomain(N, chars), Length);
        Sort(orbits);
        Add(sigs, [ Size(K), AbelianInvariants(K), Size(N), orbits ]);
        
        invs[i] := get_inv(K);
        
        # We don't have dictionaries natively easy in GAP script, just use a simple linear search to find invariant index
        # Actually we can just build a list of (invariant, index) pairs
    od;
    
    dc_data := [];
    for i in [1..n] do
        Print("Processing class ", i, "/", n, "\n");
        dc_data[i] := [];
        for j in [1..n] do
            dc_data[i][j] := [];
            dc := DoubleCosets(G, Representative(cc[i]), Representative(cc[j]));
            for D in dc do
                rep := Representative(D);
                int_K := Intersection(Representative(cc[i]), Representative(cc[j])^rep);
                
                # Fast find
                cand := get_inv(int_K);
                int_idx := -1;
                for k in [1..n] do
                    if invs[k] = cand then
                        if IsConjugate(G, Representative(cc[k]), int_K) then
                            int_idx := k;
                            break;
                        fi;
                    fi;
                od;
                
                Add(dc_data[i][j], int_idx);
            od;
            Sort(dc_data[i][j]);
        od;
    od;
    
    return [sigs, dc_data];
end;

G68 := SmallGroup(3125, 68);
G69 := SmallGroup(3125, 69);
Print("Starting G68...\n");
d68 := ShadowData(G68);
Print("Starting G69...\n");
d69 := ShadowData(G69);

Print("G68_shadow = ", String(d68), ";\n");
Print("G69_shadow = ", String(d69), ";\n");
