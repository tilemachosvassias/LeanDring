LoadPackage("TomLib");

DumpSpecies := function(G, filename)
    local T, subs, reps, i, j, K, N, W, F_rows, r, x, h, H, H_prime, row, M, f;
    T := TableOfMarks(G);
    subs := SubsTom(T);
    reps := RepresentativesTom(T);
    
    F_rows := [];
    for i in [1..Length(reps)] do
        H := reps[i];
        H_prime := DerivedSubgroup(H);
        for x in Elements(H) do
            # Fused rational condition: x^2 in H' implies it's fused rational?
            # Actually, the user says F is the Z-valued species.
            # We can just collect all species and then filter those that are Z-valued.
            # But the Z-valued species are EXACTLY the ones whose row in the character table of D(G) is rational.
            # Let's just use ALL pairs (H, h) up to conjugacy, then we can filter over Z.
            pass;
        od;
    od;
end;
QUIT;
