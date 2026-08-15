SubgroupData := function(G)
    local cc, n, i, K, N, chars, orbits, sigs;
    cc := ConjugacyClassesSubgroups(G);
    n := Length(cc);
    sigs := [];
    for i in [1..n] do
        K := Representative(cc[i]);
        N := Normalizer(G, K);
        chars := Filtered(Irr(K), x -> x[1] = 1);
        orbits := List(OrbitsDomain(N, chars), Length);
        Sort(orbits);
        Add(sigs, [ Size(K), AbelianInvariants(K), Size(N), orbits ]);
    od;
    return sigs;
end;

G68 := SmallGroup(3125, 68);
G69 := SmallGroup(3125, 69);
d68 := SubgroupData(G68);
d69 := SubgroupData(G69);

Print("G68_subgroups = ", String(d68), ";\n");
Print("G69_subgroups = ", String(d69), ";\n");
