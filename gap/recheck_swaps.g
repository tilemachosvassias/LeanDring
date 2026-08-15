Read("gap/dring_sieve_standalone.g");
Recheck := function(G, sigma, name)
  local cls, T, V, n, i, Vp, sol, bad;
  cls := SpeciesClassesD(G);; T := SpeciesTableD(G, cls);;
  V := TransposedMat(T);; n := Length(cls);
  bad := 0;
  for i in [1..n] do
    Vp := Permuted(V[i], sigma);
    sol := SolutionMat(V, Vp);   # solve directly against generator matrix
    if sol = fail or not ForAll(sol, IsInt) then bad := bad + 1; fi;
  od;
  Print(name, ": generators whose sigma-image leaves the lattice: ", bad, " of ", n, "\n");
end;
Recheck(SmallGroup(8,3), (18,19), "D4 T2-transposition (18,19)");
Recheck(SmallGroup(32,49), (5,30), "(32,49) single twin swap (5,30)");
QUIT;
