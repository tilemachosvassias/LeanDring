Read("gap/dring_sieve_standalone.g");
Witness := function(G, sigma, name)
  local cls, T, V, n, Vp, B0, i, sol, bad, f, dual, g, j, lab, supp;
  cls := SpeciesClassesD(G);; T := SpeciesTableD(G, cls);;
  V := TransposedMat(T);; n := Length(cls);
  B0 := HermiteNormalFormIntegerMat(V);;
  lab := List(cls, c -> [c.Hidx, Size(c.H), Order(c.q)]);
  # find a generator whose sigma-image leaves L
  for i in [1..n] do
    Vp := Permuted(V[i], sigma);
    sol := SolutionMat(B0, Vp);
    if sol = fail or not ForAll(sol, IsInt) then
      Print(name, ": generator ", i, " (basis [", lab[i], "]) breaks; ");
      # violated functional: dual basis of B0: f = row of B0^{-1}T detecting frac part
      dual := Inverse(B0*1);  # columns = dual functionals... B0 * dual = I
      # find dual functional with non-integer value: f_j(x) = (x * dual)[j]
      sol := Vp * dual;
      j := First([1..n], k -> not IsInt(sol[k]));
      f := dual{[1..n]}[j];  # column j of dual
      # clear denominators: f has rational entries; the congruence: (B0-lattice)·f ⊆ Z
      f := f * Lcm(List(f, DenominatorRat));
      supp := Filtered([1..n], k -> f[k] <> 0);
      Print("witness functional support (pt: coeff | K-class,|K|,ord):\n");
      for j in supp do
        Print("   pt", j, ": ", f[j], " | ", lab[j], "\n");
      od;
      return;
    fi;
  od;
  Print(name, ": no breaking generator?!\n");
end;
Witness(SmallGroup(8,3), (18,19), "D4 T2-transposition");
Witness(SmallGroup(32,49), (5,30), "(32,49) single twin swap");
QUIT;
