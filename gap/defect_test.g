Read("gap/dring_sieve_standalone.g");
DefectOf := function(G, sigma, name)
  local cls, T, V, n, Vp, U, H0, H1, D, B0, B1, M, snf;
  cls := SpeciesClassesD(G);; T := SpeciesTableD(G, cls);;
  V := TransposedMat(T);; n := Length(cls);
  Vp := List(V, r -> Permuted(r, sigma));
  B0 := HermiteNormalFormIntegerMat(V);;
  M := Concatenation(V, Vp);;
  B1 := HermiteNormalFormIntegerMat(M);;
  B1 := Filtered(B1, r -> not IsZero(r));;
  if B0 = B1 then Print(name, ": sigma PRESERVES lattice\n"); return; fi;
  # defect = (L + sigma L)/L : SNF of B0-basis matrix expressed in B1-basis
  snf := ElementaryDivisorsMat(List(B0, r -> SolutionMat(B1, r)));
  Print(name, ": defect (L+sL)/L divisors: ", Collected(Filtered(snf, x -> x > 1)), "\n");
end;
# D4: T2 transposition in G-fibre (points 18,19 per earlier run)
G := SmallGroup(8,3);;
DefectOf(G, (18,19), "D4 T2-transposition(18,19)");
# (32,49): single k=1 twin swap vs all-9 swap
G := SmallGroup(32,49);;
DefectOf(G, (5,30), "(32,49) single twin swap (5,30)");
sig := (5,30)(7,36)(9,40)(11,79)(13,51)(15,86)(17,49)(19,55)(21,27);;
DefectOf(G, sig, "(32,49) all-9 twin swap");
QUIT;
