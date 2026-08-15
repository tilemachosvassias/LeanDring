Read("gap/dring_sieve_standalone.g");
G := SmallGroup(8,3);;
cls := SpeciesClassesD(G);; T := SpeciesTableD(G, cls);;
V := TransposedMat(T);; n := Length(cls);;
lab := List(cls, c -> [c.Hidx, Size(c.H), Order(c.q)]);;
Print("G-fibre points: ", Filtered([1..n], i -> lab[i][2] = 8), "\n");
Print("point labels 15..20: ", lab{[15..20]}, "\n");
sigma := (18,19);;
for i in [1..n] do
  Vp := Permuted(V[i], sigma);
  sol := SolutionMat(V, Vp);
  if not ForAll(sol, IsInt) then
    Print("generator ", i, " ", lab[i], " breaks; non-integral coeffs at: ",
      Filtered([1..n], k -> not IsInt(sol[k])), " values ",
      List(Filtered([1..n], k -> not IsInt(sol[k])), k -> sol[k]), "\n");
    Print("  gen ", i, " coords at pts 17-20: ", V[i]{[17..20]}, "\n");
  fi;
od;
# also: coordinates of ALL generators at the G-fibre points
Print("Columns 17..20 nonzero for generators: ",
  Filtered([1..n], j -> not IsZero(V[j]{[17..20]})), "\n");
QUIT;
