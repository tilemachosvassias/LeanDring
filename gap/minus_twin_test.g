Read("gap/dring_sieve_standalone.g");
G := SmallGroup(32,50);;   # extraspecial minus, n=2: singular lines have sigma=1
cls := SpeciesClassesD(G);; T := SpeciesTableD(G, cls);;
V := TransposedMat(T);; n := Length(cls);;
lab := List(cls, c -> [Size(c.H), Order(c.q), c.Hidx]);;
# find twin pairs: ell>=2 edges between |K|=2 (ord 2) and |K|=4 (ord 2) points
B := HermiteNormalFormIntegerMat(V);;
pairs := [];;
for p in [1..n] do for q in [p+1..n] do
  if lab[p][1] = 2 and lab[q][1] = 4 and lab[p][2] = 2 and lab[q][2] = 2 then
    g := 0;
    for i in [1..n] do g := GcdInt(g, B[i][p] - B[i][q]); od;
    if g <> 0 and PValuation(g,2) >= 2 then Add(pairs, [p,q,PValuation(g,2)]); fi;
  fi;
od; od;
Print("(32,50) twin pairs (T1-line vs T3-line, ell>=2): ", pairs, "\n");
if pairs <> [] then
  p := pairs[1];
  sigma := (p[1], p[2]);
  bad := 0;
  for i in [1..n] do
    sol := SolutionMat(V, Permuted(V[i], sigma));
    if sol = fail or not ForAll(sol, IsInt) then bad := bad + 1; fi;
  od;
  Print("single twin swap (", p[1], ",", p[2], ") at sigma(K)=1: breaking generators: ", bad, " of ", n, "\n");
fi;
QUIT;
