# The only prime not covered by the Brauer tables: p = 7 for the 2-local members.
# Count absolutely irreducible 7-dimensional GF(7)-modules directly (MeatAxe).
for spec in [[1344,1],[1344,2],[10752,8]] do
  G := PerfectGroup(IsPermGroup, spec[1], spec[2]);;
  ms := IrreducibleModules(G, GF(7), 7);;
  dims := List(ms[2], m -> m.dimension);;
  Print("PerfectGroup(", spec[1], ",", spec[2], "): irreducible GF(7)-module dims (<=7): ",
        Collected(dims), "\n");
od;
QUIT;
