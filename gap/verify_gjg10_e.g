for p in [5, 7] do
  Print("p = ", p, ":\n");
  for i in [3, 8, 9, 10] do
    G := SmallGroup(p^4, i);
    F := FrattiniSubgroup(G);
    Print("  id ", i, ": |Phi| = ", Size(F), "  Phi-type = ", AbelianInvariants(F),
          "  G/Phi rank = ", Length(AbelianInvariants(G/F)), "\n");
  od;
od;
QUIT;
