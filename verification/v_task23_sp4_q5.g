q := 5;;
G := SP(4,q);;
V := Filtered(GF(q)^4, v -> v <> Zero(GF(q)^4));;
P := Image(ActionHomomorphism(G, V, OnRight));;
Print("Sp4(5) perm degree ", NrMovedPoints(P), " size ", Size(P), "\n");
t := Runtime();;
reps := RepresentativesPerfectSubgroups(P);;
Print("perfect classes: ", Length(reps), "   time ", Runtime()-t, "ms\n");
for U in reps do
  if Size(U) > 1 then
    N := Normalizer(P,U);
    Print("  |U|=", Size(U), " |N|=", Size(N), " PSN=", Size(N)=Size(U), "  ", StructureDescription(U), "\n");
  fi;
od;
QUIT;
