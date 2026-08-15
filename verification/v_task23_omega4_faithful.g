# faithful (non-projective) psn census of Omega(+1,4,q): center is C2, must NOT be quotiented
for q in [5,7,9,11] do
  G := Omega(1,4,q);;
  P := Image(ActionHomomorphism(G, Filtered(GF(q)^4, v -> v <> Zero(GF(q)^4)), OnRight));;
  Print("Omega(+,4,",q,") faithful deg ", NrMovedPoints(P), " size ", Size(P), "\n");
  reps := RepresentativesPerfectSubgroups(P);;
  hits := [];
  for U in reps do
    if Size(U) > 1 and Size(Normalizer(P,U)) = Size(U) then Add(hits, Size(U)); fi;
  od;
  Print("   psn=", Length(hits), " orders=", SortedList(hits), "\n");
od;
QUIT;
