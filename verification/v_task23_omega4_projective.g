# Orthogonal rank-2: psn of Omega(+/-,4,q) computed INTERNALLY (glue handled separately)
for q in [5,7,9,11,13,19] do
  for e in [1,-1] do
    G := Omega(e,4,q);;
    hom := ActionHomomorphism(G, NormedRowVectors(GF(q)^4), OnLines);;
    P := Image(hom);;
    reps := RepresentativesPerfectSubgroups(P);;
    hits := [];
    for U in reps do
      if Size(U) > 1 and Size(Normalizer(P,U)) = Size(U) then Add(hits, Size(U)); fi;
    od;
    Print("Omega(", e, ",4,", q, ") |G|=", Size(G), " (proj deg ", NrMovedPoints(P),
          ", |image|=", Size(P), ")  psn=", Length(hits), " orders=", SortedList(hits), "\n");
  od;
od;
QUIT;
