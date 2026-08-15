# psn census of SL(2,q) (all nontrivial perfect subgroups contain -1)
psn := function(P)
  local reps, hits, U, N;
  reps := RepresentativesPerfectSubgroups(P);
  hits := [];
  for U in reps do
    if Size(U) > 1 then
      N := Normalizer(P,U);
      if Size(N) = Size(U) then Add(hits, Size(U)); fi;
    fi;
  od;
  Sort(hits);
  return hits;
end;;
for q in [5,7,9,11,13,17,19,23,25,27,29,31,49,81,121] do
  G := Image(IsomorphismPermGroup(SL(2,q)));;
  h := psn(G);;
  Print("q=", q, "  |SL2(q)|=", Size(G), "  psn=", Length(h), "  orders=", h, "\n");
od;
QUIT;
