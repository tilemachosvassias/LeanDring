# v_task22_psn.g -- perfect self-normalizing (p.s.n.) census for Sp6(2), U4(2), A7
# Method: RepresentativesPerfectSubgroups(G) directly on a faithful permutation
# representation, then filter by Normalizer(G,U) = U. Same method as
# v_task17_u38_census.g (own p.s.n. census).

LoadPackage("atlasrep");

DoCensus := function(name, g)
  local t0, reps, cnt, u, nrm, structs, s, found, i;
  Print("=== Census: ", name, " (degree=", NrMovedPoints(g), " order=", Size(g), ") ===\n");
  t0 := Runtime();
  reps := RepresentativesPerfectSubgroups(g);
  Print(name, ": RepresentativesPerfectSubgroups classes = ", Length(reps), " time=", Runtime()-t0, "\n");
  cnt := 0;
  structs := [];
  for u in reps do
    s := Size(u);
    t0 := Runtime();
    nrm := Normalizer(g, u);
    if Size(nrm) = s and s > 1 then
      cnt := cnt + 1;
      Add(structs, s);
      Print(name, ":   HIT order=", s, " selfnorm=true  StructureDescription=");
      Print(StructureDescription(u), "  (Normalizer time=", Runtime()-t0, ")\n");
    else
      Print(name, ":   order=", s, " selfnorm=", (Size(nrm)=s), " (Normalizer time=", Runtime()-t0, ")\n");
    fi;
  od;
  Print(name, ": TOTAL psn count (nontrivial) = ", cnt, "\n");
  Print("=== END ", name, " ===\n\n");
  return cnt;
end;;

g_sp62 := AtlasGroup("S6(2)");
DoCensus("Sp6(2)", g_sp62);

g_u42 := AtlasGroup("U4(2)");
DoCensus("U4(2)", g_u42);

g_a7 := AlternatingGroup(7);
DoCensus("A7", g_a7);

Print("=== DONE v_task22_psn (Sp6(2)/U4(2)/A7) ===\n");
