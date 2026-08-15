# v_task17_probe2.g -- exact perfect-subgroup census + self-normalizing test
# for each SMALL twin factor, individually inside its own group.
# This determines, for each factor F, the "own-factor p.s.n." set and the
# full list of perfect-subgroup isomorphism types (for later Goursat/diagonal
# analysis across factor pairs).

ReportFactor := function(name, G)
  local t0, reps, u, cnt, isSelfNorm, nrm;
  Print("\n=== ", name, " (order ", Size(G), ") ===\n");
  t0 := Runtime();
  reps := RepresentativesPerfectSubgroups(G);
  Print("  RepresentativesPerfectSubgroups: ", Length(reps), " classes, time(ms)=", Runtime()-t0, "\n");
  cnt := 0;
  for u in reps do
    nrm := Normalizer(G, u);
    isSelfNorm := (Size(nrm) = Size(u));
    if isSelfNorm and Size(u) > 1 then
      cnt := cnt + 1;
    fi;
    Print("    order=", Size(u), "  StructureDescription=", StructureDescription(u),
          "  selfnorm_in_own_factor=", isSelfNorm, "\n");
  od;
  Print("  --> own-factor p.s.n. count (nontrivial): ", cnt, "\n");
  return reps;
end;;

r_pgl7 := ReportFactor("PGL(2,7)", PGL(2,7));;
r_pgl11 := ReportFactor("PGL(2,11)", PGL(2,11));;
r_s5 := ReportFactor("S5", SymmetricGroup(5));;
r_s7 := ReportFactor("S7", SymmetricGroup(7));;
r_a8 := ReportFactor("A8", AlternatingGroup(8));;
r_s8 := ReportFactor("S8", SymmetricGroup(8));;

Print("\n=== DONE probe2 ===\n");
