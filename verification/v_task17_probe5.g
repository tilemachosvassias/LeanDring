# v_task17_probe5.g -- own p.s.n. census for: L3(3).2 (Suz factor),
# L3(3) bare (Th factor, expect {1,L3(3)} only, minimal simple),
# PSL(2,125) (Th factor, unextended ambient).

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
    Print("    order=", Size(u), "  selfnorm_in_own_factor=", isSelfNorm, "\n");
  od;
  Print("  --> own-factor p.s.n. count (nontrivial): ", cnt, "\n");
  return reps;
end;;

Print("=== constructing Aut(L3(3)) = L3(3).2 via AutomorphismGroup ===\n");
t0 := Runtime();
autL33 := AutomorphismGroup(PSL(3,3));;
Print("AutomorphismGroup(PSL(3,3)) order=", Size(autL33), " time=", Runtime()-t0, "\n");
t0 := Runtime();
permAutL33 := Image(IsomorphismPermGroup(autL33));;
Print("converted to perm group, degree=", NrMovedPoints(permAutL33), " time=", Runtime()-t0, "\n");

r_l33_2 := ReportFactor("L3(3).2 = Aut(L3(3))", permAutL33);;

r_l33 := ReportFactor("L3(3) bare", PSL(3,3));;

t0 := Runtime();;
r_l2125 := ReportFactor("L2(125) bare", PSL(2,125));;
Print("PSL(2,125) total probe time(ms)=", Runtime()-t0, "\n");
