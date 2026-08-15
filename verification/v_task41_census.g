# v_task41_census.g -- psn census (mult_1) of small simple groups.
# Purpose: decide whether "census-trivial" simple groups (mult_1 = 1, i.e. no
# PROPER perfect self-normalizing subgroup) exist, and characterise them.
# Convention (Mueller / NOTES.md 4af): mult_1 counts G itself.

MultOne := function(G)
  local reps, psn, U;
  reps := RepresentativesPerfectSubgroups(G);
  psn := Filtered(reps, U -> Size(U) > 1 and Size(Normalizer(G,U)) = Size(U));
  return [Length(psn), List(psn, Size)];
end;

Run := function(name, G)
  local r;
  r := MultOne(G);
  Print(name, "  |G|=", Size(G), "  mult1=", r[1], "  psn orders=", r[2], "\n");
end;

Print("# L2(q) family\n");
for q in [5,7,8,9,11,13,16,17,19,23,25,27,29,31,32,37,41,43,49] do
  Run(Concatenation("L2(",String(q),")"), PSL(2,q));
od;

Print("# other small simple groups\n");
Run("L3(2)", PSL(3,2));
Run("L3(3)", PSL(3,3));
Run("L3(4)", PSL(3,4));
Run("U3(3)", PSU(3,3));
Run("U3(4)", PSU(3,4));
Run("Sz(8)", SuzukiGroup(8));
Run("Sp4(3)", PSp(4,3));
Run("A5", AlternatingGroup(5));
Run("A6", AlternatingGroup(6));
Run("A7", AlternatingGroup(7));
Run("A8", AlternatingGroup(8));
Run("A9", AlternatingGroup(9));
Run("M11", MathieuGroup(11));
Run("M12", MathieuGroup(12));

QUIT;
