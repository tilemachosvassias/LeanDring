Print("=== Route 2d: probe RepresentativesPerfectSubgroups / PerfectResiduum on small groups ===\n");

Print("--- PerfectResiduum(A5) ---\n");
A5 := AlternatingGroup(5);
Print(PerfectResiduum(A5), "\n");

Print("--- PerfectResiduum(S5) ---\n");
S5 := SymmetricGroup(5);
r := PerfectResiduum(S5);
Print(r, " order=", Size(r), "\n");

Print("--- RepresentativesPerfectSubgroups(S5) ---\n");
rp := RepresentativesPerfectSubgroups(S5);
Print(rp, "\n");

Print("--- RepresentativesPerfectSubgroups signature check on A5 ---\n");
rp2 := RepresentativesPerfectSubgroups(A5);
Print(rp2, "\n");

Print("--- Try on S6(2), order 1451520, small enough ---\n");
S62 := SymmetricGroup(6);
Print("dummy S6 sanity, not S6(2)\n");

Print("=== done route2d ===\n");
