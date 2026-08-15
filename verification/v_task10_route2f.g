Print("=== Route 2f: PerfectResiduum for all accessible maximals ===\n");
LoadPackage("atlasrep");

structO := [ "2.U4(3).2_2", "3^5:U4(2):2", "L4(3).2_2", "G2(3)", "G2(3)",
    "3^(3+3):L3(3)", "S6(2)", "S6(2)", "3^(1+6)_+:(2A4xA4).2", "S9", "S9",
    "(2^2xU4(2)):2", "2^6:A7", "S6xS4", "(A4x2(A4xA4).2).2" ];

Print("--- O7(3) maximal subgroups: PerfectResiduum orders ---\n");
G1 := AtlasGroup("O7(3)");
for i in [1..15] do
  M := AtlasSubgroup("O7(3)", i);
  if M = fail then
    Print(i, " (", structO[i], "): NO SLP - skip\n");
  else
    R := PerfectResiduum(M);
    Print(i, " (", structO[i], "): |M|=", Size(M), " |M'|=|R|=", Size(R),
          " M perfect: ", Size(R)=Size(M), "\n");
  fi;
od;

structS := [ "3^(1+4)_+.2U4(2)", "3^6:L3(3)", "3^(3+4):2(S4xA4)",
    "2.(A4xU4(2))", "2^(2+6):3^3:S3", "L2(27).3", "2xU3(3).2",
    "L3(3).2", "L2(13)", "L2(13)", "A5" ];

Print("--- S6(3) maximal subgroups: PerfectResiduum orders ---\n");
G2 := AtlasGroup("S6(3)");
for i in [1..11] do
  M := AtlasSubgroup("S6(3)", i);
  if M = fail then
    Print(i, " (", structS[i], "): NO SLP - skip\n");
  else
    R := PerfectResiduum(M);
    Print(i, " (", structS[i], "): |M|=", Size(M), " |M'|=|R|=", Size(R),
          " M perfect: ", Size(R)=Size(M), "\n");
  fi;
od;

Print("=== done route2f ===\n");
