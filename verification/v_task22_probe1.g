# v_task22_probe1.g -- explore fastest faithful permutation reps for
# Sp6(2), U4(2), A7, G2(3) before committing to full census scripts.

Print("=== probe1: representation options ===\n");

LoadPackage("atlasrep");

t0 := Runtime();
g := AtlasGroup("S6(2)");
Print("AtlasGroup(S6(2)): degree=", NrMovedPoints(g), " order=", Size(g), " time=", Runtime()-t0, "\n");

t0 := Runtime();
g2 := Sp(6,2);
Print("Sp(6,2) matrix group: order=", Size(g2), " time=", Runtime()-t0, "\n");

t0 := Runtime();
gu := AtlasGroup("U4(2)");
if gu = fail then
  Print("AtlasGroup(U4(2)) = fail\n");
else
  Print("AtlasGroup(U4(2)): degree=", NrMovedPoints(gu), " order=", Size(gu), " time=", Runtime()-t0, "\n");
fi;

t0 := Runtime();
ga7 := AlternatingGroup(7);
Print("A7 natural: degree=", NrMovedPoints(ga7), " order=", Size(ga7), " time=", Runtime()-t0, "\n");

t0 := Runtime();
gg2 := AtlasGroup("G2(3)");
if gg2 = fail then
  Print("AtlasGroup(G2(3)) = fail\n");
else
  Print("AtlasGroup(G2(3)): degree=", NrMovedPoints(gg2), " order=", Size(gg2), " time=", Runtime()-t0, "\n");
fi;

Print("=== DONE probe1 ===\n");
