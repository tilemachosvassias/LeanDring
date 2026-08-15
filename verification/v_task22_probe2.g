# v_task22_probe2.g -- find a permutation representation for G2(3)
LoadPackage("atlasrep");

Print("=== probe2: G2(3) rep options ===\n");
DisplayAtlasInfo("G2(3)");

Print("--- trying explicit perm request ---\n");
g := AtlasGroup("G2(3)", IsPermGroup, true);
if g = fail then
  Print("AtlasGroup(G2(3), IsPermGroup,true) = fail\n");
else
  Print("degree=", NrMovedPoints(g), " order=", Size(g), "\n");
fi;

Print("=== DONE probe2 ===\n");
