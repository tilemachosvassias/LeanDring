Print("=== Setup outer automorphism for O7(3) via O7(3).2 on 351 points ===\n");
LoadPackage("atlasrep");
G1 := AtlasGroup("O7(3)");
G1ext := AtlasGroup("O7(3).2");
Print("Size G1: ", Size(G1), "  Size G1ext: ", Size(G1ext), "\n");
Print("NrMovedPoints G1: ", NrMovedPoints(G1), "  NrMovedPoints G1ext: ", NrMovedPoints(G1ext), "\n");
Print("Is G1 subgroup of G1ext (as perm groups on same points)? ");
issub := IsSubset(G1ext, G1);
Print(issub, "\n");
if issub then
  Print("Great - can extract outer element.\n");
  g := First(G1ext, x -> not x in G1);
  Print("Found outer element g. Order: ", Order(g), "\n");
fi;
Print("=== done outer setup ===\n");
