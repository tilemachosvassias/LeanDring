Print("=== Route 2a: AtlasRep probe ===\n");
r := LoadPackage("atlasrep");
Print("atlasrep loaded: ", r, "\n");

Print("--- O7(3) ---\n");
info := AGR.InfoForName("O7(3)");
Print("AGR.InfoForName(O7(3)): ", info, "\n");
Print("AllAtlasGeneratingSetInfos O7(3): ", AllAtlasGeneratingSetInfos("O7(3)"), "\n");

Print("--- S6(3) ---\n");
info2 := AGR.InfoForName("S6(3)");
Print("AGR.InfoForName(S6(3)): ", info2, "\n");
Print("AllAtlasGeneratingSetInfos S6(3): ", AllAtlasGeneratingSetInfos("S6(3)"), "\n");

Print("=== done route2a probe ===\n");
