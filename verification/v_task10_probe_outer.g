Print("=== Probe: outer automorphism access for O7(3) and S6(3) ===\n");
LoadPackage("atlasrep");
Print("--- O7(3).2 ---\n");
info := AGR.InfoForName("O7(3).2");
Print(info, "\n");
Print("AllAtlasGeneratingSetInfos O7(3).2: ", AllAtlasGeneratingSetInfos("O7(3).2"), "\n");

Print("--- S6(3).2 ---\n");
info2 := AGR.InfoForName("S6(3).2");
Print(info2, "\n");
Print("AllAtlasGeneratingSetInfos S6(3).2: ", AllAtlasGeneratingSetInfos("S6(3).2"), "\n");
Print("=== done ===\n");
