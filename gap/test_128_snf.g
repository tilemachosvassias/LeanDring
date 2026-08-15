Read("gap/dring_sieve_standalone.g");
Read("gap/df_trace_corrected_snf.g");

G_plus := ExtraspecialGroup(128, "+");
G_minus := ExtraspecialGroup(128, "-");

cls_plus := SpeciesClassesD(G_plus);
Print("128+ number of species classes (n): ", Length(cls_plus), "\n");

cls_minus := SpeciesClassesD(G_minus);
Print("128- number of species classes (n): ", Length(cls_minus), "\n");

QUIT;
