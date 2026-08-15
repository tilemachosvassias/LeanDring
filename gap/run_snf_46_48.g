for g in ["G32_46", "G32_47", "G32_48"] do
  Read(Concatenation("results/", g, "_mat.g"));
  Print("SNF for ", g, ":\n");
  Print(ElementaryDivisorsMat(DFMAT), "\n");
od;
QUIT;
