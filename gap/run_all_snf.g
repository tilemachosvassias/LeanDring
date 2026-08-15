for g in ["D4", "Q8", "G32_49", "G32_50"] do
  Read(Concatenation("results/", g, "_mat.g"));
  Print("SNF for ", g, ":\n");
  Print(ElementaryDivisorsMat(DFMAT), "\n");
od;
QUIT;
