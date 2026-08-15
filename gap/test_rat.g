Read("gap/dring_sieve_standalone.g");
G := SmallGroup(8, 1);
cls := SpeciesClassesD(G);
T := SpeciesTableD(G, cls);
Print("T[1][1] = ", T[1][1], "\n");
Print("IsRat? ", IsRat(T[1][1]), "\n");
Print("IsInt? ", IsInt(T[1][1]), "\n");
QUIT;
