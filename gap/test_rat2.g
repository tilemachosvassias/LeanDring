Read("gap/dring_sieve_standalone.g");
G := SmallGroup(8, 1);
cls := SpeciesClassesD(G);
T := SpeciesTableD(G, cls);
found := false;
for r in T do for c in r do
  if not IsInt(c) then 
    Print("Not int: ", c, " IsRat? ", IsRat(c), " IsCyc? ", IsCyc(c), "\n"); 
    found := true; 
    break; 
  fi;
od; if found then break; fi; od;
QUIT;
