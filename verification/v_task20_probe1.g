# v_task20_probe1.g -- sanity checks: Aut() and Socle() for each simple
# factor needed for the A9..A12 twins (v_task19 witnesses), before
# building the full extension groups.

Print("=== A5 (n=9 factor 1) ===\n");
a5 := AlternatingGroup(5);;
autA5 := SymmetricGroup(5);; # Aut(A5) = S5, standard (n<>6)
Print("|A5|=", Size(a5), " |Aut(A5)|=", Size(autA5), "\n");
soc := Socle(autA5);;
Print("Socle(Aut(A5)) order = ", Size(soc), " (expect 60)\n");

Print("\n=== L2(8) (n=9 factor 2) ===\n");
l28 := PSL(2,8);;
Print("|L2(8)|=", Size(l28), "\n");
t0 := Runtime();
autl28 := AutomorphismGroup(l28);;
Print("AutomorphismGroup computed, time(ms)=", Runtime()-t0, "\n");
Print("|Aut(L2(8))| = ", Size(autl28), " (expect 1512)\n");
t0 := Runtime();
autl28p := Image(IsomorphismPermGroup(autl28));;
Print("IsomorphismPermGroup done, time(ms)=", Runtime()-t0, " degree=", NrMovedPoints(autl28p), "\n");
soc2 := Socle(autl28p);;
Print("Socle(Aut(L2(8))) order = ", Size(soc2), " (expect 504)\n");

Print("\n=== A6 (n=10 factor 1) ===\n");
a6 := AlternatingGroup(6);;
t0 := Runtime();
auta6 := AutomorphismGroup(a6);;
Print("AutomorphismGroup(A6) computed, time(ms)=", Runtime()-t0, "\n");
Print("|Aut(A6)| = ", Size(auta6), " (expect 1440)\n");
t0 := Runtime();
auta6p := Image(IsomorphismPermGroup(auta6));;
Print("IsomorphismPermGroup done, time(ms)=", Runtime()-t0, " degree=", NrMovedPoints(auta6p), "\n");
soc3 := Socle(auta6p);;
Print("Socle(Aut(A6)) order = ", Size(soc3), " (expect 360)\n");

Print("\n=== A7 (n=10 factor 2, n=11 factor 1) ===\n");
autA7 := SymmetricGroup(7);; # Aut(A7)=S7
Print("|Aut(A7)|=", Size(autA7), " (expect 5040)\n");
soc4 := Socle(autA7);;
Print("Socle(Aut(A7)) order = ", Size(soc4), " (expect 2520)\n");

Print("\n=== M11 (n=11 factor 2) ===\n");
m11 := MathieuGroup(11);;
Print("|M11|=", Size(m11), "\n");
t0 := Runtime();
autm11 := AutomorphismGroup(m11);;
Print("|Aut(M11)| = ", Size(autm11), " (expect 7920, trivial outer) time(ms)=", Runtime()-t0, "\n");

Print("\n=== L2(11) (n=12 factor 1) ===\n");
l211 := PSL(2,11);;
Print("|L2(11)|=", Size(l211), "\n");
t0 := Runtime();
autl211 := AutomorphismGroup(l211);;
Print("AutomorphismGroup(L2(11)) computed, time(ms)=", Runtime()-t0, "\n");
Print("|Aut(L2(11))| = ", Size(autl211), " (expect 1320)\n");
t0 := Runtime();
autl211p := Image(IsomorphismPermGroup(autl211));;
Print("IsomorphismPermGroup done, time(ms)=", Runtime()-t0, " degree=", NrMovedPoints(autl211p), "\n");
soc5 := Socle(autl211p);;
Print("Socle(Aut(L2(11))) order = ", Size(soc5), " (expect 660)\n");

Print("\n=== A9 (n=12 factor 2) ===\n");
autA9 := SymmetricGroup(9);; # Aut(A9)=S9
Print("|Aut(A9)|=", Size(autA9), " (expect 362880)\n");
t0 := Runtime();
soc6 := Socle(autA9);;
Print("Socle(Aut(A9)) order = ", Size(soc6), " (expect 181440) time(ms)=", Runtime()-t0, "\n");

Print("\n=== DONE probe1 ===\n");
