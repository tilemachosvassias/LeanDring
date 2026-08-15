# Audit §7o's oversized-shape example: "Q16/<z> = D8 with 11 classes vs 9".
# Check ALL normal-subgroup quotients of Q16 and their #subgroup classes,
# and separately Q32/Z, to locate where the 11-class dihedral actually lives.

clsN := G -> Length(OrdersTom(TableOfMarks(G)));

Q16 := SmallGroup(16,9);
Print("Q16 = ", StructureDescription(Q16), ", #classes = ", clsN(Q16), "\n");
Print("All quotients Q16/N (N normal) and their #subgroup classes:\n");
for N in NormalSubgroups(Q16) do
  Q := FactorGroup(Q16, N);
  Print("   |N|=", Size(N), " -> Q16/N = ", StructureDescription(Q),
        " (order ", Size(Q), "), #classes = ", clsN(Q), "\n");
od;
Print("MAX #classes over all proper quotients of Q16: ",
      Maximum(List(Filtered(NormalSubgroups(Q16), N -> Size(N) > 1),
                   N -> clsN(FactorGroup(Q16, N)))), "\n");

Print("\nQ32 = generalized quaternion order 32:\n");
Q32 := SmallGroup(32, 20);   # Q32 (verify structure below)
Print("   SmallGroup(32,20) = ", StructureDescription(Q32),
      ", #classes = ", clsN(Q32), "\n");
z := Centre(Q32);
Print("   Q32/Z = ", StructureDescription(FactorGroup(Q32, z)),
      " (order ", Size(FactorGroup(Q32,z)), "), #classes = ",
      clsN(FactorGroup(Q32, z)), "\n");
# also find the actual generalized quaternion of order 32 by name
for id in [1..NumberSmallGroups(32)] do
  if StructureDescription(SmallGroup(32,id)) = "Q32" then
    G := SmallGroup(32,id);
    Print("   Q32 is SmallGroup(32,", id, "); Q32/Z = ",
          StructureDescription(FactorGroup(G, Centre(G))),
          ", its #classes = ", clsN(FactorGroup(G, Centre(G))), "\n");
  fi;
od;

QUIT;
