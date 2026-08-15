G := SmallGroup(3125, 68);
cc := ConjugacyClassesSubgroups(G);
H := Representative(cc[50]);
Print(PositionClass(cc, H), "\n");
