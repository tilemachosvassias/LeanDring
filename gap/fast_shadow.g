G := SmallGroup(3125, 68);
cc := ConjugacyClassesSubgroups(G);
n := Length(cc);
Print("Total classes: ", n, "\n");
invs := List(cc, C -> [ Size(Representative(C)), AbelianInvariants(Representative(C)), Size(Normalizer(G, Representative(C))) ]);
Print("Unique invariants: ", Length(Set(invs)), "\n");
