#!/usr/bin/env gap
# Debug: check the structure of these groups

LoadPackage("smallgrp");

G1597 := SmallGroup(128, 1597);
G1598 := SmallGroup(128, 1598);

Print("SmallGroup(128, 1597):\n");
Print("  Order: ", Order(G1597), "\n");
Print("  AbelianInvariants: ", AbelianInvariants(G1597), "\n");
Print("  Center: ", Order(Center(G1597)), "\n");
Print("  Commutator: ", Order(DerivedSubgroup(G1597)), "\n");
Print("  Abelianization rank: ", Length(AbelianInvariants(G1597)), "\n");

Print("\nSmallGroup(128, 1598):\n");
Print("  Order: ", Order(G1598), "\n");
Print("  AbelianInvariants: ", AbelianInvariants(G1598), "\n");
Print("  Center: ", Order(Center(G1598)), "\n");
Print("  Commutator: ", Order(DerivedSubgroup(G1598)), "\n");
Print("  Abelianization rank: ", Length(AbelianInvariants(G1598)), "\n");

# Check the first element's presence
Print("\n\nDetailed check for 1597:\n");
subs := [];
for H in NormalSubgroups(G1597) do
  if Size(G1597) / Size(H) = 2 then
    Add(subs, H);
  fi;
od;

Print("Found ", Length(subs), " index-2 normal subgroups\n\n");

cc := ConjugacyClasses(G1597);
Print("First 5 conjugacy classes:\n");
for i in [1..5] do
  rep := Representative(cc[i]);
  count := 0;
  for H in subs do
    if rep in H then count := count + 1; fi;
  od;
  Print("  Class ", i, " (size ", Size(cc[i]),
        ", rep order ", Order(rep),
        "): in ", count, " subgroups\n");
od;
