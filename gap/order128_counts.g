#!/usr/bin/env gap
# Compute the RAW counts (not just mod 2)

LoadPackage("smallgrp");

Print("============================================================\n");
Print("Order-128 norm RAW COUNTS (not mod 2)\n");
Print("============================================================\n\n");

ComputeNormCounts := function(G, name)
  local cc, subs, counts, i, rep, H, count;

  Print("Group: ", name, "\n");

  subs := [];
  for H in NormalSubgroups(G) do
    if Size(G) / Size(H) = 2 then
      Add(subs, H);
    fi;
  od;

  cc := ConjugacyClasses(G);
  counts := [];

  for i in [1 .. Length(cc)] do
    rep := Representative(cc[i]);
    count := 0;
    for H in subs do
      if rep in H then
        count := count + 1;
      fi;
    od;
    Add(counts, count);
  od;

  Print("  ", Length(subs), " index-2 subgroups\n");
  Print("  ", Length(cc), " conjugacy classes\n");
  Print("  Norm counts: ", counts, "\n");
  Print("  Norm counts (mod 2): ", List(counts, x -> x mod 2), "\n");

  return counts;
end;

G1597 := SmallGroup(128, 1597);
G1598 := SmallGroup(128, 1598);

counts1597 := ComputeNormCounts(G1597, "SmallGroup(128, 1597)");
Print("\n");
counts1598 := ComputeNormCounts(G1598, "SmallGroup(128, 1598)");

Print("\n============================================================\n");
Print("COMPARISON\n");
Print("============================================================\n");

if counts1597 = counts1598 then
  Print("✗ Raw counts are IDENTICAL\n");
else
  Print("✓ Raw counts DIFFER\n");
  Print("  First 10 differences:\n");
  for i in [1 .. Minimum(10, Length(counts1597))] do
    if counts1597[i] <> counts1598[i] then
      Print("    Position ", i, ": ", counts1597[i], " vs ", counts1598[i], "\n");
    fi;
  od;
fi;

Print("\n");
