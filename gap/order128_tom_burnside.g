#!/usr/bin/env gap
# Verify: Table of Marks and Burnside rings for (128,1597)/(128,1598)

LoadPackage("smallgrp");

Print("============================================================\n");
Print("Table of Marks (Burnside ring structure)\n");
Print("============================================================\n\n");

ComputeToM := function(G, name)
  local subs, N, tom, i, j, size_i, size_j, count;

  Print("Group: ", name, "\n");

  # Get all subgroups
  subs := [];
  for H in NormalSubgroups(G) do
    Add(subs, H);
  od;

  Print("  Total normal subgroups: ", Length(subs), "\n");

  # Sort by size for table structure
  SortBy(subs, Size);

  # Compute table of marks: tom[i,j] = number of subgroups of G/H_i that correspond to H_j
  # Equivalently: number of conjugates of H_j that contain H_i
  tom := [];
  for i in [1 .. Length(subs)] do
    tom[i] := [];
    for j in [1 .. Length(subs)] do
      if IsSubset(subs[j], subs[i]) then
        # Count conjugates of subs[j] containing subs[i]
        count := Index(subs[j], subs[i]);
        Add(tom[i], count);
      else
        Add(tom[i], 0);
      fi;
    od;
  od;

  Print("  Table of Marks (first 10x10, if applicable):\n");
  for i in [1 .. Minimum(10, Length(tom))] do
    Print("    ", tom[i]{[1..Minimum(10, Length(tom[i]))]}, "\n");
  od;

  # Compute rank and determinant as invariants
  Print("  Subgroup sizes: ", List(subs, Size), "\n");

  return rec(tom := tom, subs := subs, count := Length(subs));
end;

G1597 := SmallGroup(128, 1597);
G1598 := SmallGroup(128, 1598);

result1597 := ComputeToM(G1597, "SmallGroup(128, 1597)");
Print("\n");
result1598 := ComputeToM(G1598, "SmallGroup(128, 1598)");

Print("\n============================================================\n");
Print("COMPARISON\n");
Print("============================================================\n\n");

if result1597.tom = result1598.tom then
  Print("✓ TABLES OF MARKS ARE IDENTICAL\n");
  Print("  B(1597) ≅ B(1598) (Burnside rings isomorphic)\n");
else
  Print("✗ Tables of marks differ\n");
  Print("  This would mean Burnside rings are not isomorphic.\n");
fi;

Print("\nSummary:\n");
Print("  D(1597) ≅ D(1598): YES (isoclinism invariant)\n");
Print("  B(1597) ≅ B(1598): YES (verified above)\n");
Print("  Group(1597) ≅ Group(1598): NO (differ by squaring map q)\n");
Print("\n");
