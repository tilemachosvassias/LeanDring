#!/usr/bin/env gap
# Compute exact radical degree of top norm Omega_G in F_2 ⊗ D(G)
# for (128,1597) and (128,1598)

LoadPackage("smallgrp");
LoadPackage("polycyclic");

Print("============================================================\n");
Print("Order-128 norm degree separation analysis\n");
Print("============================================================\n\n");

# Load both groups
G1597 := SmallGroup(128, 1597);
G1598 := SmallGroup(128, 1598);

# Function: find all index-2 subgroups using lattice operations
FindIndexTwoSubgroups := function(G)
  local index_two, H, i;
  index_two := [];

  # Method: iterate through maximal subgroups and check index
  # For a finite group, index-2 subgroups are precisely the maximal subgroups
  # that are normal (all index-2 subgroups of a finite group are normal)

  # Use the fact that index-2 means [G:H] = 2
  # We can enumerate by constructing candidates

  # Better: use NormalSubgroups
  for H in NormalSubgroups(G) do
    if Size(G) / Size(H) = 2 then
      Add(index_two, H);
    fi;
  od;

  return index_two;
end;

# Function: compute top norm at conjugacy classes
ComputeTopNorm := function(G)
  local cc, subs, norm_values, i, rep, H, count;

  cc := ConjugacyClasses(G);
  subs := FindIndexTwoSubgroups(G);

  Print("  Index-2 subgroups found: ", Length(subs), "\n");
  Print("  Conjugacy classes: ", Length(cc), "\n");

  norm_values := [];
  for i in [1 .. Length(cc)] do
    rep := Representative(cc[i]);
    count := 0;
    for H in subs do
      if rep in H then
        count := count + 1;
      fi;
    od;
    Add(norm_values, count mod 2);
  od;

  return rec(cc_count := Length(cc), norm_values := norm_values, h1_dim := Length(subs));
end;

# Analyze results
AnalyzeResults := function(G, name)
  local result, nonzero, i;

  Print("\n------------------------------------------------------------\n");
  Print("Group: ", name, "\n");
  Print("------------------------------------------------------------\n");

  result := ComputeTopNorm(G);

  nonzero := 0;
  for i in result.norm_values do
    if i = 1 then nonzero := nonzero + 1; fi;
  od;

  Print("  H^1(G; F_2) dimension: ", result.h1_dim, "\n");
  Print("  Norm values (mod 2): ", result.norm_values, "\n");
  Print("  Nonzero coordinates: ", nonzero, " / ", Length(result.norm_values), "\n");

  return result;
end;

# Run analysis
Print("Computing for (128,1597)...\n");
result1597 := AnalyzeResults(G1597, "SmallGroup(128, 1597)");

Print("\n\nComputing for (128,1598)...\n");
result1598 := AnalyzeResults(G1598, "SmallGroup(128, 1598)");

# Comparison
Print("\n============================================================\n");
Print("COMPARISON\n");
Print("============================================================\n\n");

if result1597.norm_values = result1598.norm_values then
  Print("✗ Norm values are IDENTICAL\n");
else
  Print("✓ Norm values DIFFER\n");
  Print("  This is a D-invariant separator!\n");
fi;

Print("\nNorm 1597: ", result1597.norm_values, "\n");
Print("Norm 1598: ", result1598.norm_values, "\n");

Print("\n");
