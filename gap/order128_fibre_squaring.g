#!/usr/bin/env gap
# Check fibre-squaring tower: does psi_2 action differ between the groups?
# psi_2 is the fibre-squaring endomorphism on species

LoadPackage("smallgrp");

Print("============================================================\n");
Print("Fibre-squaring structure: D_F tower analysis\n");
Print("============================================================\n\n");

AnalyzeSquaringTower := function(G, name)
  local cc, i, rep, order, psi2_target;

  Print("Group: ", name, "\n");

  cc := ConjugacyClasses(G);
  Print("  ", Length(cc), " conjugacy classes\n");

  # psi_2: (H, lambda) -> (H, lambda^2)
  # So for order-2/4 elements, squaring either stays in same class or moves
  Print("\n  Elements and their squarings:\n");
  Print("    rep | order | cc-size | [rep^2 in same cc?]\n");
  for i in [1 .. Minimum(15, Length(cc))] do
    rep := Representative(cc[i]);
    Print("    ", i, "   | ", Order(rep), "     | ",
          Size(cc[i]), "       | ");

    # Check if rep^2 is in the same conjugacy class
    if rep^2 in cc[i] then
      Print("YES\n");
    else
      Print("NO\n");
    fi;
  od;

  Print("\n");
end;

G1597 := SmallGroup(128, 1597);
G1598 := SmallGroup(128, 1598);

AnalyzeSquaringTower(G1597, "SmallGroup(128, 1597)");
Print("\n");
AnalyzeSquaringTower(G1598, "SmallGroup(128, 1598)");

Print("============================================================\n");
Print("Comparison: which conjugacy classes close under squaring?\n");
Print("============================================================\n");

ComputeClosureCounts := function(G)
  local cc, closed_count, i;
  cc := ConjugacyClasses(G);
  closed_count := 0;
  for i in [1 .. Length(cc)] do
    if Representative(cc[i])^2 in cc[i] then
      closed_count := closed_count + 1;
    fi;
  od;
  return closed_count;
end;

count1597 := ComputeClosureCounts(G1597);
count1598 := ComputeClosureCounts(G1598);

Print("Group 1597: ", count1597, " classes closed under squaring\n");
Print("Group 1598: ", count1598, " classes closed under squaring\n");

if count1597 = count1598 then
  Print("✗ Squaring closure counts are identical\n");
else
  Print("✓ Squaring closure counts DIFFER\n");
fi;
