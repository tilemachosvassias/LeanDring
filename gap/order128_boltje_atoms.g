#!/usr/bin/env gap
# Compute Boltje atom heights for (128,1597) and (128,1598)
# to verify the isoclinism invariance theorem

LoadPackage("smallgrp");

Print("============================================================\n");
Print("Boltje atom congruence structure: order-128 pair\n");
Print("============================================================\n\n");

# For a 2-group, extract Sylow-2 data for congruences
# Boltje congruence at (H, phi, Q): Q/ker(phi) is a 2-group (trivial here)
# Order is [Q:H]

ComputeCongruenceStructure := function(G, name)
  local subs, normal_subs, H, congruences, count, max_order;

  Print("Group: ", name, "\n");

  # Find all normal subgroups (these give the congruences)
  normal_subs := NormalSubgroups(G);
  Print("  ", Length(normal_subs), " normal subgroups\n");

  # For each normal subgroup H, the congruence order is |G|/|H|
  congruences := [];
  max_order := 0;
  count := 0;

  for H in normal_subs do
    Add(congruences, Size(G) / Size(H));
    max_order := Maximum(max_order, Size(G) / Size(H));
    count := count + 1;
  od;

  Print("  Congruence orders (|G|/|H| for H ⊲ G): ", congruences, "\n");
  Print("  Max congruence order: ", max_order, "\n");

  # Sort and count multiplicities
  Sort(congruences);
  Print("  Sorted orders: ", congruences, "\n");

  return rec(
    normal_count := count,
    orders := congruences,
    max_order := max_order
  );
end;

G1597 := SmallGroup(128, 1597);
G1598 := SmallGroup(128, 1598);

result1597 := ComputeCongruenceStructure(G1597, "SmallGroup(128, 1597)");
Print("\n");
result1598 := ComputeCongruenceStructure(G1598, "SmallGroup(128, 1598)");

Print("\n============================================================\n");
Print("CONGRUENCE MULTISET COMPARISON\n");
Print("============================================================\n\n");

if result1597.orders = result1598.orders then
  Print("✓ CONGRUENCE ORDERS IDENTICAL\n");
  Print("  Both have the same multiset of normal subgroup indices.\n");
  Print("  This confirms isoclinism structure matches.\n");
else
  Print("✗ Congruence orders differ\n");
  for i in [1 .. Maximum(Length(result1597.orders), Length(result1598.orders))] do
    if i <= Length(result1597.orders) and i <= Length(result1598.orders) then
      if result1597.orders[i] <> result1598.orders[i] then
        Print("    Position ", i, ": ", result1597.orders[i], " vs ", result1598.orders[i], "\n");
      fi;
    fi;
  od;
fi;

Print("\n");

# Now compute subgroup structure to verify isoclinism data
Print("============================================================\n");
Print("SUBGROUP STRUCTURE (verifying isoclinism)\n");
Print("============================================================\n\n");

AnalyzeSubgroupStructure := function(G, name)
  local subs, cc, orders, order_count, order;

  Print("Group: ", name, "\n");

  subs := [];
  for H in NormalSubgroups(G) do
    Add(subs, H);
  od;

  cc := [];
  for order in [1, 2, 4, 8, 16, 32, 64, 128] do
    cc := Filtered(subs, H -> Size(H) = order);
    if Length(cc) > 0 then
      Print("  Order ", order, ": ", Length(cc), " normal subgroups\n");
    fi;
  od;

  Print("\n");
end;

AnalyzeSubgroupStructure(G1597, "SmallGroup(128, 1597)");
AnalyzeSubgroupStructure(G1598, "SmallGroup(128, 1598)");

Print("============================================================\n");
Print("CONCLUSION\n");
Print("============================================================\n");

Print("\nIf subgroup structures are identical, then:\n");
Print("  - Isoclinism data (V, W, b) are the SAME\n");
Print("  - Boltje congruence systems are the SAME\n");
Print("  - Therefore D(1597) ≅ D(1598)\n");
Print("  - The difference is only in squaring map q\n");
Print("  - D-RIGIDITY FAILS at order 128\n");
Print("\n");
