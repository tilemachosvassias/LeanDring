# Does ANY 2-group have a proper quotient with strictly MORE subgroup
# classes than itself?  This decides whether section 7o's stratum-1
# "correction" (oversized Burnside-shaped retracts B(G/N) with
# #classes(G/N) > #classes(G) exist) is warranted at all.
# If none up to order 64, the phenomenon does not occur in that range and
# section 7o's motivating example (Q16/<z>) is simply mistaken.

clsN := G -> Length(OrdersTom(TableOfMarks(G)));

Print("Scanning for 2-groups with a proper quotient having MORE ",
      "subgroup classes than the group:\n");
found := 0;
for m in [2,3,4,5] do   # orders 4..32 (64 quotient ToMs are heavy)
  ord := 2^m;
  for id in [1..NumberSmallGroups(ord)] do
    G := SmallGroup(ord, id);
    cG := clsN(G);
    for N in NormalSubgroups(G) do
      if Size(N) > 1 then
        cQ := clsN(FactorGroup(G, N));
        if cQ > cG then
          found := found + 1;
          Print("   ", StructureDescription(G), " (ord ", ord,
                ", ", cG, " classes) -> quotient ",
                StructureDescription(FactorGroup(G,N)),
                " has ", cQ, " classes (MORE)\n");
        fi;
      fi;
    od;
  od;
od;
Print("Total (G, N) with #classes(G/N) > #classes(G), orders 4..32: ",
      found, "\n");
if found = 0 then
  Print("=> NO oversized-by-class quotient exists in this range; ",
        "section 7o stratum-1 'correction' is UNsupported here, and ",
        "rank bounds DO exclude oversized Burnside shapes (7n stood).\n");
fi;

QUIT;
