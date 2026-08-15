# The "B-vs-D corner" for the construction route.
# RELEVANT class for D=>B: since D recovers the character table WITH power maps,
# a D=>B counterexample must be a POWER-MAP TWIN (same char table incl. power
# maps), non-isomorphic, with the TABLE OF MARKS (B) DIFFERENT.
# We (i) sanity-check that D8/Q8 (bare Brauer, power maps differ) is NOT a
# power-map twin, and (ii) count power-map twins and their ToM agreement <=64.
# ToM tested by a permutation-invariant proxy; a DIFFERENCE is conclusive.
LogTo("/Users/tilemachosvassias/DissAnalysis/dring-project/results/order128_pairs/twin_tom_corner.out");

tomProxy := function(G)
  local M, cols;
  M := MarksTom(TableOfMarks(G)); cols := TransposedMat(M);
  return SortedList(List([1..Length(M)],
           i -> [SortedList(M[i]), SortedList(cols[i])]));
end;

isPowerMapTwin := function(ti, tj)   # same char table incl. power maps?
  return OrdersClassRepresentatives(ti) <> fail and
         TransformingPermutationsCharacterTables(ti, tj) <> fail and
         SortedList(OrdersClassRepresentatives(ti)) =
         SortedList(OrdersClassRepresentatives(tj));
end;

# (i) sanity check on D8 / Q8
d8 := CharacterTable(SmallGroup(8,3)); q8 := CharacterTable(SmallGroup(8,4));
Print("D8/Q8 power-map twin? ", isPowerMapTwin(d8,q8),
      "  (expected false: element orders differ)\n");
Print("D8 vs Q8 ToM proxy equal? ", tomProxy(SmallGroup(8,3))=tomProxy(SmallGroup(8,4)),
      "  (expected false: B differs)\n\n");

Analyse := function(n)
  local m, tabs, key, i, j, twins, bdiff;
  m := NrSmallGroups(n);
  tabs := List([1..m], i -> CharacterTable(SmallGroup(n,i)));
  # bucket by (element-order multiset, centralizer sizes, degrees): twins share all
  key := i -> [ SortedList(OrdersClassRepresentatives(tabs[i])),
                SortedList(SizesCentralizers(tabs[i])),
                SortedList(List(Irr(tabs[i]), Degree)) ];
  twins := 0; bdiff := [];
  for i in [1..m] do for j in [i+1..m] do
    if key(i) = key(j) and TransformingPermutationsCharacterTables(tabs[i],tabs[j]) <> fail then
      twins := twins + 1;
      if tomProxy(SmallGroup(n,i)) <> tomProxy(SmallGroup(n,j)) then Add(bdiff,[i,j]); fi;
    fi;
  od; od;
  Print("order ", n, ": power-map twins=", twins,
        "  of which B-different=", Length(bdiff),
        Concatenation("  ", String(bdiff)), "\n");
end;

Print("== power-map twins vs table of marks, orders <=64 ==\n");
for n in [8,16,32,64] do Analyse(n); od;
LogTo();
QUIT;
