IsMeta := G -> ForAny(NormalSubgroups(G), N -> IsCyclic(N) and IsCyclic(G/N));
key := function(t)
  return [ SortedList(OrdersClassRepresentatives(t)),
           SortedList(SizesCentralizers(t)),
           SortedList(List(Irr(t),Degree)) ];
end;
for n in [16,32,64,128] do
  ids := Filtered([1..NrSmallGroups(n)], i -> IsMeta(SmallGroup(n,i)));
  tabs := List(ids, i -> CharacterTable(SmallGroup(n,i)));
  keys := List(tabs, key);
  twins := [];
  for i in [1..Length(ids)] do for j in [i+1..Length(ids)] do
    if keys[i]=keys[j]
       and TransformingPermutationsCharacterTables(tabs[i],tabs[j])<>fail then
      Add(twins, [ids[i],ids[j]]);
    fi;
  od; od;
  Print("order ", n, ": #metacyclic=", Length(ids),
        "  char-power-map twins=", Length(twins),
        Concatenation("  ", String(twins)), "\n");
od;
QUIT;
