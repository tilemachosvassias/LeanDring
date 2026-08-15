key := t -> [ SortedList(OrdersClassRepresentatives(t)),
              SortedList(List(Irr(t),Degree)),
              SortedList(SizesCentralizers(t)) ];
n := 128;; m := NrSmallGroups(n);;
tabs := List([1..m], i -> CharacterTable(SmallGroup(n,i)));;
keys := List(tabs, key);;
seen := []; buckets := [];
for i in [1..m] do
  p := Position(seen, keys[i]);
  if p = fail then Add(seen, keys[i]); Add(buckets, [i]);
  else Add(buckets[p], i); fi;
od;
twins := [];
for b in buckets do
  if Length(b) >= 2 then
    for i in [1..Length(b)] do for j in [i+1..Length(b)] do
      if TransformingPermutationsCharacterTables(tabs[b[i]],tabs[b[j]])<>fail then
        Add(twins, [b[i],b[j]]); fi;
    od; od;
  fi;
od;
Print("RESULT order 128: ",m," groups, ",Length(buckets)," buckets, char-power-map twins = ",
      Length(twins),"  examples: ",twins{[1..Minimum(8,Length(twins))]},"\n");
QUIT;
