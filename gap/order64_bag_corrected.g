# requires FusionFieldU from task3_order64_unanchored.g (lines 1-52)
Read("gap/task3_order64_unanchored_func.g");
CorrectBag := function(G)
  local K, orbs, o, bag;
  bag := [];
  for K in ConjugacyClassesSubgroups(G) do
    for o in FusionFieldU(G, Representative(K)) do
      Add(bag, [o.cond, SortedList(o.U)]);
    od;
  od;
  Sort(bag);
  return bag;
end;
for p in [[47,48],[13,14]] do
  b1 := CorrectBag(SmallGroup(64,p[1]));
  b2 := CorrectBag(SmallGroup(64,p[2]));
  Print("(64,",p[1],") vs (64,",p[2],"): bags equal = ", b1=b2, "\n");
  if b1<>b2 then
    d1 := Filtered(b1, x -> not x in b2); d2 := Filtered(b2, x -> not x in b1);
    Print("   only in ",p[1],": ", Set(d1), "\n   only in ",p[2],": ", Set(d2), "\n");
  fi;
od;
QUIT;
