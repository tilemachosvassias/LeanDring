IsMetacyclic2Group := function(G)
  local N, Ns;
  Ns := NormalSubgroups(G);
  for N in Ns do
    if IsCyclic(N) and IsCyclic(G/N) then
      return true;
    fi;
  od;
  return false;
end;

Read("gap/task3_order64_unanchored.g");

MultisetDifference := function(bag1, bag2)
  local diff, b, found, c, diff_count;
  diff := [];
  for b in bag1 do
    found := false;
    for c in bag2 do
      if b[1] = c[1] then
        found := true;
        diff_count := b[2] - c[2];
        if diff_count > 0 then Add(diff, [b[1], diff_count]); fi;
        break;
      fi;
    od;
    if not found then Add(diff, b); fi;
  od;
  return diff;
end;

Task4 := function()
  local order, n, i, G, inv, bag, bags, b, found, sig, diff1, diff2, c, c2;
  for order in [2, 4, 8, 16, 32, 64, 128, 256] do
    Print("\nOrder ", order, ":\n");
    bags := [];
    n := NrSmallGroups(order);
    for i in [1..n] do
      G := SmallGroup(order, i);
      if IsMetacyclic2Group(G) then
        inv := UnanchoredFusionFields(G);
        bag := Collected(SplitString(inv.sig, ";"));
        # Remove empty string from split if it exists
        bag := Filtered(bag, x -> x[1] <> "");
        found := false;
        for b in bags do
          if b.bag = bag then
            Print("  Collision! Bag equality for metacyclic groups: (", order, ",", b.ids[1], ") and (", order, ",", i, ")\n");
            Add(b.ids, i);
            found := true;
            break;
          fi;
        od;
        if not found then
          Add(bags, rec(bag := bag, ids := [i]));
        fi;
      fi;
    od;
    
    Print("  Checking shadow gauge pairs for order ", order, "...\n");
    for i in [1..Length(bags)] do
      for c in [i+1..Length(bags)] do
        diff1 := MultisetDifference(bags[i].bag, bags[c].bag);
        diff2 := MultisetDifference(bags[c].bag, bags[i].bag);
        if (Length(diff1) = 2 and Length(diff2) = 1) or 
           (Length(diff1) = 1 and Length(diff2) = 2) then
          if (diff1 = [["Q", 1], ["Q(zeta_8)", 1]] and diff2 = [["Q(i)", 2]]) or
             (diff2 = [["Q", 1], ["Q(zeta_8)", 1]] and diff1 = [["Q(i)", 2]]) then
            Print("  Shadow gauge pair found! (", order, ",", bags[i].ids, 
                  ") and (", order, ",", bags[c].ids, ")\n");
          fi;
        fi;
      od;
    od;
  od;
end;

Task4();
QUIT;
