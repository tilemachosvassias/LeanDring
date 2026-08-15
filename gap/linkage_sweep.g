Read("gap/dring_sieve_standalone.g");

v2 := function(n)
  local c;
  if n = 0 then return -1; fi;
  c := 0;
  while n mod 2 = 0 do
    c := c + 1;
    n := n / 2;
  od;
  return c;
end;

LinkageMultiset := function(G)
  local df, r, c, S, B, multiset, val, p, q, g, j;
  df := SpeciesDFMatrix(G);
  S := Length(df);
  if S = 0 then return []; fi;
  B := Length(df[1]);
  multiset := [];
  for p in [1..S] do
    for q in [p+1..S] do
      g := 0;
      for j in [1..B] do
        g := GcdInt(g, df[p][j] - df[q][j]);
      od;
      val := v2(g);
      if val <> -1 then
        Add(multiset, val);
      fi;
    od;
  od;
  Sort(multiset);
  return multiset;
end;

RunSweep := function(order)
  local n, i, G, lm, linkage_lms, linkage_ids, survivors, pos;
  Print("--- Sweeping Order ", order, " ---\n");
  n := NrSmallGroups(order);
  linkage_lms := [];
  linkage_ids := [];
  for i in [1..n] do
    G := SmallGroup(order, i);
    if not IsAbelian(G) then
      lm := LinkageMultiset(G);
      pos := Position(linkage_lms, lm);
      if pos = fail then
        Add(linkage_lms, lm);
        Add(linkage_ids, [i]);
      else
        Add(linkage_ids[pos], i);
      fi;
    fi;
  od;
  
  survivors := 0;
  for i in [1..Length(linkage_lms)] do
    if Length(linkage_ids[i]) > 1 then
      Print("SURVIVORS (linkage match): ", linkage_ids[i], " -> ", linkage_lms[i], "\n");
      survivors := survivors + 1;
    fi;
  od;
  
  if survivors = 0 then
    Print("ZERO EXCEPTIONS! All groups completely separated by Linkage!\n");
  fi;
end;

RunSweep(32);
RunSweep(64);
QUIT;
