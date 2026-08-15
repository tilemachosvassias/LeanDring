IsNormOfAb := function(G, N)
  local A;
  for A in Filtered(NormalSubgroupsAbove(N, TrivialSubgroup(N), []),
                    x -> Size(x) > 1 and IsAbelian(x)) do
    if Normalizer(G, A) = N then return true; fi;
  od;
  return false;
end;
run := function(nm, G, bound)
  local t, mx, res, M, i, N;
  t := Runtime(); res := [];
  mx := List(MaximalSubgroupClassReps(G));
  SortBy(mx, x -> Index(G,x));
  Print(nm, " maximal indices: ", List(mx, x->Index(G,x)), "\n");
  for M in mx do
    i := Index(G, M);
    if i <= bound then
      if IsNormOfAb(G, M) then Add(res, i); fi;
      if i * 2 <= bound then
        for N in LowIndexSubgroups(M, QuoInt(bound, i)) do
          if Size(N) < Size(M) and IsNormOfAb(G, N) then
            Add(res, Index(G, N)); fi;
        od;
      fi;
    fi;
  od;
  Print("   -> I(G) up to ", bound, ": ", Set(res),
        "   [", Int((Runtime()-t)/1000), "s]\n");
end;
run("S4(3)", PSp(4,3), 60);
run("L4(2)", PSL(4,2), 40);
run("L4(3)", PSL(4,3), 160);
run("S4(4)", PSp(4,4), 160);
# --- the full battery actually run (NOTES.md Sec.4at) ---
# run("L3(2)", PSL(3,2),  40);  run("L3(3)", PSL(3,3), 400);
# run("L3(4)", PSL(3,4), 300);  run("L4(2)", PSL(4,2),  40);
# run("L4(3)", PSL(4,3), 160);  run("L5(2)", PSL(5,2), 200);
# run("S4(3)", PSp(4,3),  60);  run("S4(4)", PSp(4,4), 600);
# run("S4(5)", PSp(4,5), 800);  run("U4(3)", PSU(4,3), 400);
# run("Sp6(2)", Sp(6,2), 200);  run("U5(2)", PSU(5,2), 400);
