# v_task7_radical128.g
# Task 7: test the hand-derived "radical census" at order 128.
# Compute r (fused-pair count) for four direct products
#   E32+ x C2^2 = DirectProduct(SmallGroup(32,49), C2^2)   predicted r = 30099
#   E32- x C2^2 = DirectProduct(SmallGroup(32,50), C2^2)   predicted r = 27827
#   D8  x C2^4  = DirectProduct(SmallGroup(8,3),  C2^4)    predicted r = 51395
#   Q8  x C2^4  = DirectProduct(SmallGroup(8,4),  C2^4)    predicted r = 31747
# with the generic fused-pair engine (subgroup conjugacy classes, then
# orbits of N_G(K) on linear characters of K; r = total orbit count),
# copied from v_task4_rationality.g / v_task6_extraspecial128.g.
# Also report f (# rational fused pairs), D-rationality (r = f), and
# whether each r > 27632 (the extraspecial plus-type value at order 128).

# ---------- generic r-engine (copied from v_task6_extraspecial128.g) ----------
OrderRoot := function(v)
  local n, w;
  w := v; n := 1;
  while w <> 1 do w := w * v; n := n + 1; od;
  return n;
end;;

DRingInvariants := function(G)
  local classes, r, f, multiset, cls, K, N, gens, elts, m, perms, lins,
        chvals, seen, orbits, v, orbit, frontier, newfront, w, p, gv,
        rep, d, x, cnt, j, deg, n, i, done;
  Print("  computing ConjugacyClassesSubgroups ... \c");
  classes := ConjugacyClassesSubgroups(G);
  Print(Length(classes), " classes\n");
  r := 0; f := 0; multiset := []; done := 0;
  for cls in classes do
    K := Representative(cls);
    N := Normalizer(G, K);
    gens := GeneratorsOfGroup(N);
    elts := Elements(K);   # fixed (sorted) ordering of K
    m := Length(elts);
    perms := List(gens, n -> List([1..m],
                    i -> Position(elts, n * elts[i] * n^-1)));
    lins := LinearCharacters(K);
    chvals := List(lins, chi -> List(elts, x -> x ^ chi));
    seen := Set([]);
    orbits := [];
    for v in chvals do
      if not v in seen then
        orbit := [ v ]; frontier := [ v ];
        while Length(frontier) > 0 do
          newfront := [];
          for w in frontier do
            for p in perms do
              gv := w{ p };
              if not gv in orbit then
                Add(orbit, gv); Add(newfront, gv);
              fi;
            od;
          od;
          frontier := newfront;
        od;
        UniteSet(seen, orbit);
        Add(orbits, orbit);
      fi;
    od;
    for orbit in orbits do
      rep := orbit[1];
      d := 1;
      for x in rep do d := Lcm(d, OrderRoot(x)); od;
      if d <= 2 then
        deg := 1;
      else
        cnt := 0;
        for j in PrimeResidues(d) do
          gv := List(rep, x -> x ^ j);
          if gv in orbit then cnt := cnt + 1; fi;
        od;
        deg := Phi(d) / cnt;
      fi;
      r := r + 1;
      if deg = 1 then f := f + 1; fi;
      Add(multiset, [ d, deg ]);
    od;
    done := done + 1;
    if done mod 500 = 0 then
      Print("  ... ", done, " classes processed, running r = ", r, "\n");
    fi;
  od;
  Sort(multiset);
  return rec(r := r, f := f, multiset := multiset);
end;;

# ---------- sanity checks at order 32 (known values) ----------
Print("=== SANITY: order-32 analogues ===\n");
sanity := [ [ "D8 x C2^2 = G(32,46)", SmallGroup(32,46), 583 ],
            [ "Q8 x C2^2 = G(32,47)", SmallGroup(32,47), 407 ] ];;
for s in sanity do
  t0 := Runtime();;
  inv := DRingInvariants(s[2]);;
  Print(s[1], ": r = ", inv.r, "  f = ", inv.f,
        "  expected r = ", s[3],
        "  SANITY ", inv.r = s[3],
        "  > 381: ", inv.r > 381,
        "  (", Runtime() - t0, " ms)\n");
od;

# ---------- the four order-128 radical-census groups ----------
Print("\n=== MAIN: radical census at order 128 ===\n");
C2_2 := ElementaryAbelianGroup(4);;
C2_4 := ElementaryAbelianGroup(16);;
targets := [
  [ "E32+ x C2^2", DirectProduct(SmallGroup(32,49), C2_2), 30099 ],
  [ "E32- x C2^2", DirectProduct(SmallGroup(32,50), C2_2), 27827 ],
  [ "Q8  x C2^4",  DirectProduct(SmallGroup(8,4),  C2_4), 31747 ],
  [ "D8  x C2^4",  DirectProduct(SmallGroup(8,3),  C2_4), 51395 ]
];;

results := [];;
for s in targets do
  Print("\n--- ", s[1], " (order ", Size(s[2]), ") ---\n");
  t0 := Runtime();;
  inv := DRingInvariants(s[2]);;
  Print(s[1], ": r = ", inv.r, "   f = ", inv.f,
        "   D-rational = ", inv.r = inv.f,
        "   (", Runtime() - t0, " ms)\n");
  Print(s[1], ": predicted r = ", s[3], "   ");
  if inv.r = s[3] then Print("MATCH\n"); else Print("MISMATCH\n"); fi;
  Print(s[1], ": r > 27632 (E128+ value)?  ", inv.r > 27632, "\n");
  Add(results, [ s[1], s[3], inv.r, inv.f ]);
od;

# ---------- summary table ----------
Print("\n=== SUMMARY ===\n");
Print("group          predicted  computed  f       match  >27632  D-rational\n");
allmatch := true;;
allgt := true;;
for row in results do
  Print(String(row[1], -14), " ", String(row[2], 9), " ", String(row[3], 9),
        " ", String(row[4], 7), "  ");
  if row[3] = row[2] then Print("MATCH  "); else Print("MISM   "); allmatch := false; fi;
  Print(row[3] > 27632, "    ", row[3] = row[4], "\n");
  if row[3] <= 27632 then allgt := false; fi;
od;
Print("\nALL FOUR MATCH PREDICTIONS: ", allmatch, "\n");
Print("ALL FOUR STRICTLY > 27632 : ", allgt, "\n");

Print("\nDONE\n");
QUIT;
