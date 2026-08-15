# v_task6_extraspecial128.g
# Task A: decisive n=3 test of the closed-form r-formula (the exploratory task1_check.g).
# Compute r(G) DIRECTLY (generic method: subgroup conjugacy classes +
# normalizer fusion of linear characters -- same engine as
# v_task4_rationality.g, NOT the formula's stratification) for the two
# extraspecial groups of order 128 = 2^{1+6}.
# Formula predictions under audit: plus type r = 27632, minus type r = 27136.

# ---------- restate the formula's predictions (for the log only) ----------
qBinomial := function(n, k, q)
  local num, den, i;
  if k < 0 or k > n then return 0; fi;
  num := 1; den := 1;
  for i in [0..k-1] do
    num := num * (q^(n-i) - 1);
    den := den * (q^(k-i) - 1);
  od;
  return num / den;
end;;
I_d := function(m, d, q)
  local num, den, i;
  if d < 0 or d > m then return 0; fi;
  num := 1; den := 1;
  for i in [0..d-1] do
    num := num * (q^(2*m-2*i) - 1);
    den := den * (q^(i+1) - 1);
  od;
  return num / den;
end;;
S_d_plus := function(m, d, q)
  local num, den, i;
  if d < 0 or d > m then return 0; fi;
  num := 1; den := 1;
  for i in [0..d-1] do
    num := num * (q^(m-i) - 1) * (q^(m-i-1) + 1);
    den := den * (q^(i+1) - 1);
  od;
  return num / den;
end;;
S_d_minus := function(m, d, q)
  local num, den, i;
  if d < 0 or d > m-1 then return 0; fi;
  num := 1; den := 1;
  for i in [0..d-1] do
    num := num * (q^(m-i) + 1) * (q^(m-i-1) - 1);
    den := den * (q^(i+1) - 1);
  od;
  return num / den;
end;;
r_formula := function(n, type)
  local d, t3, t2, t1;
  t3 := 0; t2 := 0; t1 := 0;
  for d in [0..2*n] do t3 := t3 + qBinomial(2*n, d, 2) * 2^d; od;
  for d in [0..n] do t2 := t2 + I_d(n, d, 2); od;
  if type = "plus" then
    for d in [0..n] do t1 := t1 + S_d_plus(n, d, 2) * 2^d; od;
  else
    for d in [0..n-1] do t1 := t1 + S_d_minus(n, d, 2) * 2^d; od;
  fi;
  return t3 + t2 + t1;
end;;
Print("formula n=3 plus : ", r_formula(3, "plus"), "\n");
Print("formula n=3 minus: ", r_formula(3, "minus"), "\n");

# ---------- generic r-engine (copied from v_task4_rationality.g) ----------
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
    if done mod 200 = 0 then
      Print("  ... ", done, " classes processed, running r = ", r, "\n");
    fi;
  od;
  Sort(multiset);
  return rec(r := r, f := f, multiset := multiset);
end;;

# ---------- sanity: re-verify the four anchors with THIS engine ----------
Print("\n=== SANITY: anchors ===\n");
inv := DRingInvariants(SmallGroup(8,3));;
Print("G(8,3)  D8 : r=", inv.r, "  (expected 20: ", inv.r = 20, ")\n");
inv := DRingInvariants(SmallGroup(8,4));;
Print("G(8,4)  Q8 : r=", inv.r, "  (expected 16: ", inv.r = 16, ")\n");
inv := DRingInvariants(SmallGroup(32,49));;
Print("G(32,49)   : r=", inv.r, "  (expected 381: ", inv.r = 381, ")\n");
inv := DRingInvariants(SmallGroup(32,50));;
Print("G(32,50)   : r=", inv.r, "  (expected 349: ", inv.r = 349, ")\n");

# ---------- identify the extraspecial groups of order 128 ----------
Print("\n=== SCAN: extraspecial groups of order 128 ===\n");
IsExtraspecial2Group := function(G)
  local Z;
  Z := Center(G);
  return Size(Z) = 2 and Z = DerivedSubgroup(G) and Z = FrattiniSubgroup(G);
end;;
es := [];;
for i in [1..NrSmallGroups(128)] do
  if IsExtraspecial2Group(SmallGroup(128, i)) then Add(es, i); fi;
od;
Print("extraspecial ids at order 128: ", es, "\n");

for i in es do
  G := SmallGroup(128, i);
  ninv := Number(G, x -> x <> One(G) and x^2 = One(G));
  Print("G(128,", i, "): |Z|=", Size(Center(G)),
        " exponent=", Exponent(G),
        " involutions=", ninv,
        "  (plus type 2^{1+6}_+ has 71 involutions, minus type 55)\n");
od;

# ---------- the decisive computation ----------
Print("\n=== MAIN: r for the extraspecial groups of order 128 ===\n");
for i in es do
  G := SmallGroup(128, i);
  Print("G(128,", i, "):\n");
  t0 := Runtime();;
  inv := DRingInvariants(G);;
  Print("G(128,", i, "): r = ", inv.r, "   f = ", inv.f,
        "   (", Runtime() - t0, " ms)\n");
  Print("G(128,", i, "): degree multiset = ", Collected(inv.multiset), "\n");
  Print("G(128,", i, "): matches plus prediction 27632?  ", inv.r = 27632, "\n");
  Print("G(128,", i, "): matches minus prediction 27136? ", inv.r = 27136, "\n");
od;

Print("\nDONE\n");
QUIT;
