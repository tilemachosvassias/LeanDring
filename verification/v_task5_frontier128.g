# v_task5_frontier128.g
# T5: order-128 frontier pair SmallGroup(128,1597) / SmallGroup(128,1598).
# Same invariants as v_task4_rationality.g (r, f, degree multiset), plus
# structural verification: special 2-group with |Z| = 4, Z = G' = Phi(G).

OrderRoot := function(v)
  local n, w;
  w := v; n := 1;
  while w <> 1 do w := w * v; n := n + 1; od;
  return n;
end;;

DRingInvariants := function(G)
  local classes, r, f, multiset, cls, K, N, gens, elts, m, perms, lins,
        chvals, seen, orbits, v, orbit, frontier, newfront, w, p, gv,
        rep, d, x, cnt, j, deg, n, i;
  classes := ConjugacyClassesSubgroups(G);
  r := 0; f := 0; multiset := [];
  for cls in classes do
    K := Representative(cls);
    N := Normalizer(G, K);
    gens := GeneratorsOfGroup(N);
    elts := Elements(K);
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
  od;
  Sort(multiset);
  return rec(r := r, f := f, multiset := multiset);
end;;

results := [];;
for i in [1597, 1598] do
  G := SmallGroup(128, i);
  Print("=== SmallGroup(128,", i, ") ===\n");
  Print("structural: |Z|=", Size(Center(G)),
        " |G'|=", Size(DerivedSubgroup(G)),
        " |Phi|=", Size(FrattiniSubgroup(G)),
        " Z=G'=", Center(G) = DerivedSubgroup(G),
        " Z=Phi=", Center(G) = FrattiniSubgroup(G),
        " class=", NilpotencyClassOfGroup(G),
        " exp=", Exponent(G),
        " abelian=", IsAbelian(G), "\n");
  Print("special (Z=G'=Phi, |Z|=4): ",
        Size(Center(G)) = 4 and Center(G) = DerivedSubgroup(G)
          and Center(G) = FrattiniSubgroup(G), "\n");
  Print("special (Z=G'=Phi, any |Z|): ",
        Center(G) = DerivedSubgroup(G)
          and Center(G) = FrattiniSubgroup(G),
        "  Z elem-abelian: ", IsElementaryAbelian(Center(G)),
        "  G/Z elem-abelian: ",
        IsElementaryAbelian(FactorGroup(G, Center(G))),
        "\n#elements of order 2: ",
        Number(G, x -> Order(x) = 2),
        "  #squares=1 (order<=2): ", Number(G, x -> Order(x) <= 2), "\n");
  inv := DRingInvariants(G);
  Add(results, inv);
  Print("r=", inv.r, " f=", inv.f, " Drational=", inv.r = inv.f,
        "\nmultiset=", Collected(inv.multiset), "\n\n");
od;

Print("=== T5 VERDICT ===\n");
Print("r equal:        ", results[1].r = results[2].r,
      "  (", results[1].r, " vs ", results[2].r, ")\n");
Print("f equal:        ", results[1].f = results[2].f,
      "  (", results[1].f, " vs ", results[2].f, ")\n");
Print("multiset equal: ", results[1].multiset = results[2].multiset, "\n");
Print("full invariant vector (r,f,multiset): ",
      results[1].r = results[2].r and results[1].f = results[2].f
        and results[1].multiset = results[2].multiset, "\n");
Print("\nDONE\n");
QUIT;
