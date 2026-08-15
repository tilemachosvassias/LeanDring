# v_task4_rationality.g
# D-ring rationality sweep: orders 8, 16, 32.
# Pair = (K, lambda), K <= G subgroup, lambda linear character of K.
# Fused pair = orbit under G-conjugation, computed as: K up to G-conjugacy,
# then lambda up to N_G(K)-action.  r(G) = #fused pairs.
# Galois: for lambda of order d, S = { j in (Z/d)^x : lambda^j is N-conjugate
# to lambda }, deg = phi(d)/|S| (deg = 1 for d <= 2).  Rational iff deg = 1.
# f(G) = #rational fused pairs.  D-rational iff r = f.

# order of a root of unity (values of linear chars of 2-groups: order | 32)
OrderRoot := function(v)
  local n, w;
  w := v; n := 1;
  while w <> 1 do w := w * v; n := n + 1; od;
  return n;
end;;

# returns rec(r, f, multiset) where multiset = sorted list of [d, deg]
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
    elts := Elements(K);   # fixed (sorted) ordering of K
    m := Length(elts);
    # for each generator n of N: permutation p with (lambda^n)[i] = lambda[p[i]],
    # convention lambda^n(x) = lambda(n x n^-1)
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
          gv := List(rep, x -> x ^ j);   # roots of unity: valuewise j-th power
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

# ---------------- sanity checks ----------------
Print("=== SANITY CHECKS ===\n");
inv := DRingInvariants(SmallGroup(2,1));;
Print("C2 : r=", inv.r, " f=", inv.f, " multiset=", Collected(inv.multiset),
      "  expected r=3 f=3 : ", inv.r = 3 and inv.f = 3, "\n");
inv := DRingInvariants(SmallGroup(4,1));;
Print("C4 : r=", inv.r, " f=", inv.f, " multiset=", Collected(inv.multiset),
      "  expected r=7 f=5 : ", inv.r = 7 and inv.f = 5, "\n");

# ---------------- main sweep ----------------
data := rec(o8 := [], o16 := [], o32 := []);;

Print("\n=== ORDER 8 (5 groups) ===\n");
for i in [1..NrSmallGroups(8)] do
  G := SmallGroup(8, i);
  inv := DRingInvariants(G);
  Add(data.o8, inv);
  Print("G(8,", i, "): r=", inv.r, " f=", inv.f,
        " Drational=", inv.r = inv.f,
        " multiset=", Collected(inv.multiset), "\n");
od;

Print("\n=== ORDER 16 (14 groups) ===\n");
for i in [1..NrSmallGroups(16)] do
  G := SmallGroup(16, i);
  inv := DRingInvariants(G);
  Add(data.o16, inv);
  Print("G(16,", i, "): r=", inv.r, " f=", inv.f,
        " Drational=", inv.r = inv.f,
        " multiset=", Collected(inv.multiset), "\n");
od;

Print("\n=== ORDER 32 (51 groups) ===\n");
for i in [1..NrSmallGroups(32)] do
  G := SmallGroup(32, i);
  inv := DRingInvariants(G);
  Add(data.o32, inv);
  Print("G(32,", i, "): r=", inv.r, " f=", inv.f,
        " Drational=", inv.r = inv.f,
        " multiset=", Collected(inv.multiset),
        " abelian=", IsAbelian(G), " exp=", Exponent(G),
        " |Z|=", Size(Center(G)), " |G'|=", Size(DerivedSubgroup(G)),
        " class=", NilpotencyClassOfGroup(G), "\n");
od;

# ---------------- T2 cross-checks ----------------
Print("\n=== T2 CROSS-CHECKS ===\n");
Print("32,49: r=", data.o32[49].r, " f=", data.o32[49].f,
      " D-rational=", data.o32[49].r = data.o32[49].f, "\n");
Print("32,50: r=", data.o32[50].r, " f=", data.o32[50].f,
      " D-rational=", data.o32[50].r = data.o32[50].f, "\n");
Print("32,49 r matches 381? ", data.o32[49].r = 381,
      "  (computed ", data.o32[49].r, ")\n");
Print("32,50 r matches 349? ", data.o32[50].r = 349,
      "  (computed ", data.o32[50].r, ")\n");
Print("8,3 (D8): r=", data.o8[3].r, " f=", data.o8[3].f,
      " D-rational=", data.o8[3].r = data.o8[3].f, "\n");
Print("8,4 (Q8): r=", data.o8[4].r, " f=", data.o8[4].f,
      " D-rational=", data.o8[4].r = data.o8[4].f, "\n");
IsExtraspecial2Group := G -> Size(Center(G)) = 2
    and Center(G) = DerivedSubgroup(G)
    and Center(G) = FrattiniSubgroup(G);;
Print("extraspecial check (Z=G'=Phi, |Z|=2): 32,49 = ",
      IsExtraspecial2Group(SmallGroup(32,49)),
      ", 32,50 = ", IsExtraspecial2Group(SmallGroup(32,50)),
      ", 8,3 = ", IsExtraspecial2Group(SmallGroup(8,3)),
      ", 8,4 = ", IsExtraspecial2Group(SmallGroup(8,4)), "\n");

# ---------------- T3 collisions ----------------
Print("\n=== T3 COLLISIONS (same r, f, degree multiset) ===\n");
key := inv -> [ inv.r, inv.f, Collected(inv.multiset) ];;
for t in [49, 50] do
  coll := Filtered([1..51], j -> j <> t and key(data.o32[j]) = key(data.o32[t]));
  Print("order 32, collisions with SmallGroup(32,", t, "): ", coll, "\n");
od;
for t in [3, 4] do
  coll := Filtered([1..5], j -> j <> t and key(data.o8[j]) = key(data.o8[t]));
  Print("order 8, collisions with SmallGroup(8,", t, "): ", coll, "\n");
od;

# ---------------- summary ----------------
Print("\n=== SUMMARY ===\n");
Print("D-rational at order 8 : ",
      Number(data.o8, v -> v.r = v.f), " of 5, indices ",
      Filtered([1..5], j -> data.o8[j].r = data.o8[j].f), "\n");
Print("D-rational at order 16: ",
      Number(data.o16, v -> v.r = v.f), " of 14, indices ",
      Filtered([1..14], j -> data.o16[j].r = data.o16[j].f), "\n");
Print("D-rational at order 32: ",
      Number(data.o32, v -> v.r = v.f), " of 51, indices ",
      Filtered([1..51], j -> data.o32[j].r = data.o32[j].f), "\n");
Print("\nDONE\n");
QUIT;
