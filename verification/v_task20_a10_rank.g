# v_task20_a10_rank.g -- resolve the A10 vs twin#2 (S6 x A7) mult1 TIE
# (both = 4 exactly, v_task20_full_a10_out.txt / v_task20_a10_out.txt)
# using the FULL D-ring rank r = total number of fused (K,lambda) pairs
# (conjugacy classes of subgroups K, orbits of linear characters of K
# under N_G(K)) -- a kernel-checked, unconditional D-ring invariant
# (Nat.card {p : DRing G ->+* Z}, OrderTransfer.lean), NOT the wall-
# blocked class-count/involution-count invariants used in v_task16/17.
# Engine copied verbatim from v_task4_rationality.g (DRingInvariants),
# self-contained.  Feasibility confirmed by v_task20_a10_rank_probe.g:
# A10 has 430 subgroup conjugacy classes (3.7s), S6xA7 has 5521 (72s) --
# both tractable.

# order of a root of unity (value of a linear character)
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
        rep, d, x, cnt, j, deg, n, i, nclasses;
  classes := ConjugacyClassesSubgroups(G);
  nclasses := Length(classes);
  r := 0; f := 0; multiset := [];
  for i in [1..nclasses] do
    cls := classes[i];
    K := Representative(cls);
    N := Normalizer(G, K);
    gens := GeneratorsOfGroup(N);
    elts := Elements(K);   # fixed (sorted) ordering of K
    m := Length(elts);
    perms := List(gens, n -> List([1..m],
                    ii -> Position(elts, n * elts[ii] * n^-1)));
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
    if i mod 50 = 0 then
      Print("  ... processed ", i, "/", nclasses, " subgroup classes, r so far=", r, "\n");
    fi;
  od;
  Sort(multiset);
  return rec(r := r, f := f, multiset := multiset);
end;;

Print("=== A10 full D-ring rank r ===\n");
G1 := AlternatingGroup(10);;
t0 := Runtime();;
inv1 := DRingInvariants(G1);;
Print("A10: r=", inv1.r, " f=", inv1.f, " time(ms)=", Runtime()-t0, "\n");

Print("\n=== twin#2 = S6 x A7 full D-ring rank r ===\n");
G2 := DirectProduct(SymmetricGroup(6), AlternatingGroup(7));;
t0 := Runtime();;
inv2 := DRingInvariants(G2);;
Print("S6xA7: r=", inv2.r, " f=", inv2.f, " time(ms)=", Runtime()-t0, "\n");

Print("\n=== VERDICT ===\n");
if inv1.r <> inv2.r then
  Print("SEPARATED-PROVEN by full rank r: A10 r=", inv1.r, " vs S6xA7 twin r=", inv2.r, "\n");
else
  Print("TIE even on full rank r: both = ", inv1.r, ". Checking f and degree multiset...\n");
  if inv1.f <> inv2.f then
    Print("SEPARATED-PROVEN by f (rational fused pairs): A10 f=", inv1.f, " vs twin f=", inv2.f, "\n");
  elif Collected(inv1.multiset) <> Collected(inv2.multiset) then
    Print("SEPARATED-PROVEN by degree multiset (still a proven D-invariant: Galois data per species).\n");
  else
    Print("NOT SEPARATED even by full rank/f/multiset -- genuinely UNDECIDED at this invariant tier.\n");
  fi;
fi;
Print("=== DONE a10_rank ===\n");
