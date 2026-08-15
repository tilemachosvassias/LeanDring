# verify_5d.g -- task 5d: decide Finding F1 and assumption A2 from
# docs/audit_gap_table_algorithm.md for SmallGroup(3125,68) / (3125,69).
#
# Checks, per group:
#   (5d-1) F1 two-sidedness: for EVERY subgroup class rep K, the GAP
#          RightTransversal(G,K) meets every LEFT coset exactly once
#          (t -> canonical rep of K*t^-1 is injective).
#   (5d-2) A2: DG_G(G) subgroup sizes are nondecreasing (justifies the `break`).
#   (5d-3) Direct semantic spot-check, version-independent: recompute a
#          deterministic sample of entries of the ARCHIVED tables T1/T2 with the
#          unambiguous formula  (1/|K|) * sum over ALL g in G of
#          [H^g <= K] * lambda(h^g),  and compare exactly.
# Run:  ~/gap-4.15.1/gap -q -b provenance/gap/species/verify_5d.g
# Checked against: audit doc F1/A2 definitions; formula (D3) of STATE.md.

Read("provenance/gap/legacy/preprint_archive/Work_New");

TwoSidedCheck := function(G)
  local reps, bad, i, K, T, n;
  reps := List(ConjugacyClassesSubgroups(G), Representative);
  bad := [];
  for i in [1..Length(reps)] do
    K := reps[i];
    T := RightTransversal(G, K);
    n := Size(Set(List(T, t -> CanonicalRightCosetElement(K, t^-1))));
    if n <> Index(G, K) then Add(bad, [i, Size(K), n, Index(G, K)]); fi;
  od;
  return [Length(reps), bad];
end;

# exact species entry, full-group sum, no transversal
EntryFull := function(G, elG, H, h, K, lam, classpos, elK)
  local tot, gens, g, val;
  tot := 0;
  gens := GeneratorsOfGroup(H);
  if Length(gens) = 0 then gens := [One(H)]; fi;
  for g in elG do
    if ForAll(gens, x -> x^g in K) then
      val := h^g;
      tot := tot + lam[classpos[Position(elK, val)]];
    fi;
  od;
  return tot / Size(K);
end;

SampleCheck := function(G, T, DG, MG, rows, cols)
  local elG, mism, tested, i, j, H, h, K, lam, CC, elK, classpos, c, x, v, va;
  elG := Elements(G);
  mism := []; tested := 0;
  for j in cols do
    K := MG[j][1]; lam := MG[j][2];
    CC := ConjugacyClasses(CharacterTable(UnderlyingGroup(lam)));
    elK := Elements(K);
    classpos := [];
    for c in [1..Length(CC)] do
      for x in Elements(CC[c]) do classpos[Position(elK, x)] := c; od;
    od;
    for i in rows do
      H := DG[i][1]; h := DG[i][2];
      if Size(H) <= Size(K) then
        v := EntryFull(G, elG, H, h, K, lam, classpos, elK);
      else
        v := 0;  # containment impossible
      fi;
      va := T[i][j];
      tested := tested + 1;
      if v <> va then Add(mism, [i, j, v, va]); fi;
    od;
  od;
  return [tested, mism];
end;

RunGroup := function(id, T)
  local G, ts, DG, MG, sizes, a2, n, rows, cols, sc;
  G := SmallGroup(3125, id);
  Print("== SmallGroup(3125,", id, ")\n");
  ts := TwoSidedCheck(G);
  Print("   (5d-1) subgroup classes: ", ts[1],
        "; two-sidedness failures: ", Length(ts[2]), " ", ts[2], "\n");
  DG := DG_G(G);; MG := MG_G(G);;
  sizes := List(DG, x -> Size(x[1]));
  a2 := IsSortedList(sizes);
  Print("   (5d-2) #DG=", Length(DG), " #MG=", Length(MG),
        " archived dim=", Length(T), "; A2 nondecreasing sizes: ", a2, "\n");
  n := Length(DG);
  # deterministic spread incl. first/last blocks and mid-lattice
  rows := Set(Filtered([1, 2, 3, Int(n/8), Int(n/4), Int(n/2), Int(3*n/4),
                        n-2, n-1, n], x -> x >= 1 and x <= n));
  cols := Set(Filtered([1, 2, Int(n/7), Int(n/3), Int(n/2), Int(2*n/3),
                        Int(9*n/10), n], x -> x >= 1 and x <= n));
  sc := SampleCheck(G, T, DG, MG, rows, cols);
  Print("   (5d-3) sampled entries: ", sc[1], "; mismatches: ",
        Length(sc[2]), "\n");
  if Length(sc[2]) > 0 then Print("   MISMATCHES: ", sc[2], "\n"); fi;
  return [ts, a2, sc];
end;

Print("Reading archived tables...\n");
Read("provenance/gap/legacy/preprint_archive/G3125_68");;
Read("provenance/gap/legacy/preprint_archive/G3125_69");;
r68 := RunGroup(68, T1);;
r69 := RunGroup(69, T2);;
if Length(r68[1][2]) = 0 and Length(r69[1][2]) = 0 and r68[2] and r69[2]
   and Length(r68[3][2]) = 0 and Length(r69[3][2]) = 0 then
  Print("5d OVERALL: ALL CHECKS PASSED\n");
else
  Print("5d OVERALL: FAILURES PRESENT - see above\n");
fi;
QUIT;
