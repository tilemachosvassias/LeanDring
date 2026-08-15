# regen_3125.g -- full independent regeneration of the order-3125 species
# tables (task 5a remaining gate), with current-GAP labels.
#
# Algorithm: the (1/|K|)-normalized species sum, implemented as a sum over a
# transversal that is ASSERTED two-sided per column class (F1-safe, see
# docs/audit_gap_table_algorithm.md). Rows use DG_G_coset (gap/lib/dg_correct.g),
# the generally-correct coset-orbit parametrization, NOT Work_New::DG_G; the
# per-class count equality below is now a regression assert, not the correctness
# gate. Complexity is factored: admissible
# transversal elements are computed once per (row-class, column-class) pair,
# not per entry — this is what makes the full table feasible.
# Labels (subgroup class, fibre, character) are saved alongside each table.
#
# Run:  ~/gap-4.15.1/gap -q -b gap/species/regen_3125.g
# Output: results/n_test_3125/Tmine_{68,69}.g and *_meta.g

Read("gap/legacy/preprint_archive/Work_New");  # MG_G (columns); DG_G (superseded)
Read("gap/lib/dg_correct.g");                       # DG_G_coset (generally-correct rows)

RegenGroup := function(id)
  local G, DG, MG, n, reps, nc, classOfRow, classOfCol, a, b, i, j, K, H, h,
        RT, adm, gens, elK, CC, cpos, c, x, T, blockcols, lam, poslist,
        cnt1, cnt2, rowsOfClass, fname;
  G := SmallGroup(3125, id);
  DG := DG_G_coset(G);; MG := MG_G(G);;
  n := Length(DG);
  if Length(MG) <> n then Error("not square"); fi;
  reps := []; classOfRow := [];
  for i in [1..n] do
    a := PositionProperty(reps, r -> IsIdenticalObj(r, DG[i][1]));
    if a = fail then Add(reps, DG[i][1]); a := Length(reps); fi;
    classOfRow[i] := a;
  od;
  classOfCol := [];
  for j in [1..n] do
    a := PositionProperty(reps, r -> IsIdenticalObj(r, MG[j][1]));
    if a = fail then Error("MG subgroup missing from DG reps"); fi;
    classOfCol[j] := a;
  od;
  nc := Length(reps);
  for a in [1..nc] do  # per-class DG/MG count equality (validates DG_G here)
    cnt1 := Number([1..n], i -> classOfRow[i] = a);
    cnt2 := Number([1..n], j -> classOfCol[j] = a);
    if cnt1 <> cnt2 then Error("class count mismatch at class ", a); fi;
  od;
  rowsOfClass := List([1..nc], a -> Filtered([1..n], i -> classOfRow[i] = a));
  T := List([1..n], i -> ListWithIdenticalEntries(n, 0));
  for b in [1..nc] do
    K := reps[b];
    RT := RightTransversal(G, K);
    if Size(Set(List(RT, t -> CanonicalRightCosetElement(K, t^-1))))
       <> Index(G, K) then
      Error("transversal not two-sided for class ", b, " -- F1 fires, abort");
    fi;
    CC := ConjugacyClasses(CharacterTable(K));
    elK := Elements(K);
    cpos := [];
    for c in [1..Length(CC)] do
      for x in Elements(CC[c]) do cpos[Position(elK, x)] := c; od;
    od;
    blockcols := Filtered([1..n], j -> classOfCol[j] = b);
    for a in [1..nc] do
      H := reps[a];
      if Size(H) <= Size(K) then
        gens := GeneratorsOfGroup(H);
        if Length(gens) = 0 then gens := [One(G)]; fi;
        adm := Filtered(AsList(RT), t -> ForAll(gens, x -> x^t in K));
        if Length(adm) > 0 then
          for i in rowsOfClass[a] do
            h := DG[i][2];
            poslist := List(adm, t -> cpos[Position(elK, h^t)]);
            for j in blockcols do
              lam := MG[j][2];
              T[i][j] := Sum(poslist, p -> lam[p]);
            od;
          od;
        fi;
      fi;
    od;
    if b mod 20 = 0 then Print("  col class ", b, "/", nc, "\n"); fi;
  od;
  for j in [1..n] do  # sanity: (1,1)-row = column indices
    if T[1][j] <> Index(G, reps[classOfCol[j]]) then
      Error("row-1 sanity failed at column ", j);
    fi;
  od;
  fname := Concatenation("results/n_test_3125/Tmine_", String(id), ".g");
  PrintTo(fname, "TM", String(id), " := ", T, ";\n");
  PrintTo(Concatenation("results/n_test_3125/Tmine_", String(id), "_meta.g"),
    "META", String(id), " := rec(\n",
    "  rowClass := ", classOfRow, ",\n",
    "  colClass := ", classOfCol, ",\n",
    "  classSize := ", List(reps, Size), ",\n",
    "  classIsNormal := ", List(reps, r -> IsNormal(G, r)), ",\n",
    "  fibreOrder := ", List(DG, x -> Order(x[2])), ");\n");
  Print("group ", id, " done: ", n, "x", n, " saved\n");
  return true;
end;

Print("== regenerating (3125,68)\n"); RegenGroup(68);
Print("== regenerating (3125,69)\n"); RegenGroup(69);
Print("REGEN OVERALL: DONE\n");
QUIT;
