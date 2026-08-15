# export_256_t4_pair_1741.g -- same exporter as export_256_t4_pair.g,
# retargeted to the second order-256 T4 pair, SmallGroup(256,1741/1742)
# (queue item 2; Deiml does NOT separate this pair).
#
# This is the factored, generally-correct coset-orbit algorithm used for the
# independently regenerated order-3125 tables.  It writes the plain format
# consumed by python/crossiso.py.
#
# Run:
#   ~/gap-4.15.1/gap -q -b gap/export_256_t4_pair.g

Read("gap/legacy/preprint_archive/Work_New");  # MG_G (basis columns)
Read("gap/dg_correct.g");                     # correct species rows

FastDExport256 := function(id, filename)
  local G, DG, MG, n, reps, nc, classOfRow, classOfCol, a, b, i, j,
        K, H, h, RT, adm, gens, elK, CC, cpos, c, x, T, blockcols,
        lam, poslist, cnt1, cnt2, rowsOfClass, out, Nexp, coeffs, line,
        M, row, Hp, nat, fibreOrder;
  G := SmallGroup(256, id);
  DG := DG_G_coset(G);;
  MG := MG_G(G);;
  n := Length(DG);
  if Length(MG) <> n then Error("not square"); fi;

  reps := [];
  classOfRow := [];
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
  for a in [1..nc] do
    cnt1 := Number([1..n], i -> classOfRow[i] = a);
    cnt2 := Number([1..n], j -> classOfCol[j] = a);
    if cnt1 <> cnt2 then Error("class count mismatch at class ", a); fi;
  od;
  rowsOfClass := List([1..nc], a ->
    Filtered([1..n], i -> classOfRow[i] = a));

  T := List([1..n], i -> ListWithIdenticalEntries(n, 0));
  for b in [1..nc] do
    K := reps[b];
    RT := RightTransversal(G, K);
    if Size(Set(List(RT, t -> CanonicalRightCosetElement(K, t^-1))))
       <> Index(G, K) then
      Error("transversal not two-sided for class ", b);
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
    if b mod 20 = 0 then Print("  ", id, ": col class ", b, "/", nc, "\n"); fi;
  od;
  for j in [1..n] do
    if T[1][j] <> Index(G, reps[classOfCol[j]]) then
      Error("row-1 sanity failed at column ", j);
    fi;
  od;

  Nexp := Exponent(G);
  out := OutputTextFile(filename, false);
  SetPrintFormattingStatus(out, false);
  AppendTo(out, n, " ", Nexp, "\n");
  for i in [1..n] do
    H := DG[i][1];
    Hp := DerivedSubgroup(H);
    nat := NaturalHomomorphismByNormalSubgroupNC(H, Hp);
    fibreOrder := Order(Image(nat, DG[i][2]));
    line := Concatenation(String(Size(H)), " ", String(fibreOrder));
    for j in [1..n] do
      coeffs := CoeffsCyc(T[i][j], Nexp);
      line := Concatenation(line, " ",
        JoinStringsWithSeparator(List(coeffs, String), " "));
    od;
    AppendTo(out, line, "\n");
  od;
  M := MatTom(TableOfMarks(G));
  AppendTo(out, "MARKS ", Length(M), "\n");
  for row in M do
    AppendTo(out, JoinStringsWithSeparator(List(row, String), " "), "\n");
  od;
  CloseStream(out);
  Print("group ", id, " exported: ", n, " species, exponent ", Nexp,
        ", ", Length(M), " subgroup classes\n");
end;

FastDExport256(1741, "results/order256_t4_pairs/g256_1741.txt");
FastDExport256(1742, "results/order256_t4_pairs/g256_1742.txt");
QUIT;
