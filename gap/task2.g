Read("gap/dring_sieve_standalone.g");

Task2Verify := function(id)
  local G, cls, t, ratRows, F, r, c, K, Kp, hom, h, h2, N, s, T, Tmat, 
        Trank, k, Tseq, Tk, Tseq_snf, countsM, fusedM, TkM,
        subCols, uniqueCols, C, match,
        levels, lvl, fib, r_idx;
  G := SmallGroup(32, id);
  cls := SpeciesClassesD(G);
  t := SpeciesTableD(G, cls);
  
  ratRows := [];
  for r in [1..Length(t)] do
    if ForAll([1..Length(t[r])], c -> IsInt(t[r][c])) then Add(ratRows, r); fi;
  od;
  F := Length(ratRows);
  
  T := [];
  for r in ratRows do
    K := cls[r].H;
    Kp := DerivedSubgroup(K);
    hom := NaturalHomomorphismByNormalSubgroupNC(K, Kp);
    h := cls[r].h;
    h2 := h^2;
    N := Normalizer(G, K);
    s := fail;
    for c in ratRows do
      if cls[c].H = K then
        if ForAny(Elements(N), n -> Image(hom, (h2)^n) = Image(hom, cls[c].h)) then
          s := c;
          break;
        fi;
      fi;
    od;
    if s = fail then Error("T(r) not found!"); fi;
    Add(T, Position(ratRows, s));
  od;
  
  Print("Group 32, ", id, "\n");
  
  Tmat := NullMat(F, F);
  for r in [1..F] do
    Tmat[r][T[r]] := 1;
  od;
  
  Tseq := [];
  Tk := Tmat;
  while true do
    Trank := RankMat(Tk);
    Add(Tseq, Trank);
    Tk := Tk * Tmat;
    if RankMat(Tk) = Trank then break; fi;
  od;
  Print("T* rank sequence: ", Tseq, "\n");
  
  subCols := [];
  for c in [1..Length(t[1])] do
    Add(subCols, List(ratRows, r -> t[r][c]));
  od;
  uniqueCols := []; countsM := [];
  for c in [1..Length(subCols)] do
    match := Position(uniqueCols, subCols[c]);
    if match = fail then
      Add(uniqueCols, subCols[c]); Add(countsM, 1);
    else countsM[match] := countsM[match] + 1; fi;
  od;
  C := Length(uniqueCols);
  fusedM := [];
  for r in [1..F] do
    fusedM[r] := [];
    for c in [1..C] do fusedM[r][c] := uniqueCols[c][r] * countsM[c]; od;
  od;
  
  Tk := Tmat;
  Tseq_snf := [];
  for k in [1..Length(Tseq)] do
    TkM := Tk * fusedM;
    Add(Tseq_snf, Collected(Filtered(ElementaryDivisorsMat(TkM), x -> x <> 0)));
    Tk := Tk * Tmat;
  od;
  Print("Restricted SNF sequence:\n");
  for k in [1..Length(Tseq_snf)] do
    Print("  k=", k, " : ", Tseq_snf[k], "\n");
  od;
  
  Print("Fibre-size multiset per level:\n");
  levels := Set(List(ratRows, r -> Size(cls[r].H)));
  for lvl in levels do
    fib := [];
    for c in [1..F] do
      if Size(cls[ratRows[c]].H) = lvl then
        r_idx := 0;
        for r in [1..F] do
          if T[r] = c and Size(cls[ratRows[r]].H) = lvl then r_idx := r_idx + 1; fi;
        od;
        Add(fib, r_idx);
      fi;
    od;
    Print("  |K|=", lvl, " : ", Collected(fib), "\n");
  od;
  Print("\n");
end;

Task2Verify(13);
Task2Verify(14);
QUIT;
