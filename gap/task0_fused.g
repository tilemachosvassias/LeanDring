Read("gap/dring_sieve_standalone.g");

Task0VerifyFused := function(id)
  local G, cls, t, r, c, ratRows, subCols, uniqueCols, counts, F, C, i, j, isRat, match, fusedM, snf;
  G := SmallGroup(32, id);
  cls := SpeciesClassesD(G);
  t := SpeciesTableD(G, cls);
  
  ratRows := [];
  for r in [1..Length(t)] do
    isRat := true;
    for c in [1..Length(t[r])] do
      if not IsInt(t[r][c]) then isRat := false; break; fi;
    od;
    if isRat then Add(ratRows, r); fi;
  od;
  F := Length(ratRows);
  
  subCols := [];
  for c in [1..Length(t[1])] do
    Add(subCols, List(ratRows, r -> t[r][c]));
  od;
  
  uniqueCols := [];
  counts := [];
  for c in [1..Length(subCols)] do
    match := Position(uniqueCols, subCols[c]);
    if match = fail then
      Add(uniqueCols, subCols[c]);
      Add(counts, 1);
    else
      counts[match] := counts[match] + 1;
    fi;
  od;
  
  C := Length(uniqueCols);
  Print("Group 32,", id, "\n");
  Print("Rational rows (F): ", F, "\n");
  Print("Unique sub-columns (C): ", C, "\n");
  
  fusedM := [];
  for i in [1..F] do
    fusedM[i] := [];
    for j in [1..C] do
      fusedM[i][j] := uniqueCols[j][i] * counts[j];
    od;
  od;
  
  Print("Fused Matrix size: ", DimensionsMat(fusedM), "\n");
  Print("Rank: ", RankMat(fusedM), "\n");
  
  if F = C then
    if RankMat(fusedM) = F then
      Print("Matrix is square and non-singular.\n");
      snf := ElementaryDivisorsMat(fusedM);
      Print("SNF: ", Collected(snf), "\n\n");
    else
      Print("Matrix is square but singular.\n\n");
    fi;
  else
    Print("Matrix is NOT square.\n\n");
  fi;
end;

Task0VerifyFused(13);
Task0VerifyFused(14);
QUIT;
