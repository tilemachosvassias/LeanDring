Read("gap/dring_sieve_standalone.g");

Task0Verify := function(id)
  local G, cls, t, r, c, ratRows, ratCols, isRat, M, snf;
  G := SmallGroup(32, id);
  cls := SpeciesClassesD(G);
  t := SpeciesTableD(G, cls);
  
  ratRows := [];
  for r in [1..Length(t)] do
    isRat := true;
    for c in [1..Length(t[r])] do
      if not IsInt(t[r][c]) then
        isRat := false;
        break;
      fi;
    od;
    if isRat then Add(ratRows, r); fi;
  od;
  
  ratCols := [];
  for c in [1..Length(t[1])] do
    isRat := true;
    for r in [1..Length(t)] do
      if not IsInt(t[r][c]) then
        isRat := false;
        break;
      fi;
    od;
    if isRat then Add(ratCols, c); fi;
  od;
  
  Print("Group 32,", id, "\n");
  Print("Total size: ", Length(t), "x", Length(t[1]), "\n");
  Print("Rational rows: ", Length(ratRows), "\n");
  Print("Rational cols: ", Length(ratCols), "\n");
  
  if Length(ratRows) <> Length(ratCols) then
    Error("Square condition fails!");
  fi;
  
  M := [];
  for r in ratRows do
    Add(M, List(ratCols, c -> t[r][c]));
  od;
  
  Print("Rank: ", RankMat(M), "\n");
  if RankMat(M) <> Length(ratRows) then
    Print("Warning: matrix is singular!\n");
  else
    Print("Matrix is non-singular.\n");
  fi;
  
  snf := ElementaryDivisorsMat(M);
  Print("SNF: ", Collected(snf), "\n\n");
end;

Task0Verify(13);
Task0Verify(14);
QUIT;
