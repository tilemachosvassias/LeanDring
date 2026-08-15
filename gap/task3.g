Read("gap/dring_sieve_standalone.g");

Task3CheckRing2 := function(id)
  local G, cls, t, ratRows, F, r, c, subCols, uniqueCols, C, match, E, Einv, i, j, k, prod, c_ijk, is_int, non_int_count;
  G := SmallGroup(32, id);
  cls := SpeciesClassesD(G);
  t := SpeciesTableD(G, cls);
  
  ratRows := [];
  for r in [1..Length(t)] do
    if ForAll([1..Length(t[r])], c -> IsInt(t[r][c])) then Add(ratRows, r); fi;
  od;
  F := Length(ratRows);
  
  subCols := [];
  for c in [1..Length(t[1])] do
    Add(subCols, List(ratRows, r -> t[r][c]));
  od;
  uniqueCols := []; 
  for c in [1..Length(subCols)] do
    if Position(uniqueCols, subCols[c]) = fail then
      Add(uniqueCols, subCols[c]);
    fi;
  od;
  C := Length(uniqueCols);
  E := [];
  for r in [1..F] do
    E[r] := [];
    for c in [1..C] do E[r][c] := uniqueCols[c][r]; od;
  od;
  
  Einv := E^-1;
  is_int := true;
  non_int_count := 0;
  for i in [1..F] do
    for j in [1..F] do
      prod := [];
      for c in [1..F] do Add(prod, E[i][c] * E[j][c]); od;
      c_ijk := prod * Einv;
      for k in [1..F] do
        if not IsInt(c_ijk[k]) then
          is_int := false;
          non_int_count := non_int_count + 1;
        fi;
      od;
    od;
  od;
  
  Print("Group 32, ", id, " E ring check: ", is_int, " non-int count: ", non_int_count, "\n");
end;

Task3CheckRing2(13);
Task3CheckRing2(14);
QUIT;
