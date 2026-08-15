Read("gap/dring_sieve_standalone.g");

ExtractLocalBlocks := function(id)
  local G, cls, t, ratRows, subCols, uniqueCols, counts, fusedM, i, j, c, r, F, C, isRat, match,
        sc, K, Kp, w_size, r_classes, c_classes, blockM, snf, out, b;
  G := SmallGroup(32, id);
  cls := SpeciesClassesD(G);
  t := SpeciesTableD(G, cls);
  
  # Find rational rows and their subgroup K
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
  c_classes := [];
  for c in [1..Length(subCols)] do
    match := Position(uniqueCols, subCols[c]);
    if match = fail then
      Add(uniqueCols, subCols[c]);
      Add(counts, 1);
      Add(c_classes, c);
    else
      counts[match] := counts[match] + 1;
    fi;
  od;
  C := Length(uniqueCols);
  
  sc := ConjugacyClassesSubgroups(G);
  out := [];
  for i in [1..Length(sc)] do
    K := Representative(sc[i]);
    Kp := DerivedSubgroup(K);
    w_size := Size(Normalizer(G, K)) / Size(K);
    
    # rows belonging to K
    r_classes := Filtered(ratRows, r -> Size(cls[r].H) = Size(K) and IsConjugate(G, cls[r].H, K));
    
    # columns belonging to K (basis elements with subgroup L = K)
    # The basis classes are generated in BasisClassesD.
    # The length of BasisClassesD(G) is Length(t[1]).
    # We can identify the subgroup of column c by looking at BasisClassesD(G)[c].K
    
    # But wait! SpeciesTableD uses BasisClassesD. We can just run it.
    b := BasisClassesD(G);
    
    blockM := [];
    for r in r_classes do
      Add(blockM, []);
      for c in [1..Length(uniqueCols)] do
        if Size(b[c_classes[c]].K) = Size(K) and IsConjugate(G, b[c_classes[c]].K, K) then
          Add(blockM[Length(blockM)], uniqueCols[c][Position(ratRows, r)] * counts[c]);
        fi;
      od;
    od;
    
    if Length(blockM) > 0 then
      if Length(blockM) <> Length(blockM[1]) then
        Print("Block for K size ", Size(K), " is not square! ", Length(blockM), "x", Length(blockM[1]), "\n");
        snf := [];
      else
        snf := ElementaryDivisorsMat(blockM);
      fi;
      Add(out, rec(
        id := IdGroup(K),
        sizeK := Size(K),
        sizeA := Size(K)/Size(Kp),
        w_size := w_size,
        rat_classes := Length(r_classes),
        snf := snf
      ));
    fi;
  od;
  return out;
end;

Print("Group 32, 13:\n");
blocks13 := ExtractLocalBlocks(13);
for b in blocks13 do
  Print("K=Id", b.id, " |K|=", b.sizeK, " |A|=", b.sizeA, " |W|=", b.w_size, " rat=", b.rat_classes, " snf=", Collected(b.snf), "\n");
od;
Print("\nGroup 32, 14:\n");
blocks14 := ExtractLocalBlocks(14);
for b in blocks14 do
  Print("K=Id", b.id, " |K|=", b.sizeK, " |A|=", b.sizeA, " |W|=", b.w_size, " rat=", b.rat_classes, " snf=", Collected(b.snf), "\n");
od;
QUIT;
