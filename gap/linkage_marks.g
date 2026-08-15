GetMarks := function(fname)
  local s, lines, i, n, M, j;
  s := StringFile(fname);;
  lines := SplitString(s, "\n");;
  i := First([1..Length(lines)], k -> StartsWith(lines[k], "MARKS"));
  n := Int(SplitString(lines[i], " ")[2]);
  M := [];
  for j in [1..n] do Add(M, List(SplitString(lines[i+j], " "), Int)); od;
  return M;
end;
Linkage := function(M)
  local n, L, p, q, g, i, d;
  n := Length(M);
  L := List([1..n], i -> List([1..n], j -> 0));
  for p in [1..n] do for q in [p+1..n] do
    g := 0;
    for i in [1..n] do g := GcdInt(g, M[i][p] - M[i][q]); od;
    if g = 0 then d := 99; else d := PValuation(g, 2); fi;
    L[p][q] := d; L[q][p] := d;
  od; od;
  return L;
end;
M13 := GetMarks("results/G64_13.txt");;
M14 := GetMarks("results/G64_14.txt");;
L13 := Linkage(M13);; L14 := Linkage(M14);;
# permutation invariant: multiset of sorted linkage rows (colored-graph degree data)
r13 := SortedList(List(L13, r -> SortedList(r)));;
r14 := SortedList(List(L14, r -> SortedList(r)));;
Print("linkage row-multisets equal: ", r13 = r14, "\n");
Print("linkage value multiset 13: ", Collected(Flat(L13)), "\n");
Print("linkage value multiset 14: ", Collected(Flat(L14)), "\n");
QUIT;
