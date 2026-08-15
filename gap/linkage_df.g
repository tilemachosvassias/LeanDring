ParseTable := function(fname)
  local lines, hdr, n, N, T, i, parts, vals, j, k, c, v, s;
  s := StringFile(fname);
  lines := SplitString(s, "\n");
  hdr := List(SplitString(lines[1], " "), Int);
  n := hdr[1]; N := hdr[2];
  T := [];
  for i in [1..n] do
    parts := List(SplitString(lines[1+i], " "), Int);
    vals := [];
    for j in [1..n] do
      v := 0;
      for k in [1..N] do
        c := parts[2 + (j-1)*N + k];
        if c <> 0 then v := v + c*E(N)^(k-1); fi;
      od;
      Add(vals, v);
    od;
    Add(T, vals);
  od;
  return T;
end;
LinkDF := function(fname)
  local T, n, V, Fidx, DF, H, B, m, L, p, q, g, i, d, cols;
  T := ParseTable(fname);
  n := Length(T);
  V := TransposedMat(T);
  Fidx := Filtered([1..n], i -> ForAll(T[i], IsInt));
  DF := List(V, r -> r{Fidx});
  H := HermiteNormalFormIntegerMat(DF);
  B := Filtered(H, r -> not IsZero(r));
  m := Length(B);
  cols := TransposedMat(B);
  L := List([1..m], i -> List([1..m], j -> 0));
  for p in [1..m] do for q in [p+1..m] do
    g := 0;
    for i in [1..m] do g := GcdInt(g, B[i][p] - B[i][q]); od;
    if g = 0 then d := 99; else d := PValuation(g, 2); fi;
    L[p][q] := d; L[q][p] := d;
  od; od;
  return L;
end;
L13 := LinkDF("results/G64_13.txt");;
L14 := LinkDF("results/G64_14.txt");;
Print("D_F linkage value multisets:\n13: ", Collected(Flat(L13)), "\n14: ", Collected(Flat(L14)), "\n");
r13 := SortedList(List(L13, r -> SortedList(r)));;
r14 := SortedList(List(L14, r -> SortedList(r)));;
Print("D_F linkage row-multisets equal: ", r13 = r14, "\n");
QUIT;
