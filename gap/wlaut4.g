Read("gap/dring_sieve_standalone.g");
v2r := function(r) if r = 0 then return 999; fi; return PValuation(r, 2); end;;

TestAut := function(G, name)
  local cls, T, V, n, B, Tinv, L, LD, p, q, i, col, newcol, stable, key,
        pair, order, imgs, used, found, dfs, perm, Vp, fibs, fpres, aut,
        srcCols, projSrc;
  cls := SpeciesClassesD(G);; T := SpeciesTableD(G, cls);;
  n := Length(cls);
  V := TransposedMat(T);;
  B := HermiteNormalFormIntegerMat(V);;
  Tinv := Inverse(V);;
  L := NullMat(n,n); LD := NullMat(n,n);
  for p in [1..n] do for q in [p+1..n] do
    L[p][q]  := Minimum(List([1..n], i -> v2r(B[i][p]-B[i][q])));
    LD[p][q] := Minimum(List([1..n], i -> v2r(Tinv[p][i]-Tinv[q][i])));
    L[q][p] := L[p][q]; LD[q][p] := LD[p][q];
  od; od;
  pair := function(a,b) if a=b then return 0; fi; return [L[a][b],LD[a][b]]; end;
  col := List([1..n], p -> 1);
  stable := false;
  while not stable do
    newcol := List([1..n], p ->
      [col[p], SortedList(List([1..n], q -> [pair(p,q), col[q]]))]);
    key := Set(newcol);
    newcol := List(newcol, x -> Position(key, x));
    if newcol = col then stable := true; fi;
    col := newcol;
  od;
  Print(name, " (", n, " pts): WL class sizes: ",
    SortedList(List(Collected(col), x -> x[2])), "\n");
  order := ShallowCopy([1..n]);
  SortBy(order, x -> Number([1..n], y -> col[y] = col[x]));
  # projection lattices of source prefixes, precomputed
  srcCols := List([1..n], d -> List(order{[1..d]}, x -> x));
  projSrc := List([1..n], d ->
    HermiteNormalFormIntegerMat(List(V, r -> r{srcCols[d]})));
  imgs := List([1..n], x -> 0); used := BlistList([1..n],[]);
  found := [];
  dfs := function(d)
    local pt, c, prev, okc, imcols;
    if d > n then Add(found, ShallowCopy(imgs)); return; fi;
    pt := order[d];
    for c in [1..n] do
      if not used[c] and col[c] = col[pt] then
        okc := true;
        for prev in [1..d-1] do
          if pair(pt, order[prev]) <> pair(c, imgs[order[prev]]) then okc := false; break; fi;
        od;
        if okc then
          imgs[pt] := c;
          imcols := List(order{[1..d]}, x -> imgs[x]);
          if HermiteNormalFormIntegerMat(List(V, r -> r{imcols})) = projSrc[d] then
            used[c] := true;
            dfs(d+1);
            used[c] := false;
          fi;
          imgs[pt] := 0;
        fi;
      fi;
    od;
  end;
  dfs(1);
  Print(name, ": permutations passing all projection checks: ", Length(found), "\n");
  fibs := Set(List(Set(List(cls, c -> c.Hidx)),
    h -> Set(Filtered([1..n], j -> cls[j].Hidx = h))));
  aut := 0; fpres := 0;
  for imgs in found do
    perm := PermListList([1..n], imgs);
    Vp := List(V, r -> Permuted(r, perm));
    if HermiteNormalFormIntegerMat(Vp) = B then
      aut := aut + 1;
      if Set(List(fibs, f -> Set(List(f, x -> x^perm)))) = fibs then fpres := fpres+1; fi;
    fi;
  od;
  Print(name, ": lattice automorphisms: ", aut,
    "; fibre-PARTITION-preserving: ", fpres, "\n\n");
end;;

TestAut(SmallGroup(8,3), "D4");
TestAut(SmallGroup(8,4), "Q8");
QUIT;
