## Task 2 (verify/, round 1): D4 regression.
##
## Pipeline sanity check on G = SmallGroup(8,3) = D4 (n = 20 fused points).
## (a) Collineation image O (identical construction to v_task1) must PASS
##     the full lattice test (every generator, and every element since O
##     is tiny).
## (b) Full enumeration of ALL lattice-preserving point permutations, via
##     the exact backtrack of gap/wlaut4.g (2-WL pairwise-invariant
##     coloring + prefix-HNF pruning DFS, then HNF-equality lattice
##     filter).  Recorded prior result (NOTES.md 2n, gap/wlaut4.g):
##     |Gamma(D4)| = 64, all fibre-preserving.  This script reproduces
##     that count independently inside verify/.

LoadPackage("gap");
Read("gap/dring_sieve_standalone.g");

v2r := function(r) if r = 0 then return 999; fi; return PValuation(r, 2); end;;

LatticePreserves := function(V, B, sigma, n)
  local Vp;
  Vp := List(V, r -> Permuted(r, sigma));
  return HermiteNormalFormIntegerMat(Vp) = B;
end;;

outlog := OutputTextFile("lean_dring/LeanDring/Even/verify/v_task2_out.txt", false);
SetPrintFormattingStatus(outlog, false);

G := SmallGroup(8,3);
name := "SmallGroup(8,3) = D4";
AppendTo(outlog, "=== Task 2: D4 regression for ", name, " ===\n");

cls := SpeciesClassesD(G);; T := SpeciesTableD(G, cls);;
n := Length(cls);
AppendTo(outlog, "n (points) = ", n, "\n");
V := TransposedMat(T);;
B := HermiteNormalFormIntegerMat(V);;

########################################################################
## (a) Collineation image O, same construction as v_task1
########################################################################
FindPoint := function(subgrp, elem)
  local i;
  for i in [1..n] do
    if Size(cls[i].H) = Size(subgrp) then
      if ForAny(Elements(G), g -> subgrp^g = cls[i].H and elem^g = cls[i].h) then
        return i;
      fi;
    fi;
  od;
  return fail;
end;;

A := AutomorphismGroup(G);
gens := GeneratorsOfGroup(A);
Inn := InnerAutomorphismsAutomorphismGroup(A);
AppendTo(outlog, "|Aut(D4)| = ", Size(A), ", |Inn(D4)| = ", Size(Inn), "\n");

permImgs := [];
for gA in gens do
  imgs := List([1..n], p -> FindPoint(Image(gA, cls[p].H), Image(gA, cls[p].h)));
  Add(permImgs, PermList(imgs));
od;
O := Group(permImgs);
AppendTo(outlog, "|O| (collineation image) = ", Size(O), "\n");
AppendTo(outlog, "|Aut(D4)|/|Inn(D4)| = ", Size(A)/Size(Inn), "\n");

genPasses := 0; genFails := 0;
for gO in GeneratorsOfGroup(O) do
  if LatticePreserves(V, B, gO, n) then genPasses := genPasses + 1;
  else genFails := genFails + 1;
    AppendTo(outlog, "  *** generator of O FAILS lattice test: ", gO, " ***\n");
  fi;
od;
allPasses := 0; allFails := 0;
for elt in O do
  if LatticePreserves(V, B, elt, n) then allPasses := allPasses + 1;
  else allFails := allFails + 1;
    AppendTo(outlog, "  *** element of O FAILS lattice test: ", elt, " ***\n");
  fi;
od;
AppendTo(outlog, "O generators: ", genPasses, " PASS / ", genFails, " FAIL. ",
  "O all elements: ", allPasses, " PASS / ", allFails, " FAIL (of ", Size(O), ")\n");

########################################################################
## (b) Full enumeration of lattice-preserving permutations (wlaut4.g method)
########################################################################
AppendTo(outlog, "\n--- Full backtrack enumeration (wlaut4.g method) ---\n");

Tinv := Inverse(V);;
L := NullMat(n,n); LD := NullMat(n,n);
for p in [1..n] do for q in [p+1..n] do
  L[p][q]  := Minimum(List([1..n], i -> v2r(B[i][p]-B[i][q])));
  LD[p][q] := Minimum(List([1..n], i -> v2r(Tinv[p][i]-Tinv[q][i])));
  L[q][p] := L[p][q]; LD[q][p] := LD[p][q];
od; od;
pair := function(a,b) if a=b then return 0; fi; return [L[a][b],LD[a][b]]; end;;
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
AppendTo(outlog, "WL class sizes: ", SortedList(List(Collected(col), x -> x[2])), "\n");

order := ShallowCopy([1..n]);
SortBy(order, x -> Number([1..n], y -> col[y] = col[x]));
srcCols := List([1..n], d -> List(order{[1..d]}, x -> x));
projSrc := List([1..n], d ->
  HermiteNormalFormIntegerMat(List(V, r -> r{srcCols[d]})));

imgs2 := List([1..n], x -> 0); used := BlistList([1..n],[]);
found := [];
dfs := function(d)
  local pt, c, prev, okc, imcols;
  if d > n then Add(found, ShallowCopy(imgs2)); return; fi;
  pt := order[d];
  for c in [1..n] do
    if not used[c] and col[c] = col[pt] then
      okc := true;
      for prev in [1..d-1] do
        if pair(pt, order[prev]) <> pair(c, imgs2[order[prev]]) then okc := false; break; fi;
      od;
      if okc then
        imgs2[pt] := c;
        imcols := List(order{[1..d]}, x -> imgs2[x]);
        if HermiteNormalFormIntegerMat(List(V, r -> r{imcols})) = projSrc[d] then
          used[c] := true;
          dfs(d+1);
          used[c] := false;
        fi;
        imgs2[pt] := 0;
      fi;
    fi;
  od;
end;;
dfs(1);
AppendTo(outlog, "Permutations passing pairwise/prefix pruning: ", Length(found), "\n");

fibs := Set(List(Set(List(cls, c -> c.Hidx)),
  h -> Set(Filtered([1..n], j -> cls[j].Hidx = h))));
autCount := 0; fpres := 0; gammaGens := [];
for imgs2 in found do
  perm := PermListList([1..n], imgs2);
  Vp := List(V, r -> Permuted(r, perm));
  if HermiteNormalFormIntegerMat(Vp) = B then
    autCount := autCount + 1;
    Add(gammaGens, perm);
    if Set(List(fibs, f -> Set(List(f, x -> x^perm)))) = fibs then fpres := fpres + 1; fi;
  fi;
od;
AppendTo(outlog, "|Gamma(D4)| (exact lattice automorphisms, full enumeration) = ", autCount, "\n");
AppendTo(outlog, "Fibre-partition-preserving among them: ", fpres, "/", autCount, "\n");
AppendTo(outlog, "Expected from NOTES.md 2n / gap/wlaut4.g: 64, all fibre-preserving.\n");

GammaGrp := Group(gammaGens);
AppendTo(outlog, "|Group(Gamma generators)| = ", Size(GammaGrp), "\n");
AppendTo(outlog, "O <= Gamma: ", IsSubgroup(GammaGrp, O), "\n");

CloseStream(outlog);
Print("Task 2 done. |O| = ", Size(O), ", |Gamma| = ", autCount, "\n");
QUIT;
