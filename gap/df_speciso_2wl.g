Read("gap/dring_sieve_standalone.g");
Wr := function(s) local o; o:=OutputTextFile("/tmp/hunt128_run/speciso.out", true);
  SetPrintFormattingStatus(o,false); WriteLine(o,s); CloseStream(o); end;;

# Galois-invariant entry code (exponent-4 groups: all entries in Z[i]).
cg := function(x) local c; c:=ComplexConjugate(x); return [x+c, x*c]; end;;

BuildCoded := function(id)
  local G,cls,T,n;
  G:=SmallGroup(128,id); cls:=SpeciesClassesD(G); T:=SpeciesTableD(G,cls); n:=Length(cls);
  return rec(n:=n, C:=List(T, row->List(row, cg)));
end;;

Wr("building species table 1597 ...");  A:=BuildCoded(1597);;  Wr(Concatenation("  1597 done, rkD=",String(A.n)));
Wr("building species table 1598 ...");  B:=BuildCoded(1598);;  Wr(Concatenation("  1598 done, rkD=",String(B.n)));
n:=A.n;;

# 2-dimensional Weisfeiler-Leman on the two coded square tables, shared colour names.
rowA:=List([1..n],x->1);; colA:=List([1..n],x->1);;
rowB:=List([1..n],x->1);; colB:=List([1..n],x->1);;
round:=0; stable:=false;
while not stable and round<40 do
  round:=round+1;
  # refine columns using current row colours
  scA:=List([1..n], j->Collected(List([1..n], i->[A.C[i][j], rowA[i]])));
  scB:=List([1..n], j->Collected(List([1..n], i->[B.C[i][j], rowB[i]])));
  pool:=Set(Concatenation(scA,scB));
  ncolA:=List(scA, s->PositionSorted(pool,s));  ncolB:=List(scB, s->PositionSorted(pool,s));
  # refine rows using updated column colours
  srA:=List([1..n], i->Collected(List([1..n], j->[A.C[i][j], ncolA[j]])));
  srB:=List([1..n], i->Collected(List([1..n], j->[B.C[i][j], ncolB[j]])));
  pool2:=Set(Concatenation(srA,srB));
  nrowA:=List(srA, s->PositionSorted(pool2,s));  nrowB:=List(srB, s->PositionSorted(pool2,s));
  stable:=(ncolA=colA and ncolB=colB and nrowA=rowA and nrowB=rowB);
  colA:=ncolA; colB:=ncolB; rowA:=nrowA; rowB:=nrowB;
  Wr(Concatenation("  round ",String(round),": rowcolours=",String(Size(Set(rowA))),
     " colcolours=",String(Size(Set(colA))),
     " rowWLeq=",String(Collected(rowA)=Collected(rowB)),
     " colWLeq=",String(Collected(colA)=Collected(colB))));
od;

roweq:=Collected(rowA)=Collected(rowB);; coleq:=Collected(colA)=Collected(colB);;
Wr(Concatenation("stable after ",String(round)," rounds; rowWLeq=",String(roweq)," colWLeq=",String(coleq)));
Wr(Concatenation("row class sizes = ",String(SortedList(List(Collected(rowA),x->x[2])))));
Wr(Concatenation("col class sizes = ",String(SortedList(List(Collected(colA),x->x[2])))));
maxcls:=Maximum(List(Collected(rowA),x->x[2]));;
Wr(Concatenation("max row class size = ",String(maxcls)));

if roweq and coleq and maxcls=1 then
  # discrete: shared colours give a forced bijection; verify exact folded equality.
  fr:=List([1..n], i->Position(rowB, rowA[i]));   # G-row i -> H-row
  fc:=List([1..n], j->Position(colB, colA[j]));   # G-col j -> H-col
  ok:=ForAll([1..n], i->ForAll([1..n], j-> A.C[i][j]=B.C[fr[i]][fc[j]]));
  Wr(Concatenation("DISCRETE. SPECIES TABLES ISOMORPHIC (Galois-folded, exact) = ",String(ok)));
else
  Wr("NOT discrete -- report class sizes above; backtracking needed for a definitive iso/no-iso.");
fi;
Wr("DONE"); QUIT;
