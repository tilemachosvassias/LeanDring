Read("gap/dring_sieve_standalone.g");
Wr := function(s) local o; o:=OutputTextFile("/tmp/hunt128_run/dendro.out", true);
  SetPrintFormattingStatus(o,false); WriteLine(o,s); CloseStream(o); end;;
# Basis-free linkage dendrogram over ALL species. ell(p,q)=min_c v2(rr[p][c]-rr[q][c])
# is an ultrametric, so the whole pairwise-linkage content = nested partition of species
# by "rows agree mod 2^k". Level-wise block-size multisets are species-permutation
# invariants; if they differ for G vs H, the lattices are NOT species-perm equivalent
# => D(G) not iso D(H).  (rr encodes each Z[i] entry by its two integer coords 2Re,2Im.)
Dendro := function(id)
  local G,cls,T,n,s,x,rr,prof,k,part,red;
  G:=SmallGroup(128,id); cls:=SpeciesClassesD(G); T:=SpeciesTableD(G,cls); n:=Length(cls);
  Wr(Concatenation("  #",String(id)," table built (n=",String(n),")"));
  rr:=[];
  for s in [1..n] do
    x:=[]; Append(x, List(T[s], e-> e+ComplexConjugate(e)));        # 2Re
           Append(x, List(T[s], e-> (e-ComplexConjugate(e))*E(4))); # -2Im
    rr[s]:=x;
  od;
  prof:=[];
  for k in [1..18] do
    red:=List(rr, v-> List(v, y-> y mod 2^k));
    part:=Collected(List([1..n], s-> red[s]));  # group identical reduced rows
    Add(prof, [k, SortedList(List(part, b->b[2]))]);
  od;
  return prof;
end;;
Wr("dendrogram 1597 ...");  p1:=Dendro(1597);;
Wr("dendrogram 1598 ...");  p2:=Dendro(1598);;
for k in [1..18] do
  Wr(Concatenation("level ",String(k),": 1597 #blocks=",String(Length(p1[k][2])),
     " 1598 #blocks=",String(Length(p2[k][2])),
     "  EQUAL=",String(p1[k][2]=p2[k][2])));
od;
Wr(Concatenation("FULL DENDROGRAM (all levels) EQUAL = ", String(p1=p2)));
Wr("DONE"); QUIT;
