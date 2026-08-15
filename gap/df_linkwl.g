Read("gap/dring_sieve_standalone.g");
v2r := function(r) if r=0 then return 999; fi; return PValuation(r,2); end;;
Wr := function(s) local o; o:=OutputTextFile("/tmp/hunt128_run/linkwl.out", true);
  SetPrintFormattingStatus(o,false); WriteLine(o,s); CloseStream(o); end;;
# WL colour-class multiset of the pairwise D_F-linkage graph (a D-iso invariant,
# finer than the linkage multiset).
LinkWL := function(i)
  local G,cls,T,n,rat,m,TR,L,p,q,col,newcol,stable,key,j;
  G:=SmallGroup(128,i); cls:=SpeciesClassesD(G); T:=SpeciesTableD(G,cls); n:=Length(cls);
  rat:=Filtered([1..n],j->ForAll(T[j],IsInt)); TR:=T{rat}; m:=Length(rat);
  Wr(Concatenation("  #",String(i)," table+rat built (|F|=",String(m),"), building linkage matrix..."));
  L:=NullMat(m,m);
  for p in [1..m] do for q in [p+1..m] do
    L[p][q]:=v2r(Gcd(List([1..n],j->TR[p][j]-TR[q][j]))); L[q][p]:=L[p][q]; od; od;
  Wr(Concatenation("  #",String(i)," WL refining..."));
  col:=List([1..m],p->1); stable:=false;
  while not stable do
    newcol:=List([1..m],p->[col[p],SortedList(List([1..m],q->[L[p][q],col[q]]))]);
    key:=Set(newcol); newcol:=List(newcol,x->Position(key,x));
    if newcol=col then stable:=true; fi; col:=newcol;
  od;
  return SortedList(List(Collected(col),x->x[2]));
end;;
Wr("computing LinkWL 1597 ...");  w1:=LinkWL(1597);;  Wr(Concatenation("1597 WL sizes = ",String(w1)));
Wr("computing LinkWL 1598 ...");  w2:=LinkWL(1598);;  Wr(Concatenation("1598 WL sizes = ",String(w2)));
Wr(Concatenation("LINKAGE-GRAPH WL EQUAL = ", String(w1=w2)));
Wr("DONE"); QUIT;
