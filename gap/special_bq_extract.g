Read("gap/dring_sieve_standalone.g");
Wr := function(s) local o; o:=OutputTextFile("/tmp/hunt128_run/analyze2.out", true);
  SetPrintFormattingStatus(o,false); WriteLine(o,s); CloseStream(o); end;;
F:=GF(2);;
# express an element of the elementary abelian W in a fixed F2-basis
coordW := function(w, wbasis, W)
  local e; e:=Enumerator(W);  # not used; do discrete log by brute over 2^3
  return First(Cartesian(List(wbasis,x->[0,1])), c ->
     Product([1..Length(wbasis)], i-> wbasis[i]^c[i]) = w);
end;;
analyze := function(id)
  local G,Ph,W,gens,V,wb,i,j,lam,rk,ranks,M,qv,lambdas,cvec,forms,f,r;
  G:=SmallGroup(128,id); Ph:=FrattiniSubgroup(G); W:=DerivedSubgroup(G); # =Z=Phi
  gens:=MinimalGeneratingSet(G);                 # 4 elements -> basis of V=G/Phi=F2^4
  wb:=MinimalGeneratingSet(W);                   # 3 elements -> basis of W=F2^3
  Wr(Concatenation("=== (128,",String(id),")  dim V=",String(Length(gens)),
     " dim W=",String(Length(wb)),"  (special: V x V ->[.,.]-> W, q:V->W squaring)"));
  # commutator b(gi,gj) as W-coordinate vectors
  Wr("  commutator table [gi,gj] in W-coords:");
  for i in [1..Length(gens)] do for j in [i+1..Length(gens)] do
    Wr(Concatenation("    b(g",String(i),",g",String(j),") = ",
       String(coordW(Comm(gens[i],gens[j]),wb,W))));
  od; od;
  # squaring q(gi) in W-coords
  Wr("  squaring q(gi)=gi^2 in W-coords:");
  for i in [1..Length(gens)] do
    Wr(Concatenation("    q(g",String(i),") = ",String(coordW(gens[i]^2,wb,W))));
  od;
  # isoclinism fingerprint: for each nonzero functional lam on W, rank of alternating
  # form lam(b(.,.)) on V; multiset of the 7 ranks.
  ranks:=[];
  for lam in Filtered(Cartesian(List(wb,x->[0,1])), c->c<>List(wb,x->0)) do
    M:=NullMat(Length(gens),Length(gens),F);
    for i in [1..Length(gens)] do for j in [1..Length(gens)] do
      cvec:=coordW(Comm(gens[i],gens[j]),wb,W);
      M[i][j]:=(cvec*lam) mod 2 * One(F);
    od; od;
    Add(ranks, RankMat(M));
  od;
  Wr(Concatenation("  ISOCLINISM fingerprint (rank multiset of 7 commutator forms) = ",
     String(Collected(ranks))));
end;;
analyze(1597); analyze(1598);
Wr("DONE"); QUIT;
