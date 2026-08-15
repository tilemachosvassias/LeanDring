Read("gap/dring_sieve_standalone.g");
Wr := function(s) local o; o:=OutputTextFile("/tmp/hunt128_run/verify_structure.out", true);
  SetPrintFormattingStatus(o,false); WriteLine(o,s); CloseStream(o); end;;
F:=GF(2);; x:=Indeterminate(F,"x");;
verify := function(id)
  local G,A,cand,t,W,q,r,Vb,Wb,coordW,phi,sig,i,Zsig,Zphi,M,cp;
  G:=SmallGroup(128,id);
  # maximal abelian normal subgroup isomorphic to C4^3, index 2
  A:=First(NormalSubgroups(G), N-> Index(G,N)=2 and IsAbelian(N)
        and AbelianInvariants(N)=[4,4,4]);
  Wr(Concatenation("(128,",String(id),"): A=C4^3 normal index2 found: ",String(A<>fail)));
  t:=First(Elements(G), g-> not g in A and g^2=One(G));   # outer involution
  W:=DerivedSubgroup(G);                                  # = 2A = Z = G'
  Wb:=MinimalGeneratingSet(W);
  coordW := function(w) return First(Cartesian(List(Wb,z->[0,1])),
      c-> Product([1..Length(Wb)],i->Wb[i]^c[i])=w); end;
  Vb:=Filtered(GeneratorsOfGroup(A), g-> not g in W);     # lift a basis of A/2A
  Vb:=Filtered(MinimalGeneratingSet(A), g->true);          # 3 gens of C4^3
  # squaring sigma: v -> v^2  and off-diagonal phi: v -> [t,v]=v^t v^-1, both into W
  Zsig:=TransposedMat(List(Vb, v-> coordW(v^2)))*One(F);
  Zphi:=TransposedMat(List(Vb, v-> coordW((v^t)*v^-1)))*One(F);
  M:=Zphi * Zsig^-1;                                       # phi-hat = sigma^-1 . phi (conjugate)
  cp:=CharacteristicPolynomial(F,F,M,1);
  Wr(Concatenation("   char poly of phi-hat = ",String(cp),
     "   irreducible: ",String(IsIrreducible(cp))));
  Wr(Concatenation("   (sigma inv: ",String(RankMat(Zsig)=3),", phi inv: ",String(RankMat(Zphi)=3),")"));
end;;
verify(1597); verify(1598);
Wr("DONE"); QUIT;
