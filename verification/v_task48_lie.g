# v_task48 audit: INDEPENDENT re-check of the two Lie witnesses of v_task47,
# at parameters v_task47 did NOT test.
Print("### L_3(q): N_S(Z(Syl_p)) and [S:N]  (predict (q+1)(q^2+q+1))\n");
for q in [29,31,32,37,41,49,64] do
  S := PSL(3,q); p := SmallestRootInt(q);
  U := SylowSubgroup(S,p); ZU := Centre(U); N := Normalizer(S,ZU);
  Print("q=",q,"  |Z(U)|=",Size(ZU),"  elemabel=",IsElementaryAbelian(ZU),
        "  [S:N]=",Index(S,N),"  pred=",(q+1)*(q^2+q+1),
        "  ok=",Index(S,N)=(q+1)*(q^2+q+1),
        "  ratio-to-iota1=",Index(S,N)/(q^2+q+1),"\n");
od;
Print("\n### L_5(q)/L_7(2): N_S(U_{P2}) = P2, [S:N] = [d,2]_q, ratio q^2+1\n");
g2 := function(d,q) return ((q^d-1)*(q^(d-1)-1))/((q^2-1)*(q-1)); end;
iota1 := function(d,q) return (q^d-1)/(q-1); end;
for pr in [[5,3],[7,2],[5,4]] do
  d := pr[1]; q := pr[2];
  G := SL(d,q); gens := [];
  for i in [1..2] do for j in [3..d] do
    m := IdentityMat(d,GF(q)); m[i][j] := One(GF(q)); Add(gens, m); od; od;
  U := Group(List(gens, x->ImmutableMatrix(GF(q),x)));
  hom := NaturalHomomorphismByNormalSubgroup(G, Centre(G));
  S := Image(hom); Ub := Image(hom,U); N := Normalizer(S,Ub);
  Print("L_",d,"(",q,")  |U|=",Size(Ub)," abelian=",IsAbelian(Ub),
        "  [S:N]=",Index(S,N),"  [d,2]_q=",g2(d,q),
        "  ok=",Index(S,N)=g2(d,q),
        "  ratio-to-iota1=",Index(S,N)/iota1(d,q)," pred q^2+1=",q^2+1,"\n");
od;
QUIT;
