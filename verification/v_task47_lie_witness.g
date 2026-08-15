# v_task47_lie_witness.g -- the two Lie-side witnesses of Task 47.
#
# ind*(A) = [S : N_S(A)] for abelian A.  We verify, for L_3(q) and L_d(2):
#
#  (W3)  ind*(U_{P_1}) = q^2+q+1  ( = iota(L_3(q)) ), and
#        ind*(Z(Syl_p)) = (q+1)(q^2+q+1)   [ N_S(Z(U)) = B ]
#        and these are the two smallest values of ind* on abelian subgroups.
#
#  (W5)  for L_d(q), N_S(U_{P_2}) = P_2, so
#        ind*(U_{P_2}) = Gaussian binomial [d,2]_q .
#        Checked for L_4(2), L_5(2), L_4(3) by direct normalizer computation.

Print("### PART A: L_3(q) -- full abelian ind* spectrum, two smallest values\n");
for q in [2,3,4,5,7,8,9,11,13] do
  S := PSL(3,q);
  cc := ConjugacyClassesSubgroups(S);
  vals := [];
  for c in cc do
    H := Representative(c);
    if Size(H) > 1 and IsAbelian(H) then AddSet(vals, Size(c)); fi;
  od;
  Print("q=",q," iota1=",vals[1]," (q^2+q+1=",q^2+q+1,")   iota2=",vals[2],
        " ((q+1)(q^2+q+1)=",(q+1)*(q^2+q+1),")\n");
od;

Print("\n### PART B: N_S(Z(Syl_p)) = B  for L_3(q)\n");
for q in [2,3,4,5,7,8,9,11,13,16,17,19,23,25,27] do
  S := PSL(3,q);
  p := SmallestRootInt(q);
  U := SylowSubgroup(S, p);
  ZU := Centre(U);
  N := Normalizer(S, ZU);
  Print("q=",q,"  |Z(U)|=",Size(ZU)," (q=",q,")  [S:N(Z)]=",Index(S,N),
        "  (q+1)(q^2+q+1)=",(q+1)*(q^2+q+1),
        "  ok=",Index(S,N)=(q+1)*(q^2+q+1),"\n");
od;

Print("\n### PART C: N_S(U_{P_2}) = P_2 in L_d(q); ind* = Gaussian [d,2]_q\n");
gauss2 := function(d,q) return ((q^d-1)*(q^(d-1)-1))/((q^2-1)*(q-1)); end;
for pair in [[4,2],[5,2],[4,3],[6,2]] do
  d := pair[1]; q := pair[2];
  G := SL(d,q);
  # U_{P_2} = block upper unitriangular with 2x2 / (d-2)x(d-2) blocks:
  # matrices  [[I_2, X],[0, I_{d-2}]]
  gens := [];
  for i in [1..2] do for j in [3..d] do
    m := IdentityMat(d, GF(q)); m[i][j] := One(GF(q));
    Add(gens, m);
  od; od;
  U := Group(List(gens, x -> ImmutableMatrix(GF(q), x)));
  hom := NaturalHomomorphismByNormalSubgroup(G, Centre(G));
  S := Image(hom);
  Ubar := Image(hom, U);
  N := Normalizer(S, Ubar);
  Print("L_",d,"(",q,"):  |U_P2|=",Size(Ubar)," (q^{2(d-2)}=",q^(2*(d-2)),
        ")  IsAbelian=",IsAbelian(Ubar),
        "  [S:N(U)]=",Index(S,N),"  [d,2]_q=",gauss2(d,q),
        "  ok=",Index(S,N)=gauss2(d,q),"\n");
od;

QUIT;
