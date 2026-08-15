sym3mat := function(A, q)
  local a,b,c,d,M,i,j,k,co,t;
  a:=A[1][1]; b:=A[1][2]; c:=A[2][1]; d:=A[2][2];
  M := NullMat(4,4,GF(q));
  for i in [0..3] do
    co := [Zero(GF(q)),Zero(GF(q)),Zero(GF(q)),Zero(GF(q))];
    for j in [0..i] do for k in [0..(3-i)] do
      t := (Binomial(i,j)*Binomial(3-i,k)) * One(GF(q)) * a^j * c^(i-j) * b^k * d^(3-i-k);
      co[j+k+1] := co[j+k+1] + t;
    od; od;
    for j in [1..4] do M[i+1][j] := co[j]; od;
  od;
  return TransposedMat(M);
end;;
invAltForm := function(gens, q)
  local eqs, g, i, j, r, ns, cands, B, idx, M, A;
  eqs := [];
  for g in gens do for i in [1..4] do for j in [1..4] do
    r := ListWithIdenticalEntries(16, Zero(GF(q)));
    for idx in [1..4] do for M in [1..4] do
      r[(idx-1)*4+M] := r[(idx-1)*4+M] + g[i][idx]*g[j][M]; od; od;
    r[(i-1)*4+j] := r[(i-1)*4+j] - One(GF(q));
    Add(eqs, r);
  od; od; od;
  ns := NullspaceMat(TransposedMat(eqs));
  cands := List(ns, v -> List([1..4], i -> List([1..4], j -> v[(i-1)*4+j])));
  for B in cands do A := B - TransposedMat(B); if RankMat(A) = 4 then return A; fi; od;
  return fail;
end;;
symplBasis := function(B, q)
  local bil, e1, cand, f1, W, e2, f2;
  bil := function(u,v) return u*B*v; end;
  e1 := One(GF(q))*[1,0,0,0];
  cand := First(IdentityMat(4,GF(q)), v -> bil(e1,v) <> Zero(GF(q)));
  f1 := cand * bil(e1,cand)^-1;
  W := NullspaceMat(TransposedMat([e1*B, f1*B]));
  e2 := W[1]; f2 := W[2] * bil(e2,W[2])^-1;
  return [e1, e2, f2, f1];
end;;
q := 19;;
G := SL(2,q);; gens := GeneratorsOfGroup(G);;
B := invAltForm(List(gens, A -> sym3mat(A,q)), q);;
h := symplBasis(B,q);;
S := SP(4,q);; J := InvariantBilinearForm(S).matrix;;
if h*B*TransposedMat(h) = -J then h[1] := -h[1]; fi;
hom := ActionHomomorphism(S, NormedRowVectors(GF(q)^4), OnLines);;
PS := Image(hom);;
iso := IsomorphismPermGroup(G);; P2 := Image(iso);;
reps := RepresentativesPerfectSubgroups(P2);;
A5s := List(Filtered(reps, U -> Size(U)=120), U -> PreImage(iso,U));;
U1 := Image(hom, Group(List(GeneratorsOfGroup(A5s[1]), A -> h*sym3mat(A,q)*h^-1)));;
U2 := Image(hom, Group(List(GeneratorsOfGroup(A5s[2]), A -> h*sym3mat(A,q)*h^-1)));;
Print("q=19: |U1|=", Size(U1), " |U2|=", Size(U2), "\n");
Print("Sp4(19)-conjugate? ", IsConjugate(PS, U1, U2), "\n");
QUIT;
