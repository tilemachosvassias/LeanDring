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
  for g in gens do
    for i in [1..4] do for j in [1..4] do
      r := ListWithIdenticalEntries(16, Zero(GF(q)));
      for idx in [1..4] do for M in [1..4] do
        r[(idx-1)*4+M] := r[(idx-1)*4+M] + g[i][idx]*g[j][M];
      od; od;
      r[(i-1)*4+j] := r[(i-1)*4+j] - One(GF(q));
      Add(eqs, r);
    od; od;
  od;
  ns := NullspaceMat(TransposedMat(eqs));
  cands := List(ns, v -> List([1..4], i -> List([1..4], j -> v[(i-1)*4+j])));
  for B in cands do
    A := B - TransposedMat(B);
    if RankMat(A) = 4 then return A; fi;
  od;
  return fail;
end;;
symplBasis := function(B, q)
  local bil, e1, cand, f1, W, e2, f2;
  bil := function(u,v) return u*B*v; end;
  e1 := One(GF(q))*[1,0,0,0];
  cand := First(IdentityMat(4,GF(q)), v -> bil(e1,v) <> Zero(GF(q)));
  f1 := cand * bil(e1,cand)^-1;
  W := NullspaceMat(TransposedMat([e1*B, f1*B]));
  e2 := W[1];
  f2 := W[2] * bil(e2,W[2])^-1;
  return [e1, e2, f2, f1];
end;;
run := function(q)
  local G, gens, S3, B, h, S, J, hom, PS, iso, P2, reps, A5s, res, sub, Ug, U, N, lbl, gr;
  G := SL(2,q); gens := GeneratorsOfGroup(G);
  S3 := List(gens, A -> sym3mat(A,q));
  B := invAltForm(S3, q);
  if B = fail then Print("q=",q," NO alternating invariant form\n"); return; fi;
  h := symplBasis(B, q);
  S := SP(4,q); J := InvariantBilinearForm(S).matrix;
  gr := h*B*TransposedMat(h);
  if gr <> J then
    if gr = -J then h[1] := -h[1]; else Print("q=",q," gram mismatch\n"); return; fi;
  fi;
  hom := ActionHomomorphism(S, NormedRowVectors(GF(q)^4), OnLines);
  PS := Image(hom);
  iso := IsomorphismPermGroup(G);; P2 := Image(iso);;
  reps := RepresentativesPerfectSubgroups(P2);;
  A5s := List(Filtered(reps, U -> Size(U)=120), U -> PreImage(iso,U));
  res := [["Sym3 SL2(q)", GeneratorsOfGroup(G)]];
  for lbl in [1..Length(A5s)] do
    Add(res, [Concatenation("Sym3 2.A5_", String(lbl)), GeneratorsOfGroup(A5s[lbl])]);
  od;
  for sub in res do
    Ug := Group(List(sub[2], A -> h*sym3mat(A,q)*h^-1));
    if not IsSubset(S, GeneratorsOfGroup(Ug)) then Print("q=",q,"  !! ",sub[1]," not in Sp4\n"); continue; fi;
    U := Image(hom, Ug); N := Normalizer(PS, U);
    Print("q=", q, "  ", sub[1], ": |U|=", Size(U), " |N|=", Size(N),
          " PSN=", Size(N)=Size(U),
          " irred=", MTX.IsIrreducible(GModuleByMats(GeneratorsOfGroup(Ug), GF(q))), "\n");
  od;
end;;
for q in [7,9,11,13,19] do run(q); od;
QUIT;
