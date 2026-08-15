# v_task63_sym6.g -- correct Wall-form spinor norm, anchored on Sym^2
# (SO_3 = PGL_2 > Omega_3 = PSL_2, so theta(outer) MUST be a nonsquare for
# every odd q), then applied to Sym^4 (Omega_5 = PSp_4 anchor) and Sym^6.
#
# Prediction from the hand computation: renormalising the diagonal outer
# g = diag(nu,1) on Sym^(2m) gives an isometry with eigenvalues
# nu^(-m),...,nu^m, i.e. m hyperbolic pairs with ratios nu^1,...,nu^m and a
# fixed vector, so  theta = nu^(1+2+...+m) = nu^(m(m+1)/2).
#   m=1 (Sym^2, dim 3): nu^1  NONSQUARE  -> PSL_2 psn in Omega_3   [anchor]
#   m=2 (Sym^4, dim 5): nu^3  NONSQUARE  -> PSL_2 psn in Omega_5   [anchor]
#   m=3 (Sym^6, dim 7): nu^6  SQUARE     -> PGL_2(q) <= Omega_7(q)
#                                        -> PSL_2(q) NOT psn: 0 classes.

SymPower := function(m, k)
  local a,b,c,d,i,j,t,row,M,co;
  a:=m[1][1]; b:=m[1][2]; c:=m[2][1]; d:=m[2][2];
  M := [];
  for i in [0..k] do
    row := ListWithIdenticalEntries(k+1, Zero(a));
    for t in [0..k-i] do
      for j in [0..i] do
        co := Binomial(k-i,t)*Binomial(i,j)*a^(k-i-t)*c^t*b^(i-j)*d^j;
        row[t+j+1] := row[t+j+1] + co*One(a);
      od;
    od;
    Add(M, row);
  od;
  return TransposedMat(M);
end;;

# rows act on the right:  v -> v*g ;  B(v,w) = v*B*w^T
Theta := function(g, B)
  local n, F, W, P, X, k, chi, i, j;
  F := DefaultFieldOfMatrix(g);
  n := Length(g);
  W := g - IdentityMat(n, F);
  P := BaseMat(W);                     # basis of the residual space Im(g-1)
  k := Length(P);
  if k = 0 then return One(F); fi;
  X := List(P, w -> SolutionMat(W, w));   # X[i]*(g-1) = P[i]
  chi := List([1..k], i -> List([1..k], j -> P[j]*B*X[i]));
  return DeterminantMat(chi);
end;;

IsSq := function(x, q) return not IsZero(x) and IsOne(x^((q-1)/2)); end;;

Print("### validation of Theta: reflections r_v have theta = B(v,v) mod sq\n");
for q in [5,7,9,11,13,17,19,23,25,27] do
  F := GF(q); B := IdentityMat(5, F); ok := true;
  for i in [1..30] do
    v := Random(F^5);
    if IsZero(v*B*v) then continue; fi;
    r := IdentityMat(5,F) - 2*TransposedMat([v])*[v]/(v*B*v);
    if IsSq(Theta(r,B), q) <> IsSq(v*B*v, q) then ok := false; fi;
  od;
  Print("  q=",q," reflections ok: ",ok);
  # multiplicativity on products of two reflections
  ok := true;
  for i in [1..30] do
    v := Random(F^5); w := Random(F^5);
    if IsZero(v*B*v) or IsZero(w*B*w) then continue; fi;
    r := IdentityMat(5,F) - 2*TransposedMat([v])*[v]/(v*B*v);
    s := IdentityMat(5,F) - 2*TransposedMat([w])*[w]/(w*B*w);
    if IsSq(Theta(r*s,B),q) <> (IsSq(Theta(r,B),q) = IsSq(Theta(s,B),q))
      then ok := false; fi;
  od;
  Print("   multiplicative: ",ok,"\n");
od;

Print("\n### Sym^(2m) SL_2(q): theta of the det-normalised diagonal outer\n");
Print("    m=1,2 are ANCHORS (must be NONsquare); m=3 is the p^O7 column\n");
for q in [7,9,11,13,17,19,23,25,27,29,31,37,41,43,49,121,169] do
  F := GF(q); p := Characteristic(F);
  nu := First(Elements(F), x -> not IsZero(x) and not IsSq(x,q));
  gens := List(GeneratorsOfGroup(SL(2,q)),
               m -> List(m, r -> List(r, x->x*One(F))));
  for k in [2,4,6] do
    if k >= p then continue; fi;
    S := List(gens, m -> SymPower(m,k));
    Mo := GModuleByMats(S, F);
    B := MTX.InvariantBilinearForm(Mo);
    d := SymPower([[nu,Zero(F)],[Zero(F),One(F)]], k);
    lam := (d*B*TransposedMat(d))[1][k+1]/B[1][k+1];
    mu := First(Elements(F), x -> not IsZero(x) and x^2*lam = One(F));
    if mu = fail then Print("  q=",q," k=",k," NOT renormalisable\n"); continue; fi;
    e := mu*d;
    if not IsOne(DeterminantMat(e)) then e := -e; fi;
    th := Theta(e, B);
    Print("  q=",String(q,4)," Sym^",k," dim=",k+1,
          " absirr=",MTX.IsAbsolutelyIrreducible(Mo),
          " det=",DeterminantMat(e)=One(F),
          "  theta square = ", IsSq(th,q),
          "   [predicted nu^",k/2*(k/2+1)/2," square=",
          IsSq(nu^(k/2*(k/2+1)/2),q),"]",
          "  => PSL_2(q) psn in Omega_",k+1,": ", not IsSq(th,q), "\n");
  od;
od;
