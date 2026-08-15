# Is Q:SL_k(q) (Siegel/parabolic, R=Q case) self-normalizing in PSp_{2n}(q)?
# Test in Sp4 (k=2) and Sp6 (k=3) for small q, via the projective perm action.
test := function(n, q)
  local S, hom, P, V, W, gens, i, M, Um, U, N, d;
  d := 2*n;
  S := SP(d,q);
  hom := ActionHomomorphism(S, NormedRowVectors(GF(q)^d), OnLines);
  P := Image(hom);
  # stabilizer of the totally isotropic n-space spanned by e_1..e_n in GAP's form
  # GAP's Sp form is antidiagonal: <e_i, e_{d+1-i}> = +-1, so e_1..e_n is totally isotropic.
  W := List([1..n], i -> One(GF(q))*List([1..d], j -> Int(j=i)));
  gens := Filtered(GeneratorsOfGroup(S), g -> true);
  return [P, hom, W];
end;;
# simpler: build the Levi SL_k explicitly as block matrices diag(A, (A^-1)^T-reversed)
lev := function(n, q, A)
  local d, M, i, j, B, rev;
  d := 2*n;
  M := NullMat(d,d,GF(q));
  rev := function(X) return List(Reversed(X), r -> Reversed(r)); end;
  B := rev(TransposedMat(A^-1));
  for i in [1..n] do for j in [1..n] do
    M[i][j] := A[i][j];
    M[n+i][n+j] := B[i][j];
  od; od;
  return M;
end;;
for pair in [[2,5],[2,7],[3,3],[3,5],[3,7],[3,9]] do
  n := pair[1];; q := pair[2];; d := 2*n;;
  S := SP(d,q);;
  L := List(GeneratorsOfGroup(SL(n,q)), A -> lev(n,q,A));;
  if not IsSubset(S, L) then Print("n=",n," q=",q,": Levi not in Sp -- form mismatch\n"); continue; fi;
  # unipotent radical: upper-right block symmetric matrices
  Qg := [];;
  for i in [1..n] do for j in [i..n] do
    M := IdentityMat(d, GF(q));
    M[i][d+1-j] := One(GF(q));
    if i <> j then M[j][d+1-i] := One(GF(q)); fi;
    if M in S then Add(Qg, M); fi;
  od; od;
  Um := Group(Concatenation(L, Qg));;
  if not IsSubset(S, GeneratorsOfGroup(Um)) then Print("n=",n," q=",q,": U not in Sp\n"); continue; fi;
  hom := ActionHomomorphism(S, NormedRowVectors(GF(q)^d), OnLines);;
  P := Image(hom);;
  U := Image(hom, Um);;
  N := Normalizer(P, U);;
  Print("n=", n, " q=", q, ": |U|=", Size(U), " |N|=", Size(N), " index=", Size(N)/Size(U),
        " PSN=", Size(N)=Size(U), " perfect=", IsPerfect(U), "\n");
od;
QUIT;
