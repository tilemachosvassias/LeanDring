# Test: block products U1 x U2 <= Sp2(q) perp Sp2(q) <= Sp4(q), psn in PSp4(q)?
blk := function(A, B, q)
  local M, i, j, z;
  z := Zero(GF(q));
  M := List([1..4], i -> List([1..4], j -> z));
  M[1][1]:=A[1][1]; M[1][4]:=A[1][2]; M[4][1]:=A[2][1]; M[4][4]:=A[2][2];
  M[2][2]:=B[1][1]; M[2][3]:=B[1][2]; M[3][2]:=B[2][1]; M[3][3]:=B[2][2];
  return M;
end;;

test := function(q)
  local G2, iso, P2, reps, A5s, I2, S, hom, PS, cands, nm, name, U, gens, Um, NN, lbl;
  G2 := SL(2,q);
  iso := IsomorphismPermGroup(G2);
  P2 := Image(iso);
  reps := RepresentativesPerfectSubgroups(P2);
  A5s := List(Filtered(reps, U -> Size(U)=120), U -> PreImage(iso,U));
  Print("q=", q, ": #(2.A5 classes in SL2(q)) = ", Length(A5s), "\n");
  I2 := IdentityMat(2, GF(q));
  S := SP(4,q);
  hom := ActionHomomorphism(S, NormedRowVectors(GF(q)^4), OnLines);
  PS := Image(hom);
  Print("  PSp4(",q,") degree ", NrMovedPoints(PS), " size ", Size(PS), "\n");
  cands := [];
  Add(cands, ["SL2 x SL2",   GeneratorsOfGroup(G2), GeneratorsOfGroup(G2)]);
  Add(cands, ["SL2 x 2A5_a", GeneratorsOfGroup(G2), GeneratorsOfGroup(A5s[1])]);
  if Length(A5s) >= 2 then
    Add(cands, ["SL2 x 2A5_b", GeneratorsOfGroup(G2), GeneratorsOfGroup(A5s[2])]);
    Add(cands, ["2A5_a x 2A5_b", GeneratorsOfGroup(A5s[1]), GeneratorsOfGroup(A5s[2])]);
    Add(cands, ["2A5_a x 2A5_a", GeneratorsOfGroup(A5s[1]), GeneratorsOfGroup(A5s[1])]);
  fi;
  for lbl in cands do
    gens := Concatenation(
      List(lbl[2], A -> blk(A, I2, q)),
      List(lbl[3], B -> blk(I2, B, q)));
    Um := Group(gens);
    if not IsSubset(S, GeneratorsOfGroup(Um)) then Print("  !! not in Sp4\n"); fi;
    U := Image(hom, Um);
    NN := Normalizer(PS, U);
    Print("  ", lbl[1], ": |U|=", Size(U), " |N|=", Size(NN),
          "  PSN=", Size(NN)=Size(U), "  perfect=", IsPerfect(U), "\n");
  od;
end;;
test(9);
test(11);
QUIT;
