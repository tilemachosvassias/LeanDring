# v_task63_sym.g -- the DEFINING-CHARACTERISTIC S-columns that v_task62's
# tables carry in degree 4 (Sym^3 SL_2) but OMIT in degrees 6 and 7.
#
#   Sym^5 SL_2(q) < Sp_6(q)      (p >= 7)   -- missing from p^C6
#   Sym^6 SL_2(q) < Omega_7(q)   (p >= 7)   -- missing from p^O7
#
# For each we check, over F_q directly:
#   (1) dim, absolute irreducibility, faithfulness;
#   (2) the invariant form (alternating for k odd, symmetric for k even);
#   (3) the DIAGONAL outer automorphism g = diag(nu,1): the factor by which
#       Sym^k(g) rescales the form  (= nu^k), hence whether g can be
#       renormalised into Sp_6 / SO_7;
#   (4) for k = 6: det and SPINOR NORM of the renormalised g in SO_7(q).
#
# Rule-S verdicts:
#   k odd  (Sp): multiplier nu^k = nu (nonsquare) => outer in GSp \ Sp
#                => 1 class, PSN.
#   k even (O) : theta(g') = nu^(1+2+...+k/2); k=2 -> nu (nonsquare, and
#                indeed SO_3 = PGL_2 > Omega_3 = PSL_2, the known anchor);
#                k=4 -> nu^3 = nu (nonsquare, Omega_5 = PSp_4 anchor);
#                k=6 -> nu^6 = SQUARE  => PGL_2(q) <= Omega_7(q)
#                => PSL_2(q) NOT psn => 0 classes.

SymPower := function(m, k)
  # matrix of the k-th symmetric power of the 2x2 matrix m, basis x^k,...,y^k
  local a,b,c,d,i,j,t,row,M,co;
  a:=m[1][1]; b:=m[1][2]; c:=m[2][1]; d:=m[2][2];
  M := [];
  for i in [0..k] do              # image of x^(k-i) y^i
    row := ListWithIdenticalEntries(k+1, Zero(a));
    for t in [0..k-i] do
      for j in [0..i] do
        co := Binomial(k-i,t)*Binomial(i,j)
              * a^(k-i-t) * c^t * b^(i-j) * d^j;
        row[t+j+1] := row[t+j+1] + co*One(a);
      od;
    od;
    Add(M, row);
  od;
  return TransposedMat(M);
end;;

SpinorWall := function(g, B)
  # Wall/Zassenhaus spinor norm:  theta(g) = (-2)^k * det(chi) ,
  # k = rank(g-1), chi(x',y') = B((g-1)x', y') on the residual space.
  local n, W, bas, k, chi, i, j, F;
  F := DefaultFieldOfMatrix(g);
  n := Length(g);
  W := g - IdentityMat(n, F);
  bas := BaseMat(TransposedMat(W));      # residual space = image of g-1
  k := Length(bas);
  if k = 0 then return One(F); fi;
  # need preimages: for each basis vector w of the image pick x with (g-1)x = w
  chi := [];
  for i in [1..k] do
    Add(chi, List([1..k], j -> bas[i] * B * bas[j]));
  od;
  return (-2*One(F))^k * DeterminantMat(chi);
end;;

IsSq := function(x, q) return IsZero(x) or IsOne(x^((q-1)/2)); end;;

Print("### Sym^k SL_2(q): form type, multiplier of the diagonal outer, verdict\n");
for q in [7,9,11,13,17,19,23,25,27,29,31,37,41,43,49,121] do
  F := GF(q);
  nu := First(Elements(F), x -> not IsZero(x) and not IsSq(x,q));
  gens := List(GeneratorsOfGroup(SL(2,q)), m -> List(m, r -> List(r, x->x*One(F))));
  for k in [3,5,6] do
    if k >= Characteristic(F) then continue; fi;   # need restricted weight
    S := List(gens, m -> SymPower(m, k));
    G := Group(S);
    Mo := GModuleByMats(S, F);
    absirr := MTX.IsAbsolutelyIrreducible(Mo);
    # invariant form
    B := MTX.InvariantBilinearForm(Mo);
    alt := B = -TransposedMat(B);
    sym := B = TransposedMat(B);
    # diagonal outer
    d := SymPower([[nu,Zero(F)],[Zero(F),One(F)]], k);
    lam := (d * B * TransposedMat(d))[1][k+1] / B[1][k+1];   # scaling factor
    Print("  q=",q," k=",k,"  dim=",k+1," absirr=",absirr,
          " alt=",alt," sym=",sym,
          "  form scales by nu^",LogFFE(lam, nu),
          "  scale-is-square=",IsSq(lam,q));
    if k mod 2 = 1 then
      Print("   => multiplier nonsquare: ", not IsSq(lam,q),
            "  => PSN, 1 class: ", not IsSq(lam,q), "\n");
    else
      # renormalise d to an isometry: need mu^2 * lam = 1
      if IsSq(lam,q) then
        mu := First(Elements(F), x -> not IsZero(x) and x^2*lam = One(F));
        e := mu * d;
        Print("   det=", DeterminantMat(e));
        if not IsOne(DeterminantMat(e)) then e := -e; fi;
        th := SpinorWall(e, B);
        Print("  theta=nu^", LogFFE(th,nu), " square=", IsSq(th,q),
              "  => PGL_2 in Omega_7: ", IsSq(th,q),
              " => psn: ", not IsSq(th,q), "\n");
      else
        Print("   (outer not renormalisable into O)\n");
      fi;
    fi;
  od;
od;

Print("\n### anchor for the spinor routine: Sym^2 (SO_3 = PGL_2 > Omega_3 = PSL_2)\n");
for q in [7,11,13,17,19,23] do
  F := GF(q);
  nu := First(Elements(F), x -> not IsZero(x) and not IsSq(x,q));
  gens := List(GeneratorsOfGroup(SL(2,q)), m -> List(m, r -> List(r, x->x*One(F))));
  S := List(gens, m -> SymPower(m,2));
  Mo := GModuleByMats(S, F);
  B := MTX.InvariantBilinearForm(Mo);
  d := SymPower([[nu,Zero(F)],[Zero(F),One(F)]], 2);
  lam := (d*B*TransposedMat(d))[1][3]/B[1][3];
  mu := First(Elements(F), x -> not IsZero(x) and x^2*lam = One(F));
  e := mu*d; if not IsOne(DeterminantMat(e)) then e := -e; fi;
  th := SpinorWall(e, B);
  Print("  q=",q,"  theta(outer on Sym^2) square = ", IsSq(th,q),
        "   (expected FALSE: PGL_2 = SO_3 > Omega_3)\n");
od;
