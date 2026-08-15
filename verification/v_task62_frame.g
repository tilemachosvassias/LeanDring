#############################################################################
##  v_task62_frame.g -- the 2^6:A_7 (frame) column of Omega_7(q), directly.
##
##  Realise it as the monomial group  D:A_7 <= SO_7(q)  with V = F_q^7,
##  B = I, D = {diag(eps) : eps in {+-1}^7, prod eps_i = 1} = 2^6, A_7
##  permuting coordinates.  D pins the frame {+-e_i}, so N_{O_7}(D:A_7) is
##  the full monomial group 2^7:S_7 and N_{SO_7}(D:A_7) = <D:A_7, t> with
##      t = diag(-1,1,...,1) * (1 2),   det t = +1.
##  theta(t) = theta(r_{e_1}) * theta(r_{e_1-e_2}) = 1 * 2 = 2.
##  So 2^6:A_7 is psn in Omega_7(q)  <=>  2 is a NON-square  <=> q = +-3 (8).
#############################################################################

Read("v_task62_lib.g");
LogTo("v_task62_frame2_out.txt");

PermMat := function(p, n, F)
  local M, i;
  M := NullMat(n, n, F);
  for i in [1..n] do M[i][i^p] := One(F); od;
  return M;
end;

Print("q  |G|  irred?  det(t)  theta(t)  theta_square  psn?  ",
      "predicted(q mod 8 in {3,5})\n");
for q in Filtered([3..99], n -> IsPrimePowerInt(n) and n mod 2 = 1) do
  F := GF(q); FLD := F;
  B := IdentityMat(7, F);
  gens := [];
  # A_7 on the first 7 coordinates
  for p in GeneratorsOfGroup(AlternatingGroup(7)) do
    Add(gens, PermMat(p, 7, F));
  od;
  # D = even sign changes
  for i in [2..7] do
    d := IdentityMat(7, F); d[1][1] := -One(F); d[i][i] := -One(F);
    Add(gens, d);
  od;
  G := Group(gens);
  M := GModuleByMats(gens, F);
  t := PermMat((1,2), 7, F);
  t[1] := -t[1];                       # diag(-1,1,..,1) * (1 2)
  th := SpNorm(B, t);
  Print(q, "  ", Size(G), "  ", MTX.IsAbsolutelyIrreducible(M), "  ",
        DeterminantMat(t), "  ", th, "  ", IsSq(th), "  ",
        not IsSq(th), "  ", q mod 8 in [3,5],
        "  ok=", (not IsSq(th)) = (q mod 8 in [3,5]),
        "  t-normalises=", ForAll(gens, g -> t*g*t^-1 in G),
        "  t-in-G=", t in G, "\n");
od;
LogTo();
QUIT;
