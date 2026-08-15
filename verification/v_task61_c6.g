##  v_task61_c6.g -- identify the C_6 member 2^{1+4}.A_5 of Sp_4(q), and
##  recount the 4-dimensional 2.A_5 classes independently of
##  IsomorphicSubgroups (cross-check of v_task61_p4.g).

Print("NrPerfectGroups(1920) = ", NrPerfectGroups(1920), "\n");
for k in [1..NrPerfectGroups(1920)] do
  G := PerfectGroup(IsPermGroup, 1920, k);
  Print("  PerfectGroup(1920,", k, "): ",
        StructureDescription(G),
        "  |Z| = ", Size(Centre(G)),
        "  exponent-2^{1+4}? Sylow2 order ", Size(SylowSubgroup(G,2)), "\n");
od;

##  Cross-check: build Sym^3 of SL(2,q) explicitly and test psn in Sp(4,q).
Sym3 := function(q)
  local G, gens, M, S, F;
  F := GF(q);
  G := SL(2, F);
  gens := List(GeneratorsOfGroup(G), g -> g);
  M := GModuleByMats(gens, F);
  S := MTX.BasisModuleEndomorphisms;  # placeholder, not used
  return fail;
end;;

##  direct: the symmetric cube of the natural module, via the action on
##  homogeneous cubics in two variables.
Sym3Mat := function(g, F)
  local a,b,c,d, M, i, j, coeffs, poly, k;
  a := g[1][1]; b := g[1][2]; c := g[2][1]; d := g[2][2];
  # basis x^3, x^2 y, x y^2, y^3 ; x -> a x + c y, y -> b x + d y
  M := NullMat(4,4,F);
  for i in [0..3] do
    # image of x^{3-i} y^i  = (ax+cy)^{3-i} (bx+dy)^i
    coeffs := [One(F)*0, One(F)*0, One(F)*0, One(F)*0];
    for j in [0..3-i] do
      for k in [0..i] do
        coeffs[ (j + k) + 1 ] := coeffs[ (j+k) + 1 ]
           + Binomial(3-i, j) * a^(3-i-j) * c^j
           * Binomial(i, k) * b^(i-k) * d^k;
      od;
    od;
    # coeffs[m+1] is the coefficient of x^{3-m} y^m  -- careful with ordering
    for j in [1..4] do M[i+1][j] := coeffs[j]; od;
  od;
  return M;
end;;

for q in [5, 7, 11, 13, 19] do
  F := GF(q);
  H := SL(2, q);
  gens := List(GeneratorsOfGroup(H), g -> Sym3Mat(g, F));
  U := Group(gens);
  M := GModuleByMats(gens, F);
  Print("q = ", q, ": Sym^3 SL(2,q): |U| = ", Size(U),
        "  irreducible = ", MTX.IsIrreducible(M), "\n");
  # the invariant form
  Print("   preserves an alternating form: ",
        Length(MTX.InvariantBilinearForm(M)) > 0, "\n");
od;

QUIT;
