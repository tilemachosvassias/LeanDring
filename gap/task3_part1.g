Read("gap/dring_sieve_standalone.g");

Task3RingInvariants := function(id)
  local G, cls, t, ratRows, F, r, c, subCols, uniqueCols, C, E, Einv, i, j, k, prod, c_ijk,
        basis_sq, M_sq, rk_sq, M_mult, mult_rks, frob, frob_k, rk_frob,
        Om_ranks, Om_snf, m, edE, temp_gcd, x,
        T, K, Kp, hom, h, h2, N, s, n, isMatch, Tmat;
  G := SmallGroup(32, id);
  cls := SpeciesClassesD(G);
  t := SpeciesTableD(G, cls);
  ratRows := [];
  for r in [1..Length(t)] do
    isMatch := true;
    for c in [1..Length(t[r])] do
      if not IsInt(t[r][c]) then isMatch := false; break; fi;
    od;
    if isMatch then Add(ratRows, r); fi;
  od;
  F := Length(ratRows);
  subCols := [];
  for c in [1..Length(t[1])] do
    Add(subCols, List(ratRows, r -> t[r][c]));
  od;
  uniqueCols := [];
  for c in [1..Length(subCols)] do
    if Position(uniqueCols, subCols[c]) = fail then Add(uniqueCols, subCols[c]); fi;
  od;
  C := Length(uniqueCols);
  E := [];
  for r in [1..F] do
    E[r] := [];
    for c in [1..C] do E[r][c] := uniqueCols[c][r]; od;
  od;
  
  Einv := E^-1;
  c_ijk := [];
  for i in [1..F] do
    c_ijk[i] := [];
    for j in [1..F] do
      prod := [];
      for c in [1..F] do Add(prod, E[i][c] * E[j][c]); od;
      c_ijk[i][j] := prod * Einv;
    od;
  od;
  
  Print("Group 32, ", id, "\n");
  
  basis_sq := [];
  for i in [1..F] do
    prod := [];
    for x in c_ijk[i][i] do Add(prod, x mod 2); od;
    Add(basis_sq, prod);
  od;
  rk_sq := RankMat(basis_sq * Z(2)^0);
  Print("  Rank of squaring map mod 2: ", rk_sq, "\n");
  
  mult_rks := [];
  for i in [1..F] do
    M_mult := [];
    for j in [1..F] do
      prod := [];
      for x in c_ijk[i][j] do Add(prod, x mod 2); od;
      Add(M_mult, prod);
    od;
    Add(mult_rks, RankMat(M_mult * Z(2)^0));
  od;
  Sort(mult_rks);
  Print("  Ranks of mult by generators mod 2: ", Collected(mult_rks), "\n");
  
  frob := basis_sq * Z(2)^0;
  frob_k := frob;
  for k in [1..6] do frob_k := frob_k * frob; od;
  rk_frob := RankMat(frob_k);
  Print("  Dimension of nilradical mod 2: ", F - rk_frob, "\n");
  Print("  Number of idempotents (F_2 rank): ", rk_frob, " (2^", rk_frob, ")\n");
  
  edE := ElementaryDivisorsMat(E);
  Print("  SNF of E: ", Collected(edE), "\n");
  
  Om_snf := [];
  for m in [1..6] do
    temp_gcd := [];
    for x in edE do Add(temp_gcd, GcdInt(x, 2^m)); od;
    Add(Om_snf, Collected(temp_gcd));
  od;
  for m in [1..6] do Print("  O_", m, " SNF: ", Om_snf[m], "\n"); od;
  
  T := [];
  for r in ratRows do
    K := cls[r].H; Kp := DerivedSubgroup(K);
    hom := NaturalHomomorphismByNormalSubgroupNC(K, Kp);
    h := cls[r].h; h2 := h^2; N := Normalizer(G, K);
    s := fail;
    for c in ratRows do
      if cls[c].H = K then
        isMatch := false;
        for n in Elements(N) do
          if Image(hom, (h2)^n) = Image(hom, cls[c].h) then isMatch := true; break; fi;
        od;
        if isMatch then s := c; break; fi;
      fi;
    od;
    Add(T, Position(ratRows, s));
  od;
  Tmat := NullMat(F, F);
  for r in [1..F] do Tmat[r][T[r]] := 1; od;
  
  Print("  Rank of T* on D_F / 2 D_F: ", RankMat(Tmat * Z(2)^0), "\n");
  Print("\n");
end;

Task3RingInvariants(13);
Task3RingInvariants(14);
QUIT;
