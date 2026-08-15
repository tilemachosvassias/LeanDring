Read("gap/dring_sieve_standalone.g");
TestPerm := function(G, name)
  local cls, T, n, V, H0, i, j, L, B, g, p, q, lab, pts, swaps, sigma, Vp, H1, ok, d, KK;
  cls := SpeciesClassesD(G);
  T := SpeciesTableD(G, cls);
  n := Length(cls);
  V := TransposedMat(T);   # V[j] = ghost vector of basis j; columns = points (species)
  # lattice = row span of V restricted to... all species rational here (extraspecial)
  H0 := HermiteNormalFormIntegerMat(V);
  # point labels: subgroup class index + decoration order
  lab := List(cls, c -> [c.Hidx, Order(c.q), Size(c.H)]);
  # pairwise linkage to find twin edges (weight >= 2)
  B := Filtered(H0, r -> not IsZero(r));
  L := List([1..n], i -> List([1..n], j -> 0));
  for p in [1..n] do for q in [p+1..n] do
    g := 0;
    for i in [1..Length(B)] do g := GcdInt(g, B[i][p] - B[i][q]); od;
    if g <> 0 then d := PValuation(g,2); else d := 99; fi;
    L[p][q] := d; L[q][p] := d;
  od; od;
  Print(name, ": n=", n, "  ell>=2 edges: ");
  swaps := [];
  for p in [1..n] do for q in [p+1..n] do
    if L[p][q] >= 2 then
      Print("(", p, ",", q, ",w", L[p][q], ",|K|", lab[p][3], "/", lab[q][3], ",ord", lab[p][2], "/", lab[q][2], ") ");
      # twin candidate: |K_p| <> |K_q| and both decorations same order > 1 => twin (T1 vs T3, x-shadow)
      if lab[p][3] <> lab[q][3] and lab[p][2] > 1 and lab[q][2] > 1 then Add(swaps, [p,q]); fi;
    fi;
  od; od;
  Print("\n  twin pairs: ", swaps, "\n");
  # test twin-swap sigma (swap all twin pairs simultaneously)
  if swaps <> [] then
    sigma := ();
    for p in swaps do sigma := sigma * (p[1],p[2]); od;
    Vp := List(V, r -> Permuted(r, sigma));
    H1 := HermiteNormalFormIntegerMat(Vp);
    Print("  TWIN-SWAP preserves lattice: ", H0 = H1, "\n");
  fi;
  # test a T2 within-fibre transposition: find the G-fibre (Hidx = last class, K=G), swap two of its pts
  KK := Maximum(List(lab, x -> x[3]));
  pts := Filtered([1..n], i -> lab[i][3] = KK and lab[i][2] > 1);
  if Length(pts) >= 2 then
    sigma := (pts[1], pts[2]);
    Vp := List(V, r -> Permuted(r, sigma));
    H1 := HermiteNormalFormIntegerMat(Vp);
    Print("  T2/G-fibre transposition (", pts[1], ",", pts[2], ") preserves lattice: ", H0 = H1, "\n");
  fi;
end;
TestPerm(SmallGroup(8,3), "D4");
TestPerm(SmallGroup(8,4), "Q8");
TestPerm(SmallGroup(32,49), "(32,49)");
QUIT;
