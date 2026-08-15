# SELF-AUDIT of results/order128_pair_squaring_invariant.md
#  (1) cross-check the Qof reconstruction against direct group squaring;
#  (2) attempt a RIGOROUS table-of-marks isomorphism test (not just row multisets).
LogTo("/Users/tilemachosvassias/DissAnalysis/dring-project/results/order128_pairs/pair128_selfaudit.out");

# ---- (1) Qof correctness ----
CheckQof := function(id)
  local G, Phi, hV, V, pcV, pcP, ev, coord, q, qe, bmat, i, j, allc, c, direct, recon, ok;
  G := SmallGroup(128, id); Phi := FrattiniSubgroup(G);
  hV := NaturalHomomorphismByNormalSubgroup(G, Phi); V := Image(hV);
  pcV := Pcgs(V); pcP := Pcgs(Phi); ev := List(pcV, x->x);
  coord := z -> ExponentsOfPcElement(pcP, z) * Z(2)^0;
  q := v -> coord(PreImagesRepresentative(hV, v)^2);
  qe := List(ev, e -> q(e));
  bmat := List([1..4], i -> List([1..4], j ->
      coord(Comm(PreImagesRepresentative(hV,ev[i]), PreImagesRepresentative(hV,ev[j])))));
  # reconstruct q(v) for ALL 16 v via the quadratic-expansion formula and compare
  ok := true;
  for c in List(Tuples([0,1],4), x->x*Z(2)^0) do
    recon := Zero(qe[1]);
    for i in [1..4] do if IsOne(c[i]) then recon := recon + qe[i]; fi; od;
    for i in [1..4] do for j in [i+1..4] do
      if IsOne(c[i]) and IsOne(c[j]) then recon := recon + bmat[i][j]; fi;
    od; od;
    # direct: build the V-element from coords, square its lift
    direct := q(Product([1..4], i -> pcV[i]^(IntFFE(c[i]))));
    if recon <> direct then ok := false;
      Print("  MISMATCH id=",id," c=",c," recon=",recon," direct=",direct,"\n"); fi;
  od;
  Print("id=", id, ": Qof reconstruction matches direct squaring on all 16 vectors: ", ok, "\n");
end;
Print("== (1) Qof correctness ==\n");
CheckQof(1597); CheckQof(1598);

# ---- (2) rigorous Burnside-ring / table-of-marks isomorphism ----
Print("\n== (2) table-of-marks isomorphism ==\n");
tm1 := TableOfMarks(SmallGroup(128,1597));
tm2 := TableOfMarks(SmallGroup(128,1598));
Print("IsomorphismTom available: ", IsBound(IsomorphismTom), "\n");
if IsBound(IsomorphismTom) then
  iso := IsomorphismTom(tm1, tm2);
  Print("IsomorphismTom(tm1,tm2) = ", iso, "\n");
  Print("=> B(1597) ~ B(1598) as rings: ", iso <> fail, "\n");
else
  Print("no IsomorphismTom; reporting only necessary invariants (NOT a proof)\n");
fi;
LogTo();
QUIT;
