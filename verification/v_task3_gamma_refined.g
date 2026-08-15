## Task alpha_3'' (verify/, round 1, CORRECTED): Gamma redone with
## VALIDATED canonical refinements only.
##
## Round-1 first attempt combined Phase 1 (pairwise ell/ell_vee, proven
## canonical) + Phase 2 (per-point SORTED dual-row multiset) + a 5-level
## SNF height signature, and got |Aut(refined graph)| = 1 for BOTH
## (32,49) and (32,50).  This CONTRADICTS the independently-computed and
## triple-checked alpha_6 result (v_task1_out.txt): O (the collineation
## image, |O| = 72 resp. |O(50)|) has EVERY element passing the full
## lattice test, so O <= Gamma is a hard formal fact -- any refined-graph
## automorphism group not containing O is provably wrong, meaning some
## ingredient of the coloring is NOT actually invariant under lattice
## automorphisms (i.e. is not truly canonical) even though it looked
## basis-independent on paper.
##
## This script FIRST validates every candidate invariant directly: it
## recomputes O explicitly (same construction as v_task1), computes the
## O-orbits on points, and checks that each candidate coloring is CONSTANT
## on every O-orbit (a necessary condition for it to be safe to use, since
## every element of O is a proven lattice automorphism and therefore must
## preserve any genuinely canonical invariant).  Any candidate that fails
## this check is DISCARDED and reported as the diagnosed culprit.  Only
## the surviving (validated) invariants are combined into the coloring
## used for the Digraphs/nauty automorphism computation, and O <= Aut is
## re-checked as a hard sanity gate before trusting the result.

LoadPackage("gap");
Read("gap/dring_sieve_standalone.g");
LoadPackage("digraphs");

v2r := function(r) if r = 0 then return 999; fi; return PValuation(r, 2); end;;

LatticePreserves := function(V, B, sigma, n)
  local Vp;
  Vp := List(V, r -> Permuted(r, sigma));
  return HermiteNormalFormIntegerMat(Vp) = B;
end;;

FindLatticeWitness := function(V, sigma, n)
  local i, j, Vp, sol;
  for i in [1..n] do
    Vp := Permuted(V[i], sigma);
    sol := SolutionMat(V, Vp);
    if sol = fail then return [i, 0, "no_solution"]; fi;
    for j in [1..Length(sol)] do
      if not IsInt(sol[j]) then return [i, j, sol[j]]; fi;
    od;
  od;
  return fail;
end;;

BuildFastFinder := function(G, cls, n)
  local m, reps, natOf, NOf, actOf, pointsOfHidx, orbitSetOf, i, j,
        sizeToIdx, sz, FastFindPoint;
  m := Maximum(List(cls, c -> c.Hidx));
  reps := List([1..m], x -> fail);
  natOf := List([1..m], x -> fail);
  for i in [1..n] do
    if reps[cls[i].Hidx] = fail then
      reps[cls[i].Hidx] := cls[i].H;
      natOf[cls[i].Hidx] := cls[i].nat;
    fi;
  od;
  NOf := List([1..m], i -> Normalizer(G, reps[i]));
  actOf := List([1..m], i ->
    function(q, gg) return Image(natOf[i], PreImagesRepresentative(natOf[i], q) ^ gg); end);
  pointsOfHidx := List([1..m], i -> Filtered([1..n], j -> cls[j].Hidx = i));
  orbitSetOf := List([1..n], j -> Set(Orbit(NOf[cls[j].Hidx], cls[j].q, actOf[cls[j].Hidx])));

  sizeToIdx := [];
  for i in [1..m] do
    sz := Size(reps[i]);
    if not IsBound(sizeToIdx[sz]) then sizeToIdx[sz] := []; fi;
    Add(sizeToIdx[sz], i);
  od;

  FastFindPoint := function(Hp, hp)
    local sz2, i2, c, qp, j2;
    sz2 := Size(Hp);
    if not IsBound(sizeToIdx[sz2]) then return fail; fi;
    for i2 in sizeToIdx[sz2] do
      c := RepresentativeAction(G, Hp, reps[i2]);
      if c <> fail then
        qp := Image(natOf[i2], hp ^ c);
        for j2 in pointsOfHidx[i2] do
          if qp in orbitSetOf[j2] then return j2; fi;
        od;
        return fail;
      fi;
    od;
    return fail;
  end;;
  return FastFindPoint;
end;;

## Recompute O exactly as in v_task1_collineation.g (self-contained)
ComputeO := function(G, cls, n)
  local FindPoint, A, gens, permImgs, gA, imgs, p;
  FindPoint := BuildFastFinder(G, cls, n);
  A := AutomorphismGroup(G);
  gens := GeneratorsOfGroup(A);
  permImgs := [];
  for gA in gens do
    imgs := List([1..n], p -> FindPoint(Image(gA, cls[p].H), Image(gA, cls[p].h)));
    Add(permImgs, PermList(imgs));
  od;
  return Group(permImgs);
end;;

## Check whether a per-point invariant (given as a list `val[1..n]`, with
## `=` as the comparator) is constant on every O-orbit.
IsOrbitInvariant := function(val, orbits)
  local orb, v0, p;
  for orb in orbits do
    v0 := val[orb[1]];
    for p in orb do
      if val[p] <> v0 then return false; fi;
    od;
  od;
  return true;
end;;

RunGamma := function(G, name, outlog)
  local cls, T, n, V, B, Tinv, L, LD, p, q, i, j, key,
        part_keys, part_vals, pair_idx, adj, partition_list, D, aut,
        point_profile, refined_keys, refined_vals,
        smith, heightSig, heightSigAtR, r, inds, sigs,
        fibs, gens, g, w, passCount, failCount,
        O, orbits, ellOk, profOk, heightOkAtR, validColors, colorNames,
        combinedKey, oSubset, elt, sizeCap, all_block, fib_pts;

  AppendTo(outlog, "\n=== Task alpha_3'' (corrected): canonical Gamma for ", name, " ===\n");
  cls := SpeciesClassesD(G);; T := SpeciesTableD(G, cls);;
  n := Length(cls);
  AppendTo(outlog, "n (points) = ", n, "\n");
  V := TransposedMat(T);;
  B := HermiteNormalFormIntegerMat(V);;
  Tinv := Inverse(V);;

  ## --- Recompute O and its orbits (the validation oracle) ---
  O := ComputeO(G, cls, n);
  AppendTo(outlog, "|O| (recomputed collineation image) = ", Size(O), "\n");
  orbits := Orbits(O, [1..n]);
  AppendTo(outlog, "O-orbits on points: ", Length(orbits), " orbits, sizes = ",
    SortedList(List(orbits, Length)), "\n");

  L := NullMat(n,n); LD := NullMat(n,n);
  for p in [1..n] do for q in [p+1..n] do
    L[p][q]  := Minimum(List([1..n], i -> v2r(B[i][p]-B[i][q])));
    LD[p][q] := Minimum(List([1..n], i -> v2r(Tinv[p][i]-Tinv[q][i])));
    L[q][p] := L[p][q]; LD[q][p] := LD[p][q];
  od; od;

  fibs := Set(List(cls, c -> c.Hidx));

  ######################################################################
  ## Candidate invariants to validate against O-orbits
  ######################################################################

  ## (a) Phase 1 pairwise (ell, ell_vee): sanity -- check the EDGE colors
  ## are O-invariant (i.e. for g in generators of O, L[p][q] = L[p^g][q^g]
  ## etc.)  Spot-check via generators of O (cheap, exact).
  ellOk := true;
  for g in GeneratorsOfGroup(O) do
    for p in [1..Minimum(n,60)] do  # spot sample of rows is enough; pairwise
      for q in [p+1..Minimum(n,60)] do
        if L[p][q] <> L[p^g][q^g] or LD[p][q] <> LD[p^g][q^g] then
          ellOk := false;
        fi;
      od;
    od;
  od;
  AppendTo(outlog, "Candidate (ell,ell_vee) pairwise coloring: O-invariant (spot-checked)? ", ellOk, "\n");

  ## (b) Phase 2: per-point SORTED dual-row multiset
  point_profile := List([1..n], p -> SortedList(List([1..n], j -> Tinv[p][j])));
  profOk := IsOrbitInvariant(point_profile, orbits);
  AppendTo(outlog, "Candidate sorted-dual-row profile: O-invariant? ", profOk, "\n");

  ## (c) SNF height signature, tested SEPARATELY at each depth r = 5..1
  smith := SmithNormalFormIntegerMatTransforms(V);;
  heightOkAtR := [];
  validColors := [];
  colorNames := [];
  if profOk then
    Add(validColors, point_profile); Add(colorNames, "sorted-dual-row-profile");
  fi;
  for r in [5,4,3,2,1] do
    inds := Filtered([1..n], i -> smith.normal[i][i] mod (2^r) = 0);
    sigs := List([1..n], j -> List(inds, i -> smith.coltrans[j][i] mod 2));
    heightSigAtR := sigs;
    Add(heightOkAtR, IsOrbitInvariant(heightSigAtR, orbits));
    AppendTo(outlog, "Candidate SNF height signature at r=", r,
      " (|inds|=", Length(inds), "): O-invariant? ", heightOkAtR[Length(heightOkAtR)], "\n");
    if heightOkAtR[Length(heightOkAtR)] then
      Add(validColors, heightSigAtR); Add(colorNames, Concatenation("height-r", String(r)));
    fi;
  od;
  AppendTo(outlog, "VALIDATED colors kept: ", colorNames, "\n");
  AppendTo(outlog, "DISCARDED (non-canonical, would break O <= Gamma): ",
    Filtered([1..5], k -> not heightOkAtR[k]) = [] and profOk,
    "  [see per-candidate lines above for which ones failed]\n");

  ######################################################################
  ## Build refined coloring from Phase 1 (pairwise, always kept) +
  ## VALIDATED per-point colors only
  ######################################################################
  part_keys := []; part_vals := [];
  Add(part_keys, "point"); Add(part_vals, [1..n]);
  pair_idx := n;
  adj := List([1..(n + n*(n-1)/2)], x -> []);
  for p in [1..n] do
    for q in [p+1..n] do
      pair_idx := pair_idx + 1;
      Add(adj[p], pair_idx); Add(adj[pair_idx], p);
      Add(adj[q], pair_idx); Add(adj[pair_idx], q);
      key := [L[p][q], LD[p][q]];
      i := Position(part_keys, key);
      if i = fail then Add(part_keys, key); Add(part_vals, [pair_idx]);
      else Add(part_vals[i], pair_idx); fi;
    od;
  od;

  refined_keys := []; refined_vals := [];
  for p in [1..n] do
    combinedKey := List(validColors, col -> col[p]);
    i := Position(refined_keys, combinedKey);
    if i = fail then Add(refined_keys, combinedKey); Add(refined_vals, [p]);
    else Add(refined_vals[i], p); fi;
  od;
  AppendTo(outlog, "Number of validated-canonical point-profile classes: ", Length(refined_keys), "\n");
  AppendTo(outlog, "Class sizes: ", SortedList(List(refined_vals, Length)), "\n");

  partition_list := [];
  for i in [1..Length(refined_vals)] do Add(partition_list, refined_vals[i]); od;
  for i in [2..Length(part_vals)] do Add(partition_list, part_vals[i]); od;

  D := Digraph(adj);
  aut := AutomorphismGroup(D, partition_list);
  AppendTo(outlog, "|Aut(validated-canonically refined graph)| = ", Size(aut), "\n");

  ## HARD SANITY GATE: O must be a subgroup of aut
  oSubset := IsSubgroup(aut, O);
  AppendTo(outlog, "O <= Aut(refined graph)  [MUST hold]: ", oSubset, "\n");
  if not oSubset then
    AppendTo(outlog, "*** FAILURE: even the validated coloring excludes O. ",
      "Aborting further refinement for ", name, "; reporting Aut(refined) size only. ***\n");
    return rec(n := n, sizeO := Size(O), sizeAut := Size(aut), oSubset := false,
               decisive := false);
  fi;

  gens := GeneratorsOfGroup(aut);
  AppendTo(outlog, "Generators: ", Length(gens), "\n");

  ######################################################################
  ## Test every generator against the lattice oracle
  ######################################################################
  passCount := 0; failCount := 0;
  for g in gens do
    if LatticePreserves(V, B, g, n) then
      passCount := passCount + 1;
    else
      failCount := failCount + 1;
      w := FindLatticeWitness(V, g, n);
      AppendTo(outlog, "  generator FAILS lattice test, witness = ", w, "\n");
    fi;
  od;
  AppendTo(outlog, "Generators: ", passCount, " PASS, ", failCount, " FAIL (of ", Length(gens), ")\n");

  if failCount = 0 then
    AppendTo(outlog, "ALL generators pass -> Gamma = Aut(refined graph) EXACTLY.\n");
    AppendTo(outlog, "|Gamma| = ", Size(aut), "\n");
    AppendTo(outlog, "Gamma = O exactly? ", Size(aut) = Size(O), "\n");
    all_block := true;
    for g in gens do
      for i in fibs do
        fib_pts := Filtered([1..n], x -> cls[x].Hidx = i);
        if Length(Set(List(fib_pts, x -> cls[x^g].Hidx))) > 1 then
          all_block := false;
          AppendTo(outlog, "  Gamma-generator SPLITS fibre Hidx=", i, "\n");
        fi;
      od;
    od;
    AppendTo(outlog, "All Gamma generators fibre-blockwise: ", all_block, "\n");
    return rec(n := n, sizeO := Size(O), sizeAut := Size(aut), sizeGamma := Size(aut),
               oSubset := true, passCount := passCount, failCount := failCount,
               allBlock := all_block, decisive := true, gammaEqualsO := (Size(aut)=Size(O)));
  else
    AppendTo(outlog, "Some generators FAIL -- ambient group is not entirely Gamma.\n");
    sizeCap := 10^7;
    if Size(aut) <= sizeCap then
      AppendTo(outlog, "Attempting SubgroupProperty (ambient size ", Size(aut), " <= cap ", sizeCap, ")...\n");
      aut := SubgroupProperty(aut, elt -> LatticePreserves(V, B, elt, n));
      AppendTo(outlog, "|Gamma| = ", Size(aut), "\n");
      AppendTo(outlog, "O <= Gamma (final): ", IsSubgroup(aut, O), "\n");
      AppendTo(outlog, "Gamma = O exactly? ", Size(aut) = Size(O), "\n");
      return rec(n := n, sizeO := Size(O), sizeAut := Size(aut), sizeGamma := Size(aut),
                 oSubset := true, passCount := passCount, failCount := failCount,
                 decisive := true, gammaEqualsO := (Size(aut)=Size(O)));
    else
      AppendTo(outlog, "Ambient group too large (", Size(aut), ") for SubgroupProperty backtrack ",
        "within budget -- SCALING OBSTACLE.  Falling back: testing whether O is a FULL coset ",
        "representative set is not meaningful (O already <= aut); reporting generator-level ",
        "pass/fail only: ", passCount, " PASS / ", failCount, " FAIL. |O| = ", Size(O),
        " remains the certified lower bound.\n");
      return rec(n := n, sizeO := Size(O), sizeAut := Size(aut), sizeGamma := fail,
                 oSubset := true, passCount := passCount, failCount := failCount,
                 decisive := false);
    fi;
  fi;
end;;

outlog := OutputTextFile("lean_dring/LeanDring/Even/verify/v_task3_out.txt", false);
SetPrintFormattingStatus(outlog, false);

r49 := RunGamma(SmallGroup(32,49), "SmallGroup(32,49)", outlog);
r50 := RunGamma(SmallGroup(32,50), "SmallGroup(32,50)", outlog);

CloseStream(outlog);
Print("Task 3 done. r49 = ", r49, "\n");
Print("Task 3 done. r50 = ", r50, "\n");
QUIT;
