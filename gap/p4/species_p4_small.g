# species_p4_small.g — species-table separation for ALL groups of order 16
# and 81: the two computational cases of the "no counterexample below p^5"
# theorem (p >= 5 at order p^4 is Satz 4.11 / the formalized pairwise
# separation; orders p^n, n <= 3, are Mueller, Satz 2.8.1, at ring level).
#
# Phase 1: rank of D(G) = #M(G)/G for every group of the order.
# Phase 2: only for groups with equal rank, the full species table and a
#          permutation-invariant Weisfeiler-Leman fingerprint. Distinct
#          fingerprints prove the species tables non-isomorphic; any pair
#          left WL-equal is reported for deeper analysis (none occurs).
#
# Verified run: GAP 4.16.0, 2026-07-28; log: results/species_p4_small.log.
# Usage:  gap -q < gap/p4/species_p4_small.g > results/species_p4_small.log

# rank of D(G): number of classes [K,lambda] = sum over subgroup-class
# representatives K of the number of N_G(K)-orbits on linear characters of K
RankD := function(G)
  local r, c, H, N, ext;
  r := 0;
  for c in ConjugacyClassesSubgroups(G) do
    H := Representative(c);
    N := Normalizer(G, H);
    ext := ExternalSet(N, LinearCharacters(H));
    r := r + Length(Orbits(ext));
  od;
  return r;
end;

# full species table; rows [H,h] (N_G(H)-orbits on H/H'), cols [K,lam]
# (N_G(K)-orbits on linear characters); entry = sum over cosets of K fixed
# by H of lam evaluated at the conjugate of h into K.
SpeciesTable := function(G)
  local ccs, rows, cols, c, H, N, HD, nat, orb, o, K, lam, lams, ext,
        T, i, j, r, kcol, q, tv, entry, fixq, fixtab, hcls, kcls, ci, cj;
  ccs := ConjugacyClassesSubgroups(G);
  rows := []; cols := []; hcls := []; kcls := [];
  for ci in [1..Length(ccs)] do
    H  := Representative(ccs[ci]);
    N  := Normalizer(G, H);
    HD := DerivedSubgroup(H);
    nat := NaturalHomomorphismByNormalSubgroup(H, HD);
    orb := OrbitsDomain(N, Elements(Image(nat)),
             {x, g} -> Image(nat, PreImagesRepresentative(nat, x)^g));
    for o in orb do
      Add(rows, [H, PreImagesRepresentative(nat, Representative(o))]);
      Add(hcls, ci);
    od;
    lams := LinearCharacters(H);
    ext  := ExternalSet(N, lams);
    for o in Orbits(ext) do
      Add(cols, [H, Representative(o)]);
      Add(kcls, ci);
    od;
  od;
  if Length(rows) <> Length(cols) then
    Error("row/col count mismatch");
  fi;
  # precompute, per (row-class, col-class) pair, the fixed transversal
  # elements: q with q H q^-1 <= K (right transversal K\G)
  fixtab := [];
  for ci in [1..Length(ccs)] do
    fixtab[ci] := [];
    H := Representative(ccs[ci]);
    for cj in [1..Length(ccs)] do
      K := Representative(ccs[cj]);
      tv := RightTransversal(G, K);
      fixtab[ci][cj] := Filtered(tv,
        q -> ForAll(GeneratorsOfGroup(H), x -> q * x * q^-1 in K));
    od;
  od;
  T := [];
  for i in [1..Length(rows)] do
    r := rows[i];
    T[i] := [];
    for j in [1..Length(cols)] do
      kcol := cols[j];
      lam := kcol[2];
      entry := 0;
      for q in fixtab[hcls[i]][kcls[j]] do
        entry := entry + (q * r[2] * q^-1) ^ lam;
      od;
      T[i][j] := entry;
    od;
  od;
  return T;
end;

# permutation-invariant WL fingerprint of a square matrix over cyclotomics
WLFingerprint := function(T)
  local n, rl, cl, newrl, newcl, srl, scl, rounds;
  n := Length(T);
  rl := ListWithIdenticalEntries(n, 0);
  cl := ListWithIdenticalEntries(n, 0);
  for rounds in [1..3] do
    newrl := List([1..n], i -> SortedList(List([1..n], j -> [T[i][j], cl[j]])));
    newcl := List([1..n], j -> SortedList(List([1..n], i -> [T[i][j], rl[i]])));
    srl := Set(newrl); scl := Set(newcl);
    rl := List(newrl, x -> Position(srl, x));
    cl := List(newcl, x -> Position(scl, x));
  od;
  return [SortedList(List([1..n], i -> SortedList(T[i]))),
          Collected(rl), Collected(cl)];
end;

RunOrder := function(nord)
  local k, ids, ranks, G, i, j, tied, fps, unresolved;
  ids := [1..NumberSmallGroups(nord)];
  Print("=== order ", nord, ": ", Length(ids), " groups ===\n");
  ranks := [];
  for k in ids do
    ranks[k] := RankD(SmallGroup(nord, k));
    Print("  SmallGroup(", nord, ",", k, ")  rank D = ", ranks[k], "\n");
  od;
  Print("rank multiset: ", Collected(ranks), "\n");
  # phase 2 only for rank-tied groups
  tied := Filtered(ids, i -> Number(ids, j -> ranks[j] = ranks[i]) > 1);
  Print("groups needing phase 2 (rank ties): ", tied, "\n");
  fps := [];
  for k in tied do
    fps[k] := WLFingerprint(SpeciesTable(SmallGroup(nord, k)));
  od;
  unresolved := [];
  for i in tied do
    for j in Filtered(tied, j -> j > i) do
      if ranks[i] = ranks[j] then
        if fps[i] = fps[j] then
          Add(unresolved, [i, j]);
          Print("  !! WL-EQUAL pair (", i, ",", j, ") — needs deeper check\n");
        else
          Print("  rank tie (", i, ",", j, ") separated by WL fingerprint\n");
        fi;
      fi;
    od;
  od;
  if Length(unresolved) = 0 then
    Print("ALL ", Length(ids), " groups of order ", nord,
          " pairwise separated (rank or WL).\n");
  fi;
  return unresolved;
end;

u1 := RunOrder(16);;
u2 := RunOrder(81);;
Print("UNRESOLVED total: ", Length(u1) + Length(u2), "\n");
QUIT;
