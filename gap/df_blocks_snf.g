# df_blocks_snf.g -- blockwise elementary-divisor multiset of Z^F/D_F(G),
# F = ALL Z-valued species of D(G), via the local block model of
# results/df_nonabelian_snf_blocks.md (2026-07-11):
#
#   per subgroup class K:  A = K/K',  W = N_G(K)/K  acting on A,
#   R = { a in A : a^j in a^W for every odd j }   (fused-rational set),
#   L_K < Z^{R/W}  spanned over the linear characters lambda of K by the
#   columns  [z] -> sum_{w in W} lambda(z^w);
#   multiset(D_F) = union over classes of the invariant factors of L_K.
#
# Cross-validated against python/df_blocks_check.py (direct ev_F SNF from
# exact species tables) on all groups of order <= 16 and selected order-32
# groups; see results/df_blocks_check_zoo.log.
#
# Run from repo root:
#   ~/gap-4.15.1/gap -q -b gap/df_blocks_snf.g < /dev/null > log 2>&1 &

DFBlockDivisors := function(G)
  local divs, ccs, cls, K, N, Kp, hom, A, elms, na, pre, gensN, actg, i, j,
        orbit, orbits, seen, R, a, o, ok, jj, p, W, stab, gA, oA, expA,
        chars, t, cols, col, orb, z, s, y, val, B, ed, nz, tvecs, chi;
  divs := [];
  ccs := ConjugacyClassesSubgroups(G);
  for cls in ccs do
    K := Representative(cls);
    N := Normalizer(G, K);
    Kp := DerivedSubgroup(K);
    hom := NaturalHomomorphismByNormalSubgroupNC(K, Kp);
    A := Image(hom);
    elms := Elements(A);
    na := Length(elms);
    pre := List(elms, x -> PreImagesRepresentative(hom, x));
    W := Size(N) / Size(K);
    # N-action on A-indices via conjugation (factors through W)
    gensN := GeneratorsOfGroup(N);
    if Length(gensN) = 0 then gensN := [ One(N) ]; fi;
    actg := List(gensN, n -> List([1..na],
                 i -> Position(elms, Image(hom, pre[i]^n))));
    # orbits on 1..na
    orbits := [];
    seen := BlistList([1..na], []);
    for i in [1..na] do
      if not seen[i] then
        orbit := [i]; seen[i] := true; j := 1;
        while j <= Length(orbit) do
          for p in actg do
            if not seen[p[orbit[j]]] then
              seen[p[orbit[j]]] := true;
              Add(orbit, p[orbit[j]]);
            fi;
          od;
          j := j + 1;
        od;
        Add(orbits, Set(orbit));
      fi;
    od;
    # fused-rational set R (as indices), and its orbits
    R := [];
    for i in [1..na] do
      a := elms[i];
      o := Order(a);
      orb := First(orbits, x -> i in x);
      ok := true;
      jj := 3;
      while jj < o do
        if not Position(elms, a^jj) in orb then ok := false; break; fi;
        jj := jj + 2;
      od;
      if ok then Add(R, i); fi;
    od;
    orbits := Filtered(orbits, x -> x[1] in R or Length(Intersection(x,R))>0);
    # sanity: R is a union of orbits
    for orb in orbits do
      if Length(Intersection(orb, R)) <> Length(orb) then
        Error("R not W-stable");
      fi;
    od;
    # characters of A via independent generators
    gA := IndependentGeneratorsOfAbelianGroup(A);
    oA := List(gA, Order);
    expA := List(elms, x -> IndependentGeneratorExponents(A, x));
    tvecs := Cartesian(List(oA, m -> [0..m-1]));
    cols := [];
    for t in tvecs do
      col := [];
      for orb in orbits do
        stab := W / Length(orb);
        s := 0;
        for y in orb do
          val := Product([1..Length(gA)],
                         k -> E(oA[k])^(t[k] * expA[y][k]));
          s := s + val;
        od;
        s := stab * s;
        if not IsInt(s) then Error("non-integral block entry"); fi;
        Add(col, s);
      od;
      AddSet(cols, col);
    od;
    # B: rows = orbits, columns = distinct columns
    B := List([1..Length(orbits)], i -> List(cols, c -> c[i]));
    if Length(orbits) > 0 then
      ed := ElementaryDivisorsMat(B);
      nz := Filtered(ed, x -> x <> 0);
      if Length(nz) <> Length(orbits) then Error("L_K rank deficient"); fi;
      Append(divs, nz);
    fi;
  od;
  Sort(divs);
  return divs;
end;

DFReport := function(ord, k)
  local divs;
  divs := DFBlockDivisors(SmallGroup(ord, k));
  Print("DF_SNF ", ord, ",", k, " rank ", Length(divs), " ",
        Collected(divs), "\n");
end;

DFCensus := function(ord)
  local n, k, divs, keys, key, ppos, coll;
  n := NumberSmallGroups(ord);
  keys := []; ppos := [];
  for k in [1..n] do
    divs := DFBlockDivisors(SmallGroup(ord, k));
    coll := Collected(divs);
    Print("DF_SNF ", ord, ",", k, " rank ", Length(divs), " ", coll, "\n");
    key := Position(keys, coll);
    if key = fail then
      Add(keys, coll); Add(ppos, [k]);
    else
      Add(ppos[key], k);
    fi;
  od;
  Print("CENSUS order ", ord, ": ", n, " groups, ",
        Length(keys), " distinct DF-SNF multisets; collisions: ",
        Filtered(ppos, x -> Length(x) > 1), "\n");
end;
