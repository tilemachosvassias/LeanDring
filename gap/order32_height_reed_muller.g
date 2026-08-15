# order32_height_reed_muller.g -- exact top-fibre Reed--Muller check for
# the two extraspecial groups of order 32.
#
# For the intrinsic height code S_r=C[2] intersect 2^(r-1)C, restrict the
# Smith-transform generators to the G-fibre.  For r=1,...,4, compare this
# restriction exactly with the span of indicators of affine cosets of
# subgroups H/Z of dimension r-1.  That coset code is RM(5-r,4).  Also
# record the S_4 puncture shape on every maximal subgroup fibre.  The
# strengthened guard also checks the general anchor shadows, top-height
# persistence of the Type 1 words, failure of the Schur-square shortcut,
# and vanishing of S_4 on the punctured abelian residue.
#
# Regression anchors: the committed G32 matrices and Smith factors used by
# gpt56_height_tower_pilot.g.  All arithmetic is exact over GF(2).

Read("gap/dring_sieve_standalone.g");

if not IsBound(AFFINE_CUT_EXPORT) then
  AFFINE_CUT_EXPORT := false;
fi;

BitGF2 := function(test)
  if test then
    return One(GF(2));
  fi;
  return Zero(GF(2));
end;

CodeFromGenerators := function(gens, length)
  if Length(gens) = 0 then
    gens := [List([1..length], i -> Zero(GF(2)))];
  fi;
  return VectorSpace(GF(2), gens);
end;

SchurSquareCode := function(code)
  local basis, products, i, j;
  basis := BasisVectors(Basis(code));
  products := [];
  for i in [1..Length(basis)] do
    for j in [i..Length(basis)] do
      Add(products, List([1..Length(basis[i])],
        k -> basis[i][k] * basis[j][k]));
    od;
  od;
  return CodeFromGenerators(products, Length(basis[1]));
end;

HeightCodeOnPositions := function(mat, smith, r, positions)
  local inds, gens;
  inds := Filtered([1..Length(mat)],
    i -> smith.normal[i][i] mod (2^r) = 0);
  gens := List(inds, i -> List(positions,
    j -> (smith.coltrans[j][i] mod 2) * One(GF(2))));
  return CodeFromGenerators(gens, Length(positions));
end;

AffineCosetCode := function(G, cls, positions, ZG, r)
  local subgroups, gens, H, coset;
  subgroups := Filtered(
    List(ConjugacyClassesSubgroups(G), Representative),
    H -> Size(H) = 2^r and IsSubgroup(H, ZG));
  if ForAny(subgroups, H -> not IsNormal(G, H)) then
    Error("an extraspecial preimage H/Z was unexpectedly nonnormal");
  fi;
  gens := [];
  for H in subgroups do
    for coset in RightCosets(G, H) do
      Add(gens, List(positions,
        j -> BitGF2(cls[j].h in coset)));
    od;
  od;
  return CodeFromGenerators(gens, Length(positions));
end;

WeightDistribution := function(code)
  return Collected(List(AsList(code),
    v -> Number(v, x -> x <> Zero(GF(2)))));
end;

SignatureInteger := function(smith, inds, position)
  return Sum([1..Length(inds)],
    k -> (smith.coltrans[position][inds[k]] mod 2) * 2^(k-1));
end;

CheckExtraspecialAffineCuts := function(id)
  local mat, G, cls, smith, top, ZG, r, heightCode, cosetCode, deepCode,
        inds4, j, maximalHidxs, hidx, maximalPositions, maximalCode,
        maximalShapes, fullPositions, heightDCode, heightD1Code, allHidxs,
        heightDMinusOneCode, position, K, H, predicted, checkedType2,
        checkedType3, checkedType1, checkedType1AtD, type1AtDByK,
        schurSquareD, checkedType1InSchurSquare, residualPositions,
        residualCode, residualUnitCount, unitWord, k;

  Read(Concatenation("results/G32_", String(id), "_mat.g"));
  mat := ValueGlobal("DFMAT");
  G := SmallGroup(32, id);
  cls := SpeciesClassesD(G);
  smith := SmithNormalFormIntegerMatTransforms(TransposedMat(mat));
  top := Filtered([1..Length(cls)], j -> Size(cls[j].H) = Size(G));
  ZG := Centre(G);

  if Length(top) <> 16 or Size(ZG) <> 2 then
    Error("unexpected extraspecial top fibre");
  fi;

  if AFFINE_CUT_EXPORT then
    inds4 := Filtered([1..Length(mat)],
      i -> smith.normal[i][i] mod 16 = 0);
    for j in [1..Length(mat)] do
      Print("SIG ", id, " ", SignatureInteger(smith, inds4, j), " ",
            cls[j].Hidx, " ", Size(cls[j].H), " ", j, " ",
            BitGF2(j in top), "\n");
    od;
  fi;

  Print("SmallGroup(32,", id, ") top height codes\n");
  for r in [4,3,2,1] do
    heightCode := HeightCodeOnPositions(mat, smith, r, top);
    cosetCode := AffineCosetCode(G, cls, top, ZG, r);
    if heightCode <> cosetCode then
      Print("  mismatch at r=", r,
            ": height dim=", Dimension(heightCode),
            ", coset dim=", Dimension(cosetCode),
            ", intersection dim=", Dimension(Intersection(heightCode,
              cosetCode)), "\n");
      Error("top height code differs from the affine-coset code");
    fi;
    Print("  r=", r, ": dimension=", Dimension(heightCode),
          ", weights=", WeightDistribution(heightCode), "\n");
  od;

  deepCode := HeightCodeOnPositions(mat, smith, 5, top);
  if Dimension(deepCode) <> 0 then
    Error("S_5 should restrict trivially to the top fibre");
  fi;
  Print("  r=5: dimension=0\n");

  maximalHidxs := Set(List(
    Filtered([1..Length(cls)], j -> Size(cls[j].H) = Size(G) / 2),
    j -> cls[j].Hidx));
  maximalShapes := [];
  for hidx in maximalHidxs do
    maximalPositions := Filtered([1..Length(cls)],
      j -> cls[j].Hidx = hidx);
    maximalCode := HeightCodeOnPositions(mat, smith, 4,
      maximalPositions);
    Add(maximalShapes,
      [Length(maximalPositions), Dimension(maximalCode),
       WeightDistribution(maximalCode)]);
  od;
  Print("  maximal-fibre S_4 shapes=", Collected(maximalShapes), "\n");

  # Regression for the two general shadow formulas used in AC8--AC10.
  # Subgroups containing Z are normal, so no orbit-multiplicity correction
  # is needed for these Type 2/Type 3 rows.
  fullPositions := [1..Length(cls)];
  heightDCode := HeightCodeOnPositions(mat, smith, 4, fullPositions);
  heightD1Code := HeightCodeOnPositions(mat, smith, 5, fullPositions);
  heightDMinusOneCode := HeightCodeOnPositions(mat, smith, 3,
    fullPositions);
  schurSquareD := SchurSquareCode(heightDCode);
  residualPositions := Filtered(fullPositions, j ->
    (not IsSubgroup(cls[j].H, ZG) and Size(cls[j].H) >= 4) or
    (IsSubgroup(cls[j].H, ZG) and IsAbelian(cls[j].H) and
     not cls[j].h in ZG and
     not (Size(cls[j].H) = 4 and
          IsElementaryAbelian(cls[j].H))));
  residualCode := HeightCodeOnPositions(mat, smith, 4,
    residualPositions);
  residualUnitCount := 0;
  for j in [1..Length(residualPositions)] do
    unitWord := List([1..Length(residualPositions)],
      k -> BitGF2(k = j));
    if unitWord in residualCode then
      residualUnitCount := residualUnitCount + 1;
    fi;
  od;
  allHidxs := Set(List(cls, entry -> entry.Hidx));
  checkedType2 := 0;
  checkedType3 := 0;
  checkedType1 := 0;
  checkedType1AtD := 0;
  type1AtDByK := [0, 0, 0];
  checkedType1InSchurSquare := 0;
  for hidx in allHidxs do
    position := First([1..Length(cls)], j -> cls[j].Hidx = hidx);
    K := cls[position].H;
    if IsSubgroup(K, ZG) and not IsAbelian(K) and Size(K) < Size(G) then
      predicted := List([1..Length(cls)], j ->
        BitGF2(cls[j].Hidx = hidx or
          (Size(cls[j].H) = 2 * Size(K) and
           IsSubgroup(cls[j].H, K) and cls[j].h in K)));
      if not predicted in heightDCode then
        Error("a Type 2 cover shadow was absent from S_4");
      fi;
      checkedType2 := checkedType2 + 1;
    elif IsSubgroup(K, ZG) and IsAbelian(K) then
      predicted := List([1..Length(cls)], j ->
        BitGF2((cls[j].Hidx = hidx or
          (Size(cls[j].H) = 2 * Size(K) and
           IsAbelian(cls[j].H) and IsSubgroup(cls[j].H, K))) and
          cls[j].h in ZG));
      if not predicted in heightD1Code then
        Error("a Type 3 central-pair cover shadow was absent from S_5");
      fi;
      checkedType3 := checkedType3 + 1;
    elif not IsSubgroup(K, ZG) then
      # Size(K)=2^k.  Do not use Length(FactorsInt(Size(K))) here:
      # GAP returns FactorsInt(1)=[1], which would misclassify K=1.
      k := LogInt(Size(K), 2);
      predicted := List([1..Length(cls)], j ->
        BitGF2(cls[j].Hidx = hidx or
          (Size(cls[j].H) = 2 * Size(K) and IsAbelian(cls[j].H) and
           IsSubgroup(cls[j].H, K) and IsSubgroup(cls[j].H, ZG) and
           ForAny(Elements(K), x -> IsConjugate(G, cls[j].h, x)))));
      if (k = 0 and not predicted in heightD1Code) or
         (k = 1 and not predicted in heightDCode) or
         (k = 2 and not predicted in heightDMinusOneCode) then
        Error("a Type 1/twin shadow was absent at its predicted height");
      fi;
      if predicted in heightDCode then
        checkedType1AtD := checkedType1AtD + 1;
        type1AtDByK[k + 1] := type1AtDByK[k + 1] + 1;
      fi;
      if predicted in schurSquareD then
        checkedType1InSchurSquare := checkedType1InSchurSquare + 1;
      fi;
      checkedType1 := checkedType1 + 1;
    fi;
  od;
  Print("  anchor-shadow membership checks: Type2=", checkedType2,
        ", Type3=", checkedType3, ", Type1=", checkedType1,
        ", Type1-in-S4=", checkedType1AtD,
        " by k=", type1AtDByK,
        ", Type1-in-SchurSquare(S4)=",
        checkedType1InSchurSquare, "\n");
  Print("  punctured abelian residue: coordinates=",
        Length(residualPositions), ", S4-dimension=",
        Dimension(residualCode), ", unit anchors=",
        residualUnitCount, "\n");

  UnbindGlobal("DFMAT");
end;

CheckExtraspecialAffineCuts(49);
CheckExtraspecialAffineCuts(50);
QUIT;
