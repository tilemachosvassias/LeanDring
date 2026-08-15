# order32_height_tower.g -- intrinsic 2-socle height partitions for
# the two extraspecial groups of order 32.
#
# The committed matrix has species as rows and basis generators as columns.
# If U*A*V is the Smith form of A=TransposedMat(M), then the height-r
# socle code S_r=C[2] intersect 2^(r-1)C is spanned modulo 2 by the columns
# V_i for which the i-th Smith divisor is divisible by 2^r.  Coordinate
# equality on S_r is therefore equality of the corresponding column
# signatures. Checked against the known SNF dimensions and regenerated
# species labels for SmallGroup(32,49) and SmallGroup(32,50).

Read("gap/dring_sieve_standalone.g");

HeightPartitionData := function(mat, smith, r)
  local n, inds, sigs, classes;
  n := Length(mat);
  inds := Filtered([1..n],
    i -> smith.normal[i][i] mod (2^r) = 0);
  sigs := List([1..n],
    j -> List(inds, i -> smith.coltrans[j][i] mod 2));
  classes := List(Set(sigs),
    sig -> Filtered([1..n], j -> sigs[j] = sig));
  return rec(
    depth := r,
    dimension := Length(inds),
    basisIndices := inds,
    signatures := sigs,
    classes := classes,
    classSizeMultiset := Collected(List(classes, Length))
  );
end;

CheckRefinement := function(deep, shallow)
  local cls, i, j;
  # S_deep is contained in S_shallow. Equality on the larger shallow
  # code must imply equality on the smaller deep code.
  for cls in shallow.classes do
    for i in cls do
      for j in cls do
        if deep.signatures[i] <> deep.signatures[j] then
          Error("height partitions do not refine");
        fi;
      od;
    od;
  od;
end;

GroundShape := function(cls, positions)
  return Collected(List(positions,
    j -> [Size(cls[j].H), Order(cls[j].q)]));
end;

ExpectedSmith := function(id)
  if id = 49 then
    return [[1,1],[2,25],[4,113],[8,164],[16,46],[32,32]];
  elif id = 50 then
    return [[1,1],[2,19],[4,101],[8,154],[16,42],[32,32]];
  fi;
  Error("no Smith regression registered for this group");
end;

HeightTowerPilot := function(id)
  local mat, G, cls, smith, diag, data, r, d, prior, shapes,
        singletonLabels;

  Read(Concatenation("results/G32_", String(id), "_mat.g"));
  mat := ValueGlobal("DFMAT");
  G := SmallGroup(32, id);
  cls := SpeciesClassesD(G);
  smith := SmithNormalFormIntegerMatTransforms(TransposedMat(mat));
  diag := List([1..Length(mat)], i -> smith.normal[i][i]);

  if Collected(diag) <> ExpectedSmith(id) then
    Error("Smith factors disagree with the committed exact audit");
  fi;

  Print("SmallGroup(32,", id, ") height tower\n");
  Print("  Smith divisors: ", Collected(diag), "\n");
  data := [];
  prior := fail;
  for r in [5,4,3,2,1] do
    d := HeightPartitionData(mat, smith, r);
    Add(data, d);
    if prior <> fail then
      CheckRefinement(prior, d);
    fi;
    prior := d;
    Print("  r=", r, ": dim S_r=", d.dimension,
          ", classes=", Length(d.classes),
          ", size multiset=", d.classSizeMultiset, "\n");

    if r >= 3 then
      shapes := Collected(List(Filtered(d.classes, c -> Length(c) > 1),
        c -> [Length(c), GroundShape(cls, c)]));
      Print("       non-singleton ground shapes=", shapes, "\n");
    fi;

    if r = 5 then
      singletonLabels := List(Filtered(d.classes, c -> Length(c) = 1),
        c -> [c[1], Size(cls[c[1]].H), Order(cls[c[1]].q)]);
      Print("       singleton labels [point,|H|,ord(q)]=",
            singletonLabels, "\n");
    fi;
  od;

  if data[Length(data)].dimension <> Length(mat)-1 then
    Error("the first socle layer is not the expected even-weight code");
  fi;
  if ForAny(data[Length(data)].basisIndices,
      i -> Sum([1..Length(mat)],
        j -> smith.coltrans[j][i] mod 2) mod 2 <> 0) then
    Error("a first-socle Smith generator has odd coordinate weight");
  fi;
  if Length(data[Length(data)].classes) <> Length(mat) then
    Error("the first socle layer should separate every coordinate");
  fi;

  UnbindGlobal("DFMAT");
end;

HeightTowerPilot(49);
HeightTowerPilot(50);
QUIT;
