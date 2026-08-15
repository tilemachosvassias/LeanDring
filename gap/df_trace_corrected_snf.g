# df_trace_corrected_snf.g -- exact trace-corrected D_F presentation.
#
# Implements Theorem A of results/df_trace_corrected_blocks.md directly
# from subgroup quotients, normalizer fusion, coprime power classes, and
# transporter counts.  It does not read a species-table export.
#
# For each K it forms the fused-Galois classes in A_K=K/K', the integer
# class sums tau_C(lambda), and evaluates the decorated fused marks on the
# rational species rows.  The resulting wide integer matrix is the
# hypothesis-free trace-corrected presentation of D_F.  GAP's exact
# ElementaryDivisorsMat then gives the Smith profile.
#
# Read gap/dring_sieve_standalone.g first (for LinearCharValuesD).

DFTraceLocalData := function(G, K)
  local Kp, hom, A, elms, pre, N, actA, worbits, units, classes, rational,
        unseen, a, cls, j, orb, chars, elK, actChi, chiOrbits, chiReps,
        traces, C, chi, value;
  Kp := DerivedSubgroup(K);
  hom := NaturalHomomorphismByNormalSubgroupNC(K, Kp);
  A := Image(hom);
  elms := Elements(A);
  pre := List(elms, x -> PreImagesRepresentative(hom, x));
  N := Normalizer(G, K);
  actA := function(x, n)
    return Image(hom, PreImagesRepresentative(hom, x)^n);
  end;
  worbits := OrbitsDomain(N, elms, actA);
  units := Filtered([1..Exponent(A)], j -> Gcd(j, Exponent(A)) = 1);

  classes := [];
  rational := [];
  unseen := Set(elms);
  while Length(unseen) > 0 do
    a := unseen[1];
    cls := [];
    for j in units do
      orb := Orbit(N, a^j, actA);
      UniteSet(cls, Set(orb));
    od;
    cls := Set(cls);
    SubtractSet(unseen, cls);
    Add(classes, cls);
    Add(rational, Length(cls) = Length(Orbit(N, a, actA)));
  od;

  # Character representatives modulo W.  Coprime-power conjugates give
  # duplicate columns on F, but retaining them is harmless and keeps the
  # presentation aligned with the ordinary monomial basis.
  elK := Elements(K);
  chars := LinearCharValuesD(K);
  actChi := function(vals, n)
    return List(elK, x -> vals[Position(elK, x^(n^-1))]);
  end;
  chiOrbits := OrbitsDomain(N, chars, actChi);
  chiReps := List(chiOrbits, o -> o[1]);

  traces := [];
  for C in classes do
    Add(traces, []);
    for chi in chiReps do
      value := Sum(C, x -> chi[Position(elK,
                    PreImagesRepresentative(hom, x))]);
      if not IsInt(value) then Error("nonintegral fused-Galois trace"); fi;
      Add(traces[Length(traces)], value);
    od;
  od;

  return rec(K := K, hom := hom, A := A, elms := elms, pre := pre,
             N := N, classes := classes, rational := rational,
             elK := elK, chiReps := chiReps, traces := traces);
end;

DFTraceCorrectedMatrix := function(G)
  local reps, data, totalCols, colStart, rows, b, d, ci, row, F,
        matrix, irrClasses, irrMass, K, RT, canon, r, H, h, gens, adm,
        counts, t, y, pos, m, rem, localj, globalj, value;
  reps := List(ConjugacyClassesSubgroups(G), Representative);
  data := List(reps, K -> DFTraceLocalData(G, K));

  totalCols := 0;
  colStart := [];
  for d in data do
    Add(colStart, totalCols);
    totalCols := totalCols + Length(d.chiReps);
  od;

  rows := [];
  irrClasses := 0;
  for b in [1..Length(data)] do
    d := data[b];
    for ci in [1..Length(d.classes)] do
      if d.rational[ci] then
        Add(rows, rec(block := b, H := d.K,
                      h := PreImagesRepresentative(d.hom,d.classes[ci][1]),
                      class := ci));
      else
        irrClasses := irrClasses + 1;
      fi;
    od;
  od;
  F := Length(rows);
  matrix := List([1..F], r -> ListWithIdenticalEntries(totalCols, 0));
  irrMass := 0;

  for b in [1..Length(data)] do
    d := data[b];
    K := d.K;
    RT := RightTransversal(G, K);
    canon := Set(List(RT, t -> CanonicalRightCosetElement(K, t^-1)));
    if Length(canon) <> Index(G, K) then
      Error("transversal not two-sided at block ", b);
    fi;
    for r in [1..F] do
      H := rows[r].H;
      if Size(H) <= Size(K) then
        h := rows[r].h;
        gens := GeneratorsOfGroup(H);
        if Length(gens) = 0 then gens := [One(G)]; fi;
        adm := Filtered(AsList(RT),
                        t -> ForAll(gens, x -> x^t in K));
        if Length(adm) > 0 then
          counts := ListWithIdenticalEntries(Length(d.classes), 0);
          for t in adm do
            y := Image(d.hom, h^t);
            ci := PositionProperty(d.classes, C -> y in C);
            if ci = fail then Error("fused class lookup failed"); fi;
            counts[ci] := counts[ci] + 1;
          od;
          for ci in [1..Length(d.classes)] do
            if counts[ci] <> 0 then
              m := counts[ci] / Length(d.classes[ci]);
              if not IsInt(m) then Error("class multiplicity not integral"); fi;
              if not d.rational[ci] then
                irrMass := irrMass + counts[ci];
              fi;
              for localj in [1..Length(d.chiReps)] do
                globalj := colStart[b] + localj;
                value := m * d.traces[ci][localj];
                matrix[r][globalj] := matrix[r][globalj] + value;
              od;
            fi;
          od;
        fi;
      fi;
    od;
    if b mod 20 = 0 then
      Print("  trace block ", b, "/", Length(data), "\n");
    fi;
  od;

  Print("TRACE_MATRIX rank ", F, " cols ", totalCols,
        " irrational_classes ", irrClasses,
        " irrational_mass ", irrMass, "\n");
  return matrix;
end;

DFTraceCorrectedDivisors := function(G)
  local matrix, ed, nz;
  matrix := DFTraceCorrectedMatrix(G);
  ed := ElementaryDivisorsMat(matrix);
  nz := Filtered(ed, x -> x <> 0);
  if Length(nz) <> Length(matrix) then Error("trace matrix rank deficient"); fi;
  return nz;
end;

DFTraceReport := function(ord, id)
  local ed;
  Print("TRACE_SNF_START ", ord, ",", id, "\n");
  ed := DFTraceCorrectedDivisors(SmallGroup(ord, id));
  Print("TRACE_DF_SNF ", ord, ",", id, " rank ", Length(ed), " ",
        Collected(ed), "\n");
  return ed;
end;
