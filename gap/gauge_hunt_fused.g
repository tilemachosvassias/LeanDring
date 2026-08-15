Read("gap/dring_sieve_standalone.g");
v2r := function(r) if r = 0 then return 999; fi; return PValuation(r, 2); end;;

FusedRationalTableD := function(G)
  local cls, T, N, un, a, i, j, r, c, rowOrbits, colOrbits, orb, cc, rr, match, TF, R, C, val, B, Tinv;
  cls := SpeciesClassesD(G);
  T := SpeciesTableD(G, cls);
  N := Exponent(G);
  un := Filtered([1..N], a -> Gcd(a, N) = 1);
  
  rowOrbits := [];
  for r in [1..Length(T)] do
    if not ForAny(rowOrbits, O -> r in O) then
      orb := [r];
      for a in un do
        rr := List(T[r], x -> GaloisCyc(x, a));
        for j in [1..Length(T)] do
          if not j in orb and T[j] = rr then Add(orb, j); fi;
        od;
      od;
      Add(rowOrbits, Set(orb));
    fi;
  od;
  
  colOrbits := [];
  for c in [1..Length(T[1])] do
    if not ForAny(colOrbits, O -> c in O) then
      orb := [c];
      for a in un do
        cc := List([1..Length(T)], r -> GaloisCyc(T[r][c], a));
        for j in [1..Length(T[1])] do
          if not j in orb then
            match := true;
            for r in [1..Length(T)] do
              if T[r][j] <> cc[r] then match := false; break; fi;
            od;
            if match then Add(orb, j); fi;
          fi;
        od;
      od;
      Add(colOrbits, Set(orb));
    fi;
  od;
  
  TF := [];
  for i in [1..Length(rowOrbits)] do
    TF[i] := [];
    R := rowOrbits[i];
    for j in [1..Length(colOrbits)] do
      C := colOrbits[j];
      val := Sum(C, c -> T[R[1]][c]);
      if not IsInt(val) then Error("val is not integer"); fi;
      TF[i][j] := val;
    od;
  od;
  
  return rec(TF := TF, rowOrbits := rowOrbits, colOrbits := colOrbits, cls := cls);
end;

# Expects: ORDER, ID_START, ID_END
if not IsBound(ORDER) then ORDER := 8; fi;
if not IsBound(ID_START) then ID_START := 1; fi;
if not IsBound(ID_END) then ID_END := NrSmallGroups(ORDER); fi;

out_file := StringFormatted("results/gauge_hunt_{}_{}_{}.txt", ORDER, ID_START, ID_END);
out := OutputTextFile(out_file, false);
SetPrintFormattingStatus(out, false);

for id in [ID_START..ID_END] do
  G := SmallGroup(ORDER, id);
  name := StringFormatted("({},{})", ORDER, id);
  
  FData := FusedRationalTableD(G);
  T := FData.TF;
  n := Length(T);
  V := TransposedMat(T);
  B := HermiteNormalFormIntegerMat(V);
  Tinv := Inverse(V);
  
  bad := []; cross := 0; minmargin := 999;
  for p in [1..n] do for q in [p+1..n] do
    # Check if they are cross-fibre. In fused table, p and q are row orbits.
    # We check if their Hidx match.
    if FData.cls[FData.rowOrbits[p][1]].Hidx <> FData.cls[FData.rowOrbits[q][1]].Hidx then
      l  := Minimum(List([1..n], i -> v2r(B[i][p]-B[i][q])));
      lv := -Minimum(List([1..n], i -> v2r(Tinv[p][i]-Tinv[q][i])));
      cross := cross + 1;
      if l >= lv then
        r1 := FData.rowOrbits[p][1];
        r2 := FData.rowOrbits[q][1];
        p_label := StringFormatted("(|K|={}, ord={}, idx={})", Size(FData.cls[r1].H), Order(FData.cls[r1].h), p);
        q_label := StringFormatted("(|K|={}, ord={}, idx={})", Size(FData.cls[r2].H), Order(FData.cls[r2].h), q);
        perm := (p, q);
        Vp := List(V, r -> Permuted(r, perm));
        ok := HermiteNormalFormIntegerMat(Vp) = B;
        if not ok then
           PrintTo(out, "HNF FAILED FOR SURVIVOR IN ", name, "! p=", p, " q=", q, "\n");
        fi;
        Add(bad, [p, q, l, lv, p_label, q_label, ok]);
      fi;
      if lv - l < minmargin then minmargin := lv - l; fi;
    fi;
  od; od;
  
  line := StringFormatted("{} : {} pts, {} cross-fibre pairs; survivors: {}; min margin: {}", 
                          name, n, cross, Length(bad), minmargin);
  PrintTo(out, line, "\n");
  for b in bad do
    PrintTo(out, "  survivor: p=", b[1], " q=", b[2], " l=", b[3], " lv=", b[4], 
                 " labels: ", b[5], " <-> ", b[6], " HNF-preserves: ", b[7], "\n");
  od;
od;
CloseStream(out);
QUIT;
