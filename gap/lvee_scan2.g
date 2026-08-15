Read("gap/dring_sieve_standalone.g");
v2r := function(r) if r = 0 then return 999; fi; return PValuation(r, 2); end;;

ScanGroup := function(G, name)
  local cls, T, V, n, B, Tinv, p, q, i, l, lv, bad, cross, minmargin,
        perm, Vp, ok;
  cls := SpeciesClassesD(G);; T := SpeciesTableD(G, cls);;
  n := Length(cls);
  V := TransposedMat(T);;
  B := HermiteNormalFormIntegerMat(V);;
  Tinv := Inverse(V);;   # dual functional g has value Tinv[p][g] at point p
  bad := []; cross := 0; minmargin := 999;
  for p in [1..n] do for q in [p+1..n] do
    if cls[p].Hidx <> cls[q].Hidx then
      l  := Minimum(List([1..n], i -> v2r(B[i][p]-B[i][q])));
      lv := -Minimum(List([1..n], i -> v2r(Tinv[p][i]-Tinv[q][i])));
      cross := cross + 1;
      if l >= lv then Add(bad, [p, q, l, lv]); fi;
      if lv - l < minmargin then minmargin := lv - l; fi;
    fi;
  od; od;
  Print(name, ": ", n, " pts, ", cross, " cross-fibre pairs; ",
    "surviving (l >= lvee): ", Length(bad), "; min margin: ", minmargin, "\n");
  for i in [1..Minimum(10, Length(bad))] do
    p := bad[i][1]; q := bad[i][2];
    perm := (p, q);
    Vp := List(V, r -> Permuted(r, perm));
    ok := HermiteNormalFormIntegerMat(Vp) = B;
    Print("  survivor ", bad[i], " |K|=(", Size(cls[p].H), ",", Size(cls[q].H),
      ") ords=(", Order(cls[p].h), ",", Order(cls[q].h),
      ") HNF-preserves lattice: ", ok, "\n");
  od;
end;;

ScanGroup(SmallGroup(8,3), "D4");
ScanGroup(SmallGroup(8,4), "Q8");
ScanGroup(SmallGroup(32,49), "(32,49)");
ScanGroup(SmallGroup(32,50), "(32,50)");
QUIT;
