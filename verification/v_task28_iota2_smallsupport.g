# max |N_{S_s}(A)| over A <= A_s abelian, A <> 1, with FULL support s.
# thresholds: 12*(9-4)^(s-4) falling = 12 * 5!/(9-s)!  for s <= 9
thr := function(s) local r,i; r:=1; for i in [0..s-5] do r := r*(5-i); od;
                    return 12*r; end;
for s in [4..8] do
  S := SymmetricGroup(s); A := AlternatingGroup(s);
  best := 0; bestrep := fail; vals := [];
  for c in ConjugacyClassesSubgroups(S) do
    H := Representative(c);
    if Size(H) > 1 and IsAbelian(H) and IsSubgroup(A,H)
       and Length(MovedPoints(H)) = s then
      Add(vals, Size(Normalizer(S,H)));
      if Size(Normalizer(S,H)) > best then
        best := Size(Normalizer(S,H)); bestrep := H; fi;
    fi;
  od;
  Print("s=",s,"  #classes=",Length(vals),"  max|N_S_s(A)|=",best,
        "  threshold(12*(n-4)^(s-4) at n=9)=",thr(s),
        "  OK=", best <= thr(s), "   witness=",
        List(GeneratorsOfGroup(bestrep)), "\n");
od;
