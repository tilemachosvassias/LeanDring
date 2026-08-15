# v_task84 -- independent exhaustive recomputation of min V_10 (v_task49 claims 945)
# V_s = { [S_s:N_{S_s}(H)] * |H'| : 1 != H <= A_s fixed-point-free }
s := 10;;
A := AlternatingGroup(s);;
S := SymmetricGroup(s);;
V := [];; tot := 0;; nonab := 0;;
for cl in ConjugacyClassesSubgroups(A) do
  H := Representative(cl);
  if Size(H) = 1 then continue; fi;
  if Length(MovedPoints(H)) <> s then continue; fi;
  tot := tot + 1;
  if not IsAbelian(H) then nonab := nonab + 1; fi;
  AddSet(V, Index(S, Normalizer(S, H)) * Size(DerivedSubgroup(H)));
od;
Print("s = ", s, "  fpf classes = ", tot, " (non-abelian ", nonab, ")\n");
Print("min V_10 = ", Minimum(V), "   |V_10| = ", Length(V), "\n");
Print("V_10 = ", V, "\n");
QUIT;
