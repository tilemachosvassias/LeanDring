# v_task48 audit: independent recomputation of V_s and of I(A_n)
# NOT derived from v_task47_spec_Vs.g -- written from the definitions in
# v_task47_psn_pinned.md Theorem SPEC.
Vs := function(s)
  local A, S, cl, V, H, w;
  A := AlternatingGroup(s); S := SymmetricGroup(s);
  V := [];
  for cl in ConjugacyClassesSubgroups(A) do
    H := Representative(cl);
    if Size(H) = 1 then continue; fi;
    # fixed-point-free on [1..s]  <=>  support = s
    if Length(MovedPoints(H)) <> s then continue; fi;
    w := Factorial(s) * Size(DerivedSubgroup(H)) / Size(Normalizer(S,H));
    AddSet(V, w);
  od;
  return V;
end;;

Ispec := function(n)   # exhaustive ind* spectrum of A_n
  local A, cl, I, H;
  A := AlternatingGroup(n); I := [];
  for cl in ConjugacyClassesSubgroups(A) do
    H := Representative(cl);
    if Size(H) = 1 then continue; fi;
    AddSet(I, Index(A, Normalizer(A,H)) * Size(DerivedSubgroup(H)));
  od;
  return I;
end;;

Iunion := function(n, VV)  # union_{s=3..n} C(n,s)*V_s  (SPEC as literally stated)
  local I, s, w;
  I := [];
  for s in [3..n] do
    if not IsBound(VV[s]) then continue; fi;
    for w in VV[s] do AddSet(I, Binomial(n,s)*w); od;
  od;
  return I;
end;;

VV := [];;
for s in [3..9] do
  VV[s] := Vs(s);
  Print("V_", s, " = ", VV[s], "\n");
od;
Print("\n-- mins --\n");
for s in [3..9] do Print("min V_",s," = ",Minimum(VV[s])," ; s^6 = ",s^6,"\n"); od;

for n in [9,10] do
  Print("\n=== n = ", n, " ===\n");
  VV[n] := Vs(n);
  Print("V_",n," (min) = ", Minimum(VV[n]), " card ", Length(VV[n]), "\n");
  I := Ispec(n);
  U := Iunion(n, VV);
  Print("|I(A_n)| = ", Length(I), "  |union| = ", Length(U), "\n");
  Print("IN I BUT NOT IN UNION (SPEC failure): ", Filtered(I, x -> not x in U), "\n");
  Print("IN UNION BUT NOT IN I: ", Filtered(U, x -> not x in I), "\n");
  lo := 4*Binomial(n,4);; hi := 6*Binomial(n,5);;
  Print("hole (", lo, ",", hi, ") intruders in I: ",
        Filtered(I, x -> x > lo and x < hi), "\n");
  Print("hole intruders in UNION: ", Filtered(U, x -> x > lo and x < hi), "\n");
od;
QUIT;
