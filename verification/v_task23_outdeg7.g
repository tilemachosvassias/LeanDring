# Out-stability of the degree-7 orthogonal characters, computed from the GROUPS
# (the 2-local members have no .2 table in CTblLib).
stabTest := function(G, name, deg)
  local t, cc, n, irr, ind, cand, A, inn, gens, alpha, i, img, j, p, chi, moved, res;
  t := CharacterTable(G);
  cc := ConjugacyClasses(t);
  n := Length(cc);
  irr := Irr(t); ind := Indicator(t,2);
  cand := Filtered([1..Length(irr)], i -> irr[i][1] = deg
            and Length(ClassPositionsOfKernel(irr[i])) = 1 and ind[i] = 1);
  Print(name, "  |G|=", Size(G), "  #faithful deg-", deg, " orthogonal chars: ",
        Length(cand), "\n");
  if IsEmpty(cand) then return; fi;
  A := AutomorphismGroup(G);
  inn := InnerAutomorphismsAutomorphismGroup(A);
  Print("   |Aut|=", Size(A), "  |Out|=", Size(A)/Size(inn), "\n");
  if Size(A) = Size(inn) then
    Print("   Out = 1  =>  Stab_Out(chi) = 1  =>  BRANCH ONE (2 classes, psn)\n");
    return;
  fi;
  res := [];
  for alpha in GeneratorsOfGroup(A) do
    p := [];
    for i in [1..n] do
      img := Image(alpha, Representative(cc[i]));
      j := First([1..n], k -> img in cc[k]);
      p[i] := j;
    od;
    for i in cand do
      chi := irr[i];
      moved := ForAny([1..n], k -> chi[p[k]] <> chi[k]);
      Add(res, [i, moved]);
    od;
  od;
  for i in cand do
    Print("   chi_", i, ": moved by some generator of Aut = ",
          ForAny(Filtered(res, r -> r[1] = i), r -> r[2]), "\n");
  od;
end;;
Print("--- 2^3:L3(2) = AGL(3,2) (split) ---\n");
G1 := First(AllPrimitiveGroups(DegreeOperation, 8), g -> Size(g) = 1344);;
stabTest(G1, "2^3:L3(2) split", 7);
Print("--- perfect groups of order 1344 ---\n");
for k in [1..NrPerfectGroups(1344)] do
  stabTest(PerfectGroup(IsPermGroup, 1344, k), Concatenation("PerfectGroup(1344,", String(k), ")"), 7);
od;
Print("--- perfect groups of order 10752 ---\n");
for k in [1..NrPerfectGroups(10752)] do
  stabTest(PerfectGroup(IsPermGroup, 10752, k), Concatenation("PerfectGroup(10752,", String(k), ")"), 7);
od;
QUIT;
