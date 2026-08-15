Check := function(G, lbl)
  local els, ok, mism, tG, ccG, posG, H, tH, ccH, posH, phi, ind, g, s, x, gi;
  els := Elements(G); ok := true; mism := 0;
  tG := CharacterTable(G); ccG := ConjugacyClasses(tG);
  posG := e -> First([1..Length(ccG)], i -> e in ccG[i]);
  for H in List(ConjugacyClassesSubgroups(G), Representative) do
    tH := CharacterTable(H); ccH := ConjugacyClasses(tH);
    posH := e -> First([1..Length(ccH)], i -> e in ccH[i]);
    for phi in Filtered(Irr(tH), c -> c[1]=1) do
      ind := InducedClassFunction(phi, tG);
      for g in els do
        s := 0;
        for x in els do
          gi := x^-1*g*x;
          if gi in H then s := s + phi[posH(gi)]; fi;
        od;
        s := s/Size(H);
        if s <> ind[posG(g)] then mism := mism+1; ok := false; fi;
      od;
    od;
  od;
  Print("[",lbl,"] s_{(<g>,g)}([H,phi]) = chi_Ind(g) for ALL (g,H,phi): ",ok,
        "  mismatches=",mism,"\n");
end;
Check(DihedralGroup(8),"D8");
Check(QuaternionGroup(8),"Q8");
Check(SmallGroup(16,3),"(16,3)");
QUIT;
