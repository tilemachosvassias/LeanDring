LoadPackage("ctbllib");;
# For each S-candidate (H,chi): is chi stabilised by an outer automorphism?
# Test: induce chi to H.2; norm 2 <=> chi extends (Out fixes chi); norm 1 <=> Out moves chi.
check := function(nm, nm2)
  local t, t2, irr, ind, i, chi, indc, nrm;
  t := CharacterTable(nm);
  t2 := CharacterTable(nm2);
  if t = fail or t2 = fail then Print(nm, " / ", nm2, " : table missing\n"); return; fi;
  if GetFusionMap(t, t2) = fail then Print(nm, " -> ", nm2, " : no stored fusion\n"); return; fi;
  irr := Irr(t); ind := Indicator(t,2);
  for i in [1..Length(irr)] do
    chi := irr[i];
    if chi[1] in [2,4,6] and Length(ClassPositionsOfKernel(chi))=1 and ind[i] = -1 then
      indc := InducedClassFunction(chi, t2);
      nrm := ScalarProduct(t2, indc, indc);
      Print(nm, " in ", nm2, ": deg ", chi[1], " field ", Field(chi),
            "  Out-stable=", nrm = 2, "\n");
    fi;
  od;
end;;
check("2.A5", "2.S5");
check("2.A5", "2.A5.2");
check("2.A6", "2.A6.2_1");
check("2.A6", "2.A6.2_2");
check("2.A6", "2.A6.2_3");
check("2.L3(2)", "2.L3(2).2");
check("2.L2(13)", "2.L2(13).2");
check("2.J2", "2.J2.2");
check("U3(3)", "U3(3).2");
QUIT;
