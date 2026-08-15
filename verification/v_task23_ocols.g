LoadPackage("ctbllib");;
names := AllCharacterTableNames(IsPerfect, true, IsDuplicateTable, false);;
Print("=== orthogonal candidates: faithful irreducible, indicator +1, degree 3,4,6,7 ===\n");
for nm in names do
  t := CharacterTable(nm);
  if t = fail then continue; fi;
  if Size(t) > 10^11 then continue; fi;
  ind := Indicator(t,2);
  irr := Irr(t);
  for i in [1..Length(irr)] do
    chi := irr[i];
    if chi[1] in [3,4,6,7] and Length(ClassPositionsOfKernel(chi)) = 1 and ind[i] = 1 then
      Print(nm, "  |G|=", Size(t), "  deg=", chi[1],
            "  |Z|=", Length(ClassPositionsOfCentre(t)),
            "  field=", Field(chi), "\n");
    fi;
  od;
od;
QUIT;
