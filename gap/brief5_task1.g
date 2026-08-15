IsMetacyclic2Group := function(G)
  local N, Ns;
  Ns := NormalSubgroups(G);
  for N in Ns do
    if IsCyclic(N) and IsCyclic(G/N) then
      return true;
    fi;
  od;
  return false;
end;

PrintTask1 := function(id_list)
  local id, G;
  for id in id_list do
    G := SmallGroup(id[1], id[2]);
    Print("Group: SmallGroup(", id[1], ", ", id[2], ")\n");
    Print("  Structure: ", StructureDescription(G), "\n");
    Print("  Z(G): ", IdGroup(Center(G)), "\n");
    Print("  G': ", IdGroup(DerivedSubgroup(G)), "\n");
    Print("  G^ab: ", IdGroup(G/DerivedSubgroup(G)), "\n");
    Print("  Phi(G): ", IdGroup(FrattiniSubgroup(G)), "\n");
    Print("  Exponent: ", Exponent(G), "\n");
    Print("  Subgroup classes: ", Length(ConjugacyClassesSubgroups(G)), "\n");
    Print("  Is metacyclic: ", IsMetacyclic2Group(G), "\n");
    Print("  Generators and Relators:\n");
    Print("    ", RelatorsOfFpGroup(Image(IsomorphismFpGroup(G))), "\n");
    Print("\n");
  od;
end;

PrintTask1([[64, 13], [64, 14], [64, 47], [64, 48]]);
QUIT;
