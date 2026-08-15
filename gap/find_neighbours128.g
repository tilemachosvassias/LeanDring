LoadPackage("SmallGrp");
neighbours := [];
for i in [1..NumberSmallGroups(128)] do
  G := SmallGroup(128, i);
  if Size(DerivedSubgroup(G)) = 2 and IsElementaryAbelian(G/DerivedSubgroup(G)) then
    Add(neighbours, i);
  fi;
od;
Print("Neighbouring family IDs for 128: ", neighbours, "\n");
QUIT;
