# Track B: structure of the order-256 char-power-map-twin candidates.
for id in [3678,3679,1741,1742] do
  G := SmallGroup(256,id);
  Zc := Centre(G); P := FrattiniSubgroup(G); Dd := DerivedSubgroup(G);
  Print("(256,",id,"): |Z|=",Size(Zc)," Z=",StructureDescription(Zc),
        " |Phi|=",Size(P)," |G'|=",Size(Dd),
        " special?=", (Zc=P and P=Dd and IsElementaryAbelian(Zc)),
        " class=",NilpotencyClassOfGroup(G),
        " exp=",Exponent(G),
        " G/Phi=",StructureDescription(G/P), "\n");
od;
# are the pairs isoclinic?
Print("3678~3679 isoclinic: ", IsIsomorphicGroup(
  Image(IsomorphismGroups(DerivedSubgroup(SmallGroup(256,3678)),
                          DerivedSubgroup(SmallGroup(256,3678)))) ,
  DerivedSubgroup(SmallGroup(256,3678)))<>fail, "\n");
QUIT;
