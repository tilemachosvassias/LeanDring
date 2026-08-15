# Exact rank and level-profile audit for all order-64 pairs currently claimed
# to be non-isomorphic and isocategorical in the cited literature.
#
# Pair 135/136 is Meir--Szymik Example 3.1.  Pairs 232/236 and 215/216
# correspond respectively to Sato's category-local pairs 5.32.5/5.32.7 and
# 5.40.5/5.40.6.  Sato's completeness claim conflicts with Meir--Szymik, so
# this script audits D and B data only; it does not certify isocategoricity.

Read("gap/dring_sieve_standalone.g");;
DSelfTest();;

LevelProfile := function(G)
  local orders, sc, cls;
  orders := DivisorsInt(Size(G));
  sc := ConjugacyClassesSubgroups(G);
  cls := SpeciesClassesD(G);
  return List(orders, n -> [n,
    Number(sc, c -> Size(Representative(c)) = n),
    Number(cls, c -> Size(c.H) = n),
    Number(sc, c -> Size(Representative(c)) = n and
                    IsAbelian(Representative(c))),
    Number(cls, c -> Size(c.H) = n and IsAbelian(c.H))]);
end;

OrderDistribution := function(G)
  return List([1,2,4,8,16,32,64],
              n -> Number(Elements(G), x -> Order(x) = n));
end;

# Sato's group numbers are positions inside an order-distribution category.
ids32 := Filtered([1..267], id ->
  OrderDistribution(SmallGroup(64,id)) = [1,19,44,0,0,0,0]);;
ids40 := Filtered([1..267], id ->
  OrderDistribution(SmallGroup(64,id)) = [1,31,32,0,0,0,0]);;
if ids32[5] <> 232 or ids32[7] <> 236 or
   ids40[5] <> 215 or ids40[6] <> 216 then
  Error("Sato category-to-SmallGroup mapping changed");
fi;
Print("SATO_CATEGORY_IDS_32=", ids32, "\n");
Print("SATO_CATEGORY_IDS_40=", ids40, "\n");

for pair in [[135,136],[232,236],[215,216]] do
  p1 := LevelProfile(SmallGroup(64,pair[1]));;
  p2 := LevelProfile(SmallGroup(64,pair[2]));;
  Print("PAIR ", pair,
    " columns=[level,B1,B2,dB,D1,D2,dD,abB1,abB2,abD1,abD2]\n");
  for i in [1..Length(p1)] do
    Print([p1[i][1], p1[i][2], p2[i][2], p2[i][2]-p1[i][2],
      p1[i][3], p2[i][3], p2[i][3]-p1[i][3],
      p1[i][4], p2[i][4], p1[i][5], p2[i][5]], "\n");
  od;
od;
QUIT;
