# Continue the twist-defect localization: refine the D-rank
# defect of the isocategorical order-64 pairs by DECORATION-ORDER color
# (Order(c.q) = order of the linear character; 1 = trivial/F1, 2 = involution...).
# This connects the low-stratum twist defect to the identity-vs-involution
# localization (results/psi2_recognition_attack.md, decor_localization_result.md).
Read("gap/dring_sieve_standalone.g");;
DSelfTest();;

# lookup helper on a Collected() list
Look := function(coll, key)
  local p;
  for p in coll do if p[1] = key then return p[2]; fi; od;
  return 0;
end;

DecorColor := function(G)          # decoration-order -> count of D-species
  return Collected(List(SpeciesClassesD(G), c -> Order(c.q)));
end;
DecorLevel := function(G)          # (subgroupOrder, decorOrder) -> count
  return Collected(List(SpeciesClassesD(G),
                        c -> [Size(c.H), Order(c.q)]));
end;

for pair in [[135,136],[232,236],[215,216]] do
  G1 := SmallGroup(64,pair[1]);; G2 := SmallGroup(64,pair[2]);;
  c1 := DecorColor(G1);; c2 := DecorColor(G2);;
  colors := Set(Concatenation(List(c1,x->x[1]), List(c2,x->x[1])));
  Print("PAIR ", pair, "  (decoration-order color : D1 D2  defect)\n");
  for d in colors do
    Print("   decor-order ", d, " : ", Look(c1,d), " ", Look(c2,d),
          "   dD=", Look(c2,d)-Look(c1,d), "\n");
  od;
  # cross-tab defect, only nonzero cells
  t1 := DecorLevel(G1);; t2 := DecorLevel(G2);;
  cells := Set(Concatenation(List(t1,x->x[1]), List(t2,x->x[1])));
  Print("   nonzero (subgroupOrder,decorOrder) defects:\n");
  for cell in cells do
    dd := Look(t2,cell) - Look(t1,cell);
    if dd <> 0 then
      Print("      H-order=", cell[1], " decor-order=", cell[2],
            " : dD=", dd, "\n");
    fi;
  od;
od;
QUIT;
