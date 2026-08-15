for n in [9..13] do
  G := AlternatingGroup(n);
  idx := Set(List(Filtered(List(ConjugacyClasses(G), Representative), g -> Order(g)>1),
                  g -> Index(G, Normalizer(G, Group(g)))));
  for A in [ Group((1,2)(3,4),(1,3)(2,4)),
             Group((1,2)(3,4),(1,2)(5,6)),
             Group((1,2)(3,4),(1,3)(2,4),(1,2)(5,6)),
             Group((1,2,3),(4,5,6)) ] do
    if IsSubgroup(G,A) then Add(idx, Index(G, Normalizer(G,A))); fi;
  od;
  idx := Set(idx);
  Print("A", n, ": C(n,3)=", Binomial(n,3), " C(n,4)=", Binomial(n,4),
        "   six smallest: ", idx{[1..Minimum(6,Length(idx))]}, "\n");
od;
