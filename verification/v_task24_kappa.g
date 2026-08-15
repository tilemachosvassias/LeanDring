# kappa(G) := max over 1 <> H <= G of |N_G(H) : H'|  -- the largest conductor below |G|
# (Mueller 2.3.3: conductor of the pair (H, hH') is (N_G(H,hH') : H'); take hH' = H'.)
kappa := function(G)
  local best, c, H, d, arg;
  best := 0; arg := fail;
  for c in ConjugacyClassesSubgroups(G) do
    H := Representative(c);
    if Size(H) > 1 and Size(H) < Size(G) then
      d := Size(Normalizer(G,H)) / Size(DerivedSubgroup(H));
      if d > best then best := d; arg := H; fi;
    fi;
  od;
  return [best, arg];
end;;
for n in [5,6,7,8,9] do
  G := AlternatingGroup(n);;
  r := kappa(G);;
  Print("A", n, ": |G|=", Size(G), "  kappa=", r[1],
        "  predicted 3*(n-3)! = ", 3*Factorial(n-3),
        "  match=", r[1] = 3*Factorial(n-3),
        "  witness=", StructureDescription(r[2]), " |H|=", Size(r[2]),
        "  mindex=", Size(G)/r[1], " vs n(n-1)(n-2)/6=", n*(n-1)*(n-2)/6, "\n");
od;
QUIT;
