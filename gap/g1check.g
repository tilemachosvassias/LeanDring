Read("gap/dring_sieve_standalone.g");

RatClassesD := function(G, cls)
  local ok, c, N, ords, a, orb, nat, act, keep;
  keep := [];
  for c in cls do
    ok := true;
    if Order(c.q) > 2 then
      orb := Orbit(Normalizer(G, c.H), c.q,
        function(q, n) return Image(c.nat, PreImagesRepresentative(c.nat, q)^n); end);
      for a in Filtered([2..Order(c.q)-1], x -> Gcd(x, Order(c.q)) = 1) do
        if not c.q^a in orb then ok := false; break; fi;
      od;
    fi;
    if ok then Add(keep, c); fi;
  od;
  return keep;
end;;

CheckG1 := function(G, name)
  local cls, T, V, n, B, p1, p2, i, z, perm, Vp, ok, full;
  full := SpeciesClassesD(G);;
  cls := RatClassesD(G, full);;
  T := SpeciesTableD(G, full);;   # rows = ALL classes; select rational rows
  n := Length(full);
  # columns of V = points; keep only rational points as coordinates
  V := TransposedMat(T);;  # rows = generators (all), cols = all points
  V := List(V, r -> r{Filtered([1..n], i -> full[i] in cls)});
  B := HermiteNormalFormIntegerMat(V);;
  n := Length(cls);
  z := First(Elements(Centre(G)), x -> Order(x) = 2);
  p1 := First([1..n], i -> Size(cls[i].H) = 1);
  p2 := First([1..n], i -> cls[i].H = Subgroup(G,[z]) and Order(cls[i].h) = 1);
  perm := (p1, p2);
  Vp := List(V, r -> Permuted(r, perm));
  ok := HermiteNormalFormIntegerMat(Vp) = B;
  Print(name, ": rational pts ", n, "; central swap preserves D_F: ", ok, "\n");
end;;

CheckG1(CyclicGroup(4), "C4");
CheckG1(CyclicGroup(8), "C8");
CheckG1(ElementaryAbelianGroup(4), "C2xC2");
CheckG1(AbelianGroup([2,4]), "C2xC4");
CheckG1(SmallGroup(16,9), "Q16");
CheckG1(SmallGroup(32,20), "Q32");
CheckG1(SmallGroup(8,3), "D4");
CheckG1(SmallGroup(16,7), "D8dihedral16");
QUIT;
