Read("gap/dring_sieve_standalone.g");

# Bottom-triple gauge check on the CORRECT lattice D_F = pi(D):
# all generator columns (no dedup/multiplication), restricted to rational points.
# Tests the three bottom transpositions:
#   E1: (1,1) <-> (<z>,1)   [central edge, Theorem G1]
#   E2: (1,1) <-> (<z>,z)   [only exists for p=2]
#   E3: (<z>,1) <-> (<z>,z) [only exists for p=2]

RatClassesD := function(G, cls)
  local ok, c, orb, a, keep;
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

CheckG2 := function(G, name)
  local full, cls, T, V, B, n, p, z, p1, p2, p3, edges, e, Vp, ok, lab;
  p := PrimePGroup(G);
  full := SpeciesClassesD(G);;
  cls := RatClassesD(G, full);;
  T := SpeciesTableD(G, full);;
  n := Length(full);
  V := TransposedMat(T);;   # rows = ALL generators, cols = all points
  V := List(V, r -> r{Filtered([1..n], i -> full[i] in cls)});
  if not ForAll(Flat(V), IsInt) then
    Print(name, ": NONINTEGER ENTRIES AT RATIONAL POINTS — check filter\n");
    return;
  fi;
  B := HermiteNormalFormIntegerMat(V);;
  n := Length(cls);
  z := First(Elements(Centre(G)), x -> Order(x) = p);
  p1 := First([1..n], i -> Size(cls[i].H) = 1);
  p2 := First([1..n], i -> cls[i].H = Subgroup(G,[z]) and Order(cls[i].h) = 1);
  p3 := First([1..n], i -> cls[i].H = Subgroup(G,[z]) and Order(cls[i].h) = p);
  edges := [["E1(1<->z1)", p1, p2]];
  if p3 <> fail then
    Add(edges, ["E2(1<->zz)", p1, p3]);
    Add(edges, ["E3(z1<->zz)", p2, p3]);
  fi;
  lab := [];
  for e in edges do
    Vp := List(V, r -> Permuted(r, (e[2], e[3])));
    ok := HermiteNormalFormIntegerMat(Vp) = B;
    Add(lab, Concatenation(e[1], ":", String(ok)));
  od;
  Print(name, " (p=", p, ", ratpts ", n, "): ", JoinStringsWithSeparator(lab, "  "), "\n");
end;;

# p = 2
CheckG2(CyclicGroup(2), "C2");
CheckG2(CyclicGroup(4), "C4");
CheckG2(CyclicGroup(8), "C8");
CheckG2(CyclicGroup(16), "C16");
CheckG2(SmallGroup(8,4), "Q8");
CheckG2(SmallGroup(16,9), "Q16");
CheckG2(SmallGroup(32,20), "Q32");
CheckG2(SmallGroup(8,3), "D4");
CheckG2(ElementaryAbelianGroup(4), "C2xC2");
CheckG2(AbelianGroup([2,4]), "C2xC4");
CheckG2(SmallGroup(16,8), "SD16");
CheckG2(SmallGroup(16,6), "M16(was NOT-SQUARE)");
CheckG2(SmallGroup(16,13), "(16,13)(was NOT-SQUARE)");
# p odd
CheckG2(CyclicGroup(3), "C3");
CheckG2(CyclicGroup(9), "C9");
CheckG2(CyclicGroup(27), "C27");
CheckG2(ElementaryAbelianGroup(9), "C3xC3");
CheckG2(SmallGroup(27,3), "27_3 extraspecial exp3");
CheckG2(SmallGroup(27,4), "27_4 extraspecial exp9");
CheckG2(CyclicGroup(25), "C25");
QUIT;
