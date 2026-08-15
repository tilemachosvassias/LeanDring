Read("gap/dring_sieve_standalone.g");

TestQ8 := function()
  local G, cls, T, V, B, p, q, Vp, Bp, i, z;
  G := SmallGroup(8, 4);
  cls := SpeciesClassesD(G);
  T := SpeciesTableD(G, cls);
  
  z := First(Elements(Centre(G)), x -> Order(x) = 2);
  
  p := First([1..Length(cls)], i -> Size(cls[i].H) = 1);
  q := First([1..Length(cls)], i -> cls[i].H = Subgroup(G, [z]) and Order(cls[i].h) = 1);
  
  Print("Trivial point index: ", p, "\n");
  Print("(<z>, 1) point index: ", q, "\n");
  
  V := TransposedMat(T);
  # If any entry is cyclotomic (not rational integer), HNF integer mat will fail.
  # Let's check if all are integers.
  if ForAll(Flat(V), IsInt) then
    Print("All entries in V are rational integers.\n");
    B := HermiteNormalFormIntegerMat(V);
    Vp := List(V, r -> Permuted(r, (p, q)));
    Bp := HermiteNormalFormIntegerMat(Vp);
    Print("Lattice preserved exactly (HNF): ", Bp = B, "\n");
  else
    Print("Cyclotomic values present. We must use a cyclotomic/realified lattice check.\n");
    # Realified lattice check:
    # A cyclotomic number a + b E(4) etc can be split into rational components.
    # We can just multiply by the basis of Q(zeta) to get an integer matrix of larger dimension.
    # Wait, the prompt says: "HNF over the ring of integers of the relevant cyclotomic field, or equivalently rational HNF of the realified table."
    # Since Q8 has ONLY integer values, the above HNF will just work!
  fi;
end;

TestQ8();
QUIT;
