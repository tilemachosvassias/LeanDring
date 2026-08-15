Read("gap/dring_sieve_standalone.g");

CycToVector := function(c, N)
  local rep, vec, i;
  if IsRat(c) then
    vec := List([1..N], x -> 0);
    vec[1] := c;
    return vec;
  fi;
  rep := ExtRepOfObj(c);
  vec := List([1..N], x -> 0);
  for i in [1..Length(rep)] do
    vec[i] := rep[i];
  od;
  return vec;
end;

RealifyMatrix := function(M, N)
  local RM, r, c, vec, new_row, j;
  RM := [];
  for r in [1..Length(M)] do
    new_row := [];
    for c in [1..Length(M[r])] do
      vec := CycToVector(M[r][c], N);
      Append(new_row, vec);
    od;
    Add(RM, new_row);
  od;
  return RM;
end;

TestUnfusedE1 := function(ORDER, id, z_element_func)
  local G, full, T, V, B, p, q, Vp, Bp, z, RM, RMp, N, cell, found_cyc, lcm_den, multV;
  G := SmallGroup(ORDER, id);
  full := SpeciesClassesD(G);
  T := SpeciesTableD(G, full);
  
  z := z_element_func(G);
  
  p := First([1..Length(full)], i -> Size(full[i].H) = 1);
  q := First([1..Length(full)], i -> full[i].H = Subgroup(G, [z]) and Order(full[i].h) = 1);
  
  Print("Group (", ORDER, ",", id, "):\n");
  Print("Trivial point index: ", p, "\n");
  Print("(<z>, 1) point index: ", q, "\n");
  
  V := TransposedMat(T);
  
  found_cyc := false;
  N := 1;
  lcm_den := 1;
  for cell in Flat(V) do
    if IsRat(cell) then
      lcm_den := Lcm(lcm_den, DenominatorRat(Rat(cell)));
    else
      found_cyc := true;
      N := Lcm(N, Conductor(cell));
      # cyclotomics with rational coefficients?
      for c in ExtRepOfObj(cell) do
        if IsRat(c) then lcm_den := Lcm(lcm_den, DenominatorRat(Rat(c))); fi;
      od;
    fi;
  od;
  
  # clear denominators
  multV := V * lcm_den;
  
  if not found_cyc then
    B := HermiteNormalFormIntegerMat(multV);
    Vp := List(multV, r -> Permuted(r, (p, q)));
    Bp := HermiteNormalFormIntegerMat(Vp);
    Print("Lattice preserved exactly (HNF over Z): ", Bp = B, "\n");
  else
    Print("Cyclotomic values present. Conductor N = ", N, " Lcm Denom = ", lcm_den, "\n");
    RM := RealifyMatrix(multV, N);
    B := HermiteNormalFormIntegerMat(RM);
    Vp := List(multV, r -> Permuted(r, (p, q)));
    RMp := RealifyMatrix(Vp, N);
    Bp := HermiteNormalFormIntegerMat(RMp);
    Print("Lattice preserved exactly (Realified HNF): ", Bp = B, "\n");
  fi;
end;

Print("Testing C8...\n");
TestUnfusedE1(8, 1, G -> First(Elements(G), x -> Order(x) = 2));
Print("\nTesting Q16...\n");
TestUnfusedE1(16, 9, G -> First(Elements(Centre(G)), x -> Order(x) = 2));
QUIT;
