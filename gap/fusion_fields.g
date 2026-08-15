FusionFieldU := function(G, K)
  local Kp, hom, A, N, elements_A, orbits, res, y, y_rep, r, order_y, U, s, ys, n, is_in_orbit, seen, W_orbits, Gamma_orbits, o, rep, gamma_orb;
  
  Kp := DerivedSubgroup(K);
  hom := NaturalHomomorphismByNormalSubgroupNC(K, Kp);
  A := Image(hom);
  N := Normalizer(G, K);
  
  elements_A := Elements(A);
  seen := BlistList([1..Length(elements_A)], []);
  Gamma_orbits := [];
  
  for i in [1..Length(elements_A)] do
    if not seen[i] then
      y := elements_A[i];
      order_y := Order(y);
      r := 0;
      while 2^r < order_y do r := r + 1; od;
      
      # The W-orbit of y
      # A is K/K', so elements of N act on K. But wait, elements of N act on A?
      # Yes, n in N acts on k K' by (n^-1 k n) K'.
      # BUT A is just an abelian group isomorphic to K/Kp. We need the action.
      # To be safe, we pull back to K.
      y_rep := PreImagesRepresentative(hom, y);
      
      # W-orbit is the set of Image(hom, y_rep^n) for n in N
      # Wait, n acts by n^-1 y_rep n, which in GAP is y_rep^n
      W_orbits := function(el)
        local orb, n;
        orb := [];
        for n in Elements(N) do
          AddSet(orb, Image(hom, PreImagesRepresentative(hom, el)^n));
        od;
        return orb;
      end;
      
      # The full Gamma x W orbit of y
      gamma_orb := [];
      U := [];
      for s in [1..order_y] do
        if Gcd(s, order_y) = 1 then
          ys := y^s;
          # add the whole W-orbit of ys to gamma_orb
          for o in W_orbits(ys) do
            AddSet(gamma_orb, o);
            seen[Position(elements_A, o)] := true;
          od;
          # if ys is in W-orbit of y, then s is in U
          if ys in W_orbits(y) then
            AddSet(U, s mod order_y);
          fi;
        fi;
      od;
      
      Add(Gamma_orbits, rec(
        sizeK := Size(K),
        idK := IdGroup(K),
        cond := order_y,
        U := U
      ));
    fi;
  od;
  
  return Gamma_orbits;
end;

EncodeSubgroup := function(U)
  local u, s;
  s := "";
  for u in Set(U) do
    s := Concatenation(s, String(u), ",");
  od;
  return s;
end;

FusionFieldCensus := function(G)
  local sc, K, K_orbits, all_fields, F_count, orb, U_str, field_name, U;
  sc := ConjugacyClassesSubgroups(G);
  all_fields := [];
  F_count := 0;
  
  for K in sc do
    K_orbits := FusionFieldU(G, Representative(K));
    for orb in K_orbits do
      U := orb.U;
      if orb.cond <= 2 then
        field_name := "Q";
        F_count := F_count + 1;
      elif orb.cond = 4 then
        if 3 in U then field_name := "Q"; F_count := F_count + 1;
        else field_name := "Q(i)"; fi;
      elif orb.cond = 8 then
        if 3 in U and 5 in U then field_name := "Q"; F_count := F_count + 1;
        elif 3 in U then field_name := "Q(sqrt(-2))";
        elif 5 in U then field_name := "Q(i)";
        elif 7 in U then field_name := "Q(sqrt(2))";
        else field_name := "Q(zeta_8)"; fi;
      elif orb.cond = 16 then
        field_name := Concatenation("cond_", String(orb.cond), "_U_", EncodeSubgroup(orb.U));
      elif orb.cond = 32 then
        field_name := Concatenation("cond_", String(orb.cond), "_U_", EncodeSubgroup(orb.U));
      else
        field_name := Concatenation("cond_", String(orb.cond), "_U_", EncodeSubgroup(orb.U));
      fi;
      
      Add(all_fields, field_name);
    od;
  od;
  
  return rec(F := F_count, fields := Collected(all_fields));
end;

Print("Testing 32, 13:\n");
Print(FusionFieldCensus(SmallGroup(32, 13)), "\n");
Print("Testing 32, 14:\n");
Print(FusionFieldCensus(SmallGroup(32, 14)), "\n");
QUIT;
