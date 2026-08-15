FusionFieldU := function(G, K)
  local Kp, hom, A, N, elements_A, y, y_rep, r, order_y, U, s, ys, n, seen, W_orbits, Gamma_orbits, o, gamma_orb, i;
  
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
      
      y_rep := PreImagesRepresentative(hom, y);
      
      W_orbits := function(el)
        local orb, nn;
        orb := [];
        for nn in Elements(N) do
          AddSet(orb, Image(hom, PreImagesRepresentative(hom, el)^nn));
        od;
        return orb;
      end;
      
      gamma_orb := [];
      U := [];
      for s in [1..order_y] do
        if Gcd(s, order_y) = 1 then
          ys := y^s;
          for o in W_orbits(ys) do
            AddSet(gamma_orb, o);
            seen[Position(elements_A, o)] := true;
          od;
          if ys in W_orbits(y) then
            AddSet(U, s mod order_y);
          fi;
        fi;
      od;
      
      Add(Gamma_orbits, rec(
        cond := order_y,
        U := U
      ));
    fi;
  od;
  
  return Gamma_orbits;
end;
