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

AnchoredBattery := function(id)
  local G, cc, i, K, phi, A, No, elemsA, ccl, cmap, irr, Wreps, q, units,
        permsW, permsG, Grp, Wgrp, orbsA, ratrows, y, orbD, chvecs, cols, colreps,
        B, row, c, val, w, snf, K_orbits, K_fields, orb, U, field_name, F_count;
  G := SmallGroup(64, id);
  cc := ConjugacyClassesSubgroups(G);
  Print("### (64,", id, ") ###\n");
  F_count := 0;
  for i in [1..Length(cc)] do
    K := Representative(cc[i]);
    phi := NaturalHomomorphismByNormalSubgroup(K, DerivedSubgroup(K));
    A := Image(phi);
    elemsA := Elements(A);
    No := Normalizer(G, K);
    ccl := ConjugacyClasses(A);
    cmap := function(g) return First([1..Length(ccl)], k -> g in ccl[k]); end;
    irr := Irr(A);
    chvecs := List(irr, ch -> List(elemsA, e -> ch[cmap(e)]));
    Wreps := List(RightCosets(No, K), Representative);
    q := Exponent(A); if q = 1 then q := 2; fi;
    units := Filtered([1..q], j -> GcdInt(j, q) = 1);
    permsW := List(GeneratorsOfGroup(No), g -> PermListList(elemsA,
              List(elemsA, x -> Image(phi, PreImagesRepresentative(phi, x)^g))));
    permsG := List(units, j -> PermListList(elemsA, List(elemsA, x -> x^j)));
    Grp := Group(Concatenation(permsW, permsG), ());
    Wgrp := Group(Concatenation(permsW, [()]));
    orbsA := Orbits(Grp, [1..Length(elemsA)]);
    ratrows := Filtered(orbsA, o -> IsTransitive(Wgrp, o));
    
    cols := [];
    for c in [1..Length(chvecs)] do
      if not ForAny(cols, o -> c in o) then
        Add(cols, Set(Orbit(Grp, c, function(cc3, p)
           return First([1..Length(chvecs)], t -> chvecs[t] = Permuted(chvecs[cc3], p^-1)); end)));
      fi;
    od;
    colreps := List(cols, o -> o[1]);
    B := [];
    for y in ratrows do
      row := [];
      for c in colreps do
        val := 0;
        for w in Wreps do
          val := val + chvecs[c][First([1..Length(elemsA)],
                    t -> elemsA[t] = Image(phi, PreImagesRepresentative(phi, elemsA[y[1]])^w))];
        od;
        Add(row, val);
      od;
      Add(B, row);
    od;
    B := List(B, r -> List(r, x -> Int(x)));
    if Length(B) > 0 and Length(B[1]) > 0 then
      snf := Filtered(DiagonalOfMat(SmithNormalFormIntegerMat(B)), x -> x <> 0);
    else
      snf := [];
    fi;
    
    # Anchored Fusion Fields
    K_orbits := FusionFieldU(G, K);
    K_fields := [];
    for orb in K_orbits do
      U := orb.U;
      if orb.cond <= 2 then field_name := "Q";
      elif orb.cond = 4 then
        if 3 in U then field_name := "Q";
        else field_name := "Q(i)"; fi;
      elif orb.cond = 8 then
        if 3 in U and 5 in U then field_name := "Q";
        elif 3 in U then field_name := "Q(sqrt(-2))";
        elif 5 in U then field_name := "Q(i)";
        elif 7 in U then field_name := "Q(sqrt(2))";
        else field_name := "Q(zeta_8)"; fi;
      elif orb.cond = 16 then
        if Length(U) = 8 then field_name := "Q";
        else field_name := Concatenation("Q(zeta_16)^", String(Length(U))); fi;
      elif orb.cond = 32 then
        if Length(U) = 16 then field_name := "Q";
        else field_name := Concatenation("Q(zeta_32)^", String(Length(U))); fi;
      else
        field_name := Concatenation("Q(zeta_", String(orb.cond), ")^", String(Length(U)));
      fi;
      Add(K_fields, field_name);
    od;
    Sort(K_fields);
    
    Print("K", i, " id=", IdGroup(K), " size=", Size(K), " |N_G|=", Size(No), 
          " A=", AbelianInvariants(A), " W_orbits=", Length(Orbits(Wgrp, [1..Length(elemsA)])),
          " rat_rows=", Length(ratrows), " SNF=", Collected(snf), 
          " Fields=", K_fields, "\n");
  od;
end;

AnchoredBattery(13);
AnchoredBattery(14);
AnchoredBattery(47);
AnchoredBattery(48);
QUIT;
