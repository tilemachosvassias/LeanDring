IsMetacyclic2Group := function(G)
  local N, Ns;
  if Length(AbelianInvariants(G)) > 2 then return false; fi;
  Ns := NormalSubgroups(G);
  for N in Ns do
    if IsCyclic(N) and IsCyclic(G/N) then
      return true;
    fi;
  od;
  return false;
end;

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
      Add(Gamma_orbits, rec(cond := order_y, U := U));
    fi;
  od;
  return Gamma_orbits;
end;

UnanchoredFusionFields := function(G)
  local sc, K, K_orbits, all_fields, F_count, orb, field_name, U, sig, f;
  sc := ConjugacyClassesSubgroups(G);
  all_fields := [];
  F_count := 0;
  for K in sc do
    K_orbits := FusionFieldU(G, Representative(K));
    for orb in K_orbits do
      U := orb.U;
      if orb.cond <= 2 then field_name := "Q"; F_count := F_count + 1;
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
        if Length(U) = 8 then field_name := "Q"; F_count := F_count + 1;
        else field_name := Concatenation("Q(zeta_16)^", String(Length(U))); fi;
      elif orb.cond = 32 then
        if Length(U) = 16 then field_name := "Q"; F_count := F_count + 1;
        else field_name := Concatenation("Q(zeta_32)^", String(Length(U))); fi;
      else
        field_name := Concatenation("Q(zeta_", String(orb.cond), ")^", String(Length(U)));
      fi;
      Add(all_fields, field_name);
    od;
  od;
  Sort(all_fields);
  sig := "";
  for f in all_fields do
    sig := Concatenation(sig, f, ";");
  od;
  return rec(F := F_count, sig := sig);
end;

MultisetDifference := function(bag1, bag2)
  local diff, b, found, c, diff_count;
  diff := [];
  for b in bag1 do
    found := false;
    for c in bag2 do
      if b[1] = c[1] then
        found := true;
        diff_count := b[2] - c[2];
        if diff_count > 0 then Add(diff, [b[1], diff_count]); fi;
        break;
      fi;
    od;
    if not found then Add(diff, b); fi;
  od;
  return diff;
end;

Task4Fast := function()
  local order, n, i, G, inv, bag, bags, b, found, sig, diff1, diff2, c, c2;
  for order in [2, 4, 8, 16, 32, 64, 128, 256] do
    Print("\nOrder ", order, ":\n");
    bags := [];
    n := NrSmallGroups(order);
    for i in [1..n] do
      G := SmallGroup(order, i);
      if IsMetacyclic2Group(G) then
        inv := UnanchoredFusionFields(G);
        bag := Collected(SplitString(inv.sig, ";"));
        bag := Filtered(bag, x -> x[1] <> "");
        found := false;
        for b in bags do
          if b.bag = bag then
            Print("  Collision! Bag equality for metacyclic groups: (", order, ",", b.ids[1], ") and (", order, ",", i, ")\n");
            Add(b.ids, i);
            found := true;
            break;
          fi;
        od;
        if not found then
          Add(bags, rec(bag := bag, ids := [i]));
        fi;
      fi;
    od;
    
    Print("  Checking shadow gauge pairs for order ", order, "...\n");
    for i in [1..Length(bags)] do
      for c in [i+1..Length(bags)] do
        diff1 := MultisetDifference(bags[i].bag, bags[c].bag);
        diff2 := MultisetDifference(bags[c].bag, bags[i].bag);
        if (Length(diff1) = 2 and Length(diff2) = 1) or 
           (Length(diff1) = 1 and Length(diff2) = 2) then
          if (diff1 = [["Q", 1], ["Q(zeta_8)", 1]] and diff2 = [["Q(i)", 2]]) or
             (diff2 = [["Q", 1], ["Q(zeta_8)", 1]] and diff1 = [["Q(i)", 2]]) then
            Print("  Shadow gauge pair found! (", order, ",", bags[i].ids, 
                  ") and (", order, ",", bags[c].ids, ")\n");
          fi;
        fi;
      od;
    od;
  od;
end;

Task4Fast();
QUIT;
