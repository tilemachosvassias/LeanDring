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

EncodeSubgroup := function(U)
  local u, s;
  s := "";
  for u in Set(U) do
    s := Concatenation(s, String(u), ",");
  od;
  return s;
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
  
  Sort(all_fields);
  
  sig := "";
  for f in all_fields do
    sig := Concatenation(sig, f, ";");
  od;
  
  return rec(F := F_count, sig := sig);
end;

Order64SweepUnanchored := function()
  local clusters, id, G, inv, F, sig, c, survived, snf_clusters, G_snf, sc, match_sc;
  clusters := [];
  
  Print("Phase 1: Census (F and unanchored fusion fields bag)...\n");
  for id in [1..267] do
    G := SmallGroup(64, id);
    inv := UnanchoredFusionFields(G);
    F := inv.F;
    sig := Concatenation(String(F), "|", inv.sig);
    
    c := PositionProperty(clusters, x -> x.sig = sig);
    if c = fail then
      Add(clusters, rec(sig := sig, ids := [id]));
    else
      Add(clusters[c].ids, id);
    fi;
  od;
  
  survived := Filtered(clusters, x -> Length(x.ids) > 1);
  Print("Phase 1 complete. Found ", Length(survived), " clusters surviving the unanchored census invariant.\n");
  for c in survived do
    Print("  Cluster: ", c.ids, "\n");
  od;
  
  if Length(survived) > 0 then
    Print("\nPhase 2: Trace-corrected SNF on survivors...\n");
    Read("gap/df_trace_corrected_snf.g");
    snf_clusters := [];
    for c in survived do
      for id in c.ids do
        G := SmallGroup(64, id);
        G_snf := DFTraceCorrectedDivisors(G);
        match_sc := fail;
        for sc in snf_clusters do
          if sc.sig = c.sig and sc.snf = G_snf then
            match_sc := sc;
            break;
          fi;
        od;
        if match_sc = fail then
          Add(snf_clusters, rec(sig := c.sig, snf := G_snf, ids := [id]));
        else
          Add(match_sc.ids, id);
        fi;
      od;
    od;
    
    survived := Filtered(snf_clusters, x -> Length(x.ids) > 1);
    Print("Phase 2 complete. Found ", Length(survived), " total collisions at order 64.\n");
    for c in survived do
      Print("  FINAL COLLISION: ", c.ids, "\n");
    od;
  else
    Print("Order 64 is fully separated by F and unanchored fusion fields!\n");
  fi;
end;

Order64SweepUnanchored();
QUIT;
