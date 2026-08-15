# v_task17_part2_sporadics.g -- Tier-1 mult1 LOWER BOUND for the 5 sporadics
# (M22, M24, J2, Suz, Th), same method as v_task9: count perfect maximal
# subgroup classes from CharacterTable Maxes data, +1 for G itself (G is
# simple hence perfect and trivially self-normalizing, N_G(G)=G).
# Perfect maximal subgroups of a SIMPLE group are automatically
# self-normalizing (if N_G(M)>M for M maximal then N_G(M)=G, forcing M
# normal in G, contradicting simplicity unless M=1, excluded since M is a
# proper nontrivial maximal subgroup) -- so this is a genuine LOWER BOUND
# on mult1(G), not merely a count of maximal subgroups.

CountLinearChars := function(t)
  local irrs, count, chi;
  irrs := Irr(t);
  count := 0;
  for chi in irrs do
    if Degree(chi) = 1 then count := count + 1; fi;
  od;
  return count;
end;;

IsTablePerfect := function(t)
  return CountLinearChars(t) = 1;
end;;

MaxesPerfectReport := function(name)
  local t, m, i, mn, mt, perfectCount, perfectList, order;
  Print("\n=== ", name, " ===\n");
  t := CharacterTable(name);
  if t = fail then
    Print("  CharacterTable FAIL\n");
    return fail;
  fi;
  Print("  order=", Size(t), "  own perfect (simple, should be true)? ", IsTablePerfect(t), "\n");
  m := Maxes(t);
  if m = fail then
    Print("  Maxes: NOT STORED\n");
    return fail;
  fi;
  Print("  Maxes names: ", m, "\n");
  perfectCount := 0;
  perfectList := [];
  for mn in m do
    mt := CharacterTable(mn);
    if mt = fail then
      Print("    ", mn, ": table FAIL\n");
    else
      order := Size(mt);
      if IsTablePerfect(mt) then
        perfectCount := perfectCount + 1;
        Add(perfectList, [mn, order]);
        Print("    ", mn, " order=", order, " PERFECT\n");
      else
        Print("    ", mn, " order=", order, " not perfect\n");
      fi;
    fi;
  od;
  Print("  Perfect maximal classes: ", perfectCount, "\n");
  Print("  mult1 LOWER BOUND (perfect maximals + G itself): ", perfectCount + 1, "\n");
  return rec(perfectCount:=perfectCount, perfectList:=perfectList, table:=t);
end;;

rM22 := MaxesPerfectReport("M22");;
rM24 := MaxesPerfectReport("M24");;
rJ2 := MaxesPerfectReport("J2");;
rSuz := MaxesPerfectReport("Suz");;
rTh := MaxesPerfectReport("Th");;

Print("\n=== SUMMARY (Part 2, Tier-1 lower bounds) ===\n");
Print("M22: perfect maxes=", rM22.perfectCount, "  mult1 >= ", rM22.perfectCount+1, "\n");
Print("M24: perfect maxes=", rM24.perfectCount, "  mult1 >= ", rM24.perfectCount+1, "\n");
Print("J2:  perfect maxes=", rJ2.perfectCount, "  mult1 >= ", rJ2.perfectCount+1, "\n");
Print("Suz: perfect maxes=", rSuz.perfectCount, "  mult1 >= ", rSuz.perfectCount+1, "\n");
Print("Th:  perfect maxes=", rTh.perfectCount, "  mult1 >= ", rTh.perfectCount+1, "\n");
Print("\n=== DONE part2_sporadics ===\n");
