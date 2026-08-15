# v_task17_probe6.g -- character-table Maxes census (Tier-1 style, as v_task9)
# for U3(8) and its .3 extension(s), and for S11/A11 (Suz factor, now only
# needed as a sanity cross-check since the coprimality argument already
# settles Suz's diagonal question -- but let's still get its own p.s.n.
# lower bound in case useful for the report).

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
  Print("  order=", Size(t), "  own perfect? ", IsTablePerfect(t), "\n");
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
  return rec(perfectCount:=perfectCount, perfectList:=perfectList, table:=t);
end;;

r1 := MaxesPerfectReport("U3(8)");;
r2 := MaxesPerfectReport("U3(8).3");;
r3 := MaxesPerfectReport("U3(8).3_1");;
r4 := MaxesPerfectReport("U3(8).3_2");;
r5 := MaxesPerfectReport("U3(8).3_3");;
r6 := MaxesPerfectReport("U3(8).6");;
r7 := MaxesPerfectReport("U3(8).S3");;

Print("\n\n=== S11 / A11 (Suz) -- cross-check only, coprimality already settles diagonal ===\n");
r8 := MaxesPerfectReport("A11");;
r9 := MaxesPerfectReport("S11");;

Print("\n=== DONE probe6 ===\n");
