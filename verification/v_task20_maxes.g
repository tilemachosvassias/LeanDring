# v_task20_maxes.g -- Tier-1 mult1 LOWER BOUNDS for A9,A10,A11,A12 via
# Maxes(CharacterTable("A_n")): count maximal classes with exactly 1
# linear character (perfect), +1 for A_n itself (A_n is perfect for
# n>=5, and every maximal subgroup of a simple group is automatically
# self-normalizing -- same argument as v_task9/v_task17 Part 2).

CountLinearChars := function(table)
  local irrs, count, chi;
  irrs := Irr(table);
  count := 0;
  for chi in irrs do
    if Degree(chi) = 1 then count := count + 1; fi;
  od;
  return count;
end;;

IsGroupPerfect := function(table)
  return CountLinearChars(table) = 1;
end;;

AnalyzeAn := function(nval)
  local nm, t, m, count, perfect, name, tt, order, nlin, is_perfect, failures;
  nm := Concatenation("A", String(nval));
  t := CharacterTable(nm);
  if t = fail then
    Print(nm, ": CharacterTable FAILED to load\n");
    return fail;
  fi;
  m := Maxes(t);
  Print("\n=== ", nm, " (|", nm, "|=", Size(t), ") ===\n");
  Print(nm, " maximal subgroups: ", m, "\n");
  count := 0;
  perfect := [];
  failures := [];
  for name in m do
    tt := CharacterTable(name);
    if tt = fail then
      Print("  ", name, ": CharacterTable FAILED\n");
      Add(failures, name);
    else
      order := Size(tt);
      nlin := CountLinearChars(tt);
      is_perfect := IsGroupPerfect(tt);
      Print("  ", name, " order=", order, " linChars=", nlin, " perfect=", is_perfect, "\n");
      if is_perfect then
        count := count + 1;
        Add(perfect, [name, order]);
      fi;
    fi;
  od;
  Print(nm, ": perfect maximal classes = ", count, " (of ", Length(m), " total maximal classes)\n");
  if Length(failures) > 0 then
    Print(nm, ": load failures for ", failures, " -- lower bound may be incomplete if these turn out perfect\n");
  fi;
  Print(nm, ": mult1 LOWER BOUND = ", count, " + 1 (A_n itself, perfect & self-normalizing) = ", count+1, "\n");
  return count+1;
end;;

bounds := [];;
for n in [9,10,11,12] do
  Add(bounds, [n, AnalyzeAn(n)]);
od;

Print("\n=== SUMMARY: mult1 lower bounds ===\n");
for pair in bounds do
  Print("A", pair[1], ": mult1 >= ", pair[2], "\n");
od;
Print("=== DONE maxes ===\n");
