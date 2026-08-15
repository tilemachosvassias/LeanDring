# v_task11_qsweep.g
# Task 11: Perfect maximal subgroups of O7(q) vs S6(q)
# Extended q-sweep with sanity check at q=3

LoadPackage("ctbllib");

# Count linear characters (degree 1) in a character table
CountLinearCharacters := function(t)
  local irr, count, i;
  if t = fail then return -1; fi;
  irr := Irr(t);
  count := 0;
  for i in [1..Length(irr)] do
    if Degree(irr[i]) = 1 then count := count + 1; fi;
  od;
  return count;
end;

# A maximal is perfect iff it has exactly 1 linear character (the trivial one)
IsPerfectMaximal := function(t)
  if t = fail then return false; fi;
  return CountLinearCharacters(t) = 1;
end;

# Analyze one group's maximal subgroups
AnalyzeGroup := function(q, groupName)
  local t, maxes, i, maxName, maxTable, perfect, unknown, result;

  result := rec(
    q := q,
    groupName := groupName,
    maxCount := 0,
    perfectCount := 0,
    unknownCount := 0,
    hasTable := false,
    hasMaxes := false
  );

  # Try to load character table
  t := CharacterTable(Concatenation(groupName, "(", String(q), ")"));

  if t = fail then
    Print("  ", groupName, "(", q, "): NO TABLE\n");
    return result;
  fi;

  result.hasTable := true;
  Print("  ", groupName, "(", q, "): table loaded");

  # Check if Maxes data is available
  if not IsBound(t!.Maxes) then
    Print(" - no Maxes data\n");
    return result;
  fi;

  # Get maximal subgroups
  maxes := Maxes(t);
  if maxes = fail then
    Print(" - Maxes() failed\n");
    return result;
  fi;

  result.hasMaxes := true;
  result.maxCount := Length(maxes);
  Print(" - ", result.maxCount, " maximal classes\n");

  perfect := 0;
  unknown := 0;

  # Analyze each maximal
  for i in [1..Length(maxes)] do
    maxName := maxes[i];
    maxTable := CharacterTable(maxName);

    if maxTable = fail then
      unknown := unknown + 1;
    elif IsPerfectMaximal(maxTable) then
      perfect := perfect + 1;
    fi;
  od;

  result.perfectCount := perfect;
  result.unknownCount := unknown;

  Print("    -> perfect: ", perfect, " | unknown: ", unknown, "\n");

  return result;
end;

# Main analysis
Print("\n=== Perfect Maximal Subgroup Analysis ===\n");
Print("Comparing O7(q) vs S6(q) (PSp(6,q))\n\n");

# Initialize
qValues := [3, 5, 7, 9, 11, 13, 17, 19, 23, 25, 27];
results := [];

for q in qValues do
  Print("q = ", q, "\n");
  r1 := AnalyzeGroup(q, "O7");
  r2 := AnalyzeGroup(q, "S6");
  Add(results, rec(q := q, O7 := r1, S6 := r2));
  Print("\n");
od;

Print("\n=== SUMMARY TABLE ===\n");
Print("Format: q | O7_maxes | O7_perfect | O7_unknown | S6_maxes | S6_perfect | S6_unknown | Verdict\n");
Print("-----\n");

for i in [1..Length(results)] do
  q := results[i].q;
  r1 := results[i].O7;
  r2 := results[i].S6;

  if not r1.hasTable or not r2.hasTable then
    verdict := "NO_TABLE";
  elif not r1.hasMaxes or not r2.hasMaxes then
    verdict := "NO_MAXES";
  elif r1.maxCount = r2.maxCount and r1.perfectCount = r2.perfectCount and r1.unknownCount = r2.unknownCount then
    verdict := "SAME";
  else
    verdict := "DIFFER";
  fi;

  Print(String(q));
  Print(" | ");
  Print(String(r1.maxCount));
  Print(" | ");
  Print(String(r1.perfectCount));
  Print(" | ");
  Print(String(r1.unknownCount));
  Print(" | ");
  Print(String(r2.maxCount));
  Print(" | ");
  Print(String(r2.perfectCount));
  Print(" | ");
  Print(String(r2.unknownCount));
  Print(" | ");
  Print(verdict);
  Print("\n");
od;

Print("\nDone.\n");
