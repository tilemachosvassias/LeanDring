# v_task9_maxes.g
# Compare maximal subgroup structures of O7(3) and S6(3)
# Focus: count PERFECT maximal subgroups (those with exactly 1 linear character)

# Load character tables
Print("Loading character tables...\n");
t1 := CharacterTable("O7(3)");
t2 := CharacterTable("S6(3)");

if t1 = fail or t2 = fail then
  Print("ERROR: Failed to load one or both character tables.\n");
else
  # Get maximal subgroup names
  m1 := Maxes(t1);
  m2 := Maxes(t2);

  Print("\n=== Step 1: Maximal Subgroup Names ===\n");
  Print("O7(3) maximal subgroups: ", m1, "\n");
  Print("S6(3) maximal subgroups: ", m2, "\n");

  # Helper function: count linear characters (degree 1)
  CountLinearChars := function(table)
    local irrs, count, chi;
    irrs := Irr(table);
    count := 0;
    for chi in irrs do
      if Degree(chi) = 1 then
        count := count + 1;
      fi;
    od;
    return count;
  end;

  # Helper function: check if group is perfect
  # A group is perfect iff it has no non-trivial abelian quotients
  # For character tables: exactly 1 linear character (the trivial one)
  IsGroupPerfect := function(table)
    return CountLinearChars(table) = 1;
  end;

  # Initialize counters and lists for O7(3)
  perfect1 := [];
  count1 := 0;
  failures1 := [];

  # Process O7(3) maximal subgroups
  Print("\n=== Step 2: O7(3) Maximal Subgroups Analysis ===\n");
  Print("Name\t\t\tOrder\t\tLinear Chars\tPerfect?\n");
  Print("--------\t\t--------\t--------\t--------\n");

  for name in m1 do
    t := CharacterTable(name);
    if t = fail then
      Print(name, "\t\tFAIL\t\tN/A\t\tN/A\n");
      Add(failures1, name);
    else
      order := Size(t);
      nlin := CountLinearChars(t);
      is_perfect := IsGroupPerfect(t);
      if is_perfect then
        count1 := count1 + 1;
        Add(perfect1, [name, order]);
      fi;
      Print(name, "\t\t", order, "\t\t", nlin, "\t\t", is_perfect, "\n");
    fi;
  od;

  # Initialize counters and lists for S6(3)
  perfect2 := [];
  count2 := 0;
  failures2 := [];

  # Process S6(3) maximal subgroups
  Print("\n=== Step 3: S6(3) Maximal Subgroups Analysis ===\n");
  Print("Name\t\t\tOrder\t\tLinear Chars\tPerfect?\n");
  Print("--------\t\t--------\t--------\t--------\n");

  for name in m2 do
    t := CharacterTable(name);
    if t = fail then
      Print(name, "\t\tFAIL\t\tN/A\t\tN/A\n");
      Add(failures2, name);
    else
      order := Size(t);
      nlin := CountLinearChars(t);
      is_perfect := IsGroupPerfect(t);
      if is_perfect then
        count2 := count2 + 1;
        Add(perfect2, [name, order]);
      fi;
      Print(name, "\t\t", order, "\t\t", nlin, "\t\t", is_perfect, "\n");
    fi;
  od;

  # Summary and verdict
  Print("\n=== Step 4: Summary and Verdict ===\n");
  Print("\nO7(3):\n");
  Print("  Total maximal subgroup classes: ", Length(m1), "\n");
  Print("  Perfect maximal subgroup classes: ", count1, "\n");
  if Length(failures1) > 0 then
    Print("  Load failures: ", failures1, "\n");
  fi;
  Print("  Perfect maximal subgroups:\n");
  if count1 = 0 then
    Print("    (none)\n");
  else
    for entry in perfect1 do
      Print("    ", entry[1], " (order ", entry[2], ")\n");
    od;
  fi;

  Print("\nS6(3):\n");
  Print("  Total maximal subgroup classes: ", Length(m2), "\n");
  Print("  Perfect maximal subgroup classes: ", count2, "\n");
  if Length(failures2) > 0 then
    Print("  Load failures: ", failures2, "\n");
  fi;
  Print("  Perfect maximal subgroups:\n");
  if count2 = 0 then
    Print("    (none)\n");
  else
    for entry in perfect2 do
      Print("    ", entry[1], " (order ", entry[2], ")\n");
    od;
  fi;

  Print("\n=== VERDICT ===\n");
  if count1 = count2 then
    Print("SAME: Both O7(3) and S6(3) have ", count1, " perfect maximal subgroup classes.\n");
  else
    Print("DIFFER: O7(3) has ", count1, " perfect maximal classes; S6(3) has ", count2, ".\n");
  fi;

  Print("\n=== End of Analysis ===\n");
fi;
