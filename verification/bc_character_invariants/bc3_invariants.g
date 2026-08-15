# GAP 4.16 computation: Compare B3(3) = O7(3) vs C3(3) = S6(3) invariants
# Both have order 4585351680; same element-order spectrum; look for other differences.

LoadPackage("ctbllib");

# Load character tables
PrintTo("*stdout*", "\n=== LOADING CHARACTER TABLES ===\n");
t1 := CharacterTable("O7(3)");
t2 := CharacterTable("S6(3)");

if t1 = fail or t2 = fail then
  PrintTo("*stdout*", "ERROR: Failed to load one or both character tables.\n");
  if t1 = fail then PrintTo("*stdout*", "  O7(3) failed\n"); fi;
  if t2 = fail then PrintTo("*stdout*", "  S6(3) failed\n"); fi;
  QUIT_GAP(1);
fi;

PrintTo("*stdout*", "O7(3) loaded: identifier = ", Identifier(t1), "\n");
PrintTo("*stdout*", "S6(3) loaded: identifier = ", Identifier(t2), "\n");

# --- Task 1: Verify order ---
PrintTo("*stdout*", "\n=== TASK 1: VERIFY ORDER ===\n");
sz1 := Size(t1);
sz2 := Size(t2);
PrintTo("*stdout*", "Order of O7(3):  ", sz1, "\n");
PrintTo("*stdout*", "Order of S6(3):  ", sz2, "\n");
PrintTo("*stdout*", "Orders equal: ", sz1 = sz2, "\n");
PrintTo("*stdout*", "Expected:     4585351680\n");
if sz1 <> 4585351680 or sz2 <> 4585351680 then
  PrintTo("*stdout*", "WARNING: Order mismatch!\n");
fi;

# --- Task 2: Number of conjugacy classes ---
PrintTo("*stdout*", "\n=== TASK 2: NUMBER OF CONJUGACY CLASSES ===\n");
nc1 := NrConjugacyClasses(t1);
nc2 := NrConjugacyClasses(t2);
PrintTo("*stdout*", "O7(3) conjugacy classes:  ", nc1, "\n");
PrintTo("*stdout*", "S6(3) conjugacy classes:  ", nc2, "\n");
PrintTo("*stdout*", "Classes equal: ", nc1 = nc2, "\n");

# --- Task 3: Element-order spectra ---
PrintTo("*stdout*", "\n=== TASK 3: ELEMENT-ORDER SPECTRA ===\n");
orders1 := Set(OrdersClassRepresentatives(t1));
orders2 := Set(OrdersClassRepresentatives(t2));
PrintTo("*stdout*", "O7(3) orders:  ", orders1, "\n");
PrintTo("*stdout*", "S6(3) orders:  ", orders2, "\n");
PrintTo("*stdout*", "Orders equal: ", orders1 = orders2, "\n");

# --- Task 4: INVOLUTION COUNT (critical) ---
PrintTo("*stdout*", "\n=== TASK 4: INVOLUTION COUNT ===\n");
sizes1 := SizesConjugacyClasses(t1);
sizes2 := SizesConjugacyClasses(t2);
classorders1 := OrdersClassRepresentatives(t1);
classorders2 := OrdersClassRepresentatives(t2);

inv1 := 0;
inv2 := 0;
for i in [1..Length(classorders1)] do
  if classorders1[i] = 2 then
    inv1 := inv1 + sizes1[i];
  fi;
od;
for i in [1..Length(classorders2)] do
  if classorders2[i] = 2 then
    inv2 := inv2 + sizes2[i];
  fi;
od;

PrintTo("*stdout*", "O7(3) involuted elements:  ", inv1, "\n");
PrintTo("*stdout*", "S6(3) involuted elements:  ", inv2, "\n");
PrintTo("*stdout*", "Involution counts equal: ", inv1 = inv2, "\n");

# --- Task 5: Conjugacy class counts and element counts by order ---
PrintTo("*stdout*", "\n=== TASK 5: CONJUGACY CLASSES & ELEMENT COUNTS BY ORDER ===\n");

# Build a table for each group
classes_by_order1 := [];
elems_by_order1 := [];
for d in orders1 do
  classcount := 0;
  elemcount := 0;
  for i in [1..Length(classorders1)] do
    if classorders1[i] = d then
      classcount := classcount + 1;
      elemcount := elemcount + sizes1[i];
    fi;
  od;
  Add(classes_by_order1, [d, classcount, elemcount]);
od;

classes_by_order2 := [];
elems_by_order2 := [];
for d in orders2 do
  classcount := 0;
  elemcount := 0;
  for i in [1..Length(classorders2)] do
    if classorders2[i] = d then
      classcount := classcount + 1;
      elemcount := elemcount + sizes2[i];
    fi;
  od;
  Add(classes_by_order2, [d, classcount, elemcount]);
od;

PrintTo("*stdout*", "\nO7(3) by element order:\n");
PrintTo("*stdout*", "order | #classes | #elements\n");
PrintTo("*stdout*", "------|----------|----------\n");
for row in classes_by_order1 do
  PrintTo("*stdout*", String(row[1], 5), " | ", String(row[2], 8), " | ", row[3], "\n");
od;

PrintTo("*stdout*", "\nS6(3) by element order:\n");
PrintTo("*stdout*", "order | #classes | #elements\n");
PrintTo("*stdout*", "------|----------|----------\n");
for row in classes_by_order2 do
  PrintTo("*stdout*", String(row[1], 5), " | ", String(row[2], 8), " | ", row[3], "\n");
od;

# Flag differences in class counts
diffs := [];
for i in [1..Length(classes_by_order1)] do
  if classes_by_order1[i][2] <> classes_by_order2[i][2] or
     classes_by_order1[i][3] <> classes_by_order2[i][3] then
    Add(diffs, classes_by_order1[i][1]);
  fi;
od;

if diffs <> [] then
  PrintTo("*stdout*", "\nDIFFERENCES in class/element counts at orders: ", diffs, "\n");
else
  PrintTo("*stdout*", "\nNo differences in class/element counts by order.\n");
fi;

# --- Task 6: Cyclic-subgroup / rational-class orbits ---
PrintTo("*stdout*", "\n=== TASK 6: CYCLIC SUBGROUP ORBITS (RATIONAL CLASSES) ===\n");

# Use ClassOrbit to compute orbits; two classes are in the same orbit if one is
# a power map image of the other with exponent coprime to element order.

rational_orbits1 := [];
processed1 := [];
for i in [1..nc1] do
  if not i in processed1 then
    orbit := ClassOrbit(t1, i);
    Add(rational_orbits1, [i, Length(orbit), orbit]);
    for j in orbit do Add(processed1, j); od;
  fi;
od;

rational_orbits2 := [];
processed2 := [];
for i in [1..nc2] do
  if not i in processed2 then
    orbit := ClassOrbit(t2, i);
    Add(rational_orbits2, [i, Length(orbit), orbit]);
    for j in orbit do Add(processed2, j); od;
  fi;
od;

PrintTo("*stdout*", "\nO7(3): ", Length(rational_orbits1), " rational-class orbits\n");
for row in rational_orbits1 do
  PrintTo("*stdout*", "  Orbit containing class ", row[1], ": size ", row[2], "\n");
od;

PrintTo("*stdout*", "\nS6(3): ", Length(rational_orbits2), " rational-class orbits\n");
for row in rational_orbits2 do
  PrintTo("*stdout*", "  Orbit containing class ", row[1], ": size ", row[2], "\n");
od;

# Multisets of orbit sizes
orbsizes1 := List(rational_orbits1, row -> row[2]);
orbsizes2 := List(rational_orbits2, row -> row[2]);
orbsizes1 := Sorted(orbsizes1);
orbsizes2 := Sorted(orbsizes2);

PrintTo("*stdout*", "\nO7(3) orbit-size multiset: ", orbsizes1, "\n");
PrintTo("*stdout*", "S6(3) orbit-size multiset: ", orbsizes2, "\n");
PrintTo("*stdout*", "Orbit multisets equal: ", orbsizes1 = orbsizes2, "\n");

# --- Task 7: Frobenius-Schur indicators and character degrees ---
PrintTo("*stdout*", "\n=== TASK 7: FROBENIUS-SCHUR INDICATORS & CHARACTER DEGREES ===\n");

inds1 := Indicator(t1, 2);
inds2 := Indicator(t2, 2);
inds1_sorted := Sorted(inds1);
inds2_sorted := Sorted(inds2);

PrintTo("*stdout*", "O7(3) Frobenius-Schur indicator multiset (sorted): ", inds1_sorted, "\n");
PrintTo("*stdout*", "S6(3) Frobenius-Schur indicator multiset (sorted): ", inds2_sorted, "\n");
PrintTo("*stdout*", "Indicators equal: ", inds1_sorted = inds2_sorted, "\n");

degs1 := Set(CharacterDegrees(t1));
degs2 := Set(CharacterDegrees(t2));

PrintTo("*stdout*", "\nO7(3) character degree multiset size: ", Sum(degs1, x -> x[2]), " characters\n");
PrintTo("*stdout*", "S6(3) character degree multiset size: ", Sum(degs2, x -> x[2]), " characters\n");

# Convert to sorted lists for comparison
degs1_list := [];
for pair in degs1 do
  for i in [1..pair[2]] do Add(degs1_list, pair[1]); od;
od;
degs2_list := [];
for pair in degs2 do
  for i in [1..pair[2]] do Add(degs2_list, pair[1]); od;
od;
degs1_list := Sorted(degs1_list);
degs2_list := Sorted(degs2_list);

if degs1_list = degs2_list then
  PrintTo("*stdout*", "Character degree multisets equal: TRUE\n");
else
  PrintTo("*stdout*", "Character degree multisets equal: FALSE\n");
  # Show first 10 degrees of each to spot differences
  PrintTo("*stdout*", "  First 10 O7(3) degrees: ", degs1_list{[1..Minimum(10, Length(degs1_list))]}, "\n");
  PrintTo("*stdout*", "  First 10 S6(3) degrees: ", degs2_list{[1..Minimum(10, Length(degs2_list))]}, "\n");
fi;

# --- Bonus Task 8: q=5 tables if they exist ---
PrintTo("*stdout*", "\n=== BONUS TASK 8: q=5 CASE (O7(5) vs S6(5)) ===\n");

t1_q5 := CharacterTable("O7(5)");
t2_q5 := CharacterTable("S6(5)");

if t1_q5 <> fail and t2_q5 <> fail then
  PrintTo("*stdout*", "Both q=5 tables loaded.\n");

  sz1_q5 := Size(t1_q5);
  sz2_q5 := Size(t2_q5);
  PrintTo("*stdout*", "O7(5) order:  ", sz1_q5, "\n");
  PrintTo("*stdout*", "S6(5) order:  ", sz2_q5, "\n");
  PrintTo("*stdout*", "Orders equal: ", sz1_q5 = sz2_q5, "\n");

  nc1_q5 := NrConjugacyClasses(t1_q5);
  nc2_q5 := NrConjugacyClasses(t2_q5);
  PrintTo("*stdout*", "O7(5) conjugacy classes: ", nc1_q5, "\n");
  PrintTo("*stdout*", "S6(5) conjugacy classes: ", nc2_q5, "\n");
  PrintTo("*stdout*", "Classes equal: ", nc1_q5 = nc2_q5, "\n");

  # Involution counts for q=5
  sizes1_q5 := SizesConjugacyClasses(t1_q5);
  sizes2_q5 := SizesConjugacyClasses(t2_q5);
  classorders1_q5 := OrdersClassRepresentatives(t1_q5);
  classorders2_q5 := OrdersClassRepresentatives(t2_q5);

  inv1_q5 := 0;
  inv2_q5 := 0;
  for i in [1..Length(classorders1_q5)] do
    if classorders1_q5[i] = 2 then
      inv1_q5 := inv1_q5 + sizes1_q5[i];
    fi;
  od;
  for i in [1..Length(classorders2_q5)] do
    if classorders2_q5[i] = 2 then
      inv2_q5 := inv2_q5 + sizes2_q5[i];
    fi;
  od;

  PrintTo("*stdout*", "O7(5) involution count:  ", inv1_q5, "\n");
  PrintTo("*stdout*", "S6(5) involution count:  ", inv2_q5, "\n");
  PrintTo("*stdout*", "Involution counts equal: ", inv1_q5 = inv2_q5, "\n");

else
  if t1_q5 = fail then
    PrintTo("*stdout*", "O7(5) table not available (skip).\n");
  fi;
  if t2_q5 = fail then
    PrintTo("*stdout*", "S6(5) table not available (skip).\n");
  fi;
fi;

PrintTo("*stdout*", "\n=== COMPUTATION COMPLETE ===\n");
QUIT_GAP(0);
