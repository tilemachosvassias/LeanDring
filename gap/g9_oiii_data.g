# O-iii probe data for C9 x C9: for each conjugacy class of subgroups of
# Aut(C9xC9), export the element-order multiset of W (abstract group invariant)
# and the cycle-type multiset of W acting on Ahat (permutation invariant).
# Uses the same conjugacy-class ordering as g9_true_tables.g.
# Output: /tmp/g9_oiii.py with a Python list of dicts.
A := SmallGroup(81, 2);;
AutA := AutomorphismGroup(A);;
ccW := ConjugacyClassesSubgroups(AutA);;
els := Elements(A);;
n := Length(els);
out := OutputTextFile("/tmp/g9_oiii.py", false);;
SetPrintFormattingStatus(out, false);
PrintTo(out, "oiii_data = [\n");
for ci in [1..Length(ccW)] do
  W := Representative(ccW[ci]);
  Wl := Elements(W);
  # Element orders of W (as abstract group)
  el_orders := SortedList(List(Wl, Order));
  # Cycle types of W acting on A: for each g in W, compute the permutation
  # g induces on els and find its cycle lengths
  cyc_types := [];
  for g in Wl do
    perm := List(els, x -> Position(els, Image(g, x)));
    seen := List([1..n], x -> false);
    cyc := [];
    for i in [1..n] do
      if not seen[i] then
        L := 0;
        j := i;
        while not seen[j] do
          seen[j] := true;
          j := perm[j];
          L := L + 1;
        od;
        Add(cyc, L);
      fi;
    od;
    Sort(cyc);
    Add(cyc_types, cyc);
  od;
  Sort(cyc_types);
  AppendTo(out, "{'cls':", ci, ",'W':", Size(W),
           ",'el_orders':", el_orders,
           ",'cyc_types':", cyc_types, "},\n");
od;
AppendTo(out, "]\n");
CloseStream(out);
Print("done: ", Length(ccW), " classes\n");
QUIT;
