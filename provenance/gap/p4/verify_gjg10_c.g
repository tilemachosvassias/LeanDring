# Do full tables of marks separate SmallGroup(p^4, i) for i in {3,8,9,10}?
# (These four share identical subgroup counts after correcting GJG10's (xi) row.)
# Invariant used: the multiset over subgroup classes of
#   (|H|, |class of H|, sorted row of marks)  — a ToM-iso invariant.
CheckToM := function(p)
  local ids, i, G, tom, mat, n, inv, invs, j, k, row, subs, ords, lens;
  Print("=== p = ", p, " : ToM invariants of ids [3,8,9,10] ===\n");
  invs := [];
  for i in [3, 8, 9, 10] do
    G := SmallGroup(p^4, i);
    tom := TableOfMarks(G);
    mat := MatTom(tom);
    n := Length(mat);
    ords := OrdersTom(tom);
    lens := LengthsTom(tom);
    inv := [];
    for j in [1..n] do
      row := ShallowCopy(mat[j]);
      Sort(row);
      Add(inv, [ords[j], lens[j], row]);
    od;
    Sort(inv);
    Add(invs, [i, inv]);
    Print("  id ", i, ": #classes = ", n, "\n");
  od;
  for j in [1..3] do
    for k in [j+1..4] do
      Print("  id ", invs[j][1], " vs id ", invs[k][1], " : ToM-invariant equal = ",
            invs[j][2] = invs[k][2], "\n");
    od;
  od;
end;
CheckToM(5);
CheckToM(7);
QUIT;
