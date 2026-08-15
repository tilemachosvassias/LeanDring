# class-count polynomials for the quartet {3,8,9,10}: conjectured
# id3: 6p+5, id8: 4p+7, id9=id10: 2p+8  — confirm at p = 11, 13
for p in [11, 13] do
  Print("p = ", p, " : ");
  for i in [3, 8, 9, 10] do
    Print("id", i, "=", Length(ConjugacyClassesSubgroups(SmallGroup(p^4, i))), " ");
  od;
  Print("  [6p+5=", 6*p+5, ", 4p+7=", 4*p+7, ", 2p+8=", 2*p+8, "]\n");
od;
QUIT;
