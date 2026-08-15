# Corrected G9 (audit of an earlier run): TRUE unnormalized based orbit
# hypergroups c(i,j,k) = #{ g in W : a_i * g(b_j) in O_k } for one rep W of
# each conjugacy class of subgroups of Aut(C9 x C9). Orbit classes sorted by
# (size, then canonical); emitted as Python literals for exact pairwise
# based-iso testing (python/g9_correct.py).
A := SmallGroup(81, 2);;
AutA := AutomorphismGroup(A);;
ccW := ConjugacyClassesSubgroups(AutA);;
els := Elements(A);;
out := OutputTextFile("/tmp/g9_true.py", false);;
SetPrintFormattingStatus(out, false);
PrintTo(out, "data = [\n");
for ci in [1..Length(ccW)] do
  W := Representative(ccW[ci]);
  orbs := ShallowCopy(OrbitsDomain(W, els, function(x, a) return Image(a, x); end));
  Sort(orbs, function(a,b) return Length(a) < Length(b); end);
  n := Length(orbs);
  cls := [];
  for k in [1..n] do for x in orbs[k] do cls[Position(els, x)] := k; od; od;
  Wl := Elements(W);
  tabs := [];
  for i in [1..n] do
    a := orbs[i][1];
    row := [];
    for j in [1..n] do
      b := orbs[j][1];
      tally := List([1..n], x -> 0);
      for g in Wl do
        z := a * Image(g, b);
        k := cls[Position(els, z)];
        tally[k] := tally[k] + 1;
      od;
      Add(row, tally);
    od;
    Add(tabs, row);
  od;
  AppendTo(out, "{'cls':", ci, ",'W':", Size(W),
           ",'sizes':", List(orbs, Length), ",'S':", tabs, "},\n");
od;
AppendTo(out, "]\n");
CloseStream(out);
Print("done: ", Length(ccW), " classes\n");
QUIT;
