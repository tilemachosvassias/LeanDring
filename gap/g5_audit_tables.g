out := OutputTextFile("/tmp/g5_true.py", false);;
SetPrintFormattingStatus(out, false);
PrintTo(out, "data = {\n");
A := SmallGroup(9, 2);;
AutA := AutomorphismGroup(A);;
ccW := ConjugacyClassesSubgroups(AutA);;
els := Elements(A);;
AppendTo(out, "\"9,2\": [\n");
for ci in [10, 12] do
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
  AppendTo(out, "{'cls':", ci, ",'W':", Size(W), ",'sizes':", List(orbs, Length), ",'S':", tabs, "},\n");
od;
AppendTo(out, "],\n");
A := SmallGroup(12, 5);;
AutA := AutomorphismGroup(A);;
ccW := ConjugacyClassesSubgroups(AutA);;
els := Elements(A);;
AppendTo(out, "\"12,5\": [\n");
for ci in [9, 7] do
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
  AppendTo(out, "{'cls':", ci, ",'W':", Size(W), ",'sizes':", List(orbs, Length), ",'S':", tabs, "},\n");
od;
AppendTo(out, "],\n");
A := SmallGroup(16, 2);;
AutA := AutomorphismGroup(A);;
ccW := ConjugacyClassesSubgroups(AutA);;
els := Elements(A);;
AppendTo(out, "\"16,2\": [\n");
for ci in [11, 12, 13, 18, 29, 30, 31, 32, 34, 37, 40, 41, 42, 43, 44, 46, 47, 48, 49, 50, 53, 54, 55, 56, 57, 59, 60, 61] do
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
  AppendTo(out, "{'cls':", ci, ",'W':", Size(W), ",'sizes':", List(orbs, Length), ",'S':", tabs, "},\n");
od;
AppendTo(out, "],\n");
A := SmallGroup(16, 10);;
AutA := AutomorphismGroup(A);;
ccW := ConjugacyClassesSubgroups(AutA);;
els := Elements(A);;
AppendTo(out, "\"16,10\": [\n");
for ci in [10, 13, 15, 17, 22, 24, 30, 32, 33, 35, 36, 37, 38, 40, 41, 42, 44, 45, 46, 48, 49, 50, 51, 52, 56, 57, 62, 63, 64, 65, 66, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 79, 80, 83, 84, 85, 88, 89, 91, 92] do
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
  AppendTo(out, "{'cls':", ci, ",'W':", Size(W), ",'sizes':", List(orbs, Length), ",'S':", tabs, "},\n");
od;
AppendTo(out, "],\n");
A := SmallGroup(16, 14);;
AutA := AutomorphismGroup(A);;
ccW := ConjugacyClassesSubgroups(AutA);;
els := Elements(A);;
AppendTo(out, "\"16,14\": [\n");
for ci in [128, 129, 130, 131, 18, 19, 23, 25, 26, 27, 29, 30, 32, 33, 34, 38, 41, 45, 50, 55, 56, 57, 58, 59, 60, 64, 65, 66, 67, 69, 71, 73, 74, 75, 76, 83, 84, 85, 86, 87, 88, 93, 94, 95, 101, 103, 109, 110, 111, 113, 118, 119, 120, 121, 127] do
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
  AppendTo(out, "{'cls':", ci, ",'W':", Size(W), ",'sizes':", List(orbs, Length), ",'S':", tabs, "},\n");
od;
AppendTo(out, "],\n");
A := SmallGroup(16, 5);;
AutA := AutomorphismGroup(A);;
ccW := ConjugacyClassesSubgroups(AutA);;
els := Elements(A);;
AppendTo(out, "\"16,5\": [\n");
for ci in [26, 21] do
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
  AppendTo(out, "{'cls':", ci, ",'W':", Size(W), ",'sizes':", List(orbs, Length), ",'S':", tabs, "},\n");
od;
AppendTo(out, "],\n");
AppendTo(out, "}\n");
CloseStream(out);
QUIT;
