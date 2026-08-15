# Export multiplication tables of all SmallGroups up to order 48
out := OutputTextFile("/tmp/sg48_tables.py", false);
SetPrintFormattingStatus(out, false);
PrintTo(out, "data = [\n");

for n in [1..48] do
  for i in [1..NrSmallGroups(n)] do
    G := SmallGroup(n, i);
    els := Elements(G);
    sz := Size(G);
    mult := [];
    for a in els do
      row := [];
      for b in els do
        Add(row, Position(els, a*b) - 1);
      od;
      Add(mult, row);
    od;
    AppendTo(out, "{'n':", n, ",'i':", i, ",'M':", mult, "},\n");
  od;
od;

AppendTo(out, "]\n");
CloseStream(out);
Print("Exported all groups up to order 48.\n");
QUIT;
