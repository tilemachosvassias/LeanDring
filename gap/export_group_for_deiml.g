# export_group_for_deiml.g -- export a SmallGroup's multiplication table and
# one subgroup representative per conjugacy class, for the mod-2 Deiml/Loewy
# filter (results/deiml_filter_order256.md).  Bypasses the naive O(#subgroups
# * |G|) pure-Python subgroup enumeration in dring2.py's Group.all_subgroups()
# by using GAP's native ConjugacyClassesSubgroups (fast, kernel-optimized).
#
# Output JSON has: {"n": |G|, "mul": [[...]], "classes": [[elem-indices...]]}
# where element indices refer to positions in Elements(G) (0-based), matching
# the same ordering used for "mul".
#
# Usage: edit ORDER/ID/OUTFILE below, or call ExportGroupForDeiml directly.

ExportGroupForDeiml := function(order, id, outfile)
  local G, els, n, mul, a, row, b, out, first, cls, reps, rep, idxs, x, first2;
  G := SmallGroup(order, id);
  els := Elements(G);
  n := Length(els);
  out := OutputTextFile(outfile, false);
  SetPrintFormattingStatus(out, false);
  AppendTo(out, "{\"n\": ", n, ", \"mul\": [\n");
  first := true;
  for a in els do
    row := [];
    for b in els do
      Add(row, Position(els, a*b) - 1);
    od;
    if not first then AppendTo(out, ",\n"); fi;
    first := false;
    AppendTo(out, row);
  od;
  AppendTo(out, "\n], \"classes\": [\n");
  cls := ConjugacyClassesSubgroups(G);
  first := true;
  for rep in cls do
    reps := Representative(rep);
    idxs := List(Elements(reps), x -> Position(els, x) - 1);
    if not first then AppendTo(out, ",\n"); fi;
    first := false;
    AppendTo(out, idxs);
  od;
  AppendTo(out, "\n]}\n");
  CloseStream(out);
  Print("exported ", outfile, ": |G|=", n, ", #subgroup classes=", Length(cls), "\n");
end;
