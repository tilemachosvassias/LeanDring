# dring_export.g -- read AFTER dring_sieve_standalone.g
# Exports the species table of D(G) (exact cyclotomic entries) and the
# table of marks to a plain text file, for the exact cross-group
# isomorphism decision in crossiso.py.
#
# Usage:
#   gap> Read("gap/lib/dring_sieve_standalone.g");
#   gap> Read("gap/lib/dring_export.g");
#   gap> DExport(SmallGroup(32,13), "g32_13.txt");
#   gap> DExport(SmallGroup(32,14), "g32_14.txt");
# then locally:
#   $ python3 crossiso.py g32_13.txt g32_14.txt

DExport := function(G, filename)
  local cls, T, N, n, out, i, j, line, coeffs, M, row;
  cls := SpeciesClassesD(G);
  T   := SpeciesTableD(G, cls);
  N   := Exponent(G);
  n   := Length(cls);
  out := OutputTextFile(filename, false);
  SetPrintFormattingStatus(out, false);
  AppendTo(out, n, " ", N, "\n");
  for i in [1..n] do
    line := Concatenation(String(Size(cls[i].H)), " ",
                          String(Order(cls[i].q)));
    for j in [1..n] do
      coeffs := CoeffsCyc(T[i][j], N);
      line := Concatenation(line, " ",
        JoinStringsWithSeparator(List(coeffs, String), " "));
    od;
    AppendTo(out, line, "\n");
  od;
  M := MatTom(TableOfMarks(G));
  AppendTo(out, "MARKS ", Length(M), "\n");
  for row in M do
    AppendTo(out,
      JoinStringsWithSeparator(List(row, String), " "), "\n");
  od;
  CloseStream(out);
  Print("exported ", n, " species (exponent ", N, ") and ",
        Length(M), "x", Length(M), " marks to ", filename, "\n");
end;
