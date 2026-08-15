# Exact species metadata for the 1597/1598 ring-isomorphism search.
# Uses the same coset-orbit species convention as DG_G_coset.

Read("gap/dring_sieve_standalone.g");;

ExportMeta := function(id)
  local G, cls, out, s, N, stab, conductor, filename;
  G := SmallGroup(128, id);
  cls := SpeciesClassesD(G);
  filename := Concatenation("results/order128_pairs/g128_", String(id),
                            "_species_meta.txt");
  out := OutputTextFile(filename, false);
  SetPrintFormattingStatus(out, false);
  AppendTo(out, Length(cls), "\n");
  for s in cls do
    N := Normalizer(G, s.H);
    stab := Filtered(Elements(N), n ->
      Image(s.nat, PreImagesRepresentative(s.nat, s.q) ^ n) = s.q);
    conductor := Length(stab) / Size(s.Hp);
    if not IsInt(conductor) then Error("nonintegral conductor"); fi;
    AppendTo(out, Size(s.H), " ", Order(s.q), " ", conductor, " ",
             s.Hidx, "\n");
  od;
  CloseStream(out);
  Print("metadata ", id, ": ", Length(cls), " species -> ", filename, "\n");
end;

ExportMeta(1597);
ExportMeta(1598);
QUIT;
