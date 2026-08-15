Read("gap/dring_sieve_standalone.g");

ExportGroup := function(id)
  local G, cls, t, f, r, c, v, out;
  G := SmallGroup(32, id);
  cls := SpeciesClassesD(G);
  t := SpeciesTableD(G, cls);
  f := OutputTextFile(Concatenation("results/G32_", String(id), ".txt"), false);
  PrintTo(f, "{\n\"n\": ", Length(t), ",\n\"table\": [\n");
  for r in [1..Length(t)] do
    PrintTo(f, "[");
    for c in [1..Length(t[r])] do
      v := t[r][c];
      if IsInt(v) then
        PrintTo(f, "[", v, "]");
      else
        out := ExtRepOfObj(v);
        if Length(out) = 2 then
          PrintTo(f, "[", out[2], "]");
        else
          PrintTo(f, "[", out[2], ", ", out[4], "]");
        fi;
      fi;
      if c < Length(t[r]) then PrintTo(f, ", "); fi;
    od;
    PrintTo(f, "]");
    if r < Length(t) then PrintTo(f, ",\n"); else PrintTo(f, "\n"); fi;
  od;
  PrintTo(f, "]\n}\n");
  CloseStream(f);
end;

ExportGroup(13);
ExportGroup(14);
QUIT;
