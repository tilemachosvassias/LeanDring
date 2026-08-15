# Crosscheck the standalone exporter species rows against audited DG_G_coset.

Read("gap/dring_sieve_standalone.g");;
Read("gap/dg_correct.g");;

for id in [1597, 1598] do
  G := SmallGroup(128, id);;
  cls := SpeciesClassesD(G);;
  dg := DG_G_coset(G);;
  if Length(cls) <> Length(dg) then Error("species-count mismatch"); fi;
  for d in dg do
    hits := Filtered(cls, s -> s.H = d[1] and
      Image(s.nat, d[2]) in Orbit(Normalizer(G, s.H), s.q,
        function(pnt, n)
          return Image(s.nat, PreImagesRepresentative(s.nat, pnt) ^ n);
        end));
    if Length(hits) <> 1 then Error("coset row mismatch"); fi;
  od;
  Print("DG_G_coset crosscheck ", id, ": PASS (", Length(cls), " rows)\n");
od;
QUIT;
