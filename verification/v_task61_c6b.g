##  v_task61_c6b.g -- the C_6 column of p^C_4(q), with the CORRECT group.
##  v_task61_p4.g used PerfectGroup(1920,1) = 2^5:A_5, which is NOT the
##  C_6 member; the extraspecial-type group is PerfectGroup(1920,7) =
##  ((C2 x Q8):C2):A5 = 2^{1+4}_-.A_5 (v_task61_c6.g).

Count := function(P, phi, F, H, name)
  local isos, r, U, M, gens, n, nirr, npsn;
  isos := IsomorphicSubgroups(P, H);
  n := Length(isos); nirr := 0; npsn := 0;
  for r in isos do
    U := Image(r);
    gens := List(GeneratorsOfGroup(U), g -> PreImagesRepresentative(phi, g));
    M := GModuleByMats(gens, F);
    if MTX.IsIrreducible(M) then
      nirr := nirr + 1;
      if Size(Normalizer(P, U)) = Size(U) then npsn := npsn + 1; fi;
    fi;
  od;
  Print("  ", String(name,22), ": ", n, " classes, ", nirr,
        " irreducible, ", npsn, " PRIMITIVE psn\n");
  return npsn;
end;;

for q in [5, 7] do
  F := GF(q);
  G := Sp(4,q);
  phi := IsomorphismPermGroup(G);
  P := Image(phi);
  Print("=== q = ", q, " ===\n");
  for k in [4, 7] do
    Count(P, phi, F, PerfectGroup(IsPermGroup,1920,k),
          Concatenation("PerfectGroup(1920,", String(k), ")"));
  od;
od;
QUIT;
