# v_task17_probe1.g -- sanity check RepresentativesPerfectSubgroups on small
# groups and on the M22 twin direct product PGL(2,7) x PGL(2,11).

Print("=== probe: basic perfect-subgroup machinery ===\n");
g1 := PSL(2,7);;
Print("PSL(2,7) order: ", Size(g1), "\n");
r1 := RepresentativesPerfectSubgroups(g1);;
Print("PSL(2,7) # perfect subgroup classes: ", Length(r1), "\n");
for u in r1 do
  Print("  order ", Size(u), "\n");
od;

Print("\n=== PGL(2,7) ===\n");
g2 := PGL(2,7);;
Print("PGL(2,7) order: ", Size(g2), "\n");
r2 := RepresentativesPerfectSubgroups(g2);;
Print("PGL(2,7) # perfect subgroup classes: ", Length(r2), "\n");
for u in r2 do
  Print("  order ", Size(u), "  selfnorm=", Size(Normalizer(g2,u))=Size(u), "\n");
od;

Print("\n=== timing DirectProduct(PGL(2,7),PGL(2,11)) construction ===\n");
t0 := Runtime();;
g3 := PGL(2,11);;
Print("PGL(2,11) order: ", Size(g3), "\n");
dp := DirectProduct(g2,g3);;
Print("DirectProduct order: ", Size(dp), " time(ms)=", Runtime()-t0, "\n");
