# item 3: enumerate the faithful 2-subgroups W <= Aut(Abar) for
# Abar in {C4xC4, C4xC4xC2, C4^3}, up to conjugacy, exporting each generator's
# permutation action on the (fixed-order) element list of Abar.  Python
# (python/xprime_wclass.py) then computes, per W, whether some W-invariant
# K_1 element has nonzero square-pushforward (the R1 danger criterion for X').
PrintTo("/tmp/xprime_wclass.out", "");  # truncate
groups := [ [ "C4xC4",    [4,4]   ],
            [ "C4xC4xC2", [4,4,2] ] ];;
for gd in groups do
  name := gd[1];;  inv := gd[2];;
  A := AbelianGroup(inv);;
  els := Elements(A);;
  gg := IndependentGeneratorsOfAbelianGroup(A);;
  Aut := AutomorphismGroup(A);;
  ccs := ConjugacyClassesSubgroups(Aut);;
  reps := List(ccs, Representative);;
  reps := Filtered(reps, W -> Size(W) > 1 and IsPrimePowerInt(Size(W))
                              and SmallestPrimeDivisor(Size(W)) = 2);;
  AppendTo("/tmp/xprime_wclass.out",
           "GROUP ", name, " ninv=", inv, " nels=", Length(els),
           " n2subclasses=", Length(reps), "\n");
  # element coordinates in abelian-invariant Z/inv_i coords, fixed order
  AppendTo("/tmp/xprime_wclass.out", "ORDERS ", List(gg, Order), "\n");
  AppendTo("/tmp/xprime_wclass.out", "ELS ",
           List(els, e -> IndependentGeneratorExponents(A, e)), "\n");
  for W in reps do
    gp := List(GeneratorsOfGroup(W),
               g -> List(els, e -> Position(els, Image(g, e)) - 1));;
    AppendTo("/tmp/xprime_wclass.out",
             "W ", name, " size ", Size(W), " id ",
             StructureDescription(W), " gens ", gp, "\n");
  od;
  AppendTo("/tmp/xprime_wclass.out", "ENDGROUP ", name, "\n");
od;
Print("done; wrote /tmp/xprime_wclass.out\n");
QUIT;
