# Orthogonal GF validation: Omega(5,q) ~ PSp4(q).  Shapes for dim 5 (fixed space <=1):
#   5 (irreducible) and 4+1.  So psn(Omega5) = p^O_5 + (4-dim primitives surviving the glue).
for q in [5,7] do
  G := Omega(5,q);;
  hom := ActionHomomorphism(G, NormedRowVectors(GF(q)^5), OnLines);;
  P := Image(hom);;
  Print("Omega(5,",q,") degree ", NrMovedPoints(P), " size ", Size(P), "\n");
  reps := RepresentativesPerfectSubgroups(P);;
  Print("  perfect classes: ", Length(reps), "\n");
  for U in reps do
    if Size(U) > 1 then
      N := Normalizer(P,U);
      if Size(N) = Size(U) then
        Um := PreImage(hom, U);
        M := GModuleByMats(GeneratorsOfGroup(Um), GF(q));
        fx := NullspaceMat(TransposedMat(Concatenation(List(GeneratorsOfGroup(Um), g -> g - IdentityMat(5,GF(q))))));
        Print("  PSN |U|=", Size(U), "  irred5=", MTX.IsIrreducible(M),
              "  dim(fixed space)=", Length(fx), "  ", StructureDescription(U), "\n");
      fi;
    fi;
  od;
od;
QUIT;
