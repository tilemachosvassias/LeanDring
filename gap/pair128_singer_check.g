# AUDIT: is the "Singer operator" of §5 real? It is NOT conjugation on A/Phi
# (that is trivial), but phi_hat = sigma^-1 o phi, where phi(a)=[t,a] in 2A and
# sigma(a)=a^2 is the squaring iso A/2A -> 2A. Prior claim: charpoly is
# x^3+x+1 (1597) vs x^3+x^2+1 (1598), reciprocal irreducible cubics (Singer).
LogTo("/Users/tilemachosvassias/DissAnalysis/dring-project/results/order128_pairs/pair128_singer_check.out");

SingerOp := function(id)
  local G, Phi, A, t, U, hU, gens, reps, sigma, phi, i, Minv, Mphi, phihat, cp;
  G := SmallGroup(128, id); Phi := FrattiniSubgroup(G);
  A := First(MaximalSubgroupClassReps(G),
             m -> IsAbelian(m) and IsNormal(G,m) and StructureDescription(m)="C4 x C4 x C4");
  t := First(Elements(G), g -> Order(g)=2 and not g in A);
  hU := NaturalHomomorphismByNormalSubgroup(A, Phi);   # A -> U = A/2A = F2^3
  U := Image(hU);
  gens := IndependentGeneratorsOfAbelianGroup(U);      # basis of U
  reps := List(gens, u -> PreImagesRepresentative(hU, u));   # lifts in A
  # sigma: U -> Phi, u-bar |-> a^2  (columns = images in Pcgs(Phi) coords)
  sigma := List(reps, a -> ExponentsOfPcElement(Pcgs(Phi), a^2) * Z(2)^0);
  # phi: U -> Phi, u-bar |-> [t,a] = t^-1 a^-1 t a
  phi := List(reps, a -> ExponentsOfPcElement(Pcgs(Phi), Comm(t, a)) * Z(2)^0);
  # phi_hat = sigma^-1 o phi as a matrix on U (coords in {gens}):
  # rows of sigma/phi are images in Phi-coords; solve  phihat = phi * sigma^-1
  Minv := TransposedMat(sigma)^-1;               # Phi-coord -> U-coord
  phihat := List(phi, v -> Minv * v);            # each phi(u) back to U-coords
  phihat := ImmutableMatrix(GF(2), phihat);
  cp := CoefficientsOfUnivariatePolynomial(CharacteristicPolynomial(phihat));
  Print("id=", id, ": order(phi_hat)=", Order(phihat),
        "  charpoly coeffs(low->high)=", cp,
        "  irreducible=", IsIrreducible(CharacteristicPolynomial(phihat)),
        "  trace=", TraceMat(phihat), "\n");
  return cp;
end;

Print("== Singer operator phi_hat = sigma^-1 o [t,-] ==\n");
c1 := SingerOp(1597);
c2 := SingerOp(1598);
Print("distinct charpolys (reciprocal cubics): ", c1 <> c2, "\n");
LogTo();
QUIT;
