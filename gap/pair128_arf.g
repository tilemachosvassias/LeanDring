# Complete-enough discriminator: the multiset over the 7 nonzero functionals
# lambda: Phi -> F2 of the Arf class of the scalar quadratic form
# Q_lambda = lambda o q on V=F2^4.  Invariant under GL(W); if it differs,
# q_1597 and q_1598 are inequivalent, so q is exactly the distinguishing datum.
LogTo("/Users/tilemachosvassias/DissAnalysis/dring-project/results/order128_pairs/pair128_arf.out");

ArfSpectrum := function(id)
  local G, Phi, hV, V, vecs, q, Pelts, lambdas, spec, lam, zeros, v, qv, val, ev;
  G := SmallGroup(128, id); Phi := FrattiniSubgroup(G);
  hV := NaturalHomomorphismByNormalSubgroup(G, Phi); V := Image(hV);
  vecs := Elements(V);
  q := function(v) return PreImagesRepresentative(hV, v)^2; end;
  Pelts := Elements(Phi);
  # all group homomorphisms Phi(C2^3) -> C2, i.e. 8 functionals; take 7 nonzero
  lambdas := Filtered(Difference(
      List(Tuples([0,1], 3), c -> c), [[0,0,0]]), x->true);
  # represent a functional by a subgroup of index 2 (its kernel): lambda(z)=0 iff z in ker
  # easier: enumerate index-2 subgroups K of Phi; Q_K(v) = 0 iff q(v) in K.
  spec := [];
  for lam in Filtered(List(NormalSubgroups(Phi), K->K), K -> Size(K)=4) do
    zeros := Number(vecs, v -> q(v) in lam);
    # nondeg quadratic form on F2^4 has 10 zeros (Arf 0) or 6 zeros (Arf 1);
    # degenerate forms give other counts -- record raw zero count.
    Add(spec, zeros);
  od;
  Sort(spec);
  Print("id=", id, ": #index-2 kernels=", Length(spec),
        "   zero-count spectrum of Q_lambda = ", spec, "\n");
  Print("        (10<->Arf0, 6<->Arf1, 8/16<->degenerate on F2^4)\n");
  return spec;
end;

Print("\n==== scalar Arf spectrum of the squaring map ====\n");
s1 := ArfSpectrum(1597);
s2 := ArfSpectrum(1598);
Print("\nq INEQUIVALENT (spectra differ): ", s1 <> s2, "\n");
Print("s1=", s1, "\ns2=", s2, "\n");
LogTo();
QUIT;
