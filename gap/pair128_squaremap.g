# The intrinsic squaring map q: V=G/Phi -> Phi (a quadratic F2^4 -> F2^3),
# its polarization (commutator pairing), and the invariants that separate
# (128,1597) from (128,1598). This is the correct replacement for §5.
LogTo("/Users/tilemachosvassias/DissAnalysis/dring-project/results/order128_pairs/pair128_squaremap.out");

Analyse := function(id)
  local G, Phi, Z, hV, V, hW, W, pcV, pcW, vecs, q, v, g, sq, zeros,
        b, pairs, u, w, gu, gw, comm, radical, isZ;
  G := SmallGroup(128, id);
  Phi := FrattiniSubgroup(G);
  Z := Centre(G);
  isZ := Phi = Z;
  hV := NaturalHomomorphismByNormalSubgroup(G, Phi);   # G -> V = G/Phi
  V := Image(hV);                                       # C2^4
  pcV := Pcgs(V);
  # squaring map q: V -> Phi (well-defined iff Phi central; q(v)=lift(v)^2)
  q := function(v) return PreImagesRepresentative(hV, v)^2; end;
  vecs := Elements(V);
  zeros := Filtered(vecs, v -> q(v) = Identity(Phi));  # isotropic set q(v)=0
  Print("id=", id, ": Phi=Z(G)? ", isZ,
        "   |q^-1(0)| (incl 0) = ", Length(zeros), " of ", Length(vecs), "\n");
  # image of q inside Phi and its size
  Print("        image q multiset of Phi-orders: ",
        Collected(List(vecs, v -> Order(q(v)))), "\n");
  # polarization b(u,w) = [lift u, lift w] in Phi ; report as a form's radical dim
  b := function(u,w)
    return Comm(PreImagesRepresentative(hV,u), PreImagesRepresentative(hV,w));
  end;
  radical := Filtered(vecs, u -> ForAll(vecs, w -> b(u,w) = Identity(Phi)));
  Print("        commutator-form radical size = ", Length(radical),
        "  (=> rank of alternating form via 16/|rad|)\n");
  # finer: the multiset over v of Order(q(v)) already; also |{v: q(v)=z}| profile
  Print("        fibre-size profile of q (over Phi): ",
        Collected(List(Elements(Phi), z -> Number(vecs, v -> q(v)=z))), "\n");
  return rec(zeros:=Length(zeros), radical:=Length(radical));
end;

Print("\n==== squaring map / quadratic invariant ====\n");
r1 := Analyse(1597);
r2 := Analyse(1598);
Print("\nSEPARATED by |q^-1(0)|: ", r1.zeros <> r2.zeros,
      "   by radical: ", r1.radical <> r2.radical, "\n");
LogTo();
QUIT;
