# Z-rank of D(G) = |M(G)/G| = # G-conjugacy classes of pairs (H, hH'),
# H <= G, h in H, H' = [H,H].
# For fixed H: the pairs are the cosets hH' in H/H' = H^ab, and N_G(H) acts
# on H/H' by conjugation (well-defined: N_G(H) normalizes H, hence H').
# So the count for H is the number of N_G(H)-orbits on the SET H/H'.
# Total = sum over conjugacy classes of subgroups H.
#
# Run:  ~/gap-4.15.1/gap -q -b provenance/gap/census/rank_p3.g

NumPairsForH := function(G, H)
  local N, epi, Q, elts, orbs, seen, q, orb, x, ncan, gensN, imgs, n, pre, con;
  N   := Normalizer(G, H);
  epi := NaturalHomomorphismByNormalSubgroup(H, DerivedSubgroup(H));
  Q   := Image(epi);                       # H/H' as a group
  elts := Elements(Q);
  gensN := GeneratorsOfGroup(N);
  seen := [];
  orbs := 0;
  for q in elts do
    if q in seen then continue; fi;
    orbs := orbs + 1;
    orb := [q];
    for x in orb do
      for n in gensN do
        pre := PreImagesRepresentative(epi, x);
        con := Image(epi, n^-1 * pre * n);
        if not con in orb then Add(orb, con); fi;
      od;
    od;
    Append(seen, orb);
  od;
  return orbs;
end;

RankD := function(G)
  local ccs, total, c;
  ccs := ConjugacyClassesSubgroups(G);
  total := 0;
  for c in ccs do
    total := total + NumPairsForH(G, Representative(c));
  od;
  return total;
end;

RunG := function(id)
  local G, r;
  G := SmallGroup(id[1], id[2]);
  r := RankD(G);
  Print("SmallGroup(", id[1], ",", id[2], ")  ",
        StructureDescription(G), "  rank D(G) = ", r, "\n");
  return r;
end;

# Order 27: SmallGroup(27,3) = Heisenberg (exponent 3, = Mueller G1);
#           SmallGroup(27,4) = exponent 9 (= Mueller G2).
Print("=== order 27 (p=3) ===\n");
RunG([27,3]);
RunG([27,4]);

# Order 125 (p=5) cross-check
Print("=== order 125 (p=5) ===\n");
RunG([125,3]);
RunG([125,4]);

Print("=== Mueller's formulas ===\n");
Print("G1 = p(4p+3):  p=3 -> ", 3*(4*3+3), ",  p=5 -> ", 5*(4*5+3), "\n");
Print("G2 = 3p(p+1):   p=3 -> ", 3*3*4,      ",  p=5 -> ", 3*5*6,      "\n");
