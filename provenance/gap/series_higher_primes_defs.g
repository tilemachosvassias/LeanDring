# series_higher_primes_defs.g -- the order-p^5 series pair, its D-ring rank,
# and diagonal-block fingerprints (shared definitions).
#
# Gpq(p, q) is the order-p^5 group presented as in the paper's pc
# presentation (Section 4, eq. (7)) with 5 replaced by p; the series pair is
# q = 1 against q = NonResidue(p).  For p = 5 these are SmallGroup(3125,68)
# and SmallGroup(3125,69).  RankD(G) computes rank_Z D(G) by counting
# normalizer orbits on H/H' (Brauer's permutation lemma).  Read by
# provenance/gap/series_blocks_fast.g; for the rank-only checks at
# p = 11, 13, 17, 19 call RankD directly on Gpq(p, 1) and Gpq(p, d).
# Results: results/series_*.log in the development repository.

Gpq := function(p, q)
  local F, f, coll;
  F := FreeGroup("f1","f2","f3","f4","f5");
  f := GeneratorsOfGroup(F);
  coll := SingleCollector(F, [p,p,p,p,p]);
  SetPower(coll, 2, f[5]^q);
  SetConjugate(coll, 2, 1, f[2]*f[4]);
  SetConjugate(coll, 4, 1, f[4]*f[5]);
  SetConjugate(coll, 3, 2, f[3]*f[5]);
  return GroupByRws(coll);
end;

NonResidue := function(p)
  local d;
  for d in [2..p-1] do
    if Legendre(d, p) = -1 then return d; fi;
  od;
end;

# rank of D(G) = number of pair classes [K,lambda] = sum over subgroup
# classes of the number of N_G(K)-orbits on the linear characters of K.
# We count orbits on K/K' instead: N acts on the abelian group K/K' and on
# its dual with the same permutation character (Brauer's permutation lemma
# applied to each cyclic subgroup), so the orbit counts agree -- and orbits
# of elements are far cheaper than building character tables.  This is the
# same duality that makes the paper's order-fibre split identical on the
# character and the species side.
RankD := function(G)
  local r, c, H, N, nat, orb;
  r := 0;
  for c in ConjugacyClassesSubgroups(G) do
    H := Representative(c);
    N := Normalizer(G, H);
    nat := NaturalHomomorphismByNormalSubgroup(H, DerivedSubgroup(H));
    orb := OrbitsDomain(N, Elements(Image(nat)),
             {x, g} -> Image(nat, PreImagesRepresentative(nat, x)^g));
    r := r + Length(orb);
  od;
  return r;
end;

# For each conjugacy class of subgroups, the diagonal block of the species
# table, reduced to a permutation-invariant fingerprint: the sorted list of
# sorted rows.  Returns the sorted list of [ |H|, fingerprint ].
DiagonalBlockFingerprints := function(G)
  local ccs, out, ci, H, N, HD, nat, img, orb, o, rows, lams, cols, tv, fix,
        blk, i, j, entry, q, x;
  ccs := ConjugacyClassesSubgroups(G);
  out := [];
  for ci in [1..Length(ccs)] do
    H  := Representative(ccs[ci]);
    N  := Normalizer(G, H);
    HD := DerivedSubgroup(H);
    nat := NaturalHomomorphismByNormalSubgroup(H, HD);
    img := Elements(Image(nat));
    orb := OrbitsDomain(N, img,
             {x, g} -> Image(nat, PreImagesRepresentative(nat, x)^g));
    rows := List(orb, o -> PreImagesRepresentative(nat, Representative(o)));
    lams := LinearCharacters(H);
    cols := List(Orbits(ExternalSet(N, lams)), o -> Representative(o));
    # q in K\G with q H q^-1 <= H, for K = H: exactly the normalizer cosets
    tv  := RightTransversal(G, H);
    fix := Filtered(tv, q -> ForAll(GeneratorsOfGroup(H),
                                    x -> q * x * q^-1 in H));
    blk := [];
    for i in [1..Length(rows)] do
      blk[i] := [];
      for j in [1..Length(cols)] do
        entry := 0;
        for q in fix do
          entry := entry + (q * rows[i] * q^-1) ^ cols[j];
        od;
        blk[i][j] := entry;
      od;
      Sort(blk[i]);
    od;
    Sort(blk);
    Add(out, [ Size(H), Length(rows), blk ]);
  od;
  Sort(out);
  return out;
end;

