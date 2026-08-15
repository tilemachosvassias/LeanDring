# t4_known_brauer_pairs.g -- exact order-256 test of T4 on the ten
# published Brauer pairs of 2-groups.
#
# The weighted bipartite graph encodes every entry of MatTom.  Row vertices,
# column vertices, and one vertex for each nonzero entry have separate colours;
# entry-vertex colours encode the integer mark.  A coloured-digraph isomorphism
# is therefore exactly a pair of row/column permutations carrying one mark
# matrix to the other.  The returned permutations are verified entry-by-entry.
#
# Regression checks:
#   * a group against itself is equivalent;
#   * (32,13)/(32,14) is separated, agreeing with crossiso's exact B-side
#     decision in results/order32_pair_decision.md.
#
# Run:
#   ~/gap-4.15.1/gap -q -b gap/t4_known_brauer_pairs.g

LoadPackage("digraphs");;

ListHashT4 := function(xs)
  local h, x;
  h := 17;
  for x in xs do h := (h * 1000003 + x) mod 2147483629; od;
  return h;
end;

TomWeightedGraphT4 := function(M, values)
  local n, adj, colours, i, j, e;
  n := Length(M);
  adj := List([1..2*n], x -> []);
  # Rows and columns must not mix.
  colours := Concatenation(List([1..n], x -> 1),
                           List([1..n], x -> 2));
  for i in [1..n] do
    for j in [1..n] do
      if M[i][j] <> 0 then
        e := Length(adj) + 1;
        Add(adj, []);
        Add(colours, 2 + Position(values, M[i][j]));
        Add(adj[i], e);
        Add(adj[e], n + j);
      fi;
    od;
  od;
  return [Digraph(adj), colours];
end;

TomCertificateT4 := function(order, id1, id2)
  local A, B, n, values, g1, g2, p, rp, cp, ok;
  A := MatTom(TableOfMarks(SmallGroup(order, id1)));
  B := MatTom(TableOfMarks(SmallGroup(order, id2)));
  if Length(A) <> Length(B) then
    return rec(equivalent := false, reason := "different ranks");
  fi;
  n := Length(A);
  values := Set(Concatenation(Concatenation(A), Concatenation(B)));
  RemoveSet(values, 0);
  g1 := TomWeightedGraphT4(A, values);
  g2 := TomWeightedGraphT4(B, values);
  p := IsomorphismDigraphs(g1[1], g2[1], g1[2], g2[2]);
  if p = fail then
    return rec(equivalent := false, rank := n);
  fi;
  rp := List([1..n], i -> i^p);
  cp := List([1..n], j -> (n+j)^p - n);
  ok := ForAll([1..n], i ->
          ForAll([1..n], j -> A[i][j] = B[rp[i]][cp[j]]));
  if not ok then Error("digraph certificate failed direct verification"); fi;
  return rec(equivalent := true, rank := n,
             samePermutation := rp = cp,
             rowHash := ListHashT4(rp), colHash := ListHashT4(cp),
             rowPermutation := rp, colPermutation := cp);
end;

# Joint multiset of two ring-intrinsic species invariants: absolute-Galois
# orbit size and the tight Muller conductor (N_G(H,hH'):H').
DStage1T4 := function(order, id)
  local G, E, units, out, cl, H, Hp, N, cosets, act, orbs, o, c,
        stab, gal, a;
  G := SmallGroup(order, id);
  E := Exponent(G);
  units := Filtered([1..E], a -> GcdInt(a, E) = 1);
  out := [];
  for cl in ConjugacyClassesSubgroups(G) do
    H := Representative(cl);
    Hp := DerivedSubgroup(H);
    N := Normalizer(G, H);
    cosets := RightCosets(H, Hp);
    act := function(x, n)
      return RightCoset(Hp, Representative(x)^n);
    end;
    orbs := OrbitsDomain(N, cosets, act);
    for o in orbs do
      c := o[1];
      stab := Stabilizer(N, c, act);
      gal := Set(List(units, a -> PositionProperty(orbs, x ->
        RightCoset(Hp, Representative(c)^a) in x)));
      Add(out, [Length(gal), Size(stab) / Size(Hp)]);
    od;
  od;
  Sort(out);
  return out;
end;

ProperQuotientFingerprintT4 := function(order, id)
  local G, out, N;
  G := SmallGroup(order, id);
  out := [];
  for N in NormalSubgroups(G) do
    if Size(N) > 1 then Add(out, IdGroup(FactorGroup(G, N))); fi;
  od;
  Sort(out);
  return out;
end;

if not TomCertificateT4(8, 3, 3).equivalent then
  Error("positive ToM regression failed");
fi;
if TomCertificateT4(32, 13, 14).equivalent then
  Error("negative ToM regression failed");
fi;

Print("T4 on the ten published order-256 Brauer pairs\n");
Print("================================================\n");
pairs := [[1734,1735], [1736,1737], [1739,1740], [1741,1742],
          [3378,3380], [3379,3381], [3678,3679], [4154,4157],
          [4155,4158], [4156,4159]];;
hits := [];;
for pair in pairs do
  ct1 := CharacterTable(SmallGroup(256, pair[1]));;
  ct2 := CharacterTable(SmallGroup(256, pair[2]));;
  sameChar := TransformingPermutationsCharacterTables(ct1, ct2) <> fail;;
  cert := TomCertificateT4(256, pair[1], pair[2]);;
  Print(pair, " character+power=", sameChar,
        " ToM=", cert.equivalent);
  if cert.equivalent then
    Print(" rank=", cert.rank,
          " same-permutation=", cert.samePermutation,
          " hashes=", [cert.rowHash, cert.colHash]);
    Add(hits, pair);
  fi;
  Print("\n");
od;

Print("\nExact T4 counterexamples: ", hits, "\n");
Print("D-stage-1 and proper-quotient screens on the hits:\n");
for pair in hits do
  d1 := DStage1T4(256, pair[1]);;
  d2 := DStage1T4(256, pair[2]);;
  q1 := ProperQuotientFingerprintT4(256, pair[1]);;
  q2 := ProperQuotientFingerprintT4(256, pair[2]);;
  Print(pair, " D-ranks=", [Length(d1), Length(d2)],
        " D-stage1-equal=", d1 = d2,
        " proper-quotients-equal=", q1 = q2, "\n");
od;

QUIT;
