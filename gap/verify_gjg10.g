# Verify GJG10 (Behm-Laine-Ståhl KTH MSc thesis) claims used in the preprint:
# 1. 15 groups of order p^4 (5 abelian, 10 nonabelian)  [Satz 2.1]
# 2. subgroup counts by order for the nonabelian groups  [table, incl. the
#    "unbekannt" entries for (xiv),(xv)]
# 3. presentations (xii)/(xiii): identify SmallGroup IDs, verify Props
#    4.1, 4.2, 4.4, 4.5 (center, power identity, maximal abelian subgroup,
#    orbit count p^2+p-1)

VerifyP := function(p)
  local n, ids, G, i, nab, ab, counts, cnt, d, F, a, b, c, rels, G1, G2,
        id1, id2, Z1, A, orbs, res, subs, o, byOrder, x, ca, pretty;
  n := p^4;
  Print("=== p = ", p, " ===\n");
  ids := NumberSmallGroups(n);
  ab := Number([1..ids], i -> IsAbelian(SmallGroup(n, i)));
  Print("  #groups = ", ids, "  (abelian: ", ab, ", nonabelian: ", ids - ab, ")\n");

  # subgroup counts by order for each nonabelian group
  Print("  Subgroup counts [p, p^2, p^3] per nonabelian SmallGroup id:\n");
  for i in [1..ids] do
    G := SmallGroup(n, i);
    if not IsAbelian(G) then
      subs := ConjugacyClassesSubgroups(G);
      byOrder := [0, 0, 0];
      for cnt in subs do
        o := Size(Representative(cnt));
        if o = p then byOrder[1] := byOrder[1] + Size(cnt); fi;
        if o = p^2 then byOrder[2] := byOrder[2] + Size(cnt); fi;
        if o = p^3 then byOrder[3] := byOrder[3] + Size(cnt); fi;
      od;
      pretty := [];
      # express in the table's polynomial forms where they match
      Print("    id ", i, ": ", byOrder,
            "   [p+1=", p+1, ", p^2+p+1=", p^2+p+1,
            ", 2p^2+p+1=", 2*p^2+p+1, ", p^3+p^2+p+1=", p^3+p^2+p+1, "]\n");
    fi;
  od;

  # the presentations (xii) [d=1] and (xiii) [d=QNR]
  d := First([2..p-1], x -> Jacobi(x, p) = -1);
  Print("  chosen QNR d = ", d, "\n");
  F := FreeGroup("a", "b", "c");
  a := F.1; b := F.2; c := F.3;
  # (xii): ba = a^{1+p} b, ca = a^{1+p} b c, cb = a^p b c
  rels := [a^(p^2), b^p, c^p,
           b*a*(a^(1+p)*b)^-1, c*a*(a^(1+p)*b*c)^-1, c*b*(a^p*b*c)^-1];
  G1 := F / rels;
  id1 := IdGroup(G1);
  # (xiii): ba = a^{1+p} b, ca = a^{1+dp} b c, cb = a^{dp} b c
  rels := [a^(p^2), b^p, c^p,
           b*a*(a^(1+p)*b)^-1, c*a*(a^(1+d*p)*b*c)^-1, c*b*(a^(d*p)*b*c)^-1];
  G2 := F / rels;
  id2 := IdGroup(G2);
  Print("  (xii)  IdGroup = ", id1, "   (xiii) IdGroup = ", id2, "\n");
  if id1 = id2 then Print("  *** WARNING: (xii) and (xiii) are ISOMORPHIC — presentation issue!\n"); fi;

  # verify Props 4.1/4.2/4.4/4.5 on the PC-group images
  for res in [["(xii)", SmallGroup(id1[1], id1[2]), 1],
              ["(xiii)", SmallGroup(id2[1], id2[2]), d]] do
    G := res[2];
    Print("  ", res[1], " order = ", Size(G),
          "  |Z| = ", Size(Center(G)),
          "  Z cyclic: ", IsCyclic(Center(G)), "\n");
    # maximal abelian subgroups of index p
    A := Filtered(MaximalSubgroups(G), IsAbelian);
    Print("    #abelian maximal subgroups = ", Length(A));
    if Length(A) = 1 then
      Print("  type = ", AbelianInvariants(A[1]));
      # orbit count of G acting on A by conjugation
      orbs := OrbitsDomain(G, Elements(A[1]), OnPoints);
      Print("  #conj-orbits on A = ", Length(orbs),
            "  [p^2+p-1 = ", p^2+p-1, "]");
    fi;
    Print("\n");
  od;
  Print("\n");
end;

for p in [5, 7, 11] do
  VerifyP(p);
od;
QUIT;
