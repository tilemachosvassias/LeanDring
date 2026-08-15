# p4_sweep_profile.g — ground-truth invariant table for the order-p⁴ species sweep
#
# For every group of order p⁴ (p = 5, 7), print the invariants that a
# SpeciesTableIso preserves, so we can read off which one separates each of the
# five still-uncovered pairs in the Lean sweep:
#   {G9, CH7, Gid3}  (the N_p = p²+p+1, |G^ab| = p³ collision class)
#   {Gid8, Model(xii), Model(xiii)}  (the N_p = p²+p+1, |G^ab| = p² class; twin done)
#
# Columns:
#   id            SmallGroup id (Gid3=3, Gid8=8, twin=9&10 at p=5)
#   |G^ab|        abelianization order
#   Nsub(p,p²,p³) TOTAL number of subgroups of each order
#   Ncc(p,p²,p³)  number of CONJUGACY CLASSES of subgroups of each order (mark-table rows)
#   Ncyc_p2       number of cyclic order-p² subgroups
#   |Z|, class    centre order and nilpotency class
#
# If any of the five pairs tie on ALL of these, the separating invariant is the
# species-table dimension (# G-classes of (H, linear-char) pairs = D-ring rank);
# compute that next with a dedicated char-pair-orbit script.
#
# Run:  gap -q provenance/gap/p4/p4_sweep_profile.g   (or read from a GAP session)

CountSubsOfOrder := function(G, n)
  local subs;
  subs := Filtered(AllSubgroups(G), H -> Size(H) = n);
  return Length(subs);
end;

CountCCSubsOfOrder := function(G, n)
  local ccs;
  ccs := Filtered(ConjugacyClassesSubgroups(G), c -> Size(Representative(c)) = n);
  return Length(ccs);
end;

CountCyclicP2 := function(G, p)
  return Length(Filtered(AllSubgroups(G),
                 H -> Size(H) = p^2 and IsCyclic(H)));
end;

Profile := function(p)
  local n, i, G, ab, ns, nc, ncyc;
  n := p^4;
  Print("=== order ", n, " (p=", p, ") ===\n");
  Print("id  |Gab|  Nsub(p,p2,p3)      Ncc(p,p2,p3)   Ncyc_p2  |Z|  class\n");
  for i in [1 .. NumberSmallGroups(n)] do
    G := SmallGroup(n, i);
    ab := Size(G) / Size(DerivedSubgroup(G));
    ns := [ CountSubsOfOrder(G,p), CountSubsOfOrder(G,p^2), CountSubsOfOrder(G,p^3) ];
    nc := [ CountCCSubsOfOrder(G,p), CountCCSubsOfOrder(G,p^2), CountCCSubsOfOrder(G,p^3) ];
    ncyc := CountCyclicP2(G, p);
    Print(i, "\t", ab, "\t", ns, "\t", nc, "\t", ncyc, "\t",
          Size(Centre(G)), "\t", NilpotencyClassOfGroup(G), "\n");
  od;
  Print("\n");
end;

Profile(5);
Profile(7);
QUIT;
