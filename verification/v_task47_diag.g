# v_task47_diag.g -- the diagonal-psn route the task proposed, checked.
#
# Claim D1: for S simple nonabelian, N_{SxS}(Delta_alpha) = Delta_alpha
#           (diagonals are self-normalising in the socle).
# Claim D2: in T = (S x S).2 (swap) the diagonals are NOT psn -- the swap
#           normalises the straight diagonal.  With a third factor present,
#           a diagonal in factors 1,2 is centralised by S_3, hence not psn
#           either; only SUBDIRECT subgroups covering ALL factors can be psn.
# Claim D3: mult_1 of the socle counts Goursat data mod Inn; passing to
#           T = Q.(T/Q) divides that count by |T/Q| on free orbits, so no
#           lower bound on mult_1(T) is obtained -- confirming v_task41.

S := PSL(2,7);
G := DirectProduct(S,S);
e1 := Embedding(G,1); e2 := Embedding(G,2);
# straight diagonal
D := Subgroup(G, List(GeneratorsOfGroup(S), g -> Image(e1,g)*Image(e2,g)));
Print("|S| = ", Size(S), "  |D| = ", Size(D), "\n");
Print("D1: N_{SxS}(Delta) = Delta ?  ", Size(Normalizer(G,D)) = Size(D), "\n");

# twisted diagonals: one per element of Out(S) = C_2
A := AutomorphismGroup(S);
inn := InnerAutomorphismsAutomorphismGroup(A);
Print("|Out(S)| = ", Size(A)/Size(inn), "\n");
reps := List(RightTransversal(A, inn), x -> x);
tw := [];
for al in reps do
  Dl := Subgroup(G, List(GeneratorsOfGroup(S),
                         g -> Image(e1,g)*Image(e2,Image(al,g))));
  Add(tw, [Size(Dl), Size(Normalizer(G,Dl)) = Size(Dl)]);
od;
Print("twisted diagonals (|D|, self-normalising in SxS): ", tw, "\n");

# now T = (S x S).2 with the swap
sw := GroupHomomorphismByImages(G,G,
        Concatenation(List(GeneratorsOfGroup(S), g->Image(e1,g)),
                      List(GeneratorsOfGroup(S), g->Image(e2,g))),
        Concatenation(List(GeneratorsOfGroup(S), g->Image(e2,g)),
                      List(GeneratorsOfGroup(S), g->Image(e1,g))));
T := SemidirectProduct(Group((1,2)), GroupHomomorphismByImages(Group((1,2)),
        AutomorphismGroup(G), [(1,2)], [sw]), G);
eG := Embedding(T,2);
DT := Image(eG, D);
Print("D2: in T = (SxS).2, [N_T(Delta):Delta] = ",
      Size(Normalizer(T, DT))/Size(DT), "  (>1 means Delta is NOT psn)\n");

# mult_1 of S x S and of T
mult1 := function(g)
  local n;
  n := 0;
  for r in RepresentativesPerfectSubgroups(g) do
    if Size(r) > 1 and Size(Normalizer(g,r)) = Size(r) then n := n+1; fi;
  od;
  return n;
end;
Print("mult_1(S x S) = ", mult1(G), "   (1 + |Out(S)| = ", 1+Size(A)/Size(inn),
      " diagonals, plus S x S itself)\n");
Print("mult_1(T)     = ", mult1(T), "\n");

QUIT;
