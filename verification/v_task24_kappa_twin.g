# mindex(G) = min over nontrivial abelian H of [G:N_G(H)];  kappa(G) = |G|/mindex(G).
# (1) A10: minimise over cyclic subgroups + elementary abelian subgroups found in Sylows.
G := AlternatingGroup(10);;
best := infinity;; wit := fail;;
for c in ConjugacyClasses(G) do
  x := Representative(c);
  if Order(x) > 1 then
    H := Group(x);
    i := Index(G, Normalizer(G,H));
    if i < best then best := i; wit := ["cyclic", Order(x)]; fi;
  fi;
od;
Print("A10 min index over CYCLIC subgroups: ", best, " witness ", wit, "\n");
# elementary abelian / abelian subgroups inside Sylow subgroups
for p in [2,3,5,7] do
  P := SylowSubgroup(G, p);
  for H in Filtered(List(ConjugacyClassesSubgroups(P), Representative),
                    h -> Size(h) > 1 and IsAbelian(h)) do
    i := Index(G, Normalizer(G,H));
    if i < best then best := i; wit := ["in Syl", p, Size(H), StructureDescription(H)]; fi;
  od;
od;
Print("A10 mindex (cyclic + abelian-in-Sylow): ", best, " witness ", wit,
      "   [C(10,3) = ", Binomial(10,3), "]\n");
Print("=> kappa(A10) = ", Size(G)/best, "\n\n");
# (2) the tied twin S6 x A7  (socle A6 x A7, c = 2)
S6 := SymmetricGroup(6);; A7 := AlternatingGroup(7);;
T := DirectProduct(S6, A7);;
Print("twin S6 x A7: |T| = ", Size(T), "  (|A10| = ", Size(G), ")\n");
e1 := Embedding(T,1);; e2 := Embedding(T,2);;
A6 := AlternatingGroup(6);;
H1 := Image(e1, SylowSubgroup(A6,3));;          # C3 x C3 inside the A6 factor
H2 := Image(e2, Group((1,2,3)));;               # 3-cycle inside the A7 factor
for pair in [["Syl3(A6) = C3xC3", H1], ["3-cycle in A7", H2]] do
  i := Index(T, Normalizer(T, pair[2]));
  Print("   H = ", pair[1], ": |T:N_T(H)| = ", i,
        "   => kappa(T) >= ", Size(T)/i, "\n");
od;
QUIT;
