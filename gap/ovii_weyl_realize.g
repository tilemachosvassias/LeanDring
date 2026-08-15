# O-vii (docs/r2_abelian.md §5.22): is the Q8-vs-C8 nearfield pair realizable
# as Weyl images N_G(K)/K on a C3^2 fibre with matching shadows?
# Establishes the negative: the two order-72 regular Frobenius carriers already
# differ in their tables of marks (datum (a)), and Lemma 5.22a shows no larger
# ambient group can fuse Q8's three C4-over-K subgroups (K = Fitting is
# characteristic in each Frobenius intermediate, so any fuser lands in N_G(K),
# where the C4's are normal in the Hamiltonian Q8).

# --- The two order-72 regular Frobenius carriers on C3^2 ---
G1 := SmallGroup(72,39);;  # C3^2 : C8  (Singer)
G2 := SmallGroup(72,41);;  # C3^2 : Q8  (Dickson unit group)
Print("Tables of marks (datum (a)):\n");
Print("  (72,39) C8: order profile ", Collected(OrdersTom(TableOfMarks(G1))), "\n");
Print("  (72,41) Q8: order profile ", Collected(OrdersTom(TableOfMarks(G2))), "\n");

# --- Load-bearing facts for Lemma 5.22a / Theorem 5.22 ---
for data in [ [39,"C8"], [41,"Q8"] ] do
  G := SmallGroup(72, data[1]);;
  m36 := Filtered(List(ConjugacyClassesSubgroups(G),Representative), M->Size(M)=36);;
  Print("W=", data[2], ": #G-classes order-36 subgroups = ", Length(m36),
        "; each struct/Fitting = ");
  for M in m36 do
    Print(StructureDescription(M), "/", StructureDescription(FittingSubgroup(M)), " ");
  od;
  Print("\n");
od;
Q := QuaternionGroup(8);; C := CyclicGroup(8);;
Print("Q8 Hamiltonian (all subgroups normal): ",
      ForAll(List(ConjugacyClassesSubgroups(Q),Representative), U->IsNormal(Q,U)),
      "; #subgroup classes Q8=", Length(ConjugacyClassesSubgroups(Q)),
      " C8=", Length(ConjugacyClassesSubgroups(C)),
      "; order-4 classes Q8=3 C8=1.\n");

# --- The natural fusion attempt fails: C3^2:SL(2,3) has no C3^2 with Weyl Q8 ---
G := Image(IsomorphismPermGroup(SemidirectProduct(SL(2,3), GF(3)^2)));;
Print("C3^2:SL(2,3) (order ", Size(G), "): Weyls of its C3^2 subgroups = ");
for K in List(ConjugacyClassesSubgroups(G),Representative) do
  if Size(K)=9 and IsElementaryAbelian(K) then
    Print(StructureDescription(FactorGroup(Normalizer(G,K),K)), " ");
  fi;
od;
Print("(SL(2,3) fuses the C4's but promotes W = Q8 -> SL(2,3) = Q8:C3).\n");
