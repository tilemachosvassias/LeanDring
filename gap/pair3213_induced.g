# For each subgroup class: induced \bar W_K <= Aut(A_K); fingerprint = (A_K,
# |\bar W|, iso type of \bar W, and the Aut(A_K)-conjugacy invariant given by
# the sorted multiset of (order, cycle-structure-on-A_K) of \bar W's elements).
ProbeInd:=function(id)
  local G,cc,i,K,phi,A,No,AutA,gens,imgs,g,alpha,elemsA,indW,fp,a,perm,cyc,el;
  G:=SmallGroup(32,id);
  cc:=ConjugacyClassesSubgroups(G);
  Print("##### (32,",id,") induced Wbar in Aut(A_K) #####\n");
  for i in [1..Length(cc)] do
    K:=Representative(cc[i]);
    phi:=NaturalHomomorphismByNormalSubgroup(K,DerivedSubgroup(K));
    A:=Image(phi);
    elemsA:=Elements(A);
    No:=Normalizer(G,K);
    # induced automorphisms of A as permutations of elemsA
    indW:=[];
    for g in GeneratorsOfGroup(No) do
      perm:=PermListList(elemsA, List(elemsA, x->Image(phi,PreImagesRepresentative(phi,x)^g)));
      Add(indW,perm);
    od;
    indW:=Group(indW,());
    # fingerprint: for each element of indW, (order, sorted cycle lengths on elemsA)
    fp:=[];
    for a in Elements(indW) do
      Add(fp,[Order(a), SortedList(List(Orbits(Group(a),[1..Length(elemsA)]),Length))]);
    od;
    Sort(fp);
    Print("K",i," A=",AbelianInvariants(A)," |Wbar|=",Size(indW),
          " iso=",StructureDescription(indW)," fp=",fp,"\n");
  od;
end;;
ProbeInd(13);
ProbeInd(14);
QUIT;
