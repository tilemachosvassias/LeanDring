Pr:=function(id)
  local G,a,b,cc,i,K,W,A,act,gens,imgs,ordK,No,Wq,structW,reps;
  G:=SmallGroup(32,id);
  Print("===== SmallGroup(32,",id,") : ",StructureDescription(G)," =====\n");
  # find a cyclic C8 normal subgroup and generator action
  Print("Derived: ",StructureDescription(DerivedSubgroup(G)),
        "  Centre: ",StructureDescription(Centre(G)),
        "  G/G': ",AbelianInvariants(G/DerivedSubgroup(G)),"\n");
  cc:=ConjugacyClassesSubgroups(G);
  Print("#subgroup classes = ",Length(cc),"\n");
  for i in [1..Length(cc)] do
    K:=Representative(cc[i]);
    ordK:=Size(K);
    No:=Normalizer(G,K);
    A:=AbelianInvariants(K); # A_K = K/K' invariants
    Print(i,": |K|=",ordK," ",StructureDescription(K),
          " |N|=",Size(No)," |W|=",Size(No)/ordK,
          " A_K=K/K'=",AbelianInvariants(FactorGroup(K,DerivedSubgroup(K))),
          " classlen=",Size(cc[i]),"\n");
  od;
end;;
Pr(13);
Pr(14);
QUIT;
