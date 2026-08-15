# For A_K = C2 x C_{2^r} classes: describe induced involution on generators
# and its fixed/[sigma,A] data (Aut(A)-conjugacy fingerprint).
T5:=function(id)
  local G,cc,i,K,phi,A,No,gens,inv,g,perm,elemsA,pcgs,imgs,fixsub,commimg,s,a;
  G:=SmallGroup(32,id); cc:=ConjugacyClassesSubgroups(G);
  Print("### (32,",id,") type-5 blocks ###\n");
  for i in [1..Length(cc)] do
    K:=Representative(cc[i]);
    phi:=NaturalHomomorphismByNormalSubgroup(K,DerivedSubgroup(K));
    A:=Image(phi); 
    if not AbelianInvariants(A) in [[2,4],[2,8],[2,2]] then continue; fi;
    No:=Normalizer(G,K); elemsA:=Elements(A);
    # induced automorphisms
    for g in GeneratorsOfGroup(No) do
      s:=GroupHomomorphismByImagesNC(A,A,elemsA,
           List(elemsA,x->Image(phi,PreImagesRepresentative(phi,x)^g)));
      if Order(s)=2 then
        fixsub:=Filtered(elemsA,x->x^s=x);
        commimg:=Set(List(elemsA,x->x^s*x^-1));
        Print("K",i," A=",AbelianInvariants(A),
              " |Fix|=",Length(fixsub)," Fixinv=",AbelianInvariants(Subgroup(A,fixsub)),
              " |[s,A]|=",Length(commimg),"\n");
        break;
      fi;
    od;
  od;
end;;
T5(13); T5(14);
QUIT;
