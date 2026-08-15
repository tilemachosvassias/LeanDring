# For each subgroup class K: induced W_K action on A_K=K/K', orbit structure by
# element order, and number of rational fused-Galois classes (W-orbit = whole order class).
Analyze:=function(id)
  local G,cc,i,K,Kd,A,phi,No,gens,imgs,elts,ords,worb,gorb,e,f,orbsW,rat,line,g,aut,pcgsA,imgvec,ordset,o,cls,reps,x;
  G:=SmallGroup(32,id);
  cc:=ConjugacyClassesSubgroups(G);
  Print("##### (32,",id,") #####\n");
  for i in [1..Length(cc)] do
    K:=Representative(cc[i]);
    Kd:=DerivedSubgroup(K);
    phi:=NaturalHomomorphismByNormalSubgroup(K,Kd); # K -> A_K
    A:=Image(phi);
    No:=Normalizer(G,K);
    elts:=Elements(A);
    # W acts on A via conjugation by N_G(K) elements, mod K'
    orbsW:=[]; 
    # build the group of automorphisms of A induced by N_G(K)
    gens:=GeneratorsOfGroup(No);
    # action function: for w in No, x in A(as image), map
    # need preimage in K: A elements are cosets; pick preimage, conjugate, reimage
    # define orbit of x under all of No
    orbsW:=OrbitsDomain(No, elts, function(x,w)
        return Image(phi, PreImagesRepresentative(phi,x)^w); end);
    # order classes (Galois orbits = elements of equal order, since Aut(cyclic factors) transitive? 
    # For a general abelian A, Galois=power maps orbit; approximate order class by (order, ...). 
    # Count rational: W-orbit whose size = size of its "order class". We'll report orbit sizes by order.
    line:=[];
    for e in orbsW do
      o:=Order(Representative(e));
      Add(line,[o,Length(e)]);
    od;
    Sort(line);
    Print("K",i," |K|=",Size(K)," A_K=",AbelianInvariants(A),
          " |W|=",Size(No)/Size(K)," Worbits(order,size)=",line,"\n");
  od;
end;;
Analyze(13);
Analyze(14);
QUIT;
