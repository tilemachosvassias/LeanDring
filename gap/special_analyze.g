Read("gap/dring_sieve_standalone.g");
Wr := function(s) local o; o:=OutputTextFile("/tmp/hunt128_run/analyze.out", true);
  SetPrintFormattingStatus(o,false); WriteLine(o,s); CloseStream(o); end;;

analyze := function(id)
  local G,Z,D,Ph,minZ,r2,ct,q,V,W,natV,natW,imgs,forms,ranks,lam,B,i,j,vs,sq,elts;
  G:=SmallGroup(128,id); Z:=Center(G); D:=DerivedSubgroup(G); Ph:=FrattiniSubgroup(G);
  Wr(Concatenation("=== (128,",String(id),") ==="));
  Wr(Concatenation("  Z=G'=Phi ? Z=G':",String(Z=D)," G'=Phi:",String(D=Ph),
     "  => special 2-group: ", String(Z=D and D=Ph)));
  Wr(Concatenation("  |Z|=",String(Order(Z)),"  minimal subgroups of Z (central involutions): ",
     String(Number(Elements(Z),x->Order(x)=2))));
  # commutator form b: V x V -> W,  V=G/Phi (F2^4), W=Phi=G'=Z (F2^3)
  # For each nonzero functional lam on W, rank of the alternating form lam([.,.]) on V.
  vs := Filtered(Elements(G), x-> not x in Ph);  # coset reps live in V
  # build V-basis from a generating set mod Phi
  V := List(GeneratorsOfGroup(G));   # generators map onto a basis of G/Phi (Burnside basis)
  Wr(Concatenation("  #generators (=rank G/Phi) = ",String(Length(V))));
  # squaring map q(v)=v^2 in W, and commutator [vi,vj] in W
  Wr("  squaring of generators (orders): ");
  Wr(Concatenation("    ", String(List(V,g->[Order(g), Order(g^2)]))));
  # commutator matrix among generators (elements of G'=Z)
  Wr("  commutators [gi,gj] (as Z-elements, nontrivial pairs):");
  for i in [1..Length(V)] do for j in [i+1..Length(V)] do
    if Comm(V[i],V[j])<>One(G) then
      Wr(Concatenation("    [g",String(i),",g",String(j),"] order ",String(Order(Comm(V[i],V[j])))));
    fi;
  od; od;
  # number of squares that are nontrivial (exp-4 structure)
  Wr(Concatenation("  #squares {g^2 : g in G} = ",String(Length(Set(List(Elements(G),x->x^2))))));
  Wr(Concatenation("  x^2 lands in G'? all: ", String(ForAll(Elements(G),x-> x^2 in D))));
end;;
analyze(1597); analyze(1598);
Wr("DONE"); QUIT;
