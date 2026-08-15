G:=MathieuGroup(11);;
cl:=ConjugacyClassesSubgroups(G);;
m:=infinity;;
for c in cl do
  H:=Representative(c);
  if Size(H)>1 and IsAbelian(H) then
    i:=Index(G,Normalizer(G,H));
    if i<m then m:=i; Print("new min ",i," for abelian of order ",Size(H),"\n"); fi;
  fi;
od;
Print("nu(M11)=iota(M11)= ",m,"\n");
