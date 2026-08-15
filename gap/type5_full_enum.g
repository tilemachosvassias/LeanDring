BlockSNF:=function(A, sig)
  local elemsA,ccl,cmap,irr,chvecs,q,units,permsG,permS,Grp,Wgrp,
        orbsA,ratrows,cols,colreps,B,y,c,val,snf,idx;
  elemsA:=Elements(A); ccl:=ConjugacyClasses(A);
  cmap:=function(g) return First([1..Length(ccl)],k->g in ccl[k]); end;
  irr:=Irr(A); chvecs:=List(irr,ch->List(elemsA,e->ch[cmap(e)]));
  q:=Exponent(A); if q<2 then q:=2; fi;
  units:=Filtered([1..q],j->GcdInt(j,q)=1);
  permsG:=List(units,j->PermListList(elemsA,List(elemsA,x->x^j)));
  permS:=PermListList(elemsA,List(elemsA,x->Image(sig,x)));
  Wgrp:=Group([permS],()); Grp:=Group(Concatenation(permsG,[permS]),());
  orbsA:=Orbits(Grp,[1..Length(elemsA)]);
  ratrows:=Filtered(orbsA,o->IsTransitive(Wgrp,o));
  cols:=[];
  for c in [1..Length(chvecs)] do
    if not ForAny(cols,o->c in o) then
      Add(cols,Set(Orbit(Grp,c,function(cc,p)
        return First([1..Length(chvecs)],t->chvecs[t]=Permuted(chvecs[cc],p^-1));end)));
    fi; od;
  colreps:=List(cols,o->o[1]); B:=[];
  for y in ratrows do val:=[];
    for c in colreps do idx:=y[1];
      Add(val, chvecs[c][idx]+chvecs[c][idx^permS]); od;
    Add(B,List(val,x->Int(x))); od;
  if Length(B)>0 and Length(B[1])>0 then
    snf:=Filtered(DiagonalOfMat(SmithNormalFormIntegerMat(B)),x->x<>0);
  else snf:=[]; fi;
  return [Length(ratrows),Collected(snf)];
end;;
Enum:=function(r)
  local A,gens,t,a,Aut,invs,Phi,c,sig,fix,comm,inPhi,b;
  A:=AbelianGroup([2,2^r]); gens:=GeneratorsOfGroup(A); t:=gens[1]; a:=gens[2];
  Phi:=FrattiniSubgroup(A); Aut:=AutomorphismGroup(A);
  invs:=Filtered(ConjugacyClasses(Aut),c->Order(Representative(c))=2);
  Print("=== r=",r,": ",Length(invs)," involution-classes ===\n");
  for c in invs do sig:=Representative(c);
    fix:=Subgroup(A,Filtered(Elements(A),x->Image(sig,x)=x));
    comm:=Subgroup(A,List(Elements(A),x->Image(sig,x)*x^-1));
    inPhi:=IsSubgroup(Phi,comm); b:=BlockSNF(A,sig);
    Print("  Fix=",AbelianInvariants(fix)," |[s,A]|=",Size(comm),
          " <=Phi:",inPhi," rows=",b[1]," SNF=",b[2],"\n");
  od;
end;;
for r in [2,3,4,6] do Enum(r); od;
QUIT;
