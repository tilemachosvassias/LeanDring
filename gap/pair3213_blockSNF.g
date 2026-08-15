# Correct fused-block SNF per class. Characters via explicit class lookup.
Blk:=function(id)
  local G,cc,i,K,phi,A,No,elemsA,ccl,cmap,irr,Wreps,q,units,
        permsW,permsG,Grp,Wgrp,orbsA,ratrows,y,orbD,chvecs,cols,colreps,
        B,row,c,val,w,snf,glob,ordy,cvec;
  G:=SmallGroup(32,id); cc:=ConjugacyClassesSubgroups(G); glob:=[];
  Print("### (32,",id,") ###\n");
  for i in [1..Length(cc)] do
    K:=Representative(cc[i]);
    phi:=NaturalHomomorphismByNormalSubgroup(K,DerivedSubgroup(K));
    A:=Image(phi); elemsA:=Elements(A); No:=Normalizer(G,K);
    ccl:=ConjugacyClasses(A);
    cmap:=function(g) return First([1..Length(ccl)],k->g in ccl[k]); end;
    irr:=Irr(A);
    chvecs:=List(irr,ch->List(elemsA,e->ch[cmap(e)]));   # value vectors
    Wreps:=List(RightCosets(No,K),Representative);
    q:=Exponent(A); if q=1 then q:=2; fi;
    units:=Filtered([1..q],j->GcdInt(j,q)=1);
    # permutations on element index set
    permsW:=List(GeneratorsOfGroup(No),g->PermListList(elemsA,
              List(elemsA,x->Image(phi,PreImagesRepresentative(phi,x)^g))));
    permsG:=List(units,j->PermListList(elemsA,List(elemsA,x->x^j)));
    Grp:=Group(Concatenation(permsW,permsG),());
    Wgrp:=Group(Concatenation(permsW,[()]));
    orbsA:=Orbits(Grp,[1..Length(elemsA)]);
    # rational rows: Grp-orbit that is a single Wgrp-orbit
    ratrows:=Filtered(orbsA,o->IsTransitive(Wgrp,o));
    # dual fused classes: orbits of Grp acting on chvecs by index-permutation
    # p acts: newvec[k]=vec[k^(p^-1)]  -> permute positions
    cols:=[]; 
    for c in [1..Length(chvecs)] do
      if not ForAny(cols,o->c in o) then
        Add(cols, Set(Orbit(Grp, c, function(cc3,p)
           return First([1..Length(chvecs)],
             t->chvecs[t]=Permuted(chvecs[cc3],p^-1)); end)));
      fi;
    od;
    colreps:=List(cols,o->o[1]);
    B:=[];
    for y in ratrows do
      row:=[];
      for c in colreps do
        val:=0;
        for w in Wreps do
          val:=val+chvecs[c][First([1..Length(elemsA)],
                    t->elemsA[t]=Image(phi,PreImagesRepresentative(phi,elemsA[y[1]])^w))];
        od;
        Add(row,val);
      od;
      Add(B,row);
    od;
    B:=List(B,r->List(r,x->Int(x)));
    if Length(B)>0 and Length(B[1])>0 then
      snf:=Filtered(DiagonalOfMat(SmithNormalFormIntegerMat(B)),x->x<>0);
    else snf:=[]; fi;
    Print("K",i," A=",AbelianInvariants(A)," rows=",Length(ratrows),
          " cols=",Length(colreps)," SNF=",Collected(snf),"\n");
    Append(glob,snf);
  od;
  Print(">>> (32,",id,") GLOBAL = ",Collected(SortedList(glob)),"\n");
end;;
Blk(13); Blk(14);
QUIT;
