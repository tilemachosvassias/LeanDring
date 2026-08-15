# Build Theorem-A fused block B_K per subgroup class; rows=rational fused-Galois
# classes of A_K, cols=fused classes of dual, entry=sum_{w in W_K} lambda(y^w).
FusedBlocks:=function(id)
  local G,cc,i,K,phi,A,elts,irr,No,Wreps,q,Gamma,units,actA,actD,
        wg,fusedA,fusedD,ratRows,rowreps,colreps,B,r,c,y,lam,val,w, py,pw,img,
        allSNF,snf,diag,globalmult,orbA,orbD,isRat,o,gens,n,pcgs;
  G:=SmallGroup(32,id);
  cc:=ConjugacyClassesSubgroups(G);
  allSNF:=[];
  globalmult:=[];
  Print("##### (32,",id,") block SNFs #####\n");
  for i in [1..Length(cc)] do
    K:=Representative(cc[i]);
    phi:=NaturalHomomorphismByNormalSubgroup(K,DerivedSubgroup(K));
    A:=Image(phi);
    elts:=Elements(A);
    irr:=Irr(A);                       # dual A^ (linear chars)
    No:=Normalizer(G,K);
    Wreps:=List(RightCosets(No,K),Representative);   # W_K = N/K reps
    # Gamma = power maps a->a^j, gcd(j,|A|)=1, as permutations of elts index
    q:=Exponent(A);
    units:=Filtered([1..q],j->GcdInt(j,q)=1);
    # action of a single w (group elt of N) on element x of A:
    actWon:=function(x,w) return Image(phi, PreImagesRepresentative(phi,x)^w); end;
    # combined W,Gamma orbit on A
    wg:=function(x) local S,new,z,j,g,y2; S:=[x];
       repeat new:=[];
         for z in S do
           for g in GeneratorsOfGroup(No) do y2:=actWon(z,g); if not y2 in S then Add(new,y2); fi; od;
           for j in units do y2:=z^j; if not y2 in S then Add(new,y2); fi; od;
         od;
         S:=Union(S,new);
       until new=[]; return Set(S); end;
    # W-orbit only
    worb:=function(x) return Set(Orbit(No,x,actWon)); end;
    # fused classes of A
    fusedA:=[]; 
    for y in elts do if not ForAny(fusedA,o->y in o) then Add(fusedA,wg(y)); fi; od;
    # rational rows: fused class that equals a single W-orbit
    rowreps:=[];
    for o in fusedA do if Set(worb(o[1]))=Set(o) then Add(rowreps,o[1]); fi; od;
    # columns: fused classes of dual. Represent chars by their value-vector on elts.
    # action of Gamma,W on chars: lam -> lam' with lam'(x)=lam(x^{w or j-inv}); easier: orbit of char under precomposition
    # Build fused classes of irr by acting on index set via same wg on the group of chars:
    # char c acted by w: newc(x)=c(x^{w^-1}); by gamma j: newc(x)=c(x^{j^-1})
    actCharW:=function(c,w) return List(elts,x->c[Position(elts, Image(phi,PreImagesRepresentative(phi,x)^(w^-1)) )]); end;
    # represent chars as value lists
    charvals:=List(irr,c->List(elts,x->x^0*c[Position(Elements(A),x)]));  # placeholder
    # simpler: fused classes of dual have SAME count as fusedA; and columns are orders too.
    # We instead compute columns as Gamma,W-orbits on irr by acting on the character index.
    # Use: chars c; w-action: c^w (x)=c(x^{w^{-1}}); gamma^j: c(x^{j^{-1}}).
    invunit:=function(j) return (1/j) mod q; end;
    orbchar:=function(cidx) local S,new,z,j,g,cc2,nc,pos; S:=[cidx];
      repeat new:=[];
        for z in S do
          for g in GeneratorsOfGroup(No) do
            nc:=List(elts,x->irr[z][Position(elts, actWon(x, g^-1))]);
            pos:=First([1..Length(irr)],t->List(elts,x->irr[t][Position(elts,x)])=nc);
            if not pos in S then Add(new,pos); fi;
          od;
          for j in units do
            nc:=List(elts,x->irr[z][Position(elts, x^(invunit(j)))]);
            pos:=First([1..Length(irr)],t->List(elts,x->irr[t][Position(elts,x)])=nc);
            if not pos in S then Add(new,pos); fi;
          od;
        od; S:=Union(S,new);
      until new=[]; return Set(S); end;
    fusedD:=[]; 
    for c in [1..Length(irr)] do if not ForAny(fusedD,o->c in o) then Add(fusedD,orbchar(c)); fi; od;
    colreps:=List(fusedD,o->o[1]);
    # Build block matrix
    B:=[];
    for y in rowreps do
      r:=[];
      for c in colreps do
        val:=0;
        for w in Wreps do val:=val + irr[c][Position(elts, actWon(y,w))]; od;
        # val is a rational integer
        Add(r, val);
      od;
      Add(B,r);
    od;
    # integerize
    B:=List(B,row->List(row,x->Int(x)));
    if Length(B)=0 or Length(B[1])=0 then snf:=[]; else
      snf:=DiagonalOfMat(SmithNormalFormIntegerMat(B)); fi;
    snf:=Filtered(snf,x->x<>0);
    Print("K",i," |K|=",Size(K)," A=",AbelianInvariants(A)," rows=",Length(rowreps),
          " cols=",Length(colreps)," SNF=",Collected(snf),"\n");
    Append(globalmult,snf);
  od;
  Print(">>> GLOBAL multiset (32,",id,") = ",Collected(Filtered(globalmult,x->x<>0)),"\n");
end;;
FusedBlocks(13);
FusedBlocks(14);
QUIT;
