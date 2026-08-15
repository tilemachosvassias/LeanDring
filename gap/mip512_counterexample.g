# García-Lucas–Margolis–del Río MIP counterexample, k=3,m=3,n=4 -> order 512
mk := function(uy)  # uy = u^y relation exponent (-1 for G, +1 for H)
  local F,x,y,u,rels;
  F := FreeGroup("x","y","u");; x:=F.1;; y:=F.2;; u:=F.3;;
  rels := [ x^16, y^8, u^4,
            y^x*(y*u)^-1,          # y^x = y u
            u^x*(u)^1,             # u^x = u^-1  => u^x * u = 1
            u^y*(u^uy)^-1 ];       # u^y = u^{uy}
  return Image(IsomorphismPcGroup(F/rels));
end;
G := mk(-1);; H := mk(1);;
Print("G: order=",Size(G),"  H: order=",Size(H),"\n");
Print("non-isomorphic: ", IsomorphismGroups(G,H)=fail,"\n");
Print("exponents: exp(G)=",Exponent(G),"  exp(H)=",Exponent(H),"\n");
Print("element-order multiset equal: ",
  Collected(List(Elements(G),Order))=Collected(List(Elements(H),Order)),"\n");
Print("char-power-map TWINS: ",
  TransformingPermutationsCharacterTables(CharacterTable(G),CharacterTable(H))<>fail,"\n");
Print("=> if NOT twins: species table SEPARATES the MIP counterexample (D beats F2 group algebra)\n");
QUIT;
