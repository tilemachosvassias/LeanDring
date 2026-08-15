Read("results/D4_mat.g");; d4:=DFMAT;;
Read("results/Q8_mat.g");; q8:=DFMAT;;
Read("results/G32_49_mat.g");; g49:=DFMAT;;
Read("results/G32_50_mat.g");; g50:=DFMAT;;
Tally:=function(name,M)
  local s,diag,c,e,i;
  s:=SmithNormalFormIntegerMat(M);
  diag:=List([1..Length(s)],i->s[i][i]);
  c:=Collected(List(diag,x->x));
  Print(name," size=",Length(M)," #nonzero=",Number(diag,x->x<>0),"\n");
  Print("  divisor:mult -> ",c,"\n");
end;;
Tally("D4",d4);
Tally("Q8",q8);
Tally("G32_49",g49);
Tally("G32_50",g50);
