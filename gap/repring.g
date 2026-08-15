Wr := function(s) local o; o:=OutputTextFile("/tmp/hunt128_run/repring.out",true);
  SetPrintFormattingStatus(o,false); WriteLine(o,s); CloseStream(o); end;;
# Compare the character (representation) rings R(1597) vs R(1598) via ring invariants.
Rinv := function(id)
  local G,T,irr,n,i,j,fields,fs,sc,tens,degs;
  G:=SmallGroup(128,id); T:=CharacterTable(G); irr:=Irr(T); n:=Length(irr);
  degs := Collected(List(irr,x->x[1]));
  fields := Collected(List(irr, x-> Conductor(ValuesOfClassFunction(x))));  # 1=rational, 4=Q(i)
  fs := Collected(List(irr, x-> Indicator(T,[x],2)[1]));                        # Frobenius-Schur multiset
  tens := [];
  for i in [1..n] do for j in [i..n] do
    sc := MatScalarProducts(T, irr, [irr[i]*irr[j]]);
    Append(tens, sc[1]);
  od; od;
  return rec(n:=n, degs:=degs, fields:=fields, fs:=fs, tensmult:=Collected(tens));
end;;
a:=Rinv(1597);; b:=Rinv(1598);;
Wr(Concatenation("1597 degs=",String(a.degs),"   1598 degs=",String(b.degs)));
Wr(Concatenation("char-field-degree multiset: 1597=",String(a.fields)," 1598=",String(b.fields)," EQUAL=",String(a.fields=b.fields)));
Wr(Concatenation("Frobenius-Schur multiset:   1597=",String(a.fs)," 1598=",String(b.fs)," EQUAL=",String(a.fs=b.fs)));
Wr(Concatenation("tensor-const multiset EQUAL: ",String(a.tensmult=b.tensmult)));
Wr(Concatenation("  1597 tensmult=",String(a.tensmult)));
Wr(Concatenation("  1598 tensmult=",String(b.tensmult)));
Wr("DONE"); QUIT;
