# Thevenaz groups G(a,b) = (C11 x C11) : C5, z acts by diag(a,b).
# Two non-iso classes: {3,4} and {3,5} (orbit reps under n-power action).
MakeG := function(a,b)
  local N, g, Q, z, alpha, phi;
  N := AbelianGroup(IsPcGroup, [11,11]); g := GeneratorsOfGroup(N);
  Q := CyclicGroup(IsPcGroup, 5); z := GeneratorsOfGroup(Q)[1];
  alpha := GroupHomomorphismByImages(N, N, g, [g[1]^a, g[2]^b]);
  phi := GroupHomomorphismByImages(Q, AutomorphismGroup(N), [z], [alpha]);
  return Image(IsomorphismPermGroup(SemidirectProduct(Q, phi, N)));
end;
G1 := MakeG(3,4);; G2 := MakeG(3,5);;
Print("order G1=",Size(G1)," G2=",Size(G2),"\n");
Print("G1 ~ G2 (isomorphic groups)? ", IsomorphismGroups(G1,G2)<>fail, "\n");
Print("IdGroup G1=",IdGroup(G1)," G2=",IdGroup(G2),"\n");
# export Cayley tables (0-based, one entry per line)
Export := function(G, fn)
  local els, n, i, j, f;
  els := Elements(G); n := Length(els); f := OutputTextFile(fn,false);
  SetPrintFormattingStatus(f,false); AppendTo(f, n, "\n");
  for i in [1..n] do for j in [1..n] do
    AppendTo(f, Position(els, els[i]*els[j])-1, "\n"); od; od;
  CloseStream(f);
end;
Export(G1, "/tmp/thev_34.cay"); Export(G2, "/tmp/thev_35.cay");
Print("exported\n");
QUIT;
