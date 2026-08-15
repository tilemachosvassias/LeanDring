Read("gap/dring_sieve_standalone.g");
Read("gap/df_trace_corrected_snf.g");

CheckPairs := function()
  local pairs, p, G1, G2, snf1, snf2, id1, id2;
  pairs := [ [13,14], [47,48], [61,66], [77,80], [236,240] ];
  for p in pairs do
    id1 := p[1]; id2 := p[2];
    snf1 := DFTraceCorrectedDivisors(SmallGroup(64, id1));
    snf2 := DFTraceCorrectedDivisors(SmallGroup(64, id2));
    Print("Pair [", id1, ", ", id2, "]:\n");
    if snf1 = snf2 then
      Print("  SURVIVED SNF!\n");
    else
      Print("  SEPARATED BY SNF.\n");
    fi;
  od;
end;

CheckPairs();
QUIT;
