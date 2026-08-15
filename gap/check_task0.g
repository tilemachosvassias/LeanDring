Read("gap/dring_sieve_standalone.g");
Read("gap/df_trace_corrected_snf.g");

CheckGroup := function(id)
  local M, snf;
  M := DFTraceCorrectedMatrix(32, id);
  Print("Group 32,", id, "\n");
  Print("Dimensions: ", DimensionsMat(M), "\n");
  Print("Is square: ", DimensionsMat(M)[1] = DimensionsMat(M)[2], "\n");
  Print("Rank: ", RankMat(M), "\n");
  if DimensionsMat(M)[1] = DimensionsMat(M)[2] then
    snf := ElementaryDivisorsMat(M);
    Print("SNF counts: ", Collected(snf), "\n");
  fi;
  Print("\n");
end;

CheckGroup(13);
CheckGroup(14);
QUIT;
