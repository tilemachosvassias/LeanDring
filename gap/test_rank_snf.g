Read("results/G32_48_mat.g");
Print("Dim: ", DimensionsMat(DFMAT), "\n");
Print("Rank: ", RankMat(DFMAT), "\n");
s := ElementaryDivisorsMat(DFMAT);
Print("SNF length: ", Length(s), "\n");
Print("Number of non-zeros: ", Number(s, x -> x <> 0), "\n");
QUIT;
