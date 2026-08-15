H1 := [[1,1],[1,-1]];
H2 := KroneckerProduct(H1, H1);
H3 := KroneckerProduct(H2, H1);
M := NullMat(9, 9);
for i in [1..8] do
  for j in [1..8] do
    M[i][j] := H3[i][j];
  od;
  M[i][9] := 0;
  M[9][i] := 1;
od;
M[1][9] := 1;
M[9][9] := -1;
Print(ElementaryDivisorsMat(M), "\n");
QUIT;
