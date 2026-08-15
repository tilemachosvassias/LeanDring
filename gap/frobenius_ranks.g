ParseTable := function(fname)
  local lines, hdr, n, N, T, i, parts, vals, j, k, c, v, s;
  lines := ReadAsFunction; # dummy
  s := StringFile(fname);
  lines := SplitString(s, "\n");
  hdr := List(SplitString(lines[1], " "), Int);
  n := hdr[1]; N := hdr[2];
  T := [];
  for i in [1..n] do
    parts := List(SplitString(lines[1+i], " "), Int);
    # skip |H|, ord(q): first two entries
    vals := [];
    for j in [1..n] do
      v := 0;
      for k in [1..N] do
        c := parts[2 + (j-1)*N + k];
        if c <> 0 then v := v + c*E(N)^(k-1); fi;
      od;
      Add(vals, v);
    od;
    Add(T, vals);
  od;
  return T;
end;

FrobRanks := function(fname)
  local T, V, n, W, C, j, sol, C2, ranks, k, M;
  T := ParseTable(fname);
  n := Length(T);
  V := TransposedMat(T);       # V[j] = ghost vector of basis element j
  W := List(V, r -> List(r, x -> x^2));   # ghost of b_j^2
  C := [];
  for j in [1..n] do
    sol := SolutionMat(V, W[j]);
    if sol = fail or not ForAll(sol, IsInt) then
      Print("NON-INTEGRAL/FAIL at ", j, "\n"); return fail;
    fi;
    Add(C, sol);
  od;
  C2 := C * Z(2)^0;  # over GF(2)
  ranks := [];
  M := C2;
  for k in [1..4] do
    Add(ranks, RankMat(M));
    M := M * C2;
  od;
  return ranks;
end;

r13 := FrobRanks("results/G64_13.txt");
Print("(64,13) Frobenius ranks k=1..4 on D(G)xF2: ", r13, "\n");
r14 := FrobRanks("results/G64_14.txt");
Print("(64,14) Frobenius ranks k=1..4 on D(G)xF2: ", r14, "\n");
Print("SEPARATED: ", r13 <> r14, "\n");
QUIT;
