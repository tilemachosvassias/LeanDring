# g(m) = max |Hol(A)| = m * max |Aut(A)| over ABELIAN A of order m
# (= max |N_Sym(m)(A)| over regular abelian A of degree m)
out := [];
for m in [2..40] do
  best := 0;
  for k in [1..NrPartitions(m)] do ; od;   # placeholder
  for A in AllSmallGroups(m, IsAbelian, true) do
    a := Size(AutomorphismGroup(A));
    if a > best then best := a; fi;
  od;
  Add(out, m*best);
  Print(m, " ", m*best, "\n");
od;
