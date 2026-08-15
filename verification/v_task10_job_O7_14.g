Print("=== Job: O7_14 maximal #14 ===\n");
LoadPackage("atlasrep");
G := AtlasGroup("O7(3)");
M := AtlasSubgroup("O7(3)", 14);
if M = fail then
  Print("NO SLP for this index - ABORT\n");
else
  Print("|M| = ", Size(M), "\n");
  R := PerfectResiduum(M);
  Print("|R| = |M perfect residuum| = ", Size(R), "\n");
  Print("M perfect: ", Size(R)=Size(M), "\n");
  if Size(R) = 1 then
    Print("R trivial - no perfect subgroups to search. DONE (no hits possible)\n");
  else
    Print("Computing RepresentativesPerfectSubgroups(R)...\n");
    reps := RepresentativesPerfectSubgroups(R);
    Print("Number of perfect-subgroup classes of R: ", Length(reps), "\n");
    for u in reps do
      s := Size(u);
      if s = 1 then
        Print("  order 1 (trivial) - skip, not self-normalizing\n");
      elif s = Size(M) and Size(R) = Size(M) then
        Print("  order ", s, " = M itself (already counted as maximal class) - skip\n");
      else
        Print("  checking perfect subgroup of order ", s, " ... ");
        N := Normalizer(G, u);
        Print("|N_G(U)| = ", Size(N), "  SELF-NORMALIZING: ", Size(N)=s, "\n");
      fi;
    od;
  fi;
fi;
Print("=== Job done: O7_14 maximal #14 ===\n");
