# v_task84 -- part 2 of the Lemma CT audit (part 1 in v_task84_ct.g; the
# L2(512) control there exhausted the workspace and is dropped).
StrongCT := function(G)
  local reps, bad;
  reps := RepresentativesPerfectSubgroups(G);
  bad := Filtered(reps, U -> Size(U) > 1 and Size(U) < Size(G));
  return [Length(bad), List(bad, Size)];
end;;
Mult1 := function(G)
  local reps, cnt, U;
  reps := RepresentativesPerfectSubgroups(G);
  cnt := 0;
  for U in reps do
    if Size(U) > 1 and Size(Normalizer(G,U)) = Size(U) then cnt := cnt + 1; fi;
  od;
  return cnt;
end;;

Print("== L2(p), p prime, p = +-3 mod 10 (claimed strongly census-trivial) ==\n");
for p in [7,13,17,23,37,43,47,53,67,73] do
  G := PSL(2,p); r := StrongCT(G);
  Print("  L2(", p, ")  p mod 10 = ", p mod 10, "  proper nontrivial perfect = ",
        r[1], " ", r[2], "\n");
od;
Print("== controls, p = +-1 mod 10 (A5 must appear) ==\n");
for p in [11,19,29,31,41] do
  G := PSL(2,p); r := StrongCT(G);
  Print("  L2(", p, ") : ", r[1], " ", r[2], "\n");
od;

Print("\n== mult1 and Criterion CT ==\n");
Print("  mult1(L2(7))  = ", Mult1(PSL(2,7)),  "\n");
Print("  mult1(L2(8))  = ", Mult1(PSL(2,8)),  "\n");
Print("  mult1(L2(11)) = ", Mult1(PSL(2,11)), "\n");
Print("  mult1(L2(13)) = ", Mult1(PSL(2,13)), "\n");
Print("  mult1(L2(7) x L2(13)) = ",
      Mult1(DirectProduct(PSL(2,7),PSL(2,13))), "   (Criterion CT predicts 1)\n");
Print("  mult1(L2(7) x L2(7))  = ",
      Mult1(DirectProduct(PSL(2,7),PSL(2,7))),
      "   (control: hypothesis 'pairwise non-isomorphic' is needed)\n");
Print("  mult1(L2(7) x L2(11)) = ",
      Mult1(DirectProduct(PSL(2,7),PSL(2,11))), "   (control: 1*3 = 3)\n");

Print("\n== Lemma A-2: mult1(A_n) >= 2 for n >= 6 ==\n");
for n in [6,7,8,9] do
  Print("  mult1(A", n, ") = ", Mult1(AlternatingGroup(n)),
        "   A_{n-1} perfect: ", IsPerfectGroup(AlternatingGroup(n-1)),
        "   A_{n-1} maximal in A_n: ",
        Size(Normalizer(AlternatingGroup(n), Stabilizer(AlternatingGroup(n), n)))
          = Size(Stabilizer(AlternatingGroup(n), n)), "\n");
od;
Print("DONE\n");
QUIT;
