# v_task84 -- independent check of v_task41's Lemma CT, Lemma CT-x, Lemma PSN-x,
# Lemma A-2 and Criterion CT.  Nothing is read from v_task41's scripts.
#
# Lemma CT claims: L_2(2^f) has NO proper nontrivial perfect subgroup for every
# ODD PRIME f; likewise L_2(p) for prime p >= 7 with p = +-3 mod 10.
# The audit also checks that f = 2 is NOT claimed (L_2(4) = A_5) and that the
# 5 | 4^f - 1  <=>  2 | f  arithmetic is right.

Print("== arithmetic behind the A_5 exclusion ==\n");
for f in [1..12] do
  Print("  f = ", f, "  5 | 4^f-1 : ", (4^f-1) mod 5 = 0,
        "   5 | |L2(2^f)| = 2^f(4^f-1) : ", (2^f*(4^f-1)) mod 5 = 0,
        "   f even : ", f mod 2 = 0, "\n");
od;

Print("\n== strong census-triviality: proper nontrivial PERFECT subgroups ==\n");
StrongCT := function(G)
  local reps, bad, U;
  reps := RepresentativesPerfectSubgroups(G);
  bad := Filtered(reps, U -> Size(U) > 1 and Size(U) < Size(G));
  return [Length(bad), List(bad, Size)];
end;;

Print("q = 2^f, f odd prime (claimed strongly census-trivial):\n");
for f in [3,5,7] do
  G := PSL(2, 2^f);
  r := StrongCT(G);
  Print("  L2(2^", f, ") order ", Size(G), " : proper nontrivial perfect subgroups = ",
        r[1], " ", r[2], "\n");
od;
Print("control, f = 2 (NOT claimed): ");
G := PSL(2,4);; r := StrongCT(G);;
Print("L2(4) = A5 order ", Size(G), " : ", r[1], " ", r[2], "\n");
Print("control, f = 4 (composite, NOT claimed): ");
G := PSL(2,16);; r := StrongCT(G);;
Print("L2(16) order ", Size(G), " : ", r[1], " ", r[2],
      "  (expect A5's, since 5 | 4^4-1)\n");
Print("control, f = 6: ");
G := PSL(2,64);; r := StrongCT(G);;
Print("L2(64) order ", Size(G), " : ", r[1], " ", r[2], "\n");
Print("control, f = 9 (odd but NOT prime): ");
G := PSL(2,512);; r := StrongCT(G);;
Print("L2(512) order ", Size(G), " : ", r[1], " ", r[2],
      "  (expect L2(8), since 3 | 9)\n");

Print("\nq = p prime, p = +-3 mod 10 (claimed strongly census-trivial):\n");
for p in [7,13,17,23,37,43,47,53] do
  if (p mod 10 = 3) or (p mod 10 = 7) then
    G := PSL(2,p);
    r := StrongCT(G);
    Print("  L2(", p, ") p mod 10 = ", p mod 10, " order ", Size(G),
          " : proper nontrivial perfect = ", r[1], " ", r[2], "\n");
  fi;
od;
Print("controls p = +-1 mod 10 (A5 must appear):\n");
for p in [11,19,29,31,41] do
  G := PSL(2,p); r := StrongCT(G);
  Print("  L2(", p, ") : ", r[1], " ", r[2], "\n");
od;

Print("\n== Lemma PSN-x, Lemma CT-x, Criterion CT ==\n");
# mult_1(G) = number of conjugacy classes of perfect self-normalising subgroups
Mult1 := function(G)
  local reps, cnt, U, cls;
  reps := RepresentativesPerfectSubgroups(G);
  cnt := 0;
  for U in reps do
    if Size(U) > 1 and Size(Normalizer(G,U)) = Size(U) then cnt := cnt + 1; fi;
  od;
  return cnt;
end;;
for nm in [[PSL(2,7),"L2(7)"],[PSL(2,8),"L2(8)"],[PSL(2,11),"L2(11)"],
           [PSL(2,13),"L2(13)"],[PSL(3,3),"L3(3)"]] do
  Print("  mult1(", nm[2], ") = ", Mult1(nm[1]), "\n");
od;
G := DirectProduct(PSL(2,7), PSL(2,13));;
Print("  mult1(L2(7) x L2(13)) = ", Mult1(G), "   (Criterion CT predicts 1)\n");
G := DirectProduct(PSL(2,7), PSL(2,7));;
Print("  mult1(L2(7) x L2(7)) = ", Mult1(G), "   (control: diagonals, expect 3)\n");
G := DirectProduct(PSL(2,7), PSL(2,11));;
Print("  mult1(L2(7) x L2(11)) = ", Mult1(G), "   (control: 1*3 = 3)\n");

Print("\n== Lemma A-2: mult1(A_n) >= 2 for n >= 6 ==\n");
for n in [6,7,8,9,10] do
  Print("  mult1(A", n, ") = ", Mult1(AlternatingGroup(n)),
        "   (A_{n-1} maximal & perfect: ",
        IsPerfectGroup(AlternatingGroup(n-1)), ")\n");
od;
Print("DONE\n");
QUIT;
