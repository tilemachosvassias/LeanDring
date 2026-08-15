# v_task41_products.g -- psn census of DIRECT PRODUCTS of census-trivial
# simple groups, and more census-trivial L2(q) with large iota.
#
# Question 1 (item (1) of the task): is mult_1 multiplicative over a socle
#   with pairwise non-isomorphic census-trivial factors?  If yes, such a T
#   has mult_1 = 1, while mult_1(A_n) >= 2 always (A_{n-1} is psn).
# Question 2: do census-trivial simple groups of UNBOUNDED iota exist?
#   (iota(L2(q)) = q+1, so L2(3^f), f odd, would give an infinite family.)

MultOne := function(G)
  local reps, psn;
  reps := RepresentativesPerfectSubgroups(G);
  psn := Filtered(reps, U -> Size(U) > 1 and Size(Normalizer(G,U)) = Size(U));
  return [Length(psn), List(psn, Size)];
end;

Run := function(name, G)
  local r;
  r := MultOne(G);
  Print(name, "  |G|=", Size(G), "  mult1=", r[1], "  psn orders=", r[2], "\n");
end;

Print("# Q2: census-trivial L2(q) at larger q (iota = q+1)\n");
for q in [64,81,121,125,128,169,243,343,361,512,529,625,729] do
  Run(Concatenation("L2(",String(q),")"), PSL(2,q));
od;

Print("# Q1: direct products\n");
Run("L2(7)xL2(13)", DirectProduct(PSL(2,7), PSL(2,13)));
Run("L2(7)xL3(3)",  DirectProduct(PSL(2,7), PSL(3,3)));
Run("L2(13)xL2(17)",DirectProduct(PSL(2,13), PSL(2,17)));
Print("# control: ISOMORPHIC factors (diagonal expected)\n");
Run("L2(7)xL2(7)",  DirectProduct(PSL(2,7), PSL(2,7)));
Print("# control: a non-census-trivial factor\n");
Run("L2(7)xL2(11)", DirectProduct(PSL(2,7), PSL(2,11)));
Print("# three factors\n");
Run("L2(7)xL2(13)xL2(17)", DirectProduct(PSL(2,7), PSL(2,13), PSL(2,17)));

QUIT;
