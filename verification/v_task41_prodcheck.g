# v_task41_prodcheck.g -- Lemma CT-x, checked: mult_1 of direct products of
# (strongly) census-trivial simple groups, plus the two controls.

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

Print("# Lemma CT-x: pairwise non-isomorphic strongly census-trivial factors\n");
Run("L2(7)xL2(13)", DirectProduct(PSL(2,7), PSL(2,13)));
Run("L2(7)xL3(3)",  DirectProduct(PSL(2,7), PSL(3,3)));
Print("# control A: ISOMORPHIC factors -- diagonal expected, so mult1 > 1\n");
Run("L2(7)xL2(7)",  DirectProduct(PSL(2,7), PSL(2,7)));
Print("# control B: one non-census-trivial factor (L2(11) has two psn A5s)\n");
Run("L2(7)xL2(11)", DirectProduct(PSL(2,7), PSL(2,11)));
Print("# three factors\n");
Run("L2(7)xL2(13)xL2(17)", DirectProduct(PSL(2,7), PSL(2,13), PSL(2,17)));
QUIT;
