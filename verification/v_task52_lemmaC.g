# v_task52_lemmaC.g -- GAP cross-check of the inputs of Lemma C
#   (|Out(G)| * iota(G) <= |G|^(2/3))
# on the groups that are TIGHTEST in the exceptional window computed by
# v_task52_lemmaC.py, plus a witness check for the parabolic upper bound.
#
#   ~/gap-4.16.0/gap -q -o 4g v_task52_lemmaC.g > v_task52_lemmaC_g_out.txt

IndStar := function(G, H)
  return Index(G, Normalizer(G, H)) * Size(DerivedSubgroup(H));
end;

# exact iota over ALL conjugacy classes of subgroups
IotaExact := function(G)
  local cc, m, c, H, v;
  cc := ConjugacyClassesSubgroups(G);
  m := Size(G) * Size(G);
  for c in cc do
    H := Representative(c);
    if Size(H) > 1 then
      v := IndStar(G, H);
      if v < m then m := v; fi;
    fi;
  od;
  return m;
end;

OutSize := function(G)
  return Size(AutomorphismGroup(G)) / Size(G);
end;

Report := function(nm, G)
  local i, u, lhs, rhs;
  i := IotaExact(G);
  u := OutSize(G);
  lhs := (u * i) ^ 3;
  rhs := Size(G) ^ 2;
  Print(nm, "  |G|=", Size(G), "  iota=", i, "  |Out|=", u,
        "  (|Out|*iota)^3=", lhs, "  |G|^2=", rhs,
        "  LemmaC: ", lhs <= rhs, "\n");
end;

Print("# PART A -- exact iota and |Out| for the tightest Lemma C rows\n");
Report("A5      ", AlternatingGroup(5));
Report("A6      ", AlternatingGroup(6));
Report("A7      ", AlternatingGroup(7));
Report("L2(4)   ", PSL(2,4));
Report("L2(5)   ", PSL(2,5));
Report("L2(7)   ", PSL(2,7));
Report("L2(8)   ", PSL(2,8));
Report("L2(9)   ", PSL(2,9));
Report("L2(11)  ", PSL(2,11));
Report("L2(13)  ", PSL(2,13));
Report("L3(2)   ", PSL(3,2));
Report("L3(3)   ", PSL(3,3));
Report("L3(4)   ", PSL(3,4));

Print("\n# PART B -- Borel-Tits witness: Z(U_P) abelian, N_G(Z(U_P)) = P,\n");
Print("#           so iota(G) <= [G:P]; checked on the window groups\n");
Print("#           where the full subgroup lattice is out of reach.\n");
CheckWitness := function(nm, G, p, ub)
  local S, Z, N, ind;
  S := SylowSubgroup(G, p);
  Z := Centre(S);
  N := Normalizer(G, Z);
  ind := Index(G, N);
  Print(nm, "  |G|=", Size(G), "  ind*(Z(Syl))=", ind * Size(DerivedSubgroup(Z)),
        "  claimed iota-ub=", ub,
        "  ind* <= ub: ", ind * Size(DerivedSubgroup(Z)) <= ub, "\n");
end;
CheckWitness("U3(3)   ", PSU(3,3),  3, 28);
CheckWitness("S4(3)   ", PSp(4,3),  3, 40);
CheckWitness("Sz(8)   ", SuzukiGroup(8),  2, 65);
CheckWitness("Sz(32)  ", SuzukiGroup(32), 2, 1025);
CheckWitness("U3(5)   ", PSU(3,5),  5, 126);
CheckWitness("U3(8)   ", PSU(3,8),  2, 513);

Print("\n# PART C -- S4(3): the formula value used by the .py is the\n");
Print("#           isotropic-point index (3^4-1)/(3-1) = 40, realised by\n");
Print("#           Z(Syl_3) above.  v_task50's CTblLib row gives the even\n");
Print("#           smaller EXACT iota = 27 (an index-27 maximal 2^4:A5);\n");
Print("#           Lemma C is checked with the larger, conservative 40.\n");
G := PSp(4,3);;
Print("S4(3)   (12*40)^3 = ", (12*40)^3, " <= |G|^2 = ", Size(G)^2, " : ",
      (12*40)^3 <= Size(G)^2, "   [ |Out(S4(3))| = ", Size(AutomorphismGroup(G))/Size(G), " ]\n");
QUIT;
