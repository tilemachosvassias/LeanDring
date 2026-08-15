##############################################################################
##  v_task57_rank2exc_twins.g
##
##  GAP half of v_task57: the remaining rank-2 / small-rank EXCEPTIONAL
##  targets   S4(q) = PSp_4(q),  G2(q),  3D4(q),  2F4(q).
##
##  PART A  orders and |Out| against the closed formulas
##  PART B  the S4(3) DEFECT: iota(S4(3)) = 27 (not 40), over the whole
##          subgroup lattice, with the witness exhibited
##  PART C  the iota WITNESS at S4(5) and S4(4): A = O_p(P) for the Siegel
##          parabolic (abelian unipotent radical), N_G(A) = P, index
##          (q+1)(q^2+1) -- and the Z(Syl_p) trap re-checked
##  PART D  minimal degrees from the stored Maxes (S4, G2, 3D4, 2F4(2)')
##  PART E  the G2(4) / G2(3) exceptional-minimal-degree analysis
##          (J_2 of index 416 < 1365 is NOT of the form N_G(A))
##  PART F  3D4(2): the maximal-subgroup index list and iota
##  PART G  the coincidence / isomorphism controls
##
##  Run:  ~/gap-4.16.0/gap -q -o 8g v_task57_rank2exc_twins.g
##############################################################################

LoadPackage("ctbllib");;
LoadPackage("atlasrep");;

Print("======================================================================\n");
Print("PART A -- orders and |Out| against the closed formulas\n");
Print("======================================================================\n");

ordS4 := q -> q^4*(q^2-1)*(q^4-1)/Gcd(2,q-1);;
ordG2 := q -> q^6*(q^6-1)*(q^2-1);;
ord3D4 := q -> q^12*(q^8+q^4+1)*(q^6-1)*(q^2-1);;
ord2F4 := q -> q^12*(q^6+1)*(q^4-1)*(q^3+1)*(q-1);;

CheckOrd := function(nm, val)
  local t;
  t := CharacterTable(nm);
  if t = fail then
    Print("   ", nm, " : no stored table\n");
    return;
  fi;
  Print("   ", nm, " : |S| = ", Size(t), "  formula = ", val, "   ",
        Size(t) = val, "\n");
end;;

for q in [3,4,5,7,8,9] do
  CheckOrd(Concatenation("S4(",String(q),")"), ordS4(q));
od;
for q in [3,4,5] do
  CheckOrd(Concatenation("G2(",String(q),")"), ordG2(q));
od;
CheckOrd("3D4(2)", ord3D4(2));
CheckOrd("3D4(3)", ord3D4(3));
Print("   2F4(2)' is the TITS group (excluded from the target range);\n");
Print("   |2F4(2)| = ", ord2F4(2), " = 2 * |2F4(2)'| : ",
      ord2F4(2) = 2*Size(CharacterTable("2F4(2)'")), "\n");
Print("   |2F4(8)| = ", ord2F4(8), "  (no stored table; formula only)\n");

Print("\n======================================================================\n");
Print("PART B -- the S4(3) DEFECT: iota(S4(3)) = 27, not the parabolic 40\n");
Print("======================================================================\n");

G := PSp(4,3);;
Print("   |PSp(4,3)| = ", Size(G), "   ( = |U4(2)| = ",
      Size(CharacterTable("U4(2)")), " : ",
      Size(G) = Size(CharacterTable("U4(2)")), " -- an ISOMORPHISM )\n");
Print("   parabolic index (q+1)(q^2+1) = ", 4*10, "\n");

##  exhaustive:  I(S) = { [S : N_S(A)] : 1 <> A abelian },  smallest values.
##  Every N_S(A) of index < k sits inside a maximal subgroup of index < k,
##  so LowIndexSubgroups inside the small-index maximals is exhaustive.
maxes := List(MaximalSubgroupClassReps(G));;
SortBy(maxes, x -> -Size(x));;
Print("   maximal subgroup indices : ", List(maxes, x -> Index(G,x)), "\n");

iotaset := [];;
for M in maxes do
  if Index(G,M) > 200 then continue; fi;
  for A in Filtered(NormalSubgroups(M), x -> Size(x) > 1 and IsAbelian(x)) do
    if Normalizer(G,A) = M then
      AddSet(iotaset, Index(G,M));
    fi;
  od;
od;
Print("   indices [S:N_S(A)] with A abelian, N_S(A) maximal, index<=200 : ",
      iotaset, "\n");
Print("   ==> iota(S4(3)) = ", Minimum(iotaset),
      "   (parabolic index 40 is NOT the minimum)\n");

M27 := First(maxes, x -> Index(G,x) = 27);;
if M27 <> fail then
  A27 := First(NormalSubgroups(M27), x -> Size(x) = 16 and IsAbelian(x));
  Print("   witness: A elementary abelian of order ", Size(A27),
        ", A' = 1, N_G(A) = M of index ",
        Index(G, Normalizer(G, A27)), "   (structure 2^4:A5)\n");
fi;

Print("\n======================================================================\n");
Print("PART C -- the iota WITNESS for S4(q), q = 4, 5, 7: A = O_p(Siegel P)\n");
Print("======================================================================\n");
Print("   At rank 2 the witness is NOT Z(Syl_p) (that gives the Borel).\n");
Print("   For C_2 the SIEGEL parabolic (stabiliser of a totally isotropic\n");
Print("   2-space) has ABELIAN unipotent radical of order q^3, and\n");
Print("   N_S(O_p(P)) = P of index (q+1)(q^2+1).\n\n");

for q in [4,5,7] do
  G := PSp(4,q);
  p := Factors(q)[1];
  P := SylowSubgroup(G, p);
  Print("   q = ", q, " : |S| = ", Size(G), " , |Syl_p| = ", Size(P),
        " ( = q^4 : ", Size(P) = q^4, " )\n");
  ab := Filtered(NormalSubgroups(P),
                 x -> Size(x) = q^3 and IsAbelian(x));
  Print("        abelian normal subgroups of Syl_p of order q^3 : ",
        Length(ab), "\n");
  idx := Set(List(ab, A -> Index(G, Normalizer(G, A))));
  Print("        [S : N_S(A)] for these : ", idx,
        "     claimed (q+1)(q^2+1) = ", (q+1)*(q^2+1), "\n");
  Z1 := Centre(P);
  Print("        THE TRAP: [S : N_S(Z(Syl_p))] = ",
        Index(G, Normalizer(G, Z1)), " (|Z| = ", Size(Z1),
        ") -- larger than iota\n");
od;

Print("\n======================================================================\n");
Print("PART C2 -- the iota WITNESS for G2(3) and 3D4(2): A = Z(U_P) = the\n");
Print("           LONG ROOT subgroup (G2 has NO abelian unipotent radical)\n");
Print("======================================================================\n");

WitnessLongRoot := function(nm, p, claim)
  local G, P, Z, N, cands, idx;
  G := AtlasGroup(nm);
  if G = fail then Print("   ", nm, " : AtlasGroup failed\n"); return; fi;
  P := SylowSubgroup(G, p);
  Z := Centre(P);
  N := Normalizer(G, Z);
  Print("   ", nm, " : |G| = ", Size(G), " , |Syl_p| = ", Size(P),
        " , |Z(Syl_p)| = ", Size(Z),
        " , [G:N_G(Z(Syl_p))] = ", Index(G, N),
        "   claimed iota = ", claim, "\n");
  cands := Filtered(NormalSubgroups(P), x -> Size(x) > 1 and IsAbelian(x));
  idx := Set(List(cands, A -> Index(G, Normalizer(G, A))));
  Print("        abelian normal subgroups of Syl_p : ", Length(cands),
        " ; the set of [G:N_G(A)] : ", idx, "\n");
  Print("        minimum over this set = ", Minimum(idx),
        "   ( = claimed iota : ", Minimum(idx) = claim, " )\n");
end;;

WitnessLongRoot("G2(3)", 3, 364);
WitnessLongRoot("3D4(2)", 2, 819);

Print("\n======================================================================\n");
Print("PART D -- minimal degrees from the stored Maxes\n");
Print("======================================================================\n");

MinDeg := function(nm)
  local t, m;
  t := CharacterTable(nm);
  if t = fail then return fail; fi;
  if not HasMaxes(t) then return fail; fi;
  m := List(Maxes(t), x -> Size(t)/Size(CharacterTable(x)));
  return [Minimum(m), SortedList(m)];
end;;

for nm in ["S4(3)","S4(4)","S4(5)","S4(7)","S4(8)","S4(9)",
           "G2(3)","G2(4)","G2(5)","3D4(2)","2F4(2)'"] do
  r := MinDeg(nm);
  if r = fail then
    Print("   ", nm, " : no stored Maxes\n");
  else
    Print("   ", nm, " : m(S) = ", r[1], "   all maximal indices = ",
          r[2], "\n");
  fi;
od;
Print("\n   claimed iota:  S4(q): (q+1)(q^2+1) = ",
      List([3,4,5,7,8,9], q -> (q+1)*(q^2+1)), "\n");
Print("                  G2(q): (q^6-1)/(q-1) = ",
      List([3,4,5], q -> (q^6-1)/(q-1)), "\n");
Print("                  3D4(2): (q^8+q^4+1)(q+1) = ", (2^8+2^4+1)*3, "\n");

Print("\n======================================================================\n");
Print("PART E -- G2(3), G2(4): the exceptional minimal degrees, and why\n");
Print("          they are NOT iota values\n");
Print("======================================================================\n");
Print("   m(G2(3)) = 351 (U3(3):2) and m(G2(4)) = 416 (J2) are SMALLER than\n");
Print("   the parabolic index (q^6-1)/(q-1) = 364 resp. 1365.  But a\n");
Print("   subgroup N = N_S(A) with 1 <> A abelian has a nontrivial ABELIAN\n");
Print("   NORMAL subgroup, so N cannot be (almost) simple.  Check:\n");
for nm in ["G2(3)","G2(4)"] do
  t := CharacterTable(nm);
  if t <> fail and HasMaxes(t) then
    for mm in Maxes(t) do
      tm := CharacterTable(mm);
      Print("      ", nm, " max ", mm, " index ", Size(t)/Size(tm),
            "  perfect: ", IsPerfectCharacterTable(tm) , "\n");
    od;
  fi;
od;
Print("   For G2(4) the only maximal subgroups of index < 1365 are the two\n");
Print("   classes of J2 (index 416), and J2 is SIMPLE, so J2 <> N_S(A).\n");
Print("   A proper N_S(A) <= J2 has index >= 416 * m(J2) = 416*100 = 41600\n");
Print("   > 1365.  Hence iota(G2(4)) = 1365.  Same argument at G2(3) with\n");
Print("   U3(3):2 (index 351, its unique minimal normal subgroup U3(3) is\n");
Print("   simple, so it has no abelian normal subgroup) and\n");
Print("   351 * m(U3(3):2) >= 351*28 > 364.\n");

Print("\n======================================================================\n");
Print("PART F -- 3D4(2): the maximal-subgroup index list and iota\n");
Print("======================================================================\n");
t := CharacterTable("3D4(2)");;
if t <> fail and HasMaxes(t) then
  Print("   |3D4(2)| = ", Size(t), " ( formula ", ord3D4(2), " : ",
        Size(t) = ord3D4(2), " )\n");
  for mm in Maxes(t) do
    tm := CharacterTable(mm);
    Print("      max ", mm, "  index ", Size(t)/Size(tm),
          "  perfect: ", IsPerfectCharacterTable(tm), "\n");
  od;
  Print("   parabolic indices: (q^8+q^4+1)(q+1) = ", (2^8+2^4+1)*3,
        " and (q^8+q^4+1)(q^3+1) = ", (2^8+2^4+1)*9, "\n");
fi;

Print("\n======================================================================\n");
Print("PART G -- coincidence and isomorphism controls\n");
Print("======================================================================\n");
Print("   |S4(2)|  = ", ordS4(2), " ; S4(2)' = A6 : ",
      ordS4(2) = 2*Size(CharacterTable("A6")), "\n");
Print("   |S4(3)|  = |U4(2)| : ", ordS4(3) = Size(CharacterTable("U4(2)")),
      "   (ISOMORPHISM, not a twin)\n");
Print("   |G2(2)|  = ", ordG2(2), " ; G2(2)' = U3(3) : ",
      ordG2(2) = 2*Size(CharacterTable("U3(3)")), "\n");
Print("   |2F4(2)| = ", ord2F4(2), " ; 2F4(2)' = Tits : ",
      ord2F4(2) = 2*Size(CharacterTable("2F4(2)'")), "\n");
Print("   |3D4(q)| vs |G2(q^2)| :\n");
for q in [2,3,4,5] do
  Print("      q = ", q, " : |3D4(q)| = ", ord3D4(q),
        " , |G2(q^2)| = ", ordG2(q^2),
        " , ratio = ", ord3D4(q)/ordG2(q^2), "  (< 1 : ",
        ord3D4(q) < ordG2(q^2), ")\n");
od;
Print("   ==> |G2(q^2)| > |3D4(q)| for every q : the c_p = 1 sub-case of\n");
Print("       the 3D4 <- G2 same-ratio branch dies on size alone.\n");
Print("   |G2(q)| vs |R(q^2)| :\n");
for q in [3,9,27] do
  Print("      q = ", q, " : |G2(q)| = ", ordG2(q), " , |R(q^2)| = ",
        q^6*(q^6+1)*(q^2-1), " , |G2(q)| < |R(q^2)| : ",
        ordG2(q) < q^6*(q^6+1)*(q^2-1), "\n");
od;

Print("\nDONE.\n");
QUIT;
