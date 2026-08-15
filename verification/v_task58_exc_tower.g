####################################################################
##  v_task58_exc_tower.g -- GAP controls for the LARGE EXCEPTIONAL
##  tower  F4(q), E6(q), 2E6(q), E7(q), E8(q).
##
##  PART A  orders against the closed formulas
##  PART B  the minimal parabolic indices (= iota upper witnesses)
##          against |S| / (q^{dim U_P} |Levi| (q-1))
##  PART C  minimal degrees from the stored Maxes, where they exist
##          (F4(2), E6(2), 2E6(2)) -- the analogue of the G2(3)/G2(4)
##          exceptional-minimal-degree check
##  PART D  the a/N = 13/6 block: exact rational confirmation of the
##          identities (I1), (I2), (I3) of v_task58 PART 8
##  PART E  the E8 sporadic-floor arithmetic
##  PART F  the E7/E8 ERRATUM of the shared FAM table
####################################################################

Print("\n", RepeatedString("=",70), "\n");
Print("PART A -- orders against the closed formulas\n");
Print(RepeatedString("=",70), "\n");

ordF4  := q -> q^24*(q^12-1)*(q^8-1)*(q^6-1)*(q^2-1);
ordE6  := q -> q^36*(q^12-1)*(q^9-1)*(q^8-1)*(q^6-1)*(q^5-1)*(q^2-1)
               /Gcd(3,q-1);
ord2E6 := q -> q^36*(q^12-1)*(q^9+1)*(q^8-1)*(q^6-1)*(q^5+1)*(q^2-1)
               /Gcd(3,q+1);
ordE7  := q -> q^63*(q^18-1)*(q^14-1)*(q^12-1)*(q^10-1)*(q^8-1)*(q^6-1)
               *(q^2-1)/Gcd(2,q-1);
ordE8  := q -> q^120*(q^30-1)*(q^24-1)*(q^20-1)*(q^18-1)*(q^14-1)
               *(q^12-1)*(q^8-1)*(q^2-1);

CheckOrd := function(nm, f, q)
  local t, s;
  t := CharacterTable(nm);
  if t = fail then
    Print("   ", nm, " : no stored character table (formula value ",
          f(q), ")\n");
    return;
  fi;
  s := Size(t);
  Print("   ", nm, " : |S| = ", s, "   formula ", f(q),
        "   MATCH: ", s = f(q), "\n");
end;

CheckOrd("F4(2)",  ordF4,  2);
CheckOrd("E6(2)",  ordE6,  2);
CheckOrd("2E6(2)", ord2E6, 2);
CheckOrd("E7(2)",  ordE7,  2);
CheckOrd("E8(2)",  ordE8,  2);
CheckOrd("F4(3)",  ordF4,  3);
CheckOrd("E6(3)",  ordE6,  3);

Print("\n   sample formula values (no table needed):\n");
Print("   |F4(3)|  = ", ordF4(3),  "\n");
Print("   |E6(4)|  = ", ordE6(4),  "\n");
Print("   |2E6(3)| = ", ord2E6(3), "\n");
Print("   |E7(3)|  = ", ordE7(3),  "\n");
Print("   |E8(3)|  = ", ordE8(3),  "\n");

Print("\n", RepeatedString("=",70), "\n");
Print("PART B -- minimal parabolic indices = iota upper witnesses\n");
Print(RepeatedString("=",70), "\n");
Print("  deg_q [S:P] = dim U_P.  The minimal maximal parabolic has the\n");
Print("  LARGEST Levi:  F4/P1 (B3, q^15), E6/P1 (D5, q^16, ABELIAN),\n");
Print("  E7/P7 (E6, q^27, ABELIAN), E8/P8 (E7, q^57).\n\n");

univB := function(n,q) local i,r; r := q^(n^2);
  for i in [1..n] do r := r*(q^(2*i)-1); od; return r; end;
univD := function(n,q) local i,r; r := q^(n*(n-1))*(q^n-1);
  for i in [1..n-1] do r := r*(q^(2*i)-1); od; return r; end;
univE6 := q -> q^36*(q^12-1)*(q^9-1)*(q^8-1)*(q^6-1)*(q^5-1)*(q^2-1);
univE7 := q -> q^63*(q^18-1)*(q^14-1)*(q^12-1)*(q^10-1)*(q^8-1)*(q^6-1)
               *(q^2-1);
univE8 := q -> q^120*(q^30-1)*(q^24-1)*(q^20-1)*(q^18-1)*(q^14-1)
               *(q^12-1)*(q^8-1)*(q^2-1);
univF4 := q -> q^24*(q^12-1)*(q^8-1)*(q^6-1)*(q^2-1);

iF4 := q -> (q^12-1)*(q^4+1)/(q-1);
iE6 := q -> (q^9-1)*(q^8+q^4+1)/(q-1);
i2E6:= q -> (q^9+1)*(q^8+q^4+1)/(q+1);
iE7 := q -> (q^14-1)*(q^9+1)*(q^5+1)/(q-1);
iE8 := q -> (q^30-1)*(q^12+1)*(q^10+1)*(q^6+1)/(q-1);

for q in [2,3,4,5,7,8,9,11,13,16] do
  Print("  q = ", q, "\n");
  Print("     F4 : index ", univF4(q)/(q^15*univB(3,q)*(q-1)),
        "   formula ", iF4(q),
        "   MATCH ", univF4(q)/(q^15*univB(3,q)*(q-1)) = iF4(q), "\n");
  Print("     E6 : index ", univE6(q)/(q^16*univD(5,q)*(q-1)),
        "   formula ", iE6(q),
        "   MATCH ", univE6(q)/(q^16*univD(5,q)*(q-1)) = iE6(q), "\n");
  Print("     E7 : index ", univE7(q)/(q^27*univE6(q)*(q-1)),
        "   formula ", iE7(q),
        "   MATCH ", univE7(q)/(q^27*univE6(q)*(q-1)) = iE7(q), "\n");
  Print("     E8 : index ", univE8(q)/(q^57*univE7(q)*(q-1)),
        "   formula ", iE8(q),
        "   MATCH ", univE8(q)/(q^57*univE7(q)*(q-1)) = iE8(q), "\n");
od;

Print("\n", RepeatedString("=",70), "\n");
Print("PART C -- minimal degrees from the stored Maxes\n");
Print(RepeatedString("=",70), "\n");
Print("  (the G2(3)/G2(4) trap of v_task57: a maximal subgroup of index\n");
Print("   SMALLER than the minimal parabolic index.  Checked here for\n");
Print("   every large-exceptional table that carries Maxes.)\n\n");

MinDeg := function(nm)
  local t, m, i;
  t := CharacterTable(nm);
  if t = fail then Print("   ", nm, " : no character table\n"); return; fi;
  if not HasMaxes(t) then
    Print("   ", nm, " : table present, |S| = ", Size(t),
          " , but NO stored Maxes\n");
    return;
  fi;
  m := List(Maxes(t), x -> Size(t)/Size(CharacterTable(x)));
  Sort(m);
  Print("   ", nm, " : ", Length(m), " maximal classes ; smallest indices ",
        m{[1..Minimum(6,Length(m))]}, "\n");
  Print("        minimal permutation degree m(S) = ", m[1], "\n");
end;

MinDeg("F4(2)");
Print("        parabolic index (q^12-1)(q^4+1)/(q-1) at q=2 = ", iF4(2),
      "\n");
MinDeg("E6(2)");
Print("        parabolic index at q=2 = ", iE6(2), "\n");
MinDeg("2E6(2)");
Print("        parabolic index at q=2 = ", i2E6(2), "\n");
MinDeg("E7(2)");
MinDeg("E8(2)");
MinDeg("F4(3)");

Print("\n", RepeatedString("=",70), "\n");
Print("PART D -- the a/N = 13/6 block, exact rationals\n");
Print(RepeatedString("=",70), "\n");
ord2F4 := q -> q^12*(q^6+1)*(q^4-1)*(q^3+1)*(q-1);

Print("  (I3)  |2E6(q)| / |E6(q)|   (matched f1 = f, q1 = q) :\n");
for q in [4,7,13,16,19,25,31,37,43,49,61,64,67,73,79,97,103,109,121,127] do
  if IsPrimePowerInt(q) and q mod 3 = 1 then
    Print("     q = ", q, "  c = ", ord2E6(q)/ordE6(q), " = ",
          Float(ord2E6(q)/ordE6(q)),
          "   integer: ", IsInt(ord2E6(q)/ordE6(q)), "\n");
  fi;
od;
Print("     (and q = 2 mod 3, where the bracket is 1/3 and c < 2):\n");
for q in [2,5,8,11,17,23,29,32] do
  Print("     q = ", q, "  c = ", Float(ord2E6(q)/ordE6(q)), "\n");
od;

Print("\n  (I1)  |E6(m^2)| / |F4(m^3)| :\n");
for m in [2,3,4,5,7,8,9,11,13] do
  Print("     m = ", m, "  c = ", ordE6(m^2)/ordF4(m^3), " = ",
        Float(ordE6(m^2)/ordF4(m^3)), "   < 1 : ",
        ordE6(m^2)/ordF4(m^3) < 1, "\n");
od;

Print("\n  (I2)  |E6(q)| / |2F4(q^3)| , q = 2^f, f odd :\n");
for f in [1,3,5,7,9] do
  Print("     f = ", f, "  c = ", Float(ordE6(2^f)/ord2F4(2^(3*f))),
        "   < 2 : ", ordE6(2^f)/ord2F4(2^(3*f)) < 2, "\n");
od;

Print("\n  (I4)  |2E6(m^2)| / |F4(m^3)| and |2E6(q)|/|2F4(q^3)| :\n");
for m in [2,3,4,5,7] do
  Print("     m = ", m, "  2E6/F4 = ", Float(ord2E6(m^2)/ordF4(m^3)),
        "   < 2 : ", ord2E6(m^2)/ordF4(m^3) < 2, "\n");
od;
for f in [1,3,5,7] do
  Print("     f = ", f, "  2E6/2F4 = ", Float(ord2E6(2^f)/ord2F4(2^(3*f))),
        "   < 2 : ", ord2E6(2^f)/ord2F4(2^(3*f)) < 2, "\n");
od;

Print("\n  (I5)  |F4(q^2)| / |2F4(q)| would need f1 = 2f EVEN, but 2F4\n");
Print("        needs f1 ODD -- no admissible pair exists at all.\n");
Print("        (control, ignoring the field form:  |F4(64)|/|2F4(8)| = ",
      Float(ordF4(64)/ord2F4(8)), " )\n");

Print("\n", RepeatedString("=",70), "\n");
Print("PART E -- the E8 sporadic floor arithmetic\n");
Print(RepeatedString("=",70), "\n");
tM := CharacterTable("M");
if tM <> fail then
  Print("   |M|       = ", Size(tM), "\n");
  Print("   |E8(2)|   = ", ordE8(2), "\n");
  Print("   iota(E8(2)) (parabolic) = ", iE8(2), "\n");
  Print("   |M|^2 / |E8(2)|  = ", Float(Size(tM)^2/ordE8(2)),
        "   (Lemma Q (Q1) needs <= 1) : ", Size(tM)^2 <= ordE8(2), "\n");
  Print("   |M| divides |E8(2)| : ", ordE8(2) mod Size(tM) = 0, "\n");
  Print("   |M| divides |E8(3)| : ", ordE8(3) mod Size(tM) = 0, "\n");
fi;

Print("\n", RepeatedString("=",70), "\n");
Print("PART F -- the E7/E8 erratum in the shared FAM table\n");
Print(RepeatedString("=",70), "\n");
Print("  v_task52 carried iota(E7(q)) = (q^14-1)(q^9+1)(q^5-1)/((q^2-1)(q-1))\n");
Print("  and iota(E8(q)) with an extra (q^2-1)(q^4-1) in the denominator.\n");
Print("  Ratios wrong-value : correct-value --\n");
for q in [2,3,4,5] do
  Print("     q = ", q,
        "   E7 correct/old = ",
        iE7(q)/((q^14-1)*(q^9+1)*(q^5-1)/((q^2-1)*(q-1))),
        "   E8 correct/old = ",
        iE8(q)/((q^30-1)*(q^12+1)*(q^10+1)*(q^6+1)
                /((q-1)*(q^2-1)*(q^4-1))), "\n");
od;
Print("  (the ratios are (q^5+1)(q^2-1)/(q^5-1) and (q^2-1)(q^4-1),\n");
Print("   i.e. mu(E7) = 27 not 25 and mu(E8) = 57 not 51.)\n");

Print("\nDONE\n");
QUIT;
