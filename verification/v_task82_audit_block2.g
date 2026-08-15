#############################################################################
##  v_task82_audit_block2.g -- ADVERSARIAL AUDIT, GAP half
##
##  A  the L_3 iota-witness  O_p(maximal P)  at TWO NEW q (19, 23), not among
##     v_task55's 12 values {3,4,5,7,8,9,11,13,16,17,25,27}; both the correct
##     witness and the Z(Syl_p) trap value are recomputed.
##  B  the unitary iota correction:  iota(U_4(q)) = (q+1)(q^3+1)  [P_2]
##     against the exact CTblLib data, and the U_5 / U_6 formula at every
##     computable point.
##  C  the U_6(2) minimal-degree exception  m = 672 < 693 = [S:P_1].
##  D  Lemma X' (ppmax_{p'} <= 2^{d-1}(q+1)^{d-1}) at d = 25 and neighbours,
##     exactly, from the true factorisation of |S|_{p'}.
##
##  run:  gap -q -o 8g v_task82_audit_block2.g
#############################################################################

Print("=========== PART A : L_3 iota-witness at TWO NEW q ===============\n");
Print("  (v_task55 tested q in {3,4,5,7,8,9,11,13,16,17,25,27}; 19 and 23\n");
Print("   are new.  ind*(A) = [S:N_S(A)] * |A'| .)\n");
for q in [19, 23] do
  p := Factors(q)[1];
  G := PSL(3,q);
  P := Stabilizer(G, 1);                  # a maximal parabolic (point stab)
  A := PCore(P, p);                       # its unipotent radical
  ind := Index(G, Normalizer(G, A)) * Size(DerivedSubgroup(A));
  ZS := Centre(SylowSubgroup(G,p));
  indB := Index(G, Normalizer(G, ZS)) * Size(DerivedSubgroup(ZS));
  Print("  q=",q,"  |S|=",Size(G),"\n");
  Print("     |O_p(P)| = ",Size(A)," (q^2 = ",q^2,")  elem.abelian? ",
        IsElementaryAbelian(A),"   N_S(A)=P? ",Normalizer(G,A)=P,"\n");
  Print("     ind*(O_p(P)) = ",ind,"   q^2+q+1 = ",q^2+q+1,
        "   ok? ",ind = q^2+q+1,"\n");
  Print("     TRAP: ind*(Z(Syl_p)) = ",indB,"   (q+1)(q^2+q+1) = ",
        (q+1)*(q^2+q+1),"   ok? ",indB = (q+1)*(q^2+q+1),"\n");
od;

Print("\n=========== PART B : the unitary iota formulas ==================\n");
Print("  claim (v_task56 Trap 3):  iota(U_4(q)) = (q+1)(q^3+1)  [P_2],\n");
Print("  NOT the P_1 index (q^2+1)(q^3+1);  and for d >= 5\n");
Print("  iota(U_d(q)) = (q^d-(-1)^d)(q^{d-1}-(-1)^{d-1})/(q^2-1)  [P_1].\n\n");
u4 := function(q) return (q+1)*(q^3+1); end;
u4p1 := function(q) return (q^2+1)*(q^3+1); end;
ud := function(d,q) local s; s := (-1)^d;
      return (q^d-s)*(q^(d-1)+s)/(q^2-1); end;
Print("  d=4 : P_2 vs P_1\n");
for q in [2,3,4,5,7,8,9] do
  Print("     q=",q,"  (q+1)(q^3+1) = ",u4(q),
        "   (q^2+1)(q^3+1) = ",u4p1(q),
        "   ratio = ",Float(u4p1(q)/u4(q)),"\n");
od;
Print("\n  general formula evaluated at d=4 gives the P_1 value:\n");
for q in [2,3,4,5] do
  Print("     q=",q," general ",ud(4,q)," = P_1 ",u4p1(q),"? ",
        ud(4,q)=u4p1(q),"\n");
od;
Print("\n  against the CTblLib minimal degrees (= [S:P_min]):\n");
for r in [["U4(2)",4,2],["U4(3)",4,3],["U5(2)",5,2],["U5(4)",5,4],
          ["U6(2)",6,2],["U6(4)",6,4],["U7(2)",7,2],["U8(2)",8,2]] do
  t := CharacterTable(r[1]);
  if t = fail then Print("     ",r[1]," : no table\n"); continue; fi;
  if not HasMaxes(t) then
    if r[2] = 4 then ff := u4(r[3]); else ff := ud(r[2],r[3]); fi;
    Print("     ",r[1]," : no stored Maxes ; formula = ",ff,"\n");
    continue;
  fi;
  idx := List(Maxes(t), n -> Size(t)/Size(CharacterTable(n)));
  Sort(idx);
  f := 0;
  if r[2] = 4 then f := u4(r[3]); else f := ud(r[2],r[3]); fi;
  Print("     ",r[1]," maximal indices (first 5) ",
        idx{[1..Minimum(5,Length(idx))]},"  -> m = ",idx[1],
        " ; formula = ",f,"   equal? ",idx[1]=f,"\n");
od;

Print("\n  EXACT iota over the whole subgroup lattice, where feasible:\n");
for r in [["U4(2)",PSU(4,2)]] do
  G := r[2];
  cc := ConjugacyClassesSubgroups(G);
  vals := [];
  for s in cc do
    H := Representative(s);
    if Size(H) > 1 then
      Add(vals, Index(G, Normalizer(G,H)) * Size(DerivedSubgroup(H)));
    fi;
  od;
  vals := SSortedList(vals);
  Print("     ",r[1],"  I(S) first six: ",vals{[1..Minimum(6,Length(vals))]},
        "   iota = ",vals[1],"   (q+1)(q^3+1) = ",u4(2),"\n");
od;

Print("\n=========== PART C : the U_6(2) minimal-degree exception ========\n");
t := CharacterTable("U6(2)");
if t <> fail and HasMaxes(t) then
  idx := List(Maxes(t), n -> Size(t)/Size(CharacterTable(n)));
  Sort(idx);
  Print("  U6(2) maximal indices ",idx,"\n");
  Print("  m = ",idx[1],"   [S:P_1] = ",ud(6,2),
        "   exception (m < [S:P_1])? ",idx[1] < ud(6,2),"\n");
fi;

Print("\n=========== PART D : Lemma X' at d = 25 (exact) =================\n");
##  ppmax_{p'}(|S|)  =  max over r != p of the exact r-part of |S|.
##  claim (v_task60 Lemma X'):  ppmax_{p'} <= 2^{d-1} (q+1)^{d-1}
##  and at q = 2 the sharper  ppmax_{2'} <= 2^{3d/2-2}.
ordLU := function(X,d,q) local o,i,e;
  o := q^(d*(d-1)/2);
  if X = "L" then
    for i in [2..d] do o := o*(q^i-1); od; e := Gcd(d,q-1);
  else
    for i in [2..d] do o := o*(q^i-(-1)^i); od; e := Gcd(d,q+1);
  fi;
  return o/e;
end;
ppmax := function(o,p) local f, r, best, v, x;
  best := 1;
  f := Collected(Factors(o));
  for x in f do
    if x[1] <> p then best := Maximum(best, x[1]^x[2]); fi;
  od;
  return best;
end;
Print("  X  d   q    ppmax_{p'}(|S|)          2^{d-1}(q+1)^{d-1}      ok?\n");
for r in [["L",25,2],["L",25,3],["L",25,4],["L",25,5],
          ["U",25,2],["U",25,3],["U",24,2],["U",26,2],
          ["L",21,2],["L",21,3],["L",30,2]] do
  XX := r[1]; d := r[2]; q := r[3];
  p := Factors(q)[1];
  o := ordLU(XX,d,q);
  P := ppmax(o,p);
  B := 2^(d-1)*(q+1)^(d-1);
  Print("  ",XX,"  ",d,"  ",q,"   ",P,"   ",B,"   ",P <= B,"\n");
od;
Print("\n  the q = 2 sharpening  ppmax_{2'} <= 2^{3d/2-2}:\n");
for d in [21,23,25,30,40,46] do
  for XX in ["L","U"] do
    o := ordLU(XX,d,2);
    P := ppmax(o,2);
    B := 2^(QuoInt(3*d,2)-2);
    Print("  ",XX,"_",d,"(2)   ppmax_{2'} = ",P,"   2^(3d/2-2) = ",B,
          "   ok? ",P <= B,"\n");
  od;
od;

Print("\nDONE\n");

#############################################################################
##  PART E (added by the audit) : WHY the q = 2 sharpening of Lemma X'
##  fails in the unitary tower.  For r != p, k := ord_r(q), the LTE count
##  is m = #{ i in [2,d] : r | q^i - eps_i }.
##    linear  (eps_i = 1)     : r | q^i - 1  iff  k | i      -> m = |d/k|
##    unitary (eps_i = (-1)^i): at q = 2, r = 3, k = 2 :  3 | 2^i - 1 for
##                              i even AND 3 | 2^i + 1 for i odd, so
##                              m = d - 1, NOT |d/2|.
#############################################################################
Print("\n=========== PART E : the m-count, linear vs unitary at r = 3 ====\n");
for d in [10,21,25,46] do
  mL := 0; mU := 0;
  for i in [2..d] do
    if (2^i-1) mod 3 = 0 then mL := mL + 1; fi;
    if (2^i-(-1)^i) mod 3 = 0 then mU := mU + 1; fi;
  od;
  Print("  d=",d,"  m_L(r=3) = ",mL," (= |d/2| = ",QuoInt(d,2),")",
        "   m_U(r=3) = ",mU," (= d-1 = ",d-1,")\n");
od;
Print("  So 'k >= 2 hence m <= d/2' is a LINEAR-tower count; in the\n");
Print("  unitary tower m = d-1 at r = 3 and the sharpening is false.\n");
Print("\nDONE2\n");
