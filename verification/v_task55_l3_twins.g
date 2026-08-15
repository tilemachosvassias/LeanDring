#############################################################################
##  v_task55_l3_twins.g -- GAP checks for the rank-2 target S = L_3(q)
##
##  A  order formula  |L_3(q)| = q^3(q^2-1)(q^3-1)/gcd(3,q-1)
##  B  the iota witness  A = Z(Syl_p(S)):  A elementary abelian, A' = 1,
##     ind*(A) = [S:N_S(A)] = q^2+q+1   (Borel-Tits, N_S(Z(U_P)) = P)
##  C  EXACT iota over the whole subgroup lattice, and iota_2, where the
##     lattice is in reach (L_3(2), L_3(3))
##  D  minimal degrees from the stored Maxes:  m(L_3(q)) = q^2+q+1
##  E  |Out(L_3(q))| = 2 f gcd(3,q-1)
##  F  the four RAW census configurations of PART 6 of the .py, and their
##     death by the orbit floor;  plus the |A_8| = |L_3(4)| coincidence
##
##  run:  gap -q -o 8g v_task55_l3_twins.g
#############################################################################

Print("=========== PART A : order formula ===========\n");
for q in [2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,32] do
  G := PSL(3,q);
  o := Size(G);
  o2 := q^3*(q^2-1)*(q^3-1)/Gcd(3,q-1);
  Print("  q=",q," |PSL(3,q)|=",o," formula=",o2," ok?",o=o2,"\n");
od;

Print("\n=========== PART B : the iota witness A = O_p(P), P maximal ====\n");
##  NOTE.  A = Z(Syl_p(S)) is the WRONG witness at rank 2: its normaliser is
##  the BOREL, of index (q+1)(q^2+q+1) -- that is the iota_2 value, not iota.
##  The right witness is the unipotent radical A = O_p(P) of a MAXIMAL
##  parabolic P (the stabiliser of a projective point): A is elementary
##  abelian of order q^2, and N_S(A) = P has index q^2+q+1.  Both are
##  printed, so the rank-1-vs-rank-2 difference is visible.
for q in [3,4,5,7,8,9,11,13,16,17,25,27] do
  p := Factors(q)[1];
  G := PSL(3,q);
  P := Stabilizer(G, 1);
  A := PCore(P, p);
  ind := Index(G, Normalizer(G, A)) * Size(DerivedSubgroup(A));
  indB := Index(G, Normalizer(G, Centre(SylowSubgroup(G,p))))
          * Size(DerivedSubgroup(Centre(SylowSubgroup(G,p))));
  Print("  q=",q," |O_p(P)|=",Size(A)," (q^2=",q^2,")",
        " elemab?",IsElementaryAbelian(A),
        " ind*=",ind," q^2+q+1=",q^2+q+1," ok?",ind=q^2+q+1,
        "   | Z(Syl_p): ind*=",indB," (q+1)(q^2+q+1)=",(q+1)*(q^2+q+1),
        " ok?",indB=(q+1)*(q^2+q+1),"\n");
od;

Print("\n=========== PART C : exact iota, iota_2 over ALL subgroups ======\n");
for q in [2,3] do
  G := PSL(3,q);
  cc := ConjugacyClassesSubgroups(G);
  vals := [];
  for s in cc do
    H := Representative(s);
    if Size(H) > 1 then
      Add(vals, Index(G, Normalizer(G,H)) * Size(DerivedSubgroup(H)));
    fi;
  od;
  vals := SSortedList(vals);
  Print("  q=",q," iota=",vals[1]," (q^2+q+1=",q^2+q+1,") iota_2=",vals[2],
        " ratio=",Float(vals[2]/vals[1]),
        " first six of I(S): ",vals{[1..Minimum(6,Length(vals))]},"\n");
od;

Print("\n=========== PART D : minimal degrees from Maxes =================\n");
for q in [2,3,4,5,7,8,9,11] do
  nm := Concatenation("L3(",String(q),")");
  t := CharacterTable(nm);
  if t = fail then Print("  ",nm," : no table\n"); continue; fi;
  if not HasMaxes(t) then Print("  ",nm," : no stored Maxes\n"); continue; fi;
  idx := List(Maxes(t), n -> Size(t)/Size(CharacterTable(n)));
  Sort(idx);
  Print("  ",nm," maximal indices ",idx," -> m = ",idx[1],
        " ; q^2+q+1 = ",q^2+q+1," ok?",idx[1]=q^2+q+1,"\n");
od;

Print("\n=========== PART E : |Out(L_3(q))| ==============================\n");
for q in [2,3,4,5,7,8,9,16,27] do
  p := Factors(q)[1]; f := LogInt(q,p);
  G := PSL(3,q);
  A := AutomorphismGroup(G);
  ou := Size(A)/Size(G);
  claim := 2*f*Gcd(3,q-1);
  Print("  q=",q," |Out|=",ou," 2*f*gcd(3,q-1)=",claim," ok?",ou=claim,"\n");
od;

Print("\n=========== PART F : the four RAW census configurations =========\n");
##  q=4  : A5 x L3(2),   c = 2      q=9   : A6 x L2(27),   c = 12
##  q=16 : L2(16) x Sz(8), c = 12   q=729 : L2(729) x L2(19683), c = 108
##  each is a TWO-orbit configuration, both orbits of length 1, so each
##  factor must satisfy   |Out(S_i)| * iota(S_i)  >=  iota(S) = q^2+q+1.
Print("  |A_8| = ",Factorial(8)/2,"   |L_3(4)| = ",Size(PSL(3,4)),
      "   equal? ", Factorial(8)/2 = Size(PSL(3,4)), "\n");
Print("  q=4  : iota(S)=21   ; |Out(A5)|*iota(A5)   = 2*5   = 10  < 21\n");
Print("  q=9  : iota(S)=91   ; |Out(A6)|*iota(A6)   = 4*10  = 40  < 91\n");
Print("  q=16 : iota(S)=273  ; |Out(L2(16))|*iota   = 4*17  = 68  < 273\n");
Print("  q=729: iota(S)=532171; |Out(L2(729))|*iota = 12*730= 8760 < 532171\n");
##  the exact iota values used above, from GAP:
for nm in [["A5",AlternatingGroup(5)],["A6",AlternatingGroup(6)],
           ["L2(16)",PSL(2,16)],["L2(27)",PSL(2,27)]] do
  G := nm[2];
  cc := ConjugacyClassesSubgroups(G);
  vals := [];
  for s in cc do
    H := Representative(s);
    if Size(H) > 1 then
      Add(vals, Index(G, Normalizer(G,H)) * Size(DerivedSubgroup(H)));
    fi;
  od;
  vals := SSortedList(vals);
  Print("  exact iota(",nm[1],") = ",vals[1],
        "   |Out| = ",Size(AutomorphismGroup(G))/Size(G),"\n");
od;

Print("\n=========== PART G : the near-miss |L_3(25)| = 7*|L_4(5)| =======\n");
Print("  |L3(25)| = ",Size(PSL(3,25)),"   |L4(5)| = ",Size(PSL(4,5)),
      "   ratio = ",Size(PSL(3,25))/Size(PSL(4,5)),"\n");
Print("  |Out(L4(5))| = 8, and 7 does not divide 8  ==>  killed by the\n");
Print("  Fitting-free constraint c | |Out(S_1)|, not by order arithmetic.\n");

Print("\nDONE\n");
QUIT;
