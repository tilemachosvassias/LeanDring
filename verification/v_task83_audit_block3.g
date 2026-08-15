# v_task83 -- GAP half of the adversarial audit of v_task57/58/59.
# Independent of every earlier script: only ATLAS/CTblLib data + direct
# permutation-group computation.
LoadPackage("ctbllib");;
LoadPackage("atlasrep");;

Print("========== PART A : minimal degrees from stored Maxes ==========\n");
CheckMaxes := function(nm)
  local t, mx, idx;
  t := CharacterTable(nm);
  if t = fail then Print(nm, " : NO character table\n"); return; fi;
  if not HasMaxes(t) then Print(nm, " : table but NO stored Maxes\n"); return; fi;
  mx := Maxes(t);
  idx := List(mx, m -> Size(t)/Size(CharacterTable(m)));
  Sort(idx);
  Print(nm, " |G| = ", Size(t), "  #maxes = ", Length(mx),
        "  smallest indices = ", idx{[1..Minimum(6,Length(idx))]}, "\n");
end;;
for nm in ["S4(3)","U4(2)","S4(4)","S4(5)","G2(3)","G2(4)","3D4(2)","F4(2)",
           "S6(2)","S8(2)","S6(3)","O7(3)","O8+(2)","O8-(2)","U6(2)"] do
  CheckMaxes(nm);
od;

Print("\n========== PART B : iota(S4(3)) over the whole lattice ==========\n");
G := SP(4,3);;  G := G/Centre(G);;
G := Image(IsomorphismPermGroup(G));;
Print("  |PSp(4,3)| = ", Size(G), "\n");
cc := ConjugacyClassesSubgroups(G);;
idx := [];;
for c in cc do
  H := Representative(c);
  if Size(H) > 1 and IsAbelian(H) then
    n := Normalizer(G,H);
    if Size(n) < Size(G) then AddSet(idx, Index(G,n)); fi;
  fi;
od;
Print("  { [S:N_S(A)] : 1 <> A abelian } = ", idx, "\n");
Print("  ==> iota(PSp(4,3)) = ", Minimum(idx), "   (parabolic index (q+1)(q^2+1) = 40)\n");

Print("\n========== PART C : Sp_{2n}(2) minimal degrees, direct ==========\n");
for n in [3,4,5] do
  G := SP(2*n,2);
  Print("  Sp(",2*n,",2) : |G| = ", Size(G),
        "   2^{n-1}(2^n-1) = ", 2^(n-1)*(2^n-1),
        "   2^{2n}-1 = ", 2^(2*n)-1, "\n");
  # the O^-(2n,2) subgroup has index 2^{n-1}(2^n-1)
  H := GO(-1,2*n,2);
  Print("      |GO^-(",2*n,",2)| = ", Size(H),
        "   index in Sp = ", Size(G)/Size(H),
        "   == 2^{n-1}(2^n-1) : ", Size(G)/Size(H) = 2^(n-1)*(2^n-1), "\n");
  H := GO(1,2*n,2);
  Print("      |GO^+(",2*n,",2)| = ", Size(H),
        "   index in Sp = ", Size(G)/Size(H),
        "   == 2^{n-1}(2^n+1) : ", Size(G)/Size(H) = 2^(n-1)*(2^n+1), "\n");
od;

Print("\n========== PART D : the iota witness Z(U_P) at Sp6(3), O7(3) ==========\n");
Witness := function(G, name)
  local S, Z, N;
  S := SylowSubgroup(G, SmallestRootInteger(1));  # placeholder
  return;
end;;
# Sp6(3): P_1 unipotent radical is 3^{1+4}, non-abelian; Z has order 3.
G := SP(6,3);; G := Image(IsomorphismPermGroup(G/Centre(G)));;
Print("  |PSp(6,3)| = ", Size(G), "\n");
P := SylowSubgroup(G,3);;
Print("  |Syl_3| = ", Size(P), "   |Z(Syl_3)| = ", Size(Centre(P)),
      "   [G:N_G(Z(Syl_3))] = ", Index(G, Normalizer(G, Centre(P))), "\n");

Print("\n========== PART E : orders of the four exceptional identities ==========\n");
S4 := function(q) return q^4*(q^2-1)*(q^4-1)/Gcd(2,q-1); end;;
D43 := function(q) return q^12*(q^8+q^4+1)*(q^6-1)*(q^2-1); end;;
G2f := function(q) return q^6*(q^6-1)*(q^2-1); end;;
F42 := function(q) return q^12*(q^6+1)*(q^4-1)*(q^3+1)*(q-1); end;;
for q in [2,3,4,5,7,8,9,11,13] do
  Print("  q=",q,"  |S4(q^3)|/|3D4(q)| = ", S4(q^3)/D43(q),
        "   (q^2+1)/gcd(2,q-1) = ", (q^2+1)/Gcd(2,q-1), "\n");
od;
for q in [2,8,32,128] do
  Print("  q=",q,"  |G2(q^2)|/|2F4(q)| = ", G2f(q^2)/F42(q),
        "   q^2+q+1 = ", q^2+q+1, "\n");
od;
# cross-check against GAP's own group orders where available
Print("  |PSp(4,8)| from GAP = ", Size(SP(4,8))/Gcd(2,7),
      "  formula = ", S4(8), "\n");
Print("  |G2(4)| from table  = ", Size(CharacterTable("G2(4)")),
      "  formula = ", G2f(4), "\n");
Print("  |3D4(2)| from table = ", Size(CharacterTable("3D4(2)")),
      "  formula = ", D43(2), "\n");
Print("  |2F4(2)'| from table= ", Size(CharacterTable("2F4(2)'")),
      "  |2F4(2)| formula/2 = ", F42(2)/2, "\n");
Print("  |F4(2)| from table  = ", Size(CharacterTable("F4(2)")), "\n");

Print("\n========== PART F : E7/E8 index polynomials at small q ==========\n");
E7ord := function(q) return q^63*(q^18-1)*(q^14-1)*(q^12-1)*(q^10-1)*(q^8-1)*(q^6-1)*(q^2-1); end;;
E6ord := function(q) return q^36*(q^12-1)*(q^9-1)*(q^8-1)*(q^6-1)*(q^5-1)*(q^2-1); end;;
E8ord := function(q) return q^120*(q^30-1)*(q^24-1)*(q^20-1)*(q^18-1)*(q^14-1)*(q^12-1)*(q^8-1)*(q^2-1); end;;
for q in [2,3,4,5,7,8,9,11,13,16] do
  Print("  q=",q,
        "  [E7:P7] = ", E7ord(q)/(q^27*E6ord(q)*(q-1)),
        "  == (q^14-1)(q^9+1)(q^5+1)/(q-1) : ",
        E7ord(q)/(q^27*E6ord(q)*(q-1)) = (q^14-1)*(q^9+1)*(q^5+1)/(q-1), "\n");
od;
for q in [2,3,4,5,7,8,9,11,13,16] do
  Print("  q=",q,
        "  [E8:P8] = ", E8ord(q)/(q^57*E7ord(q)*(q-1)),
        "  == (q^30-1)(q^12+1)(q^10+1)(q^6+1)/(q-1) : ",
        E8ord(q)/(q^57*E7ord(q)*(q-1)) = (q^30-1)*(q^12+1)*(q^10+1)*(q^6+1)/(q-1), "\n");
od;
Print("  the OLD (erroneous) values:\n");
for q in [2,3,4] do
  Print("   q=",q," old iota(E7) = ", (q^14-1)*(q^9+1)*(q^5-1)/((q^2-1)*(q-1)),
        "  correct/old = ", ((q^14-1)*(q^9+1)*(q^5+1)/(q-1)) /
                            ((q^14-1)*(q^9+1)*(q^5-1)/((q^2-1)*(q-1))), "\n");
od;

Print("\n========== PART G : Monster vs E8(q) divisibility ==========\n");
M := Size(CharacterTable("M"));;
Print("  |M| = ", M, "\n");
for q in [2,3,4,5] do
  Print("  q=",q,"  |M| divides |E8(q)| ? ", E8ord(q) mod M = 0,
        "   |M|^2/|E8(q)| = ", Float(M^2/E8ord(q)), "\n");
od;
Print("  iota(E8(2)) = ", (2^30-1)*(2^12+1)*(2^10+1)*(2^6+1)/(2-1), "\n");

Print("\n== DONE ==\n");
QUIT;
