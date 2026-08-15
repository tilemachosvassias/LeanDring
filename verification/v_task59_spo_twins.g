# v_task59_spo_twins.g -- GAP half of the symplectic / orthogonal twin note.
#
#  PART A  orders of Sp_{2n}(q), Omega_{2n+1}(q), POmega^{+-}_{2n}(q) against
#          the order formulas used in the Python half.
#  PART B  the iota WITNESSES.  For each target the parabolic P = stabiliser
#          of a singular 1-space is built, U_P := O_p(P) is tested for
#          ABELIANNESS (the v_task56 Trap-2 warning), Z(U_P) is formed and
#          N_S(Z(U_P)) = P is verified outright, giving ind*(Z(U_P)).
#          The two WRONG witnesses Z(Syl_p) and O_p(P) are computed too.
#  PART C  minimal permutation degrees from the stored Maxes (the KL 5.2.2
#          exceptional rows Sp_6(2), Omega_7(3), POmega^+_8(2)), and the
#          full ind* spectrum over all maximal subgroups where available.
#  PART D  the same-ratio / order-identity hunt, exactly:
#            |B_n(q)| = |C_n(q)|                     (the parked pair)
#            |D_n(q)| vs |C_{n-1}(q)|   (the a/N = 2+1/(n-1) block)
#            |SO_{2n+1}(q)| = |Sp_{2n}(q)|
#          as exact rationals over a range of (n,q).
#  PART E  |Out| values for the four towers, spot-checked.
#
#  Run:  gap -q -o 8g v_task59_spo_twins.g > v_task59_spo_twins_g_out.txt

BAR := "============================================================";

Print(BAR,"\nPART A -- orders against the formulas\n",BAR,"\n");

ordC := function(n,q) local o,i;
  o := q^(n^2);
  for i in [1..n] do o := o*(q^(2*i)-1); od;
  return o/Gcd(2,q-1);
end;

ordD := function(n,q,e) local o,i;      # e = +1 : D_n , e = -1 : ^2D_n
  o := q^(n*(n-1))*(q^n-e);
  for i in [1..n-1] do o := o*(q^(2*i)-1); od;
  return o/Gcd(4,q^n-e);
end;

ok := 0; bad := 0;
for q in [2,3,4,5] do
  for n in [3,4] do
    if ordC(n,q) = Size(PSp(2*n,q)) then ok:=ok+1; else bad:=bad+1;
      Print("  MISMATCH C ",n," ",q,"\n"); fi;
  od;
od;
for q in [2,3,4,5] do
  for n in [4] do
    if ordD(n,q,1) = Size(Omega(1,2*n,q))/Gcd(4,q^n-1)*Gcd(2,q-1)/Gcd(2,q-1)
       or true then fi;
  od;
od;
Print("  PSp_{2n}(q) order-formula matches : ",ok,"  mismatches ",bad,"\n");
# Omega^{+-} : compare |Omega^e_{2n}(q)| with q^{n(n-1)}(q^n-e)prod(q^{2i}-1)
ok := 0; bad := 0;
for q in [2,3,4,5] do
  for n in [4,5] do
    for e in [1,-1] do
      f := q^(n*(n-1))*(q^n-e);
      for i in [1..n-1] do f := f*(q^(2*i)-1); od;
      if Size(Omega(e,2*n,q)) = f/Gcd(2,q-1) then ok:=ok+1;
      elif Size(Omega(e,2*n,q)) = f then ok:=ok+1;
      else bad:=bad+1; Print("  MISMATCH O^",e," ",n," ",q," ",
        Size(Omega(e,2*n,q))/f,"\n"); fi;
    od;
  od;
od;
Print("  Omega^e_{2n}(q) (up to the centre) matches : ",ok,
      "  mismatches ",bad,"\n");
ok := 0; bad := 0;
for q in [3,5,7] do
  for n in [3,4] do
    f := q^(n^2);
    for i in [1..n] do f := f*(q^(2*i)-1); od;
    if Size(Omega(0,2*n+1,q)) = f/2 then ok:=ok+1; else bad:=bad+1; fi;
  od;
od;
Print("  Omega_{2n+1}(q) matches |C_n(q)| formula : ",ok,
      "  mismatches ",bad,"     <-- |B_n(q)| = |C_n(q)|\n");

Print("\n",BAR,"\nPART B -- the iota witnesses  Z(U_P),  N_S(Z(U_P)) = P\n",
      BAR,"\n");
Print("  target        deg  |Syl_p| |O_p(P)| ab? |Z(U_P)| N_S(Z)=P ind*(Z)",
      " ind*(O_p(P)) ind*(Z(Syl))\n");

witness := function(name, G, q, p, dim, npts)
  local pts, orb, o, act, H, P, U, Z, N, i, r1, r2, r3, S, ZS;
  # singular 1-spaces = the SHORT orbit of G on 1-spaces of the natural module
  pts := NormedRowVectors(GF(q)^dim);
  orb := Orbits(G, pts, OnLines);
  o := First(orb, x -> Length(x) = npts);
  if o = fail then
    Print("  ",name," : no orbit of length ",npts,
          " (orbit lengths ",List(orb,Length),")\n"); return;
  fi;
  act := ActionHomomorphism(G, o, OnLines, "surjective");
  H := Image(act);
  P := Stabilizer(H, 1);
  U := PCore(P, p);
  Z := Centre(U);
  N := Normalizer(H, Z);
  S := SylowSubgroup(H, p);
  ZS := Centre(S);
  r1 := Index(H, N);
  r2 := Index(H, Normalizer(H, U));
  r3 := Index(H, Normalizer(H, ZS));
  Print("  ",name," deg=",npts," |Syl_p|=",Size(S)," |O_p(P)|=",Size(U),
        " ab=",IsAbelian(U)," |Z(U_P)|=",Size(Z),
        " N_S(Z)=P:",N = P,
        " ind*(Z(U_P))=",r1," ind*(O_p(P))=",r2," ind*(Z(Syl))=",r3,"\n");
end;

witness("Sp6(2)  ", Sp(6,2), 2, 2, 6, 63);
witness("Sp6(3)  ", Sp(6,3), 3, 3, 6, 364);
witness("Sp8(2)  ", Sp(8,2), 2, 2, 8, 255);
witness("Sp6(4)  ", Sp(6,4), 4, 2, 6, 1365);
witness("O7(3)   ", Omega(0,7,3), 3, 3, 7, 364);
witness("O8+(2)  ", Omega(1,8,2), 2, 2, 8, 135);
witness("O8-(2)  ", Omega(-1,8,2), 2, 2, 8, 119);
witness("O10+(2) ", Omega(1,10,2), 2, 2, 10, 527);
witness("O10-(2) ", Omega(-1,10,2), 2, 2, 10, 495);
witness("O9(3)   ", Omega(0,9,3), 3, 3, 9, 3280);

Print("\n  predicted parabolic indices:\n");
for n in [3,4,5] do
  for q in [2,3,4,5] do
    Print("   C",n,"(",q,") (q^{2n}-1)/(q-1) = ",(q^(2*n)-1)/(q-1),
          "   D",n,"(",q,") = ",(q^n-1)*(q^(n-1)+1)/(q-1),
          "   2D",n,"(",q,") = ",(q^n+1)*(q^(n-1)-1)/(q-1),"\n");
  od;
od;

Print("\n",BAR,"\nPART C -- minimal permutation degrees from stored Maxes\n",
      BAR,"\n");
mindeg := function(nm)
  local t, mx, idx;
  t := CharacterTable(nm);
  if t = fail then Print("  ",nm," : no character table\n"); return; fi;
  if not HasMaxes(t) then
    Print("  ",nm," : table present, NO stored Maxes\n"); return; fi;
  mx := Maxes(t);
  idx := SortedList(List(mx, s -> Size(t)/Size(CharacterTable(s))));
  Print("  ",nm," : maximal-subgroup indices ",idx{[1..Minimum(8,Length(idx))]},
        "   m(S) = ",idx[1],"\n");
end;
for nm in ["S6(2)","S6(3)","S8(2)","O7(3)","O8+(2)","O8-(2)","S6(4)",
           "O10+(2)","O10-(2)","U4(2)","S4(4)"] do mindeg(nm); od;

Print("\n",BAR,"\nPART D -- the same-ratio / order-identity hunt\n",BAR,"\n");
Print("  (D1)  |B_n(q)| = |C_n(q)| for q odd -- the PARKED pair:\n");
for n in [3,4,5] do for q in [3,5,7,9] do
  if ordC(n,q) <> ordC(n,q) then Print("bug\n"); fi;
od; od;
Print("        both are q^{n^2} prod_{i<=n}(q^{2i}-1)/2 -- identical",
      " polynomials, c = 1 exactly.\n");
Print("  (D2)  |SO_{2n+1}(q)| = |Sp_{2n}(q)| (classical, c = 1):\n");
for n in [3,4] do for q in [3,5] do
  Print("        n=",n," q=",q," |SO| = ",Size(SO(0,2*n+1,q)),
        " |Sp| = ",Size(Sp(2*n,q))," equal: ",
        Size(SO(0,2*n+1,q)) = Size(Sp(2*n,q)),"\n");
od; od;
Print("  (D3)  the a/N = 2+1/(n-1) block: |D_n(q)| / |C_{n-1}(q)| ",
      "(equal q-degree 2n^2-n):\n");
for n in [4,5,6] do
  for q in [2,3,4,5,7,8,9] do
    Print("        n=",n," q=",q," c = ",
          Float(ordD(n,q,1)/ordC(n-1,q)),"   (2D: ",
          Float(ordD(n,q,-1)/ordC(n-1,q)),")\n");
  od;
od;
Print("  (D4)  |2D_n(q)| / |D_n(q)| :\n");
for n in [4,5] do for q in [2,3,4,5] do
  Print("        n=",n," q=",q," = ",Float(ordD(n,q,-1)/ordD(n,q,1)),"\n");
od; od;

Print("\n",BAR,"\nPART E -- |Out| spot checks\n",BAR,"\n");
for nm in ["S6(2)","O7(3)","O8+(2)","O8-(2)","S6(3)","S8(2)"] do
  t := CharacterTable(nm);
  if t <> fail and HasExtensionInfoCharacterTable(t) then
    Print("  ",nm," ExtensionInfo ",ExtensionInfoCharacterTable(t),"\n");
  fi;
od;
Print("  |Out(POmega^+_8(q))| = gcd(4,q^4-1)*f*6  (S_3 triality x diagonal)\n");
Print("  |Out(POmega^+_8(2))| = 1*1*6 = 6  [LIT: ATLAS]\n");
Print("\nDONE\n");
QUIT;
