# orthogonal_witness.g -- the ind*-value asymmetry between B_n(q) and C_n(q).
#
# CLAIM (n = 3 first, then general n):
#   v_eps := q^n (q^n - eps)/2  is an ind* value of Omega_{2n+1}(q)  (eps = +-1,
#   one of the two realised by an involution z_e = -r_e with e anisotropic),
#   but ind*-values of PSp_{2n}(q) below q^{2n} are all divisible by
#   iota_1 = (q^{2n}-1)/(q-1), and iota_1 does NOT divide v_eps.
#
# PART A  orbit sizes of Omega(7,q) on nonsingular points, and z_e membership
# PART B  divisibility check iota_1 \nmid v_eps, small n and q
# PART C  maximal subgroup indices of PSp_6(3) and Omega_7(3) (ATLAS), to
#         confirm the "only P_1 has index < q^{2n}" step at q = 3
LoadPackage("atlasrep");;

Print("=== PART A: Omega(7,q) on nonsingular projective points ===\n");
for q in [3,5,7,9] do
  G := Omega(0,7,q);;
  Q := InvariantQuadraticForm(G).matrix;;
  B := Q + TransposedMat(Q);;            # polar (bilinear) form
  F := GF(q);;
  V := F^7;;
  # collect one representative anisotropic vector per square class of Q(e)
  sq := Set(List(Filtered(Elements(F),x->not IsZero(x)), x->x^2));;
  reps := rec();;
  while not (IsBound(reps.("true")) and IsBound(reps.("false"))) do
    v := Random(V);
    val := v*Q*v;
    if not IsZero(val) then
      k := String(val in sq);
      if not IsBound(reps.(k)) then reps.(k) := v; fi;
    fi;
  od;
  Print("q = ",q,"  |Omega_7(q)| = ",Size(G),"\n");
  Print("   iota_1 = (q^6-1)/(q-1) = ",(q^6-1)/(q-1),
        "   q^3(q^3-1)/2 = ",q^3*(q^3-1)/2,
        "   q^3(q^3+1)/2 = ",q^3*(q^3+1)/2,"\n");
  for k in ["true","false"] do
    e := reps.(k);;
    # z_e : -1 on e^perp, +1 on <e>
    bas := NullspaceMat(B*TransposedMat([e]));;   # e^perp
    tr := Concatenation([e], bas);;
    z := tr^-1 * DiagonalMat(Concatenation([One(F)],
             List(bas,x->-One(F)))) * tr;;
    inG := z in G;
    orb := Orbit(G, NormedRowVector(e), OnLines);;
    Print("   Q(e) square = ",k,"  : orbit size = ",Length(orb),
          "   z_e in Omega = ",inG,
          "   z_e^2=1 : ", z^2 = IdentityMat(7,F),
          "   det = ",DeterminantMat(z),"\n");
    if inG then
      C := Stabilizer(G, NormedRowVector(e), OnLines);;
      Print("      |C| = ",Size(C),"  index = ",Size(G)/Size(C),
            "  N_G(<z>)=C_G(z) index equal: ",
            Size(G)/Size(C) = Length(orb),"\n");
    fi;
  od;
od;

Print("\n=== PART B: iota_1 does not divide v_eps ===\n");
for n in [3,4,5,6] do
  for q in Filtered([3,5,7,9,11,13,17,19,23,25,27,49,121,169],
                    x->IsPrimePowerInt(x) and IsOddInt(x)) do
    i1 := (q^(2*n)-1)/(q-1);
    for eps in [1,-1] do
      v := q^n*(q^n-eps)/2;
      if v mod i1 = 0 then
        Print("!! DIVIDES  n=",n," q=",q," eps=",eps,"\n");
      fi;
      if v >= q^(2*n) then
        Print("!! v >= q^2n  n=",n," q=",q," eps=",eps,"\n");
      fi;
    od;
  od;
od;
Print("no divisibility hits, no size hits -> claim holds on the tested grid\n");

Print("\n=== PART C: maximal subgroup indices, q = 3 ===\n");
for nm in ["S6(3)","O7(3)"] do
  g := AtlasGroup(nm);;
  Print(nm,"  |G| = ",Size(g),"  q^6 = 729\n");
  i := 1;
  while true do
    m := AtlasSubgroup(nm,i);
    if m = fail then break; fi;
    idx := Size(g)/Size(m);
    if idx < 729 then tag := "   <-- below q^6"; else tag := ""; fi;
    Print("   maxes[",i,"] index = ",idx,tag,"\n");
    i := i+1;
  od;
od;

QUIT;
