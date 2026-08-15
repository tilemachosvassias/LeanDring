# v_task65 -- ADVERSARIAL AUDIT of Theorem BC-n (v_task64).
# Independent re-derivation, not a re-run of v_task64's script.
#
# PART A  B-side witness: z_e = -r_e built from the reflection formula,
#         det, spinor norm predicted by disc(V)*Q(e), Omega-membership,
#         Centralizer(G,z_e) computed DIRECTLY (v_task64 only computed the
#         point stabiliser and asserted equality), N_G(<z_e>) computed,
#         orbit sizes.
# PART B  maximal subgroup indices of S6(3)/O7(3) from CTblLib (complete
#         ATLAS lists) -- the q=3 anchor.
LoadPackage("ctbllib");;

Print("=== PART A: independent B-side witness ===\n");
for q in [3,5,7,9] do
  G := Omega(0,7,q);;
  F := GF(q);;
  Q := InvariantQuadraticForm(G).matrix;;
  B := Q + TransposedMat(Q);;
  sq := Set(List(Filtered(Elements(F),x->not IsZero(x)), x->x^2));;
  # disc(V) up to squares: det of the polar form B, normalised
  disc := DeterminantMat(B);;
  Print("q = ",q,"  |G| = ",Size(G),"  det(B) = ",disc,
        "  det(B) square? ",disc in sq,"\n");
  reps := rec();;
  while not (IsBound(reps.("true")) and IsBound(reps.("false"))) do
    v := Random(F^7);
    val := v*Q*v;
    if not IsZero(val) then
      k := String(val in sq);
      if not IsBound(reps.(k)) then reps.(k) := v; fi;
    fi;
  od;
  for k in ["true","false"] do
    e := reps.(k);;
    Qe := e*Q*e;;
    # reflection r_e: v |-> v - (B(v,e)/Q(e)) e   (row-vector convention)
    M := IdentityMat(7,F) - (B*TransposedMat([e])*[e])/Qe;;
    okref := ForAll(GeneratorsOfGroup(GL(7,q)), x-> true) and
             ForAll([1..7], i-> ForAll([1..7], j->
               (M[i]*Q*M[j] + M[j]*Q*M[i]) = (B[i][j])*One(F)));  # r_e preserves polar form
    z := -M;;
    # e^perp basis, for the disc(e^perp) spinor prediction
    bas := NullspaceMat(B*TransposedMat([e]));;
    Bp := List(bas, u -> List(bas, w -> u*B*w));;
    predsq := (DeterminantMat(Bp) in sq);   # theta(z_e) = disc(e^perp) mod squares
    orb := Orbit(G, NormedRowVector(e), OnLines);;
    Print("  Q(e) square=",k," Q(e)=",Qe,
          " | det z=",DeterminantMat(z), " z^2=1:",z^2=IdentityMat(7,F),
          " r_e orthogonal:",okref,
          " | disc(e^perp) square (theta prediction):",predsq,
          " | z in Omega:",z in G,
          " | orbit=",Length(orb),"\n");
    if z in G then
      C := Centralizer(G,z);;
      N := Normalizer(G, Group(z));;
      St := Stabilizer(G, NormedRowVector(e), OnLines);;
      Print("      |C_G(z)|=",Size(C)," |N_G(<z>)|=",Size(N),
            " |Stab_G(<e>)|=",Size(St),
            " C=N:",Size(C)=Size(N)," C=Stab:",Size(C)=Size(St),
            " [G:C]=",Size(G)/Size(C),"\n");
    fi;
  od;
  Print("   v_+=",q^3*(q^3-1)/2,"  v_-=",q^3*(q^3+1)/2,
        "  iota1=",(q^6-1)/(q-1),"  q^6=",q^6,"\n");
od;

Print("\n=== PART B: complete ATLAS maximal lists, q=3 anchor ===\n");
for nm in ["S6(3)","O7(3)"] do
  t := CharacterTable(nm);;
  Print(nm," |G|=",Size(t),"\n");
  for m in Maxes(t) do
    idx := Size(t)/Size(CharacterTable(m));
    Print("   ",m," index ",idx);
    if idx < 729 then Print("   <-- below q^6"); fi;
    Print("\n");
  od;
od;
QUIT;
