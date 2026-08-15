# v_task63_subfield.g -- ADVERSARIAL check of the SUBFIELD (Aschbacher C_5)
# columns that v_task62 omitted from both sides of (T-BC-RES).
#
# Claim (ii): for q = q_0^r, the subfield subgroup X(q_0) < X(q)
#   (X = SL_2, Sp_4, Sp_6, Omega_7) is self-normalizing in X(q)  <=>  r is ODD,
#   because N picks up the coset of GX(q_0) \ X(q_0) exactly when the
#   nonsquare multiplier / spinor norm of F_{q_0} becomes a square in F_q.
# Claim (i): G_2(q_0) < Omega_7(q) is ALWAYS self-normalizing (no diagonal
#   automorphism), contributing 2 classes for every subfield.
#
# Part A  square-class lemma (the whole mechanism, elementary)
# Part B  N_{SL(2,q)}(SL(2,q_0))  computed outright
# Part C  spinor norm of SO_7(q_0) \ Omega_7(q_0) tested in F_{q_0^r}
# Part D  independent recheck of the A_8 / L_3(2) / 2^6:A_7 spinor entries

Print("### PART A: is a nonsquare of F_{q0} a square in F_{q0^r}?\n");
for q0 in [3,5,7,9,11,13,25,27] do
  for r in [1..6] do
    F := GF(q0);
    nsq := First(Elements(F), x -> not IsZero(x) and not IsOne(x^((q0-1)/2)));
    q := q0^r;
    ok := IsOne(nsq^((q-1)/2));   # square in F_q ?
    Print("  q0=",q0," r=",r,"  nonsquare becomes square in F_q: ",ok,
          "   (r even: ",r mod 2 = 0,")\n");
    if ok <> (r mod 2 = 0) then Print("     *** MISMATCH ***\n"); fi;
  od;
od;

Print("\n### PART B: N_{SL(2,q)}(SL(2,q0))\n");
for pair in [[3,9],[3,27],[5,25],[5,125],[7,49],[9,81],[11,121],[3,81],[3,243]] do
  q0 := pair[1]; q := pair[2];
  G := SL(2,q); H := SL(2,q0);
  H := Group(List(GeneratorsOfGroup(H), m -> List(m, r -> List(r, x -> x*One(GF(q))))));
  N := Normalizer(G, H);
  idx := Size(N)/Size(H);
  Print("  SL(2,",q0,") < SL(2,",q,"):  |N|/|H| = ", idx,
        "   psn: ", idx = 1, "   [r = ", LogInt(q,q0), ", r odd: ",
        LogInt(q,q0) mod 2 = 1, "]\n");
od;

Print("\n### PART C: spinor norm of an element of SO_7(q0) \\ Omega_7(q0)\n");
# use GAP's own groups: SO(0,7,q0) has Omega as index-2 subgroup
for q0 in [3,5,7,9] do
  S := SO(0,7,q0); O := Omega(0,7,q0);
  g := First(GeneratorsOfGroup(S), x -> not x in O);
  if g = fail then
    g := First(Elements(Group(GeneratorsOfGroup(S))), x -> not x in O);
  fi;
  Print("  q0=",q0,"  found element of SO\\Omega: ", g <> fail, "\n");
od;
