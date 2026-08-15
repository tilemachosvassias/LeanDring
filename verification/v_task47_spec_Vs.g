# v_task47_spec_Vs.g -- the local spectrum sets V_s of the alternating family.
#
# For 1 <> H <= A_n with support of size s (fixed-point-free on those s points),
#     ind*(H) = [A_n : N_{A_n}(H)] * |H'|  =  C(n,s) * [S_s : N_{S_s}(H)] * |H'|
#              =  C(n,s) * w,     w = s! * |H'| / |N_{S_s}(H)|  in  V_s.
# This script computes V_s exhaustively for s = 3..smax, over ALL H (not only
# abelian ones), and reports min V_s.
#
# It also verifies the formula and the resulting spectrum directly inside
# A_9 and A_10 by an independent exhaustive subgroup-lattice computation.

smax := 9;

Print("### PART A: V_s for s = 3 .. ", smax, "\n");
for s in [3..smax] do
  G := SymmetricGroup(s);
  A := AlternatingGroup(s);
  cc := ConjugacyClassesSubgroups(G);
  V := [];  Vab := [];
  for c in cc do
    H := Representative(c);
    if Size(H) > 1 and IsSubgroup(A, H) then
      # fixed point free on [1..s]?
      if Length(MovedPoints(H)) = s then
        w := Factorial(s) * Size(DerivedSubgroup(H)) / Size(Normalizer(G, H));
        AddSet(V, w);
        if IsAbelian(H) then AddSet(Vab, w); fi;
      fi;
    fi;
  od;
  Print("V_", s, " = ", V, "   min = ", Minimum(V), "\n");
  Print("  V_", s, "^ab = ", Vab, "   min = ", Minimum(Vab), "\n");
od;

Print("\n### PART B: direct exhaustive ind* spectrum of A_n, n = 9,10\n");
for n in [9,10] do
  An := AlternatingGroup(n);
  cc := ConjugacyClassesSubgroups(An);
  I := [];
  for c in cc do
    H := Representative(c);
    if Size(H) > 1 then
      AddSet(I, Size(c) * Size(DerivedSubgroup(H)));
    fi;
  od;
  sorted := I;
  Print("n = ", n, "  #distinct ind* values = ", Length(sorted), "\n");
  Print("  smallest 8 : ", sorted{[1..Minimum(8,Length(sorted))]}, "\n");
  Print("  C(n,3)=", Binomial(n,3), " C(n,4)=", Binomial(n,4),
        " 3C(n,4)=", 3*Binomial(n,4), " 4C(n,4)=", 4*Binomial(n,4),
        " 6C(n,5)=", 6*Binomial(n,5), "\n");
  bad := Filtered(sorted, x -> x > 4*Binomial(n,4) and x < 6*Binomial(n,5));
  Print("  values strictly inside the open gap (4C(n,4), 6C(n,5)) : ", bad, "\n");
od;

QUIT;
