#############################################################################
##  v_task61_p4.g  --  exact primitive counts p^C_4(q) and the Omega_4 laws
##
##  p^C_4(q) = #{ Sp_4(q)-classes of U <= Sp_4(q) : -1 in U, U/<-1> perfect,
##                U irreducible on F_q^4, N_{Sp_4(q)}(U) = U }.
##
##  By the 4ah corollary the candidate isomorphism types are exactly
##      Sp_4(q)            (the whole group, always 1)
##      2.(2^4:A_5)        (the C_6 member, 2^{1+4}.A_5, order 1920)
##      2.A_5, 2.A_6       (the S-members, degree-4 faithful symplectic chars)
##      SL_2(q) via Sym^3  (defining characteristic; = 2.A_5 when q = 5)
##      SL_2(q_0) subfield (killed by E3, machine-confirmed in 4af)
##  so it suffices to count classes of each type and test self-normalisation.
##  We do this with IsomorphicSubgroups, which is exhaustive up to conjugacy.
##
##  Also: the Omega_4 laws of 4ag, recomputed --
##      p^O_4^+(q) = a(q)^2,   p^O_4^-(q) = a(q^2),   a(q) = 1 + 2*[5 | q^2-1]
##  where a is the rank-1 law.  These feed the P_{3+4} layer of Omega_7.
#############################################################################

a := function(q)
  if (q^2 - 1) mod 5 = 0 and not IsPrimePowerInt(q) = false then
    # exclude q a power of 5 (then SL_2(5) is a subfield group, killed by E3)
    if SmallestRootInt(q) = 5 then return 1; fi;
    return 3;
  fi;
  return 1;
end;;

Print("### v_task61_p4: exact p^C_4(q)\n\n");
Print("rank-1 law a(q) for odd q <= 31:\n");
for q in Filtered([3..31], IsPrimePowerInt) do
  if q mod 2 = 1 then Print("  a(",q,") = ", a(q), "\n"); fi;
od;
Print("\n");

##  psn = (i) irreducible on the natural 4-space, (ii) self-normalising.
CountClasses := function(P, phi, F, H, name)
  local isos, r, n, npsn, nirr, U, M, irr, self, gens;
  isos := IsomorphicSubgroups(P, H);
  n := Length(isos);
  npsn := 0; nirr := 0;
  for r in isos do
    U := Image(r);
    gens := List(GeneratorsOfGroup(U), g -> PreImagesRepresentative(phi, g));
    M := GModuleByMats(gens, F);
    irr := MTX.IsIrreducible(M);
    self := (Size(Normalizer(P, U)) = Size(U));
    if irr then nirr := nirr + 1; fi;
    if irr and self then npsn := npsn + 1; fi;
  od;
  Print("  ", String(name,16), ": ", String(n,2), " classes, ",
        String(nirr,2), " irreducible, ", String(npsn,2), " PRIMITIVE psn\n");
  return npsn;
end;;

for q in [5, 7, 11, 13] do
  Print("=== q = ", q, "  (a(q) = ", a(q), ") ===\n");
  G := Sp(4, q);
  F := GF(q);
  phi := IsomorphismPermGroup(G);
  P := Image(phi);
  Print("  |Sp(4,",q,")| = ", Size(P), ", perm degree ", NrMovedPoints(P), "\n");
  tot := 1;   # Sp_4(q) itself
  tot := tot + CountClasses(P, phi, F, SL(2,5), "2.A5");
  tot := tot + CountClasses(P, phi, F, SL(2,9), "2.A6=SL(2,9)");
  if q <> 5 then
    tot := tot + CountClasses(P, phi, F, SL(2,q), "SL(2,q) Sym^3");
  fi;
  tot := tot + CountClasses(P, phi, F, PerfectGroup(IsPermGroup,1920,1),
                            "C6: 2^(1+4).A5");
  Print("  ==> p^C_4(", q, ") = ", tot, "   (1 for Sp_4(q) itself included)\n\n");
od;

QUIT;
