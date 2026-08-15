#############################################################################
##  v_task62_sp.g  --  the SYMPLECTIC Rule-S columns p^C_4(q), p^C_6(q),
##  computed by the same module/multiplier method as v_task62_spinor.g.
##
##  For U quasisimple (or perfect with -1 in U) with a faithful absolutely
##  irreducible symplectic F_q-module of dimension d:
##     C_{Sp_d(q)}(U) = Z = <-1>, so N_{Sp}(U)/U  embeds in Stab_Out(chi);
##     Stab_Out = 1                       ->  2 Sp_d(q)-classes, both psn
##     Stab_Out = C_2, multiplier nonsq   ->  1 class, psn
##     Stab_Out = C_2, multiplier square  ->  0
##     |Stab_Out| > 2                     ->  0   (theta/mult is only C_2)
##
##  VALIDATION: must reproduce v_task61's exhaustive IsomorphicSubgroups
##  answers  p^C_4(5) = 3,  p^C_4(7) = 4  (and c_4 = 0: the order-1920 C_6
##  group embeds nowhere at q = 5, 7).
#############################################################################

LogTo("v_task62_sp_out.txt");

FLD := fail;
IsSq := function(x) return IsOne(x^((Size(FLD)-1)/2)); end;

ScalarFactor := function(C, B)
  local i, j, lam;
  lam := fail;
  for i in [1..Length(B)] do for j in [1..Length(B)] do
    if B[i][j] <> Zero(FLD) then lam := C[i][j]/B[i][j]; fi;
  od; od;
  if lam = fail or C <> lam*B then return fail; fi;
  return lam;
end;

SympColumn := function(U, outreps, q, d, name)
  local F, mods, good, m, B, seen, i, j, alpha, iso, T, c, lam, res,
        gens, mm, cnt, orb, stabfound, hom, mats;
  F := GF(q); FLD := F;
  mods := IrreducibleModules(U, F, d);
  gens := mods[1];
  mods := Filtered(mods[2], m -> m.dimension = d);
  mods := Filtered(mods, m -> MTX.IsAbsolutelyIrreducible(m));
  good := [];
  for m in mods do
    hom := GroupHomomorphismByImages(U, Group(m.generators), gens, m.generators);
    if hom = fail or Size(Image(hom)) <> Size(U) then continue; fi;
    B := MTX.InvariantBilinearForm(m);
    if B <> fail and B = -TransposedMat(B) and DeterminantMat(B) <> Zero(F) then
      Add(good, rec(mo := m, form := B, hom := hom));
    fi;
  od;
  if Length(good) = 0 then
    Print(name," q=",q,": ABSENT\n");
    return 0;
  fi;
  seen := []; res := 0;
  for i in [1..Length(good)] do
    if i in seen then continue; fi;
    orb := [i]; stabfound := [];
    for alpha in outreps do
      mats := List(gens, g -> ImagesRepresentative(good[i].hom,
                                ImagesRepresentative(alpha, g)));
      mm := GModuleByMats(mats, F);
      for j in [1..Length(good)] do
        iso := MTX.IsomorphismModules(mm, good[j].mo);
        if iso <> fail then
          if not j in orb then Add(orb, j); fi;
          if j = i then Add(stabfound, iso); fi;
        fi;
      od;
    od;
    UniteSet(seen, orb);
    B := good[i].form;
    if Length(stabfound) = 0 then
      cnt := 2;
      Print(name," q=",q,": orbit ",orb," Stab_Out=1 -> 2 classes\n");
    else
      T := stabfound[1];
      lam := ScalarFactor(T*B*TransposedMat(T), B);
      if lam = fail then Print("  !! not a similitude\n"); fi;
      if IsSq(lam) and Length(stabfound) = 1 then cnt := 0;
      elif Length(stabfound) > 1 then cnt := 0;
      else cnt := 1; fi;
      Print(name," q=",q,": orbit ",orb," |Stab_Out|=",Length(stabfound)+1,
            " mult_square=",IsSq(lam)," -> ",cnt," class(es)\n");
    fi;
    res := res + cnt;
  od;
  return res;
end;

OutReps := function(G)
  local A, I;
  A := AutomorphismGroup(G);
  I := InnerAutomorphismsAutomorphismGroup(A);
  return Filtered(List(RightTransversal(A,I)), a -> not a in I);
end;

Print("=== p^C_4(q) ===\n");
c6grp := Image(IsomorphismPermGroup(PerfectGroup(1920,7)));
for q in [5,7,9,11,13,19,25,29,31] do
  tot := 1;                                  # Sp_4(q) itself
  tot := tot + SympColumn(SL(2,5), OutReps(SL(2,5)), q, 4, "2.A5");
  tot := tot + SympColumn(SL(2,9), OutReps(SL(2,9)), q, 4, "2.A6");
  if not q in [5,9] then
    tot := tot + SympColumn(SL(2,q), OutReps(SL(2,q)), q, 4, "Sym^3 SL(2,q)");
  fi;
  tot := tot + SympColumn(c6grp, OutReps(c6grp), q, 4, "C6 2^(1+4).A5");
  Print("==> p^C_4(",q,") = ", tot, "\n\n");
od;

Print("=== p^C_6(q) ===\n");
for q in [5,7,9,11,13,19,25,29,31] do
  tot := 1;                                  # Sp_6(q) itself
  tot := tot + SympColumn(SL(2,5), OutReps(SL(2,5)), q, 6, "2.A5");
  tot := tot + SympColumn(SL(2,7), OutReps(SL(2,7)), q, 6, "SL(2,7)");
  tot := tot + SympColumn(SL(2,13), OutReps(SL(2,13)), q, 6, "2.L2(13)");
  tot := tot + SympColumn(SU(3,3), OutReps(SU(3,3)), q, 6, "U3(3)");
  Print("  (2.J2 handled separately)\n");
  Print("==> p^C_6(",q,") = ", tot, " + [2.J2 column]\n\n");
od;

LogTo();
QUIT;
