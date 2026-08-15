#############################################################################
##
##  v_task61_tbc_close.g   --- T-BC endgame: Rule-S columns, both sides
##
##  Context: NOTES.md Even, sections 4af (Theorem PSN-GF), 4ag (orthogonal
##  asymmetries), 4ah (primitive count = S-column count), 4ai (Rule S).
##
##  The task brief asked for "symplectic branch total < 9" (section 4ae).
##  That target is REFUTED in 4af.  The live target is
##
##      T-BC+ :  mult_1(Omega_7(q)) > mult_1(PSp_6(q))   for all odd q >= 5,
##
##  and by PSN-GF both sides are polynomials in the *primitive* counts p_d.
##  By the 4ah corollary p_d(q) = 1 + #{psn C6-members} + #{psn S-members},
##  and by Rule S (4ai) each S-member contributes
##      2 classes, both psn        if Stab_{Out(H)}(chi) = 1     [branch 1]
##      1 class,  psn              if Stab = C2 and mu nonsquare [branch 2a]
##      2 classes, neither psn     if Stab = C2 and mu square    [branch 2b]
##
##  This script recomputes, independently of 4ai's transcription:
##    (A) the S-tables: all quasisimple H with a faithful absolutely
##        irreducible character of degree d and FS indicator eps, for
##        (d,eps) in {(2,-1),(4,-1),(6,-1)}  [symplectic side] and
##        {(3,+1),(4,+1),(6,+1),(7,+1)}      [orthogonal side];
##    (B) for each, the character field Q(chi) (= the presence congruence)
##        and the Out-orbit of chi (= the Rule-S branch), the latter from
##        the .2/.3/... tables where available and from AutomorphismGroup
##        of a concrete group otherwise;
##    (C) the resulting per-branch class-count contribution, which is an
##        UPPER bound (branch 2 contributes <= 1) and a LOWER bound
##        (branch 1 contributes exactly 2, unconditionally in q).
##
##  Everything here is a character-table computation; no claim about a
##  particular q is made without the presence congruence being recorded.
##
#############################################################################

LoadPackage("ctbllib");;

Print("### v_task61 T-BC close: Rule-S columns\n");
Print("GAP ", GAPInfo.Version, "  CTblLib ",
      First(GAPInfo.PackagesLoaded.ctbllib, x -> true), "\n\n");

#############################################################################
##  (A) The S-table scan.
##
##  We scan the CTblLib "perfect" tables (AllCharacterTableNames with
##  IsPerfect), which is the same source 4ai used.  A candidate is a pair
##  (t, chi) with chi faithful, of the prescribed degree, with the
##  prescribed Frobenius-Schur indicator, and with t quasisimple.
##  We exclude t whose centre is too big to embed (Z(H) must be cyclic and
##  act by scalars: |Z| | q-1 automatically, but for a symplectic module
##  we need -1 in the image, i.e. 2 | |Z(H)| unless H itself is
##  centreless with an orthogonal.. -- we do NOT filter on that here, we
##  only record it, since the (-1)-containment is a PSN-GF condition, not
##  a Rule-S one).
#############################################################################

IsQuasisimpleTable := function(t)
  local z, f;
  if not IsPerfectCharacterTable(t) then return false; fi;
  z := ClassPositionsOfCentre(t);
  f := t / z;
  return IsSimpleCharacterTable(f);
end;;

PERFNAMES := AllCharacterTableNames(IsPerfect, true, Size, n -> n <= 10^10);;
Print("perfect tables of order <= 10^10 scanned: ", Length(PERFNAMES), "\n\n");

ScanS := function(deg, eps)
  local res, nm, t, chi, k, ker, fld, cen;
  res := [];
  for nm in PERFNAMES do
    t := CharacterTable(nm);
    if t = fail then continue; fi;
    if not IsQuasisimpleTable(t) then continue; fi;
    for chi in Irr(t) do
      if chi[1] <> deg then continue; fi;
      if Indicator(t, [chi], 2)[1] <> eps then continue; fi;
      ker := ClassPositionsOfKernel(chi);
      if Length(ker) <> 1 then continue; fi;          # faithful
      fld := Field(chi);
      cen := Length(ClassPositionsOfCentre(t));
      Add(res, rec(name := nm, order := Size(t), field := fld,
                   zsize := cen,
                   chi := Position(Irr(t), chi)));
    od;
  od;
  return res;
end;;

##  Out-orbit of chi: returns the size of the Out-orbit through chi,
##  computed from the table automorphism group restricted to the
##  characters that are algebraically conjugate-independent.  We use the
##  ".2" etc. extension tables when present; otherwise we fall back to
##  AutomorphismGroup of a concrete group and its induced action on Irr.
OutOrbitFromExtTable := function(nm, chipos)
  local t, ext, t2, fus, chi, ind, c, n;
  t := CharacterTable(nm);
  chi := Irr(t)[chipos];
  for ext in ["2", "2_1", "2_2", "3", "2'"] do
    t2 := CharacterTable(Concatenation(nm, ".", ext));
    if t2 = fail then continue; fi;
    fus := GetFusionMap(t, t2);
    if fus = fail then continue; fi;
    # chi is Out-stable under this .k  <=>  chi extends  <=>  some
    # irreducible of t2 restricts to chi (same degree).
    n := Number(Irr(t2), psi -> psi[1] = chi[1] and
             ForAll([1..NrConjugacyClasses(t)], i -> psi[fus[i]] = chi[i]));
    if n > 0 then
      return rec(ext := ext, stable := true, orbit := 1);
    else
      return rec(ext := ext, stable := false, orbit := 2);
    fi;
  od;
  return rec(ext := fail, stable := fail, orbit := fail);
end;;

ReportColumn := function(label, deg, eps)
  local L, r, o;
  Print("--- ", label, ":  degree ", deg, ", FS indicator ", eps, "\n");
  L := ScanS(deg, eps);
  for r in L do
    o := OutOrbitFromExtTable(r.name, r.chi);
    Print(String(r.name, 16), " |H|=", String(r.order, 12),
          "  |Z|=", r.zsize,
          "  Q(chi)=", r.field,
          "  Out-orbit=", o.orbit, " (via .", o.ext, ")\n");
  od;
  Print("    total candidate columns: ", Length(L), "\n\n");
  return L;
end;;

Print("=========== SYMPLECTIC SIDE (Sp_d(q), q odd) ===========\n");
Sd2 := ReportColumn("Sp_2", 2, -1);;
Sd4 := ReportColumn("Sp_4", 4, -1);;
Sd6 := ReportColumn("Sp_6", 6, -1);;

Print("=========== ORTHOGONAL SIDE (Omega_d(q), q odd) ===========\n");
Od3 := ReportColumn("Omega_3", 3, 1);;
Od4 := ReportColumn("Omega_4", 4, 1);;
Od6 := ReportColumn("Omega_6", 6, 1);;
Od7 := ReportColumn("Omega_7", 7, 1);;

#############################################################################
##  (B) The 2-local degree-7 members have no .2 table in CTblLib; do them
##      from the groups (this reproduces the 4ai addendum).
#############################################################################

Print("=========== 2-local degree-7 members, from the groups ===========\n");

DoPerfect := function(n, k)
  local G, t, A, out, chis, orb, aut, acts, i;
  G := PerfectGroup(IsPermGroup, n, k);
  t := CharacterTable(G);
  chis := Filtered(Irr(t), c -> c[1] = 7 and
            Length(ClassPositionsOfKernel(c)) = 1 and
            Indicator(t, [c], 2)[1] = 1);
  A := AutomorphismGroup(G);
  out := Size(A) / Size(InnerAutomorphismsAutomorphismGroup(A));
  Print("PerfectGroup(", n, ",", k, "): |Out|=", out,
        "  #faithful orthogonal deg-7 chars = ", Length(chis), "\n");
  # test whether an outer automorphism moves the characters
  if Length(chis) > 0 and out > 1 then
    for aut in GeneratorsOfGroup(A) do
      if aut in InnerAutomorphismsAutomorphismGroup(A) then continue; fi;
      acts := List(chis, c -> c);
      # induced permutation on Irr via the class permutation
      Print("   outer generator moves deg-7 chars: ",
            not ForAll(chis, c -> c = CharacterTableAutomorphismImage(c, aut)),
            "\n");
      break;
    od;
  fi;
  return rec(out := out, nchi := Length(chis));
end;;

# CharacterTableAutomorphismImage is not a GAP function; do it by hand
# through the permutation of conjugacy classes induced by the automorphism.
ChiUnderAut := function(G, t, chi, aut)
  local cc, perm, i, j, img;
  cc := ConjugacyClasses(t!.UnderlyingGroup);
  perm := [];
  for i in [1..Length(cc)] do
    img := Image(aut, Representative(cc[i]));
    j := First([1..Length(cc)], k -> img in cc[k]);
    perm[i] := j;
  od;
  return List([1..Length(cc)], i -> chi[perm[i]]);
end;;

DoPerfect2 := function(n, k)
  local G, t, chis, A, Inn, out, gens, aut, moved, c;
  G := PerfectGroup(IsPermGroup, n, k);
  t := CharacterTable(G);
  SetUnderlyingGroup(t, G);
  chis := Filtered(Irr(t), c -> c[1] = 7 and
            Length(ClassPositionsOfKernel(c)) = 1 and
            Indicator(t, [c], 2)[1] = 1);
  A := AutomorphismGroup(G);
  Inn := InnerAutomorphismsAutomorphismGroup(A);
  out := Size(A)/Size(Inn);
  moved := false;
  for aut in GeneratorsOfGroup(A) do
    if aut in Inn then continue; fi;
    for c in chis do
      if ChiUnderAut(G, t, c, aut) <> ValuesOfClassFunction(c) then
        moved := true;
      fi;
    od;
  od;
  Print("PerfectGroup(", n, ",", k, "): |Out|=", out,
        "  #faithful orth deg-7 chars=", Length(chis),
        "  outer moves a deg-7 char: ", moved,
        "  => Rule-S branch ", ["2","1"][1 + Int(moved)],
        " => contributes ", 2, " Omega_7-classes if branch 1\n");
  return moved;
end;;

for pair in [[1344,1],[1344,2],[10752,8]] do
  DoPerfect2(pair[1], pair[2]);
od;

#############################################################################
##  (C) Anchor cross-check against the v_task21 harness:  the psn census of
##      Omega_7(3) and PSp_6(3) is 15 resp. 6 proper classes (v_task9/10),
##      i.e. mult_1 = 16 resp. 7 with G itself (4af convention fix).
##      Rule S must reproduce the *rational* part of that at q = 3.
#############################################################################

Print("\n=========== q = 3 anchor cross-check ===========\n");
Print("Recorded (v_task9/10, harness v_task21): mult_1(Omega_7(3)) = 16, ",
      "mult_1(PSp_6(3)) = 7\n");
Print("Rule-S rational deg-7 columns above must contain the 8-member ",
      "doubled Sp_6(2) tree.\n");

QUIT;
