###########################################################################
## 0. spinor norm machinery
###########################################################################

# square class of a nonzero element of the field FLD: true = square
FLD := fail;                    # set by the callers
IsSq := function(x)
  return IsOne(x^((Size(FLD)-1)/2));
end;

# Wall-form spinor norm of an isometry g of the symmetric bilinear form B.
# Returns a field element whose square class is the spinor norm.
SpNorm := function(B, g)
  local n, F, M, ns, comp, P, X, k, i, v, sp;
  n := Length(B); F := FLD;
  M := g - IdentityMat(n, F);
  ns := NullspaceMat(M);                      # kernel of g-1
  # complement basis P of ker(g-1)
  P := BaseSteinitzVectors(IdentityMat(n,F), ns).factorspace;
  k := Length(P);
  if k = 0 then return One(F); fi;            # g = 1
  X := P * M;                                 # basis of residual space
  sp := P * B * TransposedMat(X);
  return (-2*One(F))^k * DeterminantMat(sp);
end;

# the scalar lam with C = lam*B (fail if none)
ScalarFactor := function(C, B)
  local i, j, lam;
  lam := fail;
  for i in [1..Length(B)] do for j in [1..Length(B)] do
    if B[i][j] <> Zero(FLD) then lam := C[i][j]/B[i][j]; fi;
  od; od;
  if lam = fail or C <> lam*B then return fail; fi;
  return lam;
end;

# check: is g an isometry of B?
IsIsom := function(B, g) return g*B*TransposedMat(g) = B; end;

Refl := function(B, v)
  local n, F;
  n := Length(B); F := FLD;
  # row-vector convention:  w |-> w - 2 (w B v^T)/(v B v^T) v
  return IdentityMat(n,F) - 2*(B*TransposedMat([v]))*[v]/(v*B*v);
end;

###########################################################################
## 1. VALIDATION of the spinor norm routine
###########################################################################

ValidateSpinor := function(q)
  local F, B, n, i, v, r, ok, g, h, a, b, om, gens, bad, x;
  F := GF(q); FLD := F; n := 7;
  # a random-ish nondegenerate symmetric form: diagonal with mixed classes
  B := IdentityMat(n, F);
  B[1][1] := PrimitiveRoot(F);                # nonsquare entry
  ok := true;
  # (a) theta(reflection) = B(v,v) mod squares
  for i in [1..40] do
    repeat v := Random(F^n); until v*B*v <> Zero(F);
    r := Refl(B, v);
    if not IsIsom(B, r) then ok := false; Print("  !! reflection not isometry\n"); fi;
    if IsSq(SpNorm(B,r)) <> IsSq(v*B*v) then
      ok := false; Print("  !! theta(refl) wrong\n");
    fi;
  od;
  # (b) homomorphy on random products of reflections
  for i in [1..40] do
    repeat v := Random(F^n); until v*B*v <> Zero(F);
    a := Refl(B,v);
    repeat v := Random(F^n); until v*B*v <> Zero(F);
    b := Refl(B,v);
    g := a*b;
    if IsSq(SpNorm(B,g)) <> (IsSq(SpNorm(B,a)) = IsSq(SpNorm(B,b))) then
      ok := false; Print("  !! theta not multiplicative\n");
    fi;
  od;
  # (c) longer words
  for i in [1..30] do
    g := IdentityMat(n,F); x := true;
    for b in [1..6] do
      repeat v := Random(F^n); until v*B*v <> Zero(F);
      r := Refl(B,v); g := g*r; x := (x = IsSq(v*B*v));
    od;
    if IsSq(SpNorm(B,g)) <> x then ok := false; Print("  !! word failed\n"); fi;
  od;
  # (d) Omega(0,7,q): every generator has square spinor norm w.r.t. its own form
  om := Omega(0,n,q);
  B := InvariantBilinearForm(om).matrix;
  bad := 0;
  for g in GeneratorsOfGroup(om) do
    if not IsIsom(B,g) then Print("  !! Omega gen not isometry\n"); ok := false; fi;
    if not IsSq(SpNorm(B,g)) then bad := bad+1; fi;
  od;
  if bad > 0 then ok := false; Print("  !! ",bad," Omega generators with nonsquare theta\n"); fi;
  # (e) an element of SO \ Omega must have nonsquare theta:
  #     product of two reflections whose norms differ in square class
  repeat v := Random(F^n); until v*B*v <> Zero(F) and IsSq(v*B*v);
  a := Refl(B,v);
  repeat v := Random(F^n); until v*B*v <> Zero(F) and not IsSq(v*B*v);
  b := Refl(B,v);
  g := a*b;
  if DeterminantMat(g) <> One(F) then ok := false; Print("  !! det\n"); fi;
  if IsSq(SpNorm(B,g)) then ok := false; Print("  !! SO\\Omega elt has square theta\n"); fi;
  # (f) theta must be SURJECTIVE on SO(0,7,q) (since [SO:Omega] = 2):
  #     some product of SO generators must have nonsquare theta.
  h := SO(0,n,q);
  if not false in List(GeneratorsOfGroup(h), x -> IsSq(SpNorm(B,x))) then
    # generators happen to be in Omega; try random words
    x := true; g := One(h);
    for i in [1..200] do
      g := g * Random(GeneratorsOfGroup(h));
      if not IsSq(SpNorm(B,g)) then x := false; break; fi;
    od;
    if x then ok := false; Print("  !! theta never nonsquare on SO\n"); fi;
  fi;
  Print("  validate q=",q,": ", ok, "\n");
  return ok;
end;



###########################################################################
## 2. the columns
###########################################################################

# All 7-dimensional absolutely irreducible GF(q)-modules of U carrying an
# invariant symmetric bilinear form, grouped into Out(U)-orbits;
# for each orbit report the branch and the class count.

ColumnData := function(U, aut, outreps, q, name)
  local F, mods, good, m, B, seen, i, j, alpha, iso, T, c, lam, d, th, res,
        gens, mm, ok, r, cnt, orb, stabfound, hom, mats;
  F := GF(q); FLD := F;
  mods := IrreducibleModules(U, F, 7);
  gens := mods[1];                 # generator list the modules refer to
  mods := Filtered(mods[2], m -> m.dimension = 7);
  mods := Filtered(mods, m -> MTX.IsAbsolutelyIrreducible(m));
  # faithful only, and orthogonal (invariant nondegenerate SYMMETRIC form)
  good := [];
  for m in mods do
    hom := GroupHomomorphismByImages(U, Group(m.generators), gens, m.generators);
    if hom = fail or Size(Image(hom)) <> Size(U) then continue; fi;
    B := MTX.InvariantBilinearForm(m);
    if B <> fail and B = TransposedMat(B) and DeterminantMat(B) <> Zero(F) then
      Add(good, rec(mo := m, form := B, hom := hom));
    fi;
  od;
  if Length(good) = 0 then
    Print(name, " q=", q, ": ABSENT (no faithful 7-dim orthogonal abs.irr. module)\n");
    return rec(name:=name, q:=q, present:=false, classes:=0);
  fi;
  res := rec(name:=name, q:=q, present:=true, nmod:=Length(good),
             orbits:=[], classes:=0);
  seen := [];
  for i in [1..Length(good)] do
    if i in seen then continue; fi;
    orb := [i]; stabfound := [];
    for alpha in outreps do        # outreps: NON-inner coset representatives
      # twisted module  M^alpha :  g |-> rho(alpha(g))
      mats := List(gens, g -> ImagesRepresentative(good[i].hom,
                                ImagesRepresentative(alpha, g)));
      mm := GModuleByMats(mats, F);
      for j in [1..Length(good)] do
        iso := MTX.IsomorphismModules(mm, good[j].mo);
        if iso <> fail then
          if not j in orb then Add(orb, j); fi;
          if j = i then Add(stabfound, rec(alpha:=alpha, T:=iso)); fi;
        fi;
      od;
    od;
    UniteSet(seen, orb);
    B := good[i].form;
    cnt := fail; th := fail;
    if Length(stabfound) = 0 then
      cnt := 2;      # Stab_Out(chi) = 1 : Rule-S branch 1
      Print(name," q=",q,": orbit ",orb," Stab_Out=1  -> 2 classes\n");
    else
      # N_SO(U)/U  =  Stab_Out(chi), of order 1 + #stabfound.
      # psn  <=>  theta is injective on it  <=>  |Stab| = 2 and theta nonsquare.
      ok := false;
      for r in stabfound do
        T := r.T;
        lam := ScalarFactor(T*B*TransposedMat(T), B);
        if lam = fail then Print("  !! form not scaled\n"); continue; fi;
        if not IsSq(lam) then Print("  !! nonsquare similitude factor (impossible)\n"); fi;
        T := T / RootFFE(F, lam, 2);
        if not IsIsom(B,T) then Print("  !! not isometry after scaling\n"); fi;
        d := DeterminantMat(T);
        if d = -One(F) then T := -T; fi;
        if DeterminantMat(T) <> One(F) then Print("  !! det<>1\n"); fi;
        th := SpNorm(B, T);
        if IsSq(th) or Length(stabfound) > 1 then cnt := 0; else cnt := 1; fi;
        Print(name," q=",q,": orbit ",orb," |Stab_Out|=",Length(stabfound)+1,
              " det0=",d," theta_square=",IsSq(th)," -> ",cnt," class(es)\n");
        ok := true; break;
      od;
      if not ok then cnt := 2; fi;
    fi;
    Add(res.orbits, rec(orb:=orb, count:=cnt));
    res.classes := res.classes + cnt;
  od;
  Print(name," q=",q,": #modules=",Length(good)," TOTAL ",res.classes,
        " Omega_7(q)-class(es)\n");
  return res;
end;

