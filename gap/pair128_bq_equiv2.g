# Definitive (b,q)-equivalence test, cleanly structured (all locals at top).
LogTo("/Users/tilemachosvassias/DissAnalysis/dring-project/results/order128_pairs/pair128_bq_equiv2.out");

GetData := function(id)
  local G, Phi, hV, V, pcV, ev, pcP, coord, q, i, j, qe, bmat;
  G := SmallGroup(128, id); Phi := FrattiniSubgroup(G);
  hV := NaturalHomomorphismByNormalSubgroup(G, Phi); V := Image(hV);
  pcV := Pcgs(V); pcP := Pcgs(Phi);
  ev := List(pcV, x -> x);
  coord := z -> ExponentsOfPcElement(pcP, z) * Z(2)^0;
  q := v -> coord(PreImagesRepresentative(hV, v)^2);
  qe := List(ev, e -> q(e));
  bmat := List([1..4], i -> List([1..4], j ->
      coord(Comm(PreImagesRepresentative(hV, ev[i]),
                 PreImagesRepresentative(hV, ev[j])))));
  return rec(qe:=qe, bmat:=bmat);
end;

Qof := function(D, c)
  local r, i, j;
  r := Zero(D.qe[1]);
  for i in [1..4] do if IsOne(c[i]) then r := r + D.qe[i]; fi; od;
  for i in [1..4] do for j in [i+1..4] do
    if IsOne(c[i]) and IsOne(c[j]) then r := r + D.bmat[i][j]; fi;
  od; od;
  return r;
end;

Bof := function(D, c, d)
  local r, i, j;
  r := Zero(D.qe[1]);
  for i in [1..4] do for j in [1..4] do
    if IsOne(c[i]) and IsOne(d[j]) then r := r + D.bmat[i][j]; fi;
  od; od;
  return r;
end;

# test one alpha (4x4 GF2 matrix): does a compatible beta in GL(3,2) exist?
TestAlpha := function(D1, D2, A, nz)
  local basisSrc, basisTgt, c, Ac, s, t, M, betaImg, beta, dd;
  basisSrc := []; basisTgt := [];
  for c in nz do
    Ac := A * c;
    s := Qof(D1, c); t := Qof(D2, Ac);
    if RankMat(Concatenation(basisSrc, [s])) > Length(basisSrc) then
      Add(basisSrc, s); Add(basisTgt, t);
    fi;
  od;
  if Length(basisSrc) < 3 then return false; fi;
  M := TransposedMat(basisSrc)^-1;
  betaImg := TransposedMat(basisTgt);
  beta := betaImg * M;               # beta(x) = beta * x
  if RankMat(beta) < 3 then return false; fi;
  for c in nz do
    if beta * Qof(D1,c) <> Qof(D2, A*c) then return false; fi;
  od;
  for c in nz do for dd in nz do
    if beta * Bof(D1,c,dd) <> Bof(D2, A*c, A*dd) then return false; fi;
  od; od;
  return true;
end;

SearchEquiv := function(D1, D2)
  local nz, A, cnt;
  nz := Filtered(List(Tuples([0,1],4), c -> c*Z(2)^0), c -> not IsZero(c));
  cnt := 0;
  for A in GL(4,2) do
    cnt := cnt + 1;
    if TestAlpha(D1, D2, A, nz) then
      Print("  found compatible (alpha,beta) after ", cnt, " matrices\n");
      return true;
    fi;
  od;
  Print("  exhausted ", cnt, " matrices in GL(4,2), none compatible\n");
  return false;
end;

D1 := GetData(1597);
D2 := GetData(1598);
Print("qe(1597)=", D1.qe, "\nqe(1598)=", D2.qe, "\n");
# sanity: a group must be self-equivalent
Print("self-check 1597~1597: ", SearchEquiv(D1, D1), "\n");
eq := SearchEquiv(D1, D2);
Print("\n(b,q) EQUIVALENT between 1597 and 1598: ", eq, "\n");
Print("=> distinction lives EXACTLY in the (b,q)=psi^2 squaring datum: ", not eq, "\n");
LogTo();
QUIT;
