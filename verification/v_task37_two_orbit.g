####################################################################
# v_task37_two_orbit.g -- data for the elimination of case (b) of the
#   transported ratio trick (NOTES.md 4av, input I5).
#
# PART A.  The bottom of the conductor spectrum of A_n, uniformly in n.
#   For 1 <> H <= A_n put   ind*(H) = [A_n : N_{A_n}(H)] * |H'|
#   (so ind*(H) = |A_n| / conductor(H,H'), the quantity 4aj/4ak minimise).
#   For H abelian ind*(H) = [A_n : N(H)] = the invariant I(.) of 4as.
#   With s = |supp(H)| and s <= n-2  (4as Step 1),
#       ind*(H) = n^{(s)} * |H'| / |N_{S_s}(H)| ,
#   and for s in {n-1,n} the right side may drop by a factor 2.
#   So the bottom of the spectrum is computed ONCE, by enumerating the
#   conjugacy classes of fixed-point-free subgroups H <= A_s for small s
#   and recording the rational  f(H) = |H'| / |N_{S_s}(H)| .
#
# PART B.  g(m) = max{ m*|Aut(B)| : B abelian of order m }  (4as Step 3),
#   fed to the DP in v_task37_two_orbit.py.
#
# PART C.  Falsification of the third-value transport (star_3) on the
#   ten Fitting-free test groups of v_task34.
#
# PART D.  The ratio-3 test: for which almost simple pairs S <= K <= Abar
#   is  iota_2(K<=Abar) = 3 * iota(K<=Abar) ?   (branch (b2)).
####################################################################

Print("=== PART A: bottom of the A_n conductor spectrum, uniform in n ===\n");
Print("# rows:  s  |  H  |  |H'|  |  |N_{S_s}(H)|  |  ind* = n^(s) * f\n");
Print("# f is printed as |H'|/|N_{S_s}(H)|; only the smallest f's matter.\n\n");

partA := function(smax)
  local s, Ss, cc, c, H, sup, nrm, hd, f, L, r;
  for s in [3..smax] do
    Ss := SymmetricGroup(s);
    cc := ConjugacyClassesSubgroups(Ss);
    L := [];
    for c in cc do
      H := Representative(c);
      if Size(H) = 1 then continue; fi;
      # fixed point free on [1..s]
      sup := Union(List(GeneratorsOfGroup(H), g -> MovedPoints(g)));
      if Size(sup) <> s then continue; fi;
      # all elements even
      if not IsSubgroup(AlternatingGroup(s), H) then continue; fi;
      nrm := Normalizer(Ss, H);
      hd  := DerivedSubgroup(H);
      f   := Size(hd) / Size(nrm);
      Add(L, [f, StructureDescription(H), Size(hd), Size(nrm), IsAbelian(H)]);
    od;
    Sort(L, function(a,b) return a[1] < b[1]; end);
    Print("s = ", s, "   (", Length(L), " ffp all-even classes)\n");
    for r in L{[1..Minimum(8, Length(L))]} do
      Print("   f = ", r[1], "  H = ", r[2], "  |H'| = ", r[3],
            "  |N_{S_s}(H)| = ", r[4], "  abelian: ", r[5], "\n");
    od;
    Print("\n");
  od;
end;

partA(8);

Print("\n=== PART B: g(m) = max m*|Aut(B)|, B abelian of order m ===\n");
gtab := [];
for m in [2..64] do
  best := 0;
  for A in AllSmallGroups(m, IsAbelian, true) do
    best := Maximum(best, m * Size(AutomorphismGroup(A)));
  od;
  Add(gtab, best);
od;
Print("g(2..64) := ", gtab, ";\n");

Print("\n=== PART C: third-value transport (star_3) on the v_task34 groups ===\n");

Ivals := function(G, bound)
  local res, N, A, i;
  res := [];
  for N in LowIndexSubgroups(G, bound) do
    i := Index(G, N);
    for A in NormalSubgroups(N) do
      if Size(A) > 1 and IsAbelian(A) and Normalizer(G, A) = N then
        Add(res, i); break;
      fi;
    od;
  od;
  return Set(res);
end;

a1 := (1,2,3);;  b1 := (1,2,3,4,5);;
a2 := (6,7,8);;  b2 := (6,7,8,9,10);;
sw := (1,6)(2,7)(3,8)(4,9)(5,10);;
tt := (1,2)(6,7);;

tests := [
 ["A5 x A5      ", Group(a1,b1,a2,b2), 40],
 ["A5 wr C2     ", Group(a1,b1,a2,b2,sw), 40],
 ["(A5xA5).2 dia", Group(a1,b1,a2,b2,tt), 40],
 ["(A5xA5).2^2  ", Group(a1,b1,a2,b2,sw,tt), 40],
 ["A5 x A6      ", DirectProduct(AlternatingGroup(5),AlternatingGroup(6)), 40],
 ["A5 x L2(7)   ", DirectProduct(AlternatingGroup(5),PSL(2,7)), 40],
 ["A5 x PGL(2,9)", DirectProduct(AlternatingGroup(5),PGL(2,9)), 40],
 ["A5 wr C3     ", WreathProduct(AlternatingGroup(5),CyclicGroup(IsPermGroup,3)), 40]
];

for t in tests do
  v := Ivals(t[2], t[3]);
  Print(t[1], "  I(T) up to ", t[3], " = ", v, "\n");
od;

Print("\n=== PART D: ratio-3 test  iota_2(K<=Abar) = 3*iota(K<=Abar) ===\n");

IF_RATIO3 := function(r) if r = 3 then return "   <<< RATIO 3"; fi; return ""; end;

ratio := function(nm, K, Abar, bound)
  local res, N, A, i, v, r;
  res := [];
  for N in LowIndexSubgroups(Abar, bound) do
    i := Index(Abar, N);
    for A in NormalSubgroups(N) do
      if Size(A) > 1 and IsAbelian(A) and IsSubgroup(K, A)
         and Normalizer(Abar, A) = N then
        Add(res, i); break;
      fi;
    od;
  od;
  res := Set(res);
  if Length(res) >= 2 then
    r := res[2]/res[1];
    Print(nm, "  I = ", res{[1..Minimum(5,Length(res))]},
          "   iota2/iota = ", r, IF_RATIO3(r), "\n");
  else
    Print(nm, "  I = ", res, "  (too few values below bound)\n");
  fi;
  return res;
end;

ratio("A5 <= A5        ", AlternatingGroup(5), AlternatingGroup(5), 60);
ratio("A5 <= S5        ", AlternatingGroup(5), SymmetricGroup(5), 60);
ratio("A6 <= A6        ", AlternatingGroup(6), AlternatingGroup(6), 60);
ratio("A6 <= S6        ", AlternatingGroup(6), SymmetricGroup(6), 60);
ratio("A6 <= PGL(2,9)  ", DerivedSubgroup(PGL(2,9)), PGL(2,9), 60);
ratio("L2(7) <= L2(7)  ", PSL(2,7), PSL(2,7), 60);
ratio("L2(7) <= PGL(2,7)", PSL(2,7), PGL(2,7), 60);
ratio("L2(8) <= L2(8)  ", PSL(2,8), PSL(2,8), 120);
ratio("L2(11)<= L2(11) ", PSL(2,11), PSL(2,11), 120);
ratio("L2(13)<= L2(13) ", PSL(2,13), PSL(2,13), 200);
ratio("L3(2) <= L3(2)  ", PSL(3,2), PSL(3,2), 60);
ratio("L3(3) <= L3(3)  ", PSL(3,3), PSL(3,3), 200);
ratio("U3(3) <= U3(3)  ", PSU(3,3), PSU(3,3), 200);
ratio("S4(3) <= S4(3)  ", PSp(4,3), PSp(4,3), 200);
ratio("A7 <= A7        ", AlternatingGroup(7), AlternatingGroup(7), 200);
ratio("A7 <= S7        ", AlternatingGroup(7), SymmetricGroup(7), 200);
ratio("M11 <= M11      ", MathieuGroup(11), MathieuGroup(11), 300);

Print("\n=== done ===\n");
QUIT;
