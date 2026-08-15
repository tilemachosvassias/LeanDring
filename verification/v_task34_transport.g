####################################################################
# v_task34_transport.g  --  falsification of the S -> T transport
#   lemmas for the conductors iota, iota_2  (NOTES.md 4ar item 3).
#
# For a finite group G put
#     I(G) = { [G : N_G(A)] : 1 <> A <= G abelian }
#          = { |A^G| : 1 <> A <= G abelian }   (class of SUBgroups)
#     iota(G) = min I(G),  iota_2(G) = second smallest element of I(G).
#
# CLAIM under test (transport):  T Fitting-free, socle Q = S_1 x...x S_k,
# K = kernel of the T-action on the factors, K_i = i-th component of K,
# Abar_i = almost-simple group induced on S_i by its T-stabiliser T_i,
# l_O = orbit length.  Put  I(K_i <= Abar_i) = { [Abar_i : N(A)] :
# 1 <> A <= K_i abelian }.  Then, up to intrusion by multi-support
# subgroups and by abelian A not inside K,
#
#     I(T)  \supseteq  P := Union_O  l_O * I(K_i <= Abar_i)
#     iota(T)   = min P
#     iota_2(T) = second smallest element of P.
#
# NOTE the two corrections the data forced: the ORBIT LENGTH multiplies,
# and the right group is the almost-simple pair (K_i, Abar_i), not S_i.
#
# Method: exact, exhaustive below a bound.  I(G) restricted to values
# <= bound is computed from LowIndexSubgroups(G,bound): every value
# [G:N_G(A)] <= bound is realised by the subgroup N = N_G(A), which has
# index <= bound, and A is a nontrivial abelian NORMAL subgroup of N
# with N_G(A) = N.  So we scan all subgroups of index <= bound and all
# their abelian normal subgroups.  No sampling, no heuristics.
####################################################################

# I(G) intersected with [1,bound], plus a witness for each value.
Ivals := function(G, bound)
  local res, N, A, i, wit, k;
  res := []; wit := rec();
  for N in LowIndexSubgroups(G, bound) do
    i := Index(G, N);
    for A in NormalSubgroups(N) do
      if Size(A) > 1 and IsAbelian(A) and Normalizer(G, A) = N then
        Add(res, i);
        k := Concatenation("i", String(i));
        if not IsBound(wit.(k)) then wit.(k) := StructureDescription(A); fi;
        break;
      fi;
    od;
  od;
  return rec(vals := Set(res), wit := wit);
end;

report := function(nm, G, bound)
  local r, v, s;
  r := Ivals(G, bound);
  s := "";
  for v in r.vals do
    s := Concatenation(s, String(v), "(", r.wit.(Concatenation("i",String(v))), ") ");
  od;
  Print(nm, "  |G|=", Size(G), "  I(G) up to ", bound, " : ", r.vals, "\n");
  Print("      witnesses: ", s, "\n");
  return r.vals;
end;

Print("=== PART 1: simple and almost simple (the Ahat table) ===\n\n");
report("A5            ", AlternatingGroup(5), 40);
report("S5            ", SymmetricGroup(5), 40);
report("A6            ", AlternatingGroup(6), 60);
report("S6            ", SymmetricGroup(6), 60);
report("PGL(2,9)      ", PGL(2,9), 60);
report("M10           ", Image(IsomorphismPermGroup(SmallGroup(720,764))), 60);
report("PGammaL(2,9)  ", Image(IsomorphismPermGroup(AutomorphismGroup(AlternatingGroup(6)))), 60);
report("L2(7)         ", PSL(2,7), 40);
report("PGL(2,7)      ", PGL(2,7), 40);
report("A7            ", AlternatingGroup(7), 60);
report("S7            ", SymmetricGroup(7), 60);

Print("\n=== PART 2: Fitting-free non-simple T ===\n\n");

a1 := (1,2,3);;  b1 := (1,2,3,4,5);;
a2 := (6,7,8);;  b2 := (6,7,8,9,10);;
sw := (1,6)(2,7)(3,8)(4,9)(5,10);;
tt := (1,2)(6,7);;                     # diagonal outer (transposition,transposition)
t1 := (1,2)(3,4);;                     # not needed, kept for clarity

T4 := Group(a1,b1,a2,b2);;                 # A5 x A5              (l=1,1; Ahat=A5)
T1 := Group(a1,b1,a2,b2,sw);;              # A5 wr C2             (l=2;   Ahat=A5)
T2 := Group(a1,b1,a2,b2,tt);;              # (A5xA5).2 diagonal   (l=1,1; Ahat=S5)
T3 := Group(a1,b1,a2,b2,sw,tt);;           # (A5xA5).2^2          (l=2;   Ahat=S5)

report("A5 x A5           ", T4, 40);
report("A5 wr C2          ", T1, 40);
report("(A5xA5).2 diagonal", T2, 40);
report("(A5xA5).2^2       ", T3, 40);

# mixed factors: A5 x A6, S5 x A6, and A5 x L2(7)
d56 := DirectProduct(AlternatingGroup(5), AlternatingGroup(6));;
report("A5 x A6           ", d56, 40);
d56b := DirectProduct(SymmetricGroup(5), AlternatingGroup(6));;
report("S5 x A6           ", d56b, 40);
d57 := DirectProduct(AlternatingGroup(5), PSL(2,7));;
report("A5 x L2(7)        ", d57, 40);
# a "second-best orbit" test: an l=2 orbit of A5 against a single A6
d_mix := DirectProduct(T1, AlternatingGroup(6));;
report("(A5 wr C2) x A6   ", d_mix, 24);
# fusion test: socle A6, Ahat = M10 / PGL(2,9) / PGammaL(2,9), inside a product
d_m10 := DirectProduct(AlternatingGroup(5), PGL(2,9));;
report("A5 x PGL(2,9)     ", d_m10, 30);

Print("\n=== PART 3: the exact identity |A^T| = l * f * |A^{S_i}| ===\n");
Print("    (single-factor witnesses; f = # of S_i-classes fused by T)\n\n");

checkid := function(nm, T, Q, emb, A)
  local NA, i, lQ, lT;
  lT := Index(T, Normalizer(T, A));
  lQ := Index(Q, Normalizer(Q, A));
  Print(nm, ": |A^T| = ", lT, ",  |A^Q| = ", lQ,
        ",  ratio = ", lT/lQ, "\n");
end;

V := Group((1,2)(3,4),(1,3)(2,4));;    # Klein 4-group in factor 1, iota-witness of A5
C5 := Group((1,2,3,4,5));;             # iota_2-witness of A5
for pair in [["A5xA5      ", T4], ["A5wrC2     ", T1],
             ["(A5xA5).2d ", T2], ["(A5xA5).2^2", T3]] do
  Print(pair[1], "  V4 : |A^T| = ", Index(pair[2], Normalizer(pair[2], V)),
        "   C5 : |A^T| = ", Index(pair[2], Normalizer(pair[2], C5)), "\n");
od;

Print("\n=== PART 4: the outer branch, A cap Q = 1 ===\n\n");
Q1 := Group(a1,b1,a2,b2);;
for g in [sw, tt, sw*tt] do
  A := Group(g);
  Print("A = <", g, ">  |A|=", Size(A),
        "  A cap Q = ", Size(Intersection(A, Q1)),
        "  |A^T3| = ", Index(T3, Normalizer(T3, A)),
        "  [Q:C_Q(A)] = ", Index(Q1, Centralizer(Q1, g)), "\n");
od;
Print("\n(in A5 wr C2, T1:)\n");
for g in [sw] do
  A := Group(g);
  Print("A = <swap>  |A^T1| = ", Index(T1, Normalizer(T1, A)),
        "  [Q:C_Q(A)] = ", Index(Q1, Centralizer(Q1, g)), "\n");
od;

Print("\n=== PART 5: PerfectGroup / mixed sanity, socle-internal min ===\n\n");
report("A5 x A5 x A5      ", Group(a1,b1,a2,b2,(11,12,13),(11,12,13,14,15)), 24);
report("A5 wr C3          ",
   Group(a1,b1,a2,b2,(11,12,13),(11,12,13,14,15),
         (1,6,11)(2,7,12)(3,8,13)(4,9,14)(5,10,15)), 24);


Print("\n=== PART 6: programmatic PASS/FAIL of the transport formula ===\n");
Print("   predicted single-factor values  =  Union_O  l_O * I(K_i, Abar_i)\n");
Print("   where K_i = K cap (i-th component), classes taken under Abar_i.\n\n");

# I of the PAIR (K,Abar):  { [Abar : N_Abar(A)] : 1<>A<=K abelian }
IvalsPair := function(K, Abar, bound)
  local res, c, A;
  res := [];
  for c in ConjugacyClassesSubgroups(K) do
    A := Representative(c);
    if Size(A) > 1 and IsAbelian(A) then
      Add(res, Index(Abar, Normalizer(Abar, A)));
    fi;
  od;
  return Set(Filtered(res, x -> x <= bound));
end;

testT := function(nm, T, bound, data)
  local pred, d, s, obs, i2p, i2o;
  pred := [];
  for d in data do            # d = [ l_O, K_i, Abar_i ]
    for s in IvalsPair(d[2], d[3], bound) do
      if d[1]*s <= bound then Add(pred, d[1]*s); fi;
    od;
  od;
  pred := Set(pred);
  obs  := Ivals(T, bound).vals;
  Print(nm, "\n   predicted single-factor values <= ", bound, " : ", pred, "\n");
  Print("   observed I(T) <= ", bound, "               : ", obs, "\n");
  Print("   [C1] predicted subset of observed : ", IsSubset(obs, pred), "\n");
  Print("   [C2] iota(T) = min predicted      : ", Minimum(obs) = Minimum(pred),
        "   (", Minimum(obs), " vs ", Minimum(pred), ")\n");
  if Length(obs) >= 2 and Length(pred) >= 2 then
    i2o := obs[2]; i2p := pred[2];
    Print("   [C3] iota_2(T) = 2nd predicted    : ", i2o = i2p,
          "   (", i2o, " vs ", i2p, ")\n");
  fi;
  Print("\n");
end;

A5 := AlternatingGroup(5);;  S5 := SymmetricGroup(5);;
A6 := AlternatingGroup(6);;  S6g := SymmetricGroup(6);;
testT("A5 x A5            (l=1,1; K_i=A5, Abar=A5)", T4, 40,
      [[1,A5,A5],[1,A5,A5]]);
testT("A5 wr C2           (l=2;   K_i=A5, Abar=A5)", T1, 40,
      [[2,A5,A5]]);
testT("(A5xA5).2 diagonal (l=1,1; K_i=A5, Abar=S5)", T2, 40,
      [[1,A5,S5],[1,A5,S5]]);
testT("(A5xA5).2^2        (l=2;   K_i=A5, Abar=S5)", T3, 40,
      [[2,A5,S5]]);
testT("A5 x A6            (l=1,1)", d56, 40, [[1,A5,A5],[1,A6,A6]]);
testT("S5 x A6            (l=1,1; K_1=S5)", d56b, 40, [[1,S5,S5],[1,A6,A6]]);
testT("A5 x L2(7)         (l=1,1)", d57, 40, [[1,A5,A5],[1,PSL(2,7),PSL(2,7)]]);
testT("(A5 wr C2) x A6    (l=2 and l=1)", d_mix, 24, [[2,A5,A5],[1,A6,A6]]);
testT("A5 x PGL(2,9)      (l=1,1; K_2=A6, Abar_2=PGL(2,9))", d_m10, 30,
      [[1,A5,A5],[1,A6,PGL(2,9)]]);
testT("A5 wr C3           (l=3)", Group(a1,b1,a2,b2,(11,12,13),(11,12,13,14,15),
         (1,6,11)(2,7,12)(3,8,13)(4,9,14)(5,10,15)), 24, [[3,A5,A5]]);

QUIT;
