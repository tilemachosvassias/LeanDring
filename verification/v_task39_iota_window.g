# v_task39_iota_window.g -- the FULL value window I(S) cap [iota(S), 2*iota(S)].
#
# The pair invariant satisfies iota(K <= Abar) = f(A)*[S:N_S(A)] with
# f | |Out S| <= 2 (Lemma F, v_task36), hence iota(S) <= iota(K<=Abar) <=
# 2*iota(S) and the candidate set for the scan is
#     V(S) = { m*w : w in I(S), w <= 2*iota(S), 1 <= m <= |Out S| }.
# This script computes a SUPERSET of I(S) cap [1, 2*iota(S)] by the same
# Lemma SP recursion as v_task39_sporadic_iota.g, run in set-collecting mode
# (a superset is exactly what is wanted: it can only make the scan larger).
# `unresolved` lists the places where a character table in the recursion has
# no stored Maxes; every one of them is "subgroups of index <= 2 inside the
# iota-witness itself", which can only produce the endpoint value 2*iota(S)
# -- already in V(S).  The single exception, Co3 / U4(3).2_3' at cap 3, is
# settled by hand: U4(3).2 has no subgroup of index 3, and its index-2
# subgroup U4(3) is simple, so F <> 1 is impossible there.
# Hence V(S) as fed to v_task39_sporadic_scan.c is COMPLETE.

LoadPackage("ctbllib");;
socle := rec();; socle.("A6.2^2"):=6;; socle.("L2(16).2"):=17;;
socle.("L3(4).2_1"):=21;; socle.("U6(2).2"):=672;; socle.("L3(7).2"):=57;;
alias := rec(M12M2:="M11", M12M4:="A6.2^2", J3M3:="L2(19)", J3M2:="L2(19)",
             HSM3:="U3(5).2", McLM3:="M22", ONM2:="L3(7).2");;
alias.("2F4(2)'M2"):="L3(3).2";;
unres := [];;
# vals(X,cap) : SUPERSET of { [X:N] <= cap : N <= X, F(N) <> 1 }
vals := function(ct, cap)
  local key, r, m, mt, idx, w, b;
  key := Identifier(ct);
  if IsBound(alias.(key)) then
    mt := CharacterTable(alias.(key));
    if mt <> fail then ct := mt; key := Identifier(ct); fi; fi;
  if cap < 1 then return []; fi;
  if not HasMaxes(ct) then
    if IsBound(socle.(key)) then b := socle.(key); else b := 2; fi;
    if b <= cap then Add(unres, [key, cap, b]); fi;
    return [];
  fi;
  r := [];
  for m in Maxes(ct) do
    mt := CharacterTable(m);
    if mt = fail then Add(unres,[m,cap,0]); continue; fi;
    idx := Size(ct)/Size(mt);
    if idx > cap then continue; fi;
    if ClassPositionsOfFittingSubgroup(mt) <> [1] then AddSet(r, idx); fi;
    for w in vals(mt, QuoInt(cap, idx)) do AddSet(r, idx*w); od;
  od;
  return r;
end;;
names := ["M11","M12","M22","M23","M24","J1","J2","J3","HS","McL","He","Ru",
          "Suz","Co1","Co2","Co3","Fi22","Fi23","Fi24'","HN","Th","ON","Ly",
          "J4","B","M","2F4(2)'"];;
out := rec(M12:=2,M22:=2,J2:=2,J3:=2,HS:=2,McL:=2,He:=2,Suz:=2,Fi22:=2,HN:=2,ON:=2);;
out.("Fi24'"):=2;; out.("2F4(2)'"):=2;;
for nm in names do
  t := CharacterTable(nm);
  good := [];
  for s in Maxes(t) do ct:=CharacterTable(s);
    if ct<>fail and ClassPositionsOfFittingSubgroup(ct)<>[1] then
      Add(good, Size(t)/Size(ct)); fi; od;
  io := Minimum(good);
  unres := [];
  v := vals(t, 2*io);
  Print(nm, "  iota=", io, "  I(S) cap [1,2iota] = ", v,
        "   unresolved=", Length(unres), "\n");
  if Length(unres) > 0 then Print("     ", unres, "\n"); fi;
od;
QUIT;
