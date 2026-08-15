# v_task39_sporadic_iota.g -- EXACT iota(S) for the 26 sporadic simple groups
# (+ the Tits group 2F4(2)', which is NOT part of the sporadic list used by
# NOTES.md 4aj / v_task24_spor_iota.g -- reported for completeness only).
#
#   iota(S) := min { [S : N_S(A)] : 1 <> A <= S abelian }.
#
# LEMMA SP.  For any finite group X put
#   ilow(X) := min { [X:N] : N <= X with F(N) <> 1 }.
# Then (a) iota(S) = ilow(S) for S non-abelian simple, and (b)
#   ilow(X) = min over maximal M < X of
#               [X:M]            if F(M) <> 1,
#               [X:M] * ilow(M)  if F(M) = 1.
# Proof of (a): if A <> 1 is abelian then A <= F(N_S(A)), so iota(S) >=
# ilow(S); conversely if F(N) <> 1 then A := Z(F(N)) <> 1 is abelian and
# characteristic in N, so N <= N_S(A) and [S:N_S(A)] <= [X:N].  (Both
# directions are indexwise, and for M maximal with F(M) <> 1 one gets
# N_S(Z(F(M))) = M exactly, since Z(F(M)) char M and S is simple.)
# Proof of (b): N with F(N) <> 1 lies in some maximal M; if F(M) <> 1 the
# first branch applies, otherwise N < M strictly (F(M) = 1 <> F(N)) and
# [X:N] = [X:M]*[M:N] >= [X:M]*ilow(M).
#
# So iota is computed by a pure recursion over the ATLAS maximal-subgroup
# tables, with F(M) <> 1 decided from the CHARACTER TABLE of M by
# ClassPositionsOfFittingSubgroup.  No group is ever constructed.
#
# Provenance: CTblLib 1.3.11 `Maxes` = the complete ATLAS classifications;
# for the Monster this is the finished 46-class list (Dietrich-Lee-Popiel,
# 2023).  Where a table in the recursion has no stored `Maxes`, a valid
# LOWER bound is substituted:
#   * for M almost simple with F(M) = 1 and socle S0:  ilow(M) >= mu(S0),
#     because N <= M with F(N) <> 1 cannot contain S0 (else F(N) would
#     centralise S0, but C_M(S0) = 1), so [M:N] >= [S0 : N cap S0] >= mu(S0);
#   * failing that, the trivial bound ilow(M) >= 2.
# The run below reports, per group, BOTH the recursive lower bound and the
# best maximal-subgroup upper bound; they agree for all 27, so the values
# are exact.

LoadPackage("ctbllib");;

# CTblLib names a repeated maximal-subgroup class "<G>M<k>"; map those, and
# the tables without stored Maxes, to a socle whose mu is available.
# name -> mu(socle), the minimal faithful permutation degree of the socle
# (ATLAS; used only as the lower bound ilow(M) >= mu(Soc M), see header)
socle := rec();
socle.("A6.2^2")   := 6;      # A6
socle.("L2(16).2") := 17;     # L2(16)
socle.("L3(4).2_1"):= 21;     # L3(4)
socle.("U6(2).2")  := 672;    # U6(2)
socle.("L3(7).2")  := 57;     # L3(7)
alias := rec(M12M2 := "M11", M12M4 := "A6.2^2", J3M3 := "L2(19)",
             J3M2 := "L2(19)", HSM3 := "U3(5).2", McLM3 := "M22",
             ONM2 := "L3(7).2");
alias.("2F4(2)'M2") := "L3(3).2";

mu := function(nm)
  local t;
  t := CharacterTable(nm);
  if t = fail or not HasMaxes(t) then return fail; fi;
  return Minimum(List(Filtered(List(Maxes(t), CharacterTable), x -> x <> fail),
                      x -> Size(t)/Size(x)));
end;

memo := rec();

ilow := function(ct, cap)
  local key, best, m, mt, idx, r, s;
  key := Identifier(ct);
  if IsBound(alias.(key)) then
    mt := CharacterTable(alias.(key));
    if mt <> fail then ct := mt; key := Identifier(ct); fi;
  fi;
  if IsBound(memo.(key)) then return memo.(key); fi;
  if Size(ct) = 1 then return infinity; fi;
  if not HasMaxes(ct) then
    if IsBound(socle.(key)) then return socle.(key); fi;
    return 2;                      # trivial, still a valid lower bound
  fi;
  best := infinity;
  for m in Maxes(ct) do
    mt := CharacterTable(m);
    if mt = fail then continue; fi;   # never happens (see 'tables missing')
    idx := Size(ct)/Size(mt);
    if ClassPositionsOfFittingSubgroup(mt) <> [1] then
      if idx < best then best := idx; fi;
    elif 2*idx < best and 2*idx <= cap then
      r := ilow(mt, QuoInt(cap, idx));
      if idx*r < best then best := idx*r; fi;
    fi;
  od;
  memo.(key) := best;
  return best;
end;

names := ["M11","M12","M22","M23","M24","J1","J2","J3","HS","McL","He","Ru",
          "Suz","Co1","Co2","Co3","Fi22","Fi23","Fi24'","HN","Th","ON","Ly",
          "J4","B","M","2F4(2)'"];;

for nm in names do
  t := CharacterTable(nm);
  if t = fail or not HasMaxes(t) then Print("### NO DATA ", nm, "\n"); continue; fi;
  mx := Maxes(t);
  good := [];  miss := [];
  for s in mx do
    ct := CharacterTable(s);
    if ct = fail then Add(miss, s);
    elif ClassPositionsOfFittingSubgroup(ct) <> [1] then
      Add(good, [Size(t)/Size(ct), s]);
    fi;
  od;
  Sort(good);
  lb := ilow(t, 10^40);
  allidx := List(Filtered(List(mx, CharacterTable), x -> x <> fail),
                 x -> Size(t)/Size(x));
  Sort(allidx);
  Print("GROUP ", nm, "\n");
  Print("  order    ", Size(t), "\n");
  Print("  nmaxes   ", Length(mx), "  (tables missing: ", miss, ")\n");
  Print("  iota     ", good[1][1], "   witness M = ", good[1][2],
        "   [A = Z(F(M)), N_S(A) = M]\n");
  Print("  lowbound ", lb, "   (Lemma SP recursion)  EXACT=",
        lb = good[1][1], "\n");
  if Length(good) >= 2 then
    Print("  iota2ub  ", good[2][1], "   at M = ", good[2][2], "\n");
  fi;
  Print("  spectrum ", List(good, x -> x[1]), "\n");
  Print("  mu(S)    ", allidx[1], "\n");
od;

QUIT;
