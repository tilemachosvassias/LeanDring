# v_task50_sporadic_twins.g -- exact iota(S) (Lemma SP recursion, v_task39)
# for every simple group that occurs as a socle factor in the Phase-1 order
# census of v_task50_sporadic_twins.py, plus |Out(S)|.
#
#   iota(S) := min { [S : N_S(A)] : 1 <> A <= S abelian }  =  ilow(S)
#
# Lemma SP and its proof: see v_task39_sporadic_iota.g header (verbatim).
# The recursion is run top-down over CTblLib `Maxes`; where a table has no
# stored Maxes a valid LOWER bound is substituted, so `lowbound` is always a
# genuine lower bound and `iota` (smallest index of a maximal subgroup with
# F <> 1) is always a genuine UPPER bound.  For Phase 2 of v_task50 the
# UPPER bound is what is needed (it makes the kill test conservative).

LoadPackage("ctbllib");;

memo := rec();

ilow := function(ct, cap)
  local key, best, m, mt, idx, r;
  key := Identifier(ct);
  if IsBound(memo.(key)) then return memo.(key); fi;
  if Size(ct) = 1 then return infinity; fi;
  if not HasMaxes(ct) then return 2; fi;
  best := infinity;
  for m in Maxes(ct) do
    mt := CharacterTable(m);
    if mt = fail then continue; fi;
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

names := ["U3(3)","A5","A6","A7","A8","A9","A10","A11","A12",
          "L2(8)","L2(11)","L2(13)","L2(16)","L2(17)","L2(19)","L2(23)",
          "L2(25)","L2(27)","L2(29)","L2(31)","L2(32)","L2(47)","L2(49)",
          "L2(64)","L2(125)",
          "L3(2)","L3(3)","L3(4)","L3(5)","L3(16)","L4(3)","L4(4)",
          "L5(2)","L5(4)","L6(2)","L6(4)",
          "U3(4)","U3(5)","U3(8)","U4(3)","U4(4)","U4(8)","U5(2)","U6(2)",
          "S4(3)","S4(4)","S4(5)","S4(8)","S6(2)","S6(3)","S6(4)","S8(2)",
          "S10(2)","O7(3)","O8+(2)","O8-(2)","O10+(2)","O10-(2)","O12+(2)",
          "Sz(8)","3D4(2)","G2(4)","F4(2)","2F4(2)'",
          "M11","M12","M22","M23","M24","J1","J2","J3","HS"];;

for nm in names do
  t := CharacterTable(nm);
  if t = fail then Print("MISSING ", nm, "\n"); continue; fi;
  if not HasMaxes(t) then
    Print("NOMAXES ", nm, "  order ", Size(t), "\n"); continue; fi;
  good := [];
  for s in Maxes(t) do
    ct := CharacterTable(s);
    if ct = fail then continue; fi;
    if ClassPositionsOfFittingSubgroup(ct) <> [1] then
      Add(good, [Size(t)/Size(ct), s]);
    fi;
  od;
  Sort(good);
  lb := ilow(t, 10^40);
  Print("IOTA ", nm, " ", Size(t), " ", good[1][1], " ", lb, " ",
        lb = good[1][1], " ", good[1][2], "\n");
od;

QUIT;
