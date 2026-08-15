# v_task81_iota.g
# ADVERSARIAL INDEPENDENT RE-VERIFICATION of iota-values.
# Written from scratch; does not read or reuse v_task39_sporadic_iota.g or
# v_task50_sporadic_twins.g.
#
# DEFINITIONS (as re-derived here):
#   ind*(H) := [G:N_G(H)] * |H'|      for 1 <> H <= G
#   iota(G) := min over 1 <> H <= G of ind*(H)
#
#   ilow(X) := min{ [X:N] : N <= X, F(N) <> 1 }        (F = Fitting subgroup)
#
# Elementary facts used (proved, not assumed):
#   (a) ilow(X) = min{ [X:N_X(A)] : 1 <> A <= X abelian }.
#       "<=": if A abelian <> 1 then A <| N_X(A) so F(N_X(A)) <> 1.
#       ">=": if F(N) <> 1 take A := Z(F(N)) <> 1, char in N, so N <= N_X(A).
#   (b) ilow(X) = 1 iff F(X) <> 1 (take N = X).
#   (c) If F(X) = 1 then any witness N is proper, hence contained in a maximal
#       M < X, and [X:N] = [X:M]*[M:N] >= [X:M]*ilow(M).  Conversely every
#       maximal M contributes [X:M]*ilow(M).  Hence
#          ilow(X) = min over maximal M < X of [X:M]*ilow(M).
#   Combining (b),(c):  ilow(X) = 1 if F(X) <> 1, else min_M [X:M]*ilow(M).
#
# For G non-abelian simple the project's "Lemma SP" says iota(G) = ilow(G).
# METHOD A below computes ilow from CTblLib character tables.
# METHOD B recomputes ilow from the ACTUAL GROUPS via MaximalSubgroupClassReps.
# METHOD C computes the *full* definition min over ALL H of [G:N_G(H)]*|H'|
#          from the complete subgroup lattice, for small G.
#
# Lower/upper bookkeeping: when a maximal subgroup's table is not in the
# library we cannot recurse.  We then use a PROVABLE lower bound for ilow(M)
# and record +infinity as the upper bound.  Hence lo <= ilow <= up always,
# and lo = up certifies exactness.

LoadPackage("ctbllib");;

INF := infinity;;

########################################################################
# provable lower bound for ilow(X) when F(X) = 1 and we cannot recurse
########################################################################
# Any witness N has F(N) <> 1, and F(X) = 1, so N is PROPER in X.
#  - general: [X:N] divides |X| and is > 1, so [X:N] >= least prime divisor.
#  - X simple: N is core-free, so X embeds in Sym([X:N]); hence |X| divides
#    ([X:N])!.  So [X:N] >= min{ n : |X| divides n! }.
FallbackLB := function(tbl)
  local n, f, s;
  s := Size(tbl);
  if IsSimpleCharacterTable(tbl) then
    n := 1; f := 1;
    while f mod s <> 0 do
      n := n + 1; f := f * n;
    od;
    return n;
  fi;
  return Minimum(Set(Factors(s)));
end;;

########################################################################
# METHOD A : character-table recursion
########################################################################
memoA := rec();;
fallbackLog := [];;

ilowA := function(tbl)
  local id, res, lo, up, wlo, wup, m, mt, idx, sub, clo, cup, maxs, szs, i;
  id := Identifier(tbl);
  if IsBound(memoA.(id)) then return memoA.(id); fi;
  # temporary guard against (impossible) cycles
  memoA.(id) := rec(lo := 1, up := INF, wlo := "<recursing>", wup := "");

  if ClassPositionsOfFittingSubgroup(tbl) <> [1] then
    res := rec(lo := 1, up := 1, wlo := "self (F<>1)", wup := "self (F<>1)");
    memoA.(id) := res;
    return res;
  fi;

  if not HasMaxes(tbl) then
    Add(fallbackLog, [id, Size(tbl), "no Maxes stored", FallbackLB(tbl)]);
    res := rec(lo := FallbackLB(tbl), up := INF,
               wlo := "LOWER BOUND ONLY (no Maxes)", wup := "unknown");
    memoA.(id) := res;
    return res;
  fi;

  maxs := Maxes(tbl);
  lo := INF; up := INF; wlo := "none"; wup := "none";
  for i in [1..Length(maxs)] do
    m := maxs[i];
    mt := CharacterTable(m);
    if mt = fail then
      # A maximal subgroup we cannot see at all: we cannot even bound its
      # index, so the *lower* bound for this X is destroyed.  Degrade lo to
      # the universally valid FallbackLB(X) and record it loudly.
      Add(fallbackLog, [Concatenation(id, " -> ", m), 0,
                        "MAXIMAL SUBGROUP TABLE MISSING - lo degraded", 0]);
      if FallbackLB(tbl) < lo then lo := FallbackLB(tbl); fi;
      wlo := Concatenation("degraded by missing table ", m);
      cup := INF; clo := INF;
    else
      idx := Size(tbl) / Size(mt);
      sub := ilowA(mt);
      clo := idx * sub.lo;
      if sub.up = INF then cup := INF; else cup := idx * sub.up; fi;
    fi;
    if clo < lo then lo := clo; wlo := Concatenation(m, " (index ", String(idx), ")"); fi;
    if cup < up then up := cup; wup := Concatenation(m, " (index ", String(idx), ")"); fi;
  od;
  res := rec(lo := lo, up := up, wlo := wlo, wup := wup);
  memoA.(id) := res;
  return res;
end;;

# top-level report with per-maximal breakdown
ReportA := function(name)
  local tbl, maxs, i, m, mt, idx, sub, r, bottomed, best, cup, clo;
  tbl := CharacterTable(name);
  if tbl = fail then
    Print("### ", name, " : NO CHARACTER TABLE IN LIBRARY\n\n");
    return fail;
  fi;
  Print("### ", name, "  (id=", Identifier(tbl), ", |G|=", Size(tbl),
        ", simple=", IsSimpleCharacterTable(tbl), ")\n");
  if ClassPositionsOfFittingSubgroup(tbl) <> [1] then
    Print("    F(G) <> 1  -> ilow = 1\n\n"); return 1;
  fi;
  if not HasMaxes(tbl) then
    r := ilowA(tbl);
    Print("    NO MAXES STORED -> lower bound only: ilow >= ", r.lo, "\n\n");
    return r;
  fi;
  maxs := Maxes(tbl);
  bottomed := INF;
  for i in [1..Length(maxs)] do
    m := maxs[i]; mt := CharacterTable(m);
    if mt = fail then Print("    ", m, " : TABLE MISSING\n"); continue; fi;
    idx := Size(tbl)/Size(mt);
    sub := ilowA(mt);
    if sub.up = INF then cup := INF; else cup := idx*sub.up; fi;
    clo := idx*sub.lo;
    Print("    max ", String(m, -14), " index ", String(idx, 9),
          "  F(M)<>1: ", ClassPositionsOfFittingSubgroup(mt) <> [1],
          "  ilow(M) in [", sub.lo, ",", sub.up, "]",
          "  contrib [", clo, ",", cup, "]\n");
    if ClassPositionsOfFittingSubgroup(mt) <> [1] and idx < bottomed then
      bottomed := idx;
    fi;
  od;
  r := ilowA(tbl);
  Print("  => ilow(", name, ") in [", r.lo, ", ", r.up, "]  ");
  if r.lo = r.up then Print("EXACT = ", r.lo); else Print("NOT PINNED"); fi;
  Print("\n     witness (upper): ", r.wup, "\n");
  Print("     min index of a maximal M with F(M)<>1 : ", bottomed, "\n");
  if r.lo = r.up and r.lo = bottomed then
    Print("     BOTTOMED OUT AT A MAXIMAL SUBGROUP: yes\n");
  else
    Print("     BOTTOMED OUT AT A MAXIMAL SUBGROUP: NO (deeper recursion or not pinned)\n");
  fi;
  Print("\n");
  return r;
end;;

########################################################################
# METHOD B : recursion on the ACTUAL GROUP
########################################################################
ilowB := function(G)
  local M, v, best;
  if Size(FittingSubgroup(G)) > 1 then return 1; fi;
  best := INF;
  for M in MaximalSubgroupClassReps(G) do
    v := Index(G, M) * ilowB(M);
    if v < best then best := v; fi;
  od;
  return best;
end;;

# direct "min over abelian A" version, from the full subgroup lattice
AbelianMinC := function(G)
  local cc, H, best, v;
  best := INF;
  for cc in ConjugacyClassesSubgroups(G) do
    H := Representative(cc);
    if Size(H) = 1 then continue; fi;
    if not IsAbelian(H) then continue; fi;
    v := Index(G, Normalizer(G, H));
    if v < best then best := v; fi;
  od;
  return best;
end;;

# full definition: min over ALL 1 <> H <= G of [G:N_G(H)]*|H'|
AllHMinC := function(G)
  local cc, H, best, v, wit;
  best := INF; wit := fail;
  for cc in ConjugacyClassesSubgroups(G) do
    H := Representative(cc);
    if Size(H) = 1 then continue; fi;
    v := Index(G, Normalizer(G, H)) * Size(DerivedSubgroup(H));
    if v < best then best := v; wit := H; fi;
  od;
  return [best, wit];
end;;

########################################################################
Print("======================================================================\n");
Print("PART A : ilow from CTblLib character tables (independent recursion)\n");
Print("======================================================================\n\n");

resA := rec();;
namesA := ["M22","L3(4)","Fi22","Suz","U6(2)","2F4(2)'","M11","M23","U4(2)",
           "S4(3)","L3(2)","L2(11)","A6","U3(3)","L2(13)","M24","A7","A8",
           "A5","L2(8)","L2(16)","L2(25)","L2(27)","L2(32)"];;
for nm in namesA do
  resA.(nm) := ReportA(nm);
od;

Print("\n----------------------------------------------------------------------\n");
Print("FALLBACK LOG (places where a genuine LOWER bound was substituted)\n");
Print("----------------------------------------------------------------------\n");
if Length(fallbackLog) = 0 then
  Print("  (none)\n");
else
  for e in fallbackLog do
    Print("  ", e[1], "  |G|=", e[2], "  reason: ", e[3], "  LB used: ", e[4], "\n");
  od;
fi;

Print("\n----------------------------------------------------------------------\n");
Print("SUMMARY TABLE (method A)\n");
Print("----------------------------------------------------------------------\n");
for nm in namesA do
  r := resA.(nm);
  if r = fail then
    Print(String(nm,-10), " : no table\n");
  elif IsInt(r) then
    Print(String(nm,-10), " : ", r, "\n");
  else
    Print(String(nm,-10), " : lo=", String(r.lo,9), "  up=", String(r.up,9));
    if r.lo = r.up then Print("  EXACT\n"); else Print("  NOT PINNED\n"); fi;
  fi;
od;

Print("\n======================================================================\n");
Print("PART B : ilow recomputed from the ACTUAL GROUPS (MaximalSubgroupClassReps)\n");
Print("======================================================================\n");
grpsB := [ ["A5", AlternatingGroup(5)],
           ["L3(2)", PSL(3,2)],
           ["A6", AlternatingGroup(6)],
           ["L2(11)", PSL(2,11)],
           ["L2(13)", PSL(2,13)],
           ["A7", AlternatingGroup(7)],
           ["U3(3)", PSU(3,3)],
           ["M11", MathieuGroup(11)],
           ["L2(8)", PSL(2,8)],
           ["L2(16)", PSL(2,16)],
           ["L2(25)", PSL(2,25)],
           ["L2(27)", PSL(2,27)],
           ["L2(32)", PSL(2,32)],
           ["A8", AlternatingGroup(8)],
           ["L3(4)", PSL(3,4)],
           ["U4(2)", PSU(4,2)],
           ["M12", MathieuGroup(12)],
           ["M22", MathieuGroup(22)],
           ["M23", MathieuGroup(23)],
           ["M24", MathieuGroup(24)] ];;
for pair in grpsB do
  Print(String(pair[1],-8), " |G|=", String(Size(pair[2]),12),
        "  ilowB = ", ilowB(pair[2]), "\n");
od;

Print("\n======================================================================\n");
Print("PART C : FULL definition min over ALL H of [G:N_G(H)]*|H'| (subgroup lattice)\n");
Print("         vs abelian-only min over A of [G:N_G(A)]\n");
Print("======================================================================\n");
grpsC := [ ["A5", AlternatingGroup(5)],
           ["L3(2)", PSL(3,2)],
           ["A6", AlternatingGroup(6)],
           ["L2(11)", PSL(2,11)],
           ["L2(13)", PSL(2,13)],
           ["L2(8)", PSL(2,8)],
           ["L2(16)", PSL(2,16)],
           ["A7", AlternatingGroup(7)],
           ["U3(3)", PSU(3,3)],
           ["M11", MathieuGroup(11)],
           ["L2(25)", PSL(2,25)],
           ["L2(27)", PSL(2,27)],
           ["U4(2)", PSU(4,2)] ];;
for pair in grpsC do
  a := AllHMinC(pair[2]);
  b := AbelianMinC(pair[2]);
  Print(String(pair[1],-8), " |G|=", String(Size(pair[2]),8),
        "  min over ALL H = ", String(a[1],6),
        "  (witness |H|=", Size(a[2]), ", H abelian=", IsAbelian(a[2]), ")",
        "   min over ABELIAN A = ", String(b,6),
        "   agree=", a[1] = b, "\n");
od;

Print("\n======================================================================\n");
Print("PART D : method A vs method B vs the PROJECT'S CLAIMED values\n");
Print("======================================================================\n");
# claimed values supplied by the caller; 0 = no claim made
claims := [ ["M22",77], ["L3(4)",21], ["Fi22",3510], ["Suz",22880],
            ["U6(2)",0], ["2F4(2)'",1755], ["M11",55], ["M23",253],
            ["M24",759], ["U3(3)",28], ["U4(2)",27], ["S4(3)",27],
            ["A6",10], ["A7",35], ["A8",15], ["L3(2)",7], ["L2(11)",0],
            ["L2(13)",0], ["A5",0], ["L2(8)",0], ["L2(16)",0],
            ["L2(25)",0], ["L2(27)",0], ["L2(32)",0] ];;
bvals := rec();;
for pair in grpsB do bvals.(pair[1]) := ilowB(pair[2]); od;
Print(String("group",-10), String("A.lo",10), String("A.up",10),
      String("B",10), String("claim",10), "  verdict\n");
for c in claims do
  nm := c[1]; r := resA.(nm);
  Print(String(nm,-10), String(r.lo,10), String(r.up,10));
  if IsBound(bvals.(nm)) then Print(String(bvals.(nm),10));
  else Print(String("-",10)); fi;
  if c[2] = 0 then Print(String("(none)",10)); else Print(String(c[2],10)); fi;
  Print("  ");
  # verdict
  if IsBound(bvals.(nm)) and r.lo = r.up and bvals.(nm) <> r.lo then
    Print("*** A/B MISMATCH ***");
  elif c[2] = 0 then
    Print("no claim");
  elif r.lo = r.up and r.lo = c[2] then
    Print("CONFIRMED (exact)");
  elif IsBound(bvals.(nm)) and bvals.(nm) = c[2] then
    Print("CONFIRMED via method B");
  else
    Print("*** MISMATCH WITH CLAIM ***");
  fi;
  Print("\n");
od;

Print("\nDONE\n");
QUIT;
