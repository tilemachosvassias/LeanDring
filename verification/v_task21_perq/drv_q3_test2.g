Q := 3;;
#
# v_task21_tbc.g
#
# Empirical skeleton of theorem T-BC: perfect maximal subgroup counts of
# PSp(6,q) versus Omega(7,q) for odd prime powers q.
#
# Method:
#  ms := ClassicalMaximalsGeneric("S", 6, q)   -- maximal subgroups of quasisimple Sp(6,q),
#                                                  center Z = <-One> of order 2 (q odd).
#  mo := ClassicalMaximalsGeneric("O", 7, q)   -- maximal subgroups of quasisimple Omega(7,q),
#                                                  trivial center.
#
# For each maximal M we need [M:M'] (M' = DerivedSubgroup(M)) and, when [M:M']=2,
# whether Z <= M'.  Direct GAP DerivedSubgroup()/Index() on these matrix groups
# uses generic BSGS methods whose cost explodes with |M| (calibration: q=13's
# largest Sp(6,q)-maximal, |M| ~ 6.1e17, exhausted a 10GB memory cap after several
# minutes without finishing; q=11, |M| ~ 4.1e16, took 177s; q=9, |M| ~ 1.6e15, took 48s).
# This is infeasible for q up to 125 where several maximals have |M| ~ q^14 or larger
# (e.g. the G2(q)-order maximals of O7(q) alone have order q^6(q^6-1)(q^2-1)).
#
# Instead we use the `recog` package (matrix group constructive recognition, complexity
# governed by dimension and log(q), not by |G|) to certify [M:M'] EXACTLY via a
# deterministic fixed-point computation of the derived subgroup as a normal closure:
#   M' = normal closure in M of {[g_i,g_j] : g_i,g_j generators of M}
# (standard fact: the normal closure of the generator-pairwise-commutators of any
# generating set equals the full derived subgroup).  We build up a generating set H
# for M', and repeatedly check via recog's fast constructive membership test
# (SLPforElement) whether conjugating each generator of H by each generator of M
# stays inside H; any failures are added as new generators and we iterate to a
# fixed point.  Once no new generators are needed, H is verified NORMAL in M and
# contains the generator-commutators, hence H = M' exactly (not a heuristic).
# recog's Size(ri) then gives |M'| directly from the recognition tree (no BSGS
# on the natural module needed).
#
# Cross-validated against plain GAP DerivedSubgroup()/Index() for q=3 (S,6,3 and
# O,7,3): all indices and Z-membership verdicts matched exactly.
#
# ClassicalMaximals is not part of the standard GAP distribution.  Point
# CLASSICAL_MAXIMALS_PATH at a checkout of it before running this script;
# if it is installed as an ordinary GAP package, leave it unbound.
if IsBound(CLASSICAL_MAXIMALS_PATH) then
  SetPackagePath("ClassicalMaximals", CLASSICAL_MAXIMALS_PATH);
fi;
LoadPackage("ClassicalMaximals");
LoadPackage("recog");
SetInfoLevel(InfoRecog, 0);
SetInfoLevel(InfoClassicalMaximals, 0);

# Prevent GAP's interactive break loop on internal errors (recog occasionally
# hits hard errors, e.g. "Orbit too long" / usage errors, on certain inputs).
# Without this, an uncaught error under `gap -q < script` drops into a break
# loop that then consumes the REST OF THE SCRIPT as debugger commands,
# silently corrupting all subsequent computation. With BreakOnError := false,
# an uncaught Error() aborts only the current top-level statement and cleanly
# resumes reading the next one.
BreakOnError := false;;

# Safe wrappers: catch hard errors from recog and turn them into `fail`
# instead of entering (or, worse, un-entering) a break loop.
SafeRecognise := function(G)
    local r;
    r := CALL_WITH_CATCH(RecogniseGroup, [G]);
    if r[1] = true then return r[2]; else return fail; fi;
end;;

SafeSLP := function(ri, g)
    local r;
    r := CALL_WITH_CATCH(SLPforElement, [ri, g]);
    if r[1] = true then return r[2]; else return fail; fi;
end;;

# ---------------------------------------------------------------------------
# DerivedIndexRecog(M): exact [M:M'] via recog, with a per-M wall-clock budget.
# Returns a record:
#   ok=true:  sizeM, sizeD, idx, rounds, zInD (membership of -One(M) in M'),
#             tmsec
#   ok=false: reason in {"TIMEOUT","ROUNDCAP","RECOG_FAIL"}, rounds, tmsec
# ---------------------------------------------------------------------------
BudgetMsPerM := 180000;;  # 3 minutes per maximal subgroup

DerivedIndexRecog := function(M)
    local gens, comms, i, j, Hgens, mgens, ri, changed, newgens, h, g, img,
          rounds, zelt, zmem, sz, t0, elapsed, roundcap, reason, recogFails,
          maxRecogFails;
    t0 := Runtime();;
    gens := GeneratorsOfGroup(M);;
    mgens := gens;;
    comms := [];;
    for i in [1..Length(gens)] do
        for j in [1..Length(gens)] do
            if i <> j then Add(comms, Comm(gens[i], gens[j])); fi;
        od;
    od;
    Hgens := ShallowCopy(comms);;
    changed := true;; rounds := 0;; ri := fail;; roundcap := 25;; reason := "";;
    recogFails := 0;; maxRecogFails := 3;;
    while changed do
        rounds := rounds + 1;;
        if rounds > roundcap then reason := "ROUNDCAP"; break; fi;
        elapsed := Runtime() - t0;;
        if elapsed > BudgetMsPerM then reason := "TIMEOUT"; break; fi;
        ri := SafeRecognise(Group(Hgens));
        if ri = fail then
            recogFails := recogFails + 1;;
            if recogFails > maxRecogFails then
                reason := "RECOG_FAIL";
                break;
            fi;
            rounds := rounds - 1;; # retry doesn't count as progress
            continue;
        fi;
        newgens := [];; changed := false;;
        for g in mgens do
            for h in Hgens do
                img := h^g;
                if SafeSLP(ri, img) = fail then
                    Add(newgens, img); changed := true;;
                fi;
            od;
        od;
        elapsed := Runtime() - t0;;
        if elapsed > BudgetMsPerM then reason := "TIMEOUT"; changed := false; break; fi;
        if changed then Hgens := Concatenation(Hgens, newgens); fi;
    od;
    if reason <> "" then
        return rec(ok := false, reason := reason, rounds := rounds,
                    tmsec := Runtime() - t0, sizeM := Size(M));
    fi;
    sz := Size(ri);;
    zelt := -One(M);;
    zmem := (SafeSLP(ri, zelt) <> fail);;
    return rec(ok := true, sizeM := Size(M), sizeD := sz, idx := Size(M)/sz,
                rounds := rounds, zInD := zmem, tmsec := Runtime() - t0);
end;;

G2Order := function(q)
    return q^6 * (q^6 - 1) * (q^2 - 1);
end;;

# Perfectness verdict downstairs, given idx=[M:M'] and (if idx=2) whether Z<=M'.
# S-type (PSp6(q), |Z|=2): perfect iff idx=1, or idx=2 and Z not<=M'.
# O-type (Omega7(q), |Z|=1): perfect iff idx=1.
PerfectVerdictS := function(res)
    if not res.ok then return "UNKNOWN"; fi;
    if res.idx = 1 then return true; fi;
    if res.idx = 2 and not res.zInD then return true; fi;
    return false;
end;;

PerfectVerdictO := function(res)
    if not res.ok then return "UNKNOWN"; fi;
    return res.idx = 1;
end;;

ProcessList := function(label, ms, verdictFn, q)
    local i, M, res, ord, verdict, isG2;
    Print("--- ", label, " q=", q, "  count=", Length(ms), " ---\n");
    for i in [1..Length(ms)] do
        M := ms[i];;
        ord := Size(M);;
        isG2 := (ord = G2Order(q));;
        res := DerivedIndexRecog(M);;
        if res.ok then
            verdict := verdictFn(res);;
            Print(label, "_M", i, ": |M|=", ord, "  [M:M']=", res.idx,
                  "  zInD=", res.zInD, "  perfect=", verdict,
                  "  isG2order=", isG2, "  rounds=", res.rounds,
                  "  t=", res.tmsec, "ms\n");
        else
            Print(label, "_M", i, ": |M|=", ord, "  DERIVED_FAILED reason=",
                  res.reason, "  rounds=", res.rounds, "  isG2order=", isG2,
                  "  t=", res.tmsec, "ms\n");
        fi;
    od;
end;;

# ---------------------------------------------------------------------------
# Main sweep. Q is read from the environment via GAP command line
# (set by the driver shell script as: Q := <value>;; )
# ---------------------------------------------------------------------------
if not IsBound(Q) then
    Print("ERROR: Q not bound. Use the driver script.\n");
    QUIT;
fi;

q := Q;;
Print("=== q = ", q, " ===\n");
Print("q mod 4 = ", q mod 4, "  q mod 3 = ", q mod 3, "  IsPrimeInt(q) = ",
      IsPrimeInt(q), "  Factors(q) = ", Factors(q), "\n");

tS0 := Runtime();;
ms := ClassicalMaximalsGeneric("S", 6, q);;
Print("S,6,", q, ": generated ", Length(ms), " maximals in ",
      Runtime()-tS0, "ms\n");
ProcessList("S", ms, PerfectVerdictS, q);

tO0 := Runtime();;
mo := ClassicalMaximalsGeneric("O", 7, q);;
Print("O,7,", q, ": generated ", Length(mo), " maximals in ",
      Runtime()-tO0, "ms\n");
ProcessList("O", mo, PerfectVerdictO, q);

Print("=== END q = ", q, " ===\n");
QUIT;
