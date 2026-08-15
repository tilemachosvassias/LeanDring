Q := 37;; TYPESTR := "S";; IDXV := 7;;
#
# v_task21_one.g -- process ONE maximal subgroup: type S or O, dimension n,
# field q, index IDX into ClassicalMaximalsGeneric(...) list. Prints one
# result line. Meant to be run under an external `timeout` so a pathological
# recog method (unbounded orbit growth etc.) can be killed without losing
# the rest of the sweep. Bound vars: Q, TYPESTR ("S"/"O"), IDXV (integer).
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
BreakOnError := false;;

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

G2Order := function(q)
    return q^6 * (q^6 - 1) * (q^2 - 1);
end;;

DerivedIndexRecog := function(M)
    local gens, comms, i, j, Hgens, mgens, ri, changed, newgens, h, g, img,
          rounds, zelt, zmem, sz, roundcap, reason, recogFails, maxRecogFails;
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
        ri := SafeRecognise(Group(Hgens));
        if ri = fail then
            recogFails := recogFails + 1;;
            if recogFails > maxRecogFails then reason := "RECOG_FAIL"; break; fi;
            rounds := rounds - 1;;
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
        if changed then Hgens := Concatenation(Hgens, newgens); fi;
    od;
    if reason <> "" then
        return rec(ok := false, reason := reason, rounds := rounds, sizeM := Size(M));
    fi;
    sz := Size(ri);;
    zelt := -One(M);;
    zmem := (SafeSLP(ri, zelt) <> fail);;
    return rec(ok := true, sizeM := Size(M), sizeD := sz, idx := Size(M)/sz,
                rounds := rounds, zInD := zmem);
end;;

if not IsBound(Q) or not IsBound(TYPESTR) or not IsBound(IDXV) then
    Print("ERROR: Q/TYPESTR/IDXV not bound\n");
    QUIT;
fi;

q := Q;;
if TYPESTR = "S" then
    ms := ClassicalMaximalsGeneric("S", 6, q);;
else
    ms := ClassicalMaximalsGeneric("O", 7, q);;
fi;

if IDXV > Length(ms) then
    Print("ERROR: IDXV out of range\n");
    QUIT;
fi;

M := ms[IDXV];;
ord := Size(M);;
isG2 := (ord = G2Order(q));;
res := DerivedIndexRecog(M);;
if res.ok then
    Print("RESULT ", TYPESTR, " q=", q, " idx=", IDXV, " sizeM=", ord,
          " index=", res.idx, " zInD=", res.zInD, " isG2order=", isG2,
          " rounds=", res.rounds, "\n");
else
    Print("RESULT ", TYPESTR, " q=", q, " idx=", IDXV, " sizeM=", ord,
          " FAILED reason=", res.reason, " isG2order=", isG2,
          " rounds=", res.rounds, "\n");
fi;
QUIT;
