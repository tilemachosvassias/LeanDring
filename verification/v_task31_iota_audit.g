## v_task31_iota_audit.g
## Audit I(S) = {[S:N_S(A)] : 1 != A <= S abelian} at every exceptional
## isomorphism listed in NOTES.md Even/§4at "A defect in Lemma ι-μ":
##   S4(3) = U4(2), L4(2) = A8, S4(2)' = A6, L3(2) = L2(7),
##   G2(2)' = U3(3), L2(4) = L2(5) = A5, L2(9) = A6.
##
## Method: enumerate ConjugacyClassesSubgroups(S), keep nontrivial abelian
## reps, compute Index(S, Normalizer(S,A)), collect the set of indices,
## report the smallest few and the true iota = Minimum of that set.

IotaSet := function(G, label)
    local ccs, c, A, idx, seen, name;
    name := StructureDescription(G);
    Print("\n=== ", label, "  (order ", Size(G), ", ", name, ") ===\n");
    ccs := ConjugacyClassesSubgroups(G);
    seen := [];
    for c in ccs do
        A := Representative(c);
        if Size(A) > 1 and IsAbelian(A) then
            idx := Index(G, Normalizer(G, A));
            AddSet(seen, idx);
        fi;
    od;
    Print("I(S) sorted (all distinct values found): ", seen, "\n");
    if Length(seen) > 0 then
        Print("iota_true = ", Minimum(seen), "\n");
    fi;
    return seen;
end;;

# --- helper: does C(n,3) = m*val have a solution for n in [3..bound], m in {1,2} ---
CheckNewSolutions := function(val, bound)
    local n, m, C;
    Print("Checking C(n,3) = m*", val, " for m in {1,2}, n <= ", bound, ":\n");
    for m in [1,2] do
        for n in [3..bound] do
            C := n*(n-1)*(n-2)/6;
            if C = m*val then
                Print("  FOUND: m=", m, ", n=", n, ", C(n,3)=", C, "\n");
            fi;
            if C > m*val then
                break;
            fi;
        od;
    od;
end;;

BOUND := 1000000;

# 1. S4(3) = U4(2), order 25920 -- reference check, already done in v_task29
G := SP(4,3);
G := FactorGroup(G, Center(G));  # PSp(4,3), the simple group S4(3)
S := Image(IsomorphismPermGroup(G));
iset := IotaSet(S, "S4(3) ~ U4(2)  [order 25920]");
CheckNewSolutions(Minimum(iset), BOUND);

# 2. L4(2) = A8, order 20160
G := AlternatingGroup(8);
iset := IotaSet(G, "L4(2) ~ A8  [order 20160]");
CheckNewSolutions(Minimum(iset), BOUND);

# 3. S4(2)' = A6, order 360
G := AlternatingGroup(6);
iset := IotaSet(G, "S4(2)' ~ A6  [order 360]");
CheckNewSolutions(Minimum(iset), BOUND);

# 4. L3(2) = L2(7), order 168
G := PSL(3,2);
S := Image(IsomorphismPermGroup(G));
iset := IotaSet(S, "L3(2) ~ L2(7)  [order 168]");
CheckNewSolutions(Minimum(iset), BOUND);

# 5. G2(2)' = U3(3), order 6048
G := PSU(3,3);
S := Image(IsomorphismPermGroup(G));
iset := IotaSet(S, "G2(2)' ~ U3(3)  [order 6048]");
CheckNewSolutions(Minimum(iset), BOUND);

# 6. L2(4) = L2(5) = A5, order 60
G := AlternatingGroup(5);
iset := IotaSet(G, "L2(4) ~ L2(5) ~ A5  [order 60]");
CheckNewSolutions(Minimum(iset), BOUND);

# 7. L2(9) = A6, order 360 -- same group as case 3, list again for completeness
G := AlternatingGroup(6);
iset := IotaSet(G, "L2(9) ~ A6  [order 360, same group as S4(2)']");
CheckNewSolutions(Minimum(iset), BOUND);

Print("\n=== DONE ===\n");
QUIT;
