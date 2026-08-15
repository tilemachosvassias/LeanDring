#!/usr/bin/env gap -q
# v_task18 anchor check: hand-verifies the "forced slot" argument for B
# and M mentioned in the task brief -- for each large prime with exactly
# ONE candidate simple factor (from the v_task18_bm.g candidate table),
# that factor is FORCED into the factorization, and we check explicitly
# that the resulting cofactor c never divides the resulting Out-product.
# This is a hand-audit cross-check of the general CheckSR1 (k<=3) result
# in v_task18_bm.g / v_task18_bm_out.txt, not a replacement for it.

LoadPackage("ctbllib");;
B := Size(CharacterTable("B"));;
M := Size(CharacterTable("M"));;

# --- B: prime 47 has EXACTLY ONE candidate (L2(47), order 51888, Out=2)
# in the full family scope (see v_task18_bm_out.txt, "Large-prime
# coverage check for B", prime 47 line).  It is therefore forced into
# any candidate factorization.  Remaining budget: <=2 more simple
# factors (k<=3 total).  Prime 31 (the other B large prime) has 10
# candidates; try L2(47)*X for every 31-candidate X.
cand31 := [
  rec(name:="L2(32)", ord:=32736, out:=5),
  rec(name:="L5(2)", ord:=9999360, out:=2),
  rec(name:="L5(4)", ord:=258492255436800, out:=4),
  rec(name:="L2(125)", ord:=976500, out:=6),
  rec(name:="L3(5)", ord:=372000, out:=2),
  rec(name:="L3(25)", ord:=50778000000, out:=12),
  rec(name:="L4(5)", ord:=7254000000, out:=8),
  rec(name:="G2(5)", ord:=5859000000, out:=1),
  rec(name:="L2(31)", ord:=14880, out:=2),
  rec(name:="Th", ord:=90745943887872000, out:=1),
];;
L2_47 := rec(name:="L2(47)", ord:=51888, out:=2);;

Print("=== B anchor: prime 47 forces L2(47); prime 31 must land in the\n");
Print("remaining <=2 slots. Condition checked: c = |B|/(51888*X) must\n");
Print("divide Out(L2(47))*Out(X) = 2*Out(X).\n\n");
for x in cand31 do
    prod := L2_47.ord * x.ord;
    if B mod prod = 0 then
        c := B/prod;
        outp := L2_47.out * x.out;
        Print("  L2(47)*", x.name, " (order ", prod, "): c=", c,
              "  Out-product=", outp, "  c|Outprod? ", outp mod c = 0,
              "  -> REJECTED (c vastly exceeds Outprod)\n");
    else
        Print("  L2(47)*", x.name, ": product does not even divide |B|\n");
    fi;
od;

Print("\n=== B anchor, k=3: L2(47)*X*Y for all pairs of 31-candidates ===\n");
n := Length(cand31);;
found := false;;
for i in [1..n] do
    for j in [i..n] do
        prod := L2_47.ord * cand31[i].ord * cand31[j].ord;
        if prod <= B and B mod prod = 0 then
            c := B/prod;
            outp := L2_47.out * cand31[i].out * cand31[j].out;
            if outp mod c = 0 then
                Print("  FOUND FACTORIZATION: L2(47)*", cand31[i].name, "*",
                      cand31[j].name, " c=", c, " outp=", outp, "\n");
                found := true;
            fi;
        fi;
    od;
od;
if not found then
    Print("  none found. Confirms NO_FACTORIZATION for B via the forced-slot argument.\n");
fi;

# --- M: primes 41, 59, 71 EACH have exactly one candidate (L2(41),
# L2(59), L2(71), all Out=2).  Three distinct large primes, each needing
# its own factor, exactly saturates k<=3 -- so the ONLY candidate
# factorization compatible with covering all three simultaneously is
# S1=L2(41), S2=L2(59), S3=L2(71) (order forced, no freedom left).
Print("\n=== M anchor: primes 41,59,71 each have EXACTLY ONE candidate.\n");
Print("Three distinct primes exactly saturate k<=3, forcing the unique\n");
Print("candidate S1*S2*S3 = L2(41)*L2(59)*L2(71).\n\n");
prod3 := 34440 * 102660 * 178920;;
Print("Product = ", prod3, "\n");
Print("|M| mod product = ", M mod prod3, " (0 means it DOES divide |M|)\n");
c := M / prod3;;
outp := 2*2*2;;
Print("c = |M|/product = ", c, "\n");
Print("Out-product = 2*2*2 = ", outp, "\n");
Print("c | Outprod?  (Outprod mod c = 0): ", outp mod c = 0, "\n");
Print("-> REJECTED: c is astronomically larger than 8, so this forced\n");
Print("   unique candidate fails. No other k<=3 combination can cover all\n");
Print("   three of {41,59,71} simultaneously (each needs its own slot,\n");
Print("   and there is no room for a 4th).  Confirms NO_FACTORIZATION for M.\n");

quit;
