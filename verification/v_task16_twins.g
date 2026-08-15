#!/usr/bin/env gap -q
# v_task16: for the 5 sporadic groups flagged FACTORIZATION in v_task15
# (M22, M24, J2, Suz, Th), check whether the arithmetic order-twin actually
# EXISTS as a genuine group (c must embed as an actual subgroup of
# Out(socle) = prod_i Out(S_i), not just satisfy c | |Out(socle)| as a
# number), and if it exists, separate it from the sporadic by cheap
# invariants (class count, involution count).
#
# Existence argument used per pair (checked/printed below):
#   - M22: socle L2(7)xL2(11), Out(socle)=C2xC2 (order 4). c=4 = the WHOLE
#     group Out(socle) -- trivially "embeds" as itself (elementary abelian
#     C2xC2, NOT cyclic C4 -- C4 does not embed in C2xC2, but we don't need
#     it to: the realized extension is the full elementary-abelian one).
#     Concrete witness: Aut(L2(7)) x Aut(L2(11)) = PGL(2,7) x PGL(2,11)
#     = L2(7).2 x L2(11).2.
#   - J2: socle A5xA7, Out(socle)=C2xC2, c=4=whole group, same argument.
#     Witness: Aut(A5) x Aut(A7) = S5 x S7 = A5.2 x A7.2.
#   - Suz: socle L3(3)xA11, Out(socle)=C2xC2, c=4=whole group, same
#     argument. Witness: Aut(L3(3)) x Aut(A11) = L3(3).2 x A11.2 (=S11).
#   - M24: socle L2(23)xA8, Out(socle)=C2xC2 (order 4). c=2: ANY group of
#     even order has a subgroup of order 2 (Cauchy), and C2xC2 concretely
#     has three: witnesses (a) L2(23).2 x A8 (extend factor 1 only),
#     (b) L2(23) x A8.2 (extend factor 2 only). [a third "diagonal"
#     embedding also exists as a fiber-product subgroup of L2(23).2xA8.2
#     of index 2; not constructed here, but its existence needs no separate
#     argument since (a)/(b) already witness existence of SOME order-2
#     extension.]
#   - Th: socle L3(3)xL2(125)xU3(8), Out(socle) = C2 x C6 x (S3x3), order
#     2*6*18=216. c=3: 3 | 216, so by Cauchy's theorem Out(socle) (a group
#     of order 216) has an element of order 3, hence a subgroup of order 3
#     -- existence needs no structural subtlety here since c is prime.
#     Witness used: L3(3) x L2(125) x U3(8).3_1 (extend the U3(8) factor
#     only, by one of the three ATLAS-distinct order-3 subgroups of its
#     Out = S3x3).
#
# All witnesses are built as PRODUCTS OF LIBRARY CHARACTER TABLES
# (CTblLib), and Size() is checked against the sporadic's own order as a
# hard correctness gate before any invariant is trusted.

InvolutionCount := function(t)
    local ords, sizes, i, tot;
    ords := OrdersClassRepresentatives(t);
    sizes := SizesConjugacyClasses(t);
    tot := 0;
    for i in [1..Length(ords)] do
        if ords[i] = 2 then
            tot := tot + sizes[i];
        fi;
    od;
    return tot;
end;;

Report := function(label, sporadicName, twinLabel, twinTable)
    local sp, spOrd, twOrd, spClasses, twClasses, spInv, twInv;
    Print("\n=== ", label, " ===\n");
    sp := CharacterTable(sporadicName);
    spOrd := Size(sp);
    twOrd := Size(twinTable);
    Print("Sporadic: ", sporadicName, "  order=", spOrd, "\n");
    Print("Twin:     ", twinLabel, "  order=", twOrd, "\n");
    if spOrd <> twOrd then
        Print("*** ORDER MISMATCH -- witness invalid! ***\n");
        return fail;
    fi;
    Print("Order match: OK (", spOrd, " = ", twOrd, ")\n");
    spClasses := NrConjugacyClasses(sp);
    twClasses := NrConjugacyClasses(twinTable);
    spInv := InvolutionCount(sp);
    twInv := InvolutionCount(twinTable);
    Print("NrConjugacyClasses: sporadic=", spClasses, "  twin=", twClasses,
          "  ", (spClasses<>twClasses), "-> DIFFER=", spClasses<>twClasses, "\n");
    Print("InvolutionCount:    sporadic=", spInv, "  twin=", twInv,
          "  DIFFER=", spInv<>twInv, "\n");
    if spClasses <> twClasses or spInv <> twInv then
        Print("VERDICT: SEPARATED (class-count and/or involution-count differ)\n");
    else
        Print("VERDICT: UNSEPARATED by these invariants -- need conductor-1 count\n");
    fi;
    return rec(spClasses:=spClasses, twClasses:=twClasses, spInv:=spInv, twInv:=twInv);
end;;

Print("###################################################################\n");
Print("# v_task16: order-twin EXISTENCE + separation for the 5 sporadics\n");
Print("# flagged FACTORIZATION in v_task15\n");
Print("###################################################################\n");

# ---------------------------------------------------------------------
# M22 : socle L2(7) x L2(11), c=4 = |Out(socle)| = |C2 x C2|
# ---------------------------------------------------------------------
t := CharacterTable("L2(7).2") * CharacterTable("L2(11).2");;
Report("M22 vs (L2(7)xL2(11)) order-twin", "M22",
       "L2(7).2 x L2(11).2  [= PGL(2,7) x PGL(2,11)]", t);;

# ---------------------------------------------------------------------
# J2 : socle A5 x A7, c=4 = |Out(socle)| = |C2 x C2|
# ---------------------------------------------------------------------
t := CharacterTable("A5.2") * CharacterTable("A7.2");;
Report("J2 vs (A5xA7) order-twin", "J2",
       "A5.2 x A7.2  [= S5 x S7]", t);;

# ---------------------------------------------------------------------
# Suz : socle L3(3) x A11, c=4 = |Out(socle)| = |C2 x C2|
# ---------------------------------------------------------------------
t := CharacterTable("L3(3).2") * CharacterTable("A11.2");;
Report("Suz vs (L3(3)xA11) order-twin", "Suz",
       "L3(3).2 x A11.2  [= Aut(L3(3)) x S11]", t);;

# ---------------------------------------------------------------------
# M24 : socle L2(23) x A8, c=2 (a subgroup of order 2 of Out=C2xC2;
# two independent witnesses -- extend one factor at a time)
# ---------------------------------------------------------------------
t := CharacterTable("L2(23).2") * CharacterTable("A8");;
Report("M24 vs (L2(23)xA8) order-twin, witness (a)", "M24",
       "L2(23).2 x A8", t);;

t := CharacterTable("L2(23)") * CharacterTable("A8.2");;
Report("M24 vs (L2(23)xA8) order-twin, witness (b)", "M24",
       "L2(23) x A8.2  [= L2(23) x S8]", t);;

# ---------------------------------------------------------------------
# Th : socle L3(3) x L2(125) x U3(8), c=3 (a subgroup of order 3 of
# Out(socle) = C2 x C6 x (S3x3), order 216; witness extends the U3(8)
# factor only by one of its three ATLAS order-3 subgroups)
# ---------------------------------------------------------------------
t := CharacterTable("L3(3)") * CharacterTable("L2(125)") * CharacterTable("U3(8).3_1");;
Report("Th vs (L3(3)xL2(125)xU3(8)) order-twin", "Th",
       "L3(3) x L2(125) x U3(8).3_1", t);;

Print("\n###################################################################\n");
Print("# END v_task16\n");
Print("###################################################################\n");
