# v_task20_a10_rank_probe.g -- FEASIBILITY PROBE only: how expensive is
# ConjugacyClassesSubgroups on the two order-1814400 groups tied at
# mult1=4 (A10 and its twin#2 = S6 x A7)?  Timing/class-count only, no
# character-orbit work yet -- decide whether the full DRingInvariants
# rank computation (v_task4_rationality.g engine) is tractable before
# committing to it.

Print("=== A10, |A10|=1814400: ConjugacyClassesSubgroups timing probe ===\n");
G1 := AlternatingGroup(10);;
t0 := Runtime();;
cls1 := ConjugacyClassesSubgroups(G1);;
Print("A10: ", Length(cls1), " subgroup conjugacy classes, time(ms)=", Runtime()-t0, "\n");

Print("\n=== twin#2 = S6 x A7, |T|=1814400: ConjugacyClassesSubgroups timing probe ===\n");
G2 := DirectProduct(SymmetricGroup(6), AlternatingGroup(7));;
t0 := Runtime();;
cls2 := ConjugacyClassesSubgroups(G2);;
Print("S6xA7: ", Length(cls2), " subgroup conjugacy classes, time(ms)=", Runtime()-t0, "\n");

Print("=== DONE rank_probe ===\n");
