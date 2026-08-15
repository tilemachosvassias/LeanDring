# v_task17_coprimality_checks.g -- the arithmetic facts underlying the
# Goursat "no diagonal" arguments for Suz and Th (and the M24 cases,
# which were also confirmed by direct brute-force census). A perfect
# subgroup U2 of a group K can only witness a Goursat diagonal quotient
# Q (of order |Q|) if |Q| divides |K| (Lagrange); if a prime p | |Q| but
# p does not divide |K| at all, no such U2 can exist.

Print("Suz: L3(3).2 x S11 -- does 13 divide |S11| = 11! ?\n");
Print("  |L3(3)| = ", Size(PSL(3,3)), "  13 | |L3(3)|: ", Size(PSL(3,3)) mod 13 = 0, "\n");
Print("  |S11| = ", Factorial(11), "  13 | |S11|: ", Factorial(11) mod 13 = 0, "\n");

Print("\nM24(a): L2(23).2 x A8 -- does 23 divide |A8|?\n");
Print("  |L2(23)| = ", Size(PSL(2,23)), "  23 | |L2(23)|: ", Size(PSL(2,23)) mod 23 = 0, "\n");
Print("  |A8| = ", Size(AlternatingGroup(8)), "  23 | |A8|: ", Size(AlternatingGroup(8)) mod 23 = 0, "\n");

Print("\nM24(b): L2(23) x S8 -- does 23 divide |S8|?\n");
Print("  |S8| = ", Size(SymmetricGroup(8)), "  23 | |S8|: ", Size(SymmetricGroup(8)) mod 23 = 0, "\n");

Print("\nTh: L2(125) x U3(8).3 -- does 31 divide |U3(8).3|?\n");
Print("  |L2(125)| = ", Size(PSL(2,125)), "  31 | |L2(125)|: ", Size(PSL(2,125)) mod 31 = 0, "\n");
Print("  |U3(8).3| = 16547328  31 | |U3(8).3|: ", 16547328 mod 31 = 0, "\n");

Print("\nAlso: |L3(3)| = ", Size(PSL(3,3)), " = 2^4.3^3.13 (13 is the private prime)\n");
Print("|U3(8)| computed = 2^9 * 3^4 * 7 * 19 = ", 2^9*3^4*7*19, "  (matches PSU(3,8) order? ", 2^9*3^4*7*19 = Size(PSU(3,8)), ")\n");
Print("|U3(8).3| = 3 * that = ", 3*2^9*3^4*7*19, "\n");

Print("\n=== DONE coprimality_checks ===\n");
