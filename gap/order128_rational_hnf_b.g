# Parallel half B of the exact rational HNF/dual-functional extraction.
Read("results/order128_pairs/g128_1597_1598_rational_matrices.g");;
Print("computing untransported HNF B\n");
HB := Filtered(HermiteNormalFormIntegerMat(MB), r -> not IsZero(r));;
out := OutputTextFile("results/order128_pairs/g128_1598_rational_hnf.g", false);;
SetPrintFormattingStatus(out, false);;
AppendTo(out, "HB := ", HB, ";;\n");;
CloseStream(out);;
Print("HNF B saved: ", Length(HB), " rows\n");
QUIT;
