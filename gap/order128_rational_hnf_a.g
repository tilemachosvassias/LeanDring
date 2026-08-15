# Parallel half A of the exact rational HNF/dual-functional extraction.
Read("results/order128_pairs/g128_1597_1598_rational_matrices.g");;
Print("computing untransported HNF A\n");
HA0 := Filtered(HermiteNormalFormIntegerMat(MA0), r -> not IsZero(r));;
out := OutputTextFile("results/order128_pairs/g128_1597_rational_hnf.g", false);;
SetPrintFormattingStatus(out, false);;
AppendTo(out, "HA0 := ", HA0, ";;\n");;
CloseStream(out);;
Print("HNF A saved: ", Length(HA0), " rows\n");
QUIT;
