# Exact EDM comparison for matrices extracted from the independent generic
# DExport files g256_174{1,2}_generic.txt.

Read("results/order256_t4_pairs/dfmat_1741_generic.g");;
ed1 := Filtered(ElementaryDivisorsMat(DFMAT), x -> x <> 0);;
Unbind(DFMAT);;
GASMAN("collect");
Print("GENERIC_DIRECT_DF_SNF 256,1741 rank ", Length(ed1), " ",
      Collected(ed1), "\n");

Read("results/order256_t4_pairs/dfmat_1742_generic.g");;
ed2 := Filtered(ElementaryDivisorsMat(DFMAT), x -> x <> 0);;
Print("GENERIC_DIRECT_DF_SNF 256,1742 rank ", Length(ed2), " ",
      Collected(ed2), "\n");

if ed1 = ed2 then
  Print("GENERIC_DIRECT_DF_VERDICT 1741,1742 AGREE\n");
else
  Print("GENERIC_DIRECT_DF_VERDICT 1741,1742 DIFFER\n");
fi;
QUIT;
