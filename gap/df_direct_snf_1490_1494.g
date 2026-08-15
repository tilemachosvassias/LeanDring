# df_direct_snf_1490_1494.g -- exact Z-elementary divisors of the DIRECT
# F-restricted species-table lattices of SmallGroup(128,1490/1494), from
# the matrices written by python/df_direct_snf_export.py. This certifies
# the blockwise DF-SNF separation of the pair independently of Lemma S-in-R
# (results/df_nonabelian_snf_blocks.md par. 4-5).
Read("results/order128_pairs/dfmat_1490.g");;
ed := Filtered(ElementaryDivisorsMat(DFMAT), x -> x <> 0);;
Print("DIRECT_DF_SNF 128,1490 rank ", Length(ed), " ", Collected(ed), "\n");
Read("results/order128_pairs/dfmat_1494.g");;
ed := Filtered(ElementaryDivisorsMat(DFMAT), x -> x <> 0);;
Print("DIRECT_DF_SNF 128,1494 rank ", Length(ed), " ", Collected(ed), "\n");
QUIT;
