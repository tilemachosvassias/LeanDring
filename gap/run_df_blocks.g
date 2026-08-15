# run_df_blocks.g -- validation zoo + censuses + big-pair runs for the
# blockwise D_F SNF (gap/df_blocks_snf.g). Output: one DF_SNF line per
# group; compare the order-8/16 lines against python/df_blocks_check.py.
# Run from repo root:
#   ~/gap-4.15.1/gap -q -b gap/run_df_blocks.g < /dev/null > log 2>&1 &

Read("gap/df_blocks_snf.g");;

for k in [1..5] do DFReport(8, k); od;
for k in [1..14] do DFReport(16, k); od;

DFCensus(32);
DFCensus(64);

# order-128: all members of the 37 ToM-differ DSieve clusters
for k in [96,97,278,281,373,374,375,376,379,386,380,385,381,383,382,384,
          555,556,594,596,595,597,650,651,652,653,657,658,659,660,719,720,
          765,766,767,768,797,799,798,800,807,808,809,818,819,820,825,826,
          827,828,831,832,956,958,957,959,964,965,967,968,1490,1494,
          1504,1515,1802,1803,1805,1806,1817,1821,1818,1822,
          1958,1959,1961,1962,1970,1971] do
  DFReport(128, k);
od;

# order-256 T4 pairs (Brauer pairs with equal ToM; D-side probes)
for k in [3678,3679,1741,1742,4156,4159] do DFReport(256, k); od;

Print("ALL DONE\n");
QUIT;
