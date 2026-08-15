Read("gap/dring_sieve_standalone.g");
Read("gap/dring_export.g");

# n=1
DExport(DihedralGroup(8), "results/D4.txt");
DExport(QuaternionGroup(8), "results/Q8.txt");

# n=2
DExport(SmallGroup(32, 49), "results/G32_49.txt");
DExport(SmallGroup(32, 50), "results/G32_50.txt");

# n=3
# DExport(ExtraspecialGroup(128, "+"), "results/G128_plus.txt");
# DExport(ExtraspecialGroup(128, "-"), "results/G128_minus.txt");
QUIT;
