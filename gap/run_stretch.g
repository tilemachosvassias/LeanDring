Read("gap/dring_sieve_standalone.g");
Read("gap/dring_export.g");

# Order 32
for i in [46, 47, 48] do
  DExport(SmallGroup(32, i), Concatenation("results/G32_", String(i), ".txt"));
od;

QUIT;
