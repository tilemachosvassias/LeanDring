# Export the full D-species tables needed by the exact 1597/1598 checker.
# Run from the repository root:
#   ~/gap-4.15.1/gap -q -b gap/export_128_1597_1598.g < /dev/null

Read("gap/dring_sieve_standalone.g");;
Read("gap/dring_export.g");;

for k in [1597, 1598] do
  Print("exporting SmallGroup(128,", k, ")\n");
  DExport(SmallGroup(128, k),
          Concatenation("results/order128_pairs/g128_", String(k), ".txt"));
od;

Print("1597/1598 exports done\n");
QUIT;
