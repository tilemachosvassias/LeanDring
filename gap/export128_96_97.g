# export128_96_97.g -- N0a priority sidecar for the first ToM-differ survivor.

LogTo("results/order128_pairs/export_96_97.log");
Print("ORDER-128 PRIORITY EXPORT: groups 96 and 97\n");
Read("gap/dring_sieve_standalone.g");
Read("gap/dring_export.g");
DExport(SmallGroup(128, 96), "results/order128_pairs/g128_96.txt");
DExport(SmallGroup(128, 97), "results/order128_pairs/g128_97.txt");
Print("ORDER-128 PRIORITY EXPORT COMPLETE\n");
LogTo();
QUIT;
