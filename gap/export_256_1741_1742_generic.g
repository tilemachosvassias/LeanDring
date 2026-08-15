# export_256_1741_1742_generic.g -- independent generic DExport
# certification path for the order-256 T4 pair (1741,1742).
#
# Unlike export_256_t4_pair_1741.g, this uses the self-contained
# SpeciesClassesD/SpeciesTableD implementation from
# dring_sieve_standalone.g.  Outputs are kept under distinct filenames so
# hashes and matrices can be compared without overwriting prior evidence.
#
# Run from the repository root:
#   ~/gap-4.15.1/gap -q -b gap/export_256_1741_1742_generic.g

Read("gap/dring_sieve_standalone.g");;
Read("gap/dring_export.g");;

Print("GENERIC_EXPORT_START 256,1741\n");
DExport(SmallGroup(256,1741),
        "results/order256_t4_pairs/g256_1741_generic.txt");
Print("GENERIC_EXPORT_DONE 256,1741\n");

Print("GENERIC_EXPORT_START 256,1742\n");
DExport(SmallGroup(256,1742),
        "results/order256_t4_pairs/g256_1742_generic.txt");
Print("GENERIC_EXPORT_DONE 256,1742\n");

QUIT;
