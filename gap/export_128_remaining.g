# export_128_remaining.g -- DExport for all members of the 29 remaining
# un-exported ToM-differ clusters of the order-128 batch
# (results/order128_batch_status.md "What remains" item 2).
# Run from the repo root:
#   ~/gap-4.15.1/gap -q -b gap/export_128_remaining.g < /dev/null

Read("gap/dring_sieve_standalone.g");;
Read("gap/dring_export.g");;

ids := [ 380, 385, 381, 383, 382, 384, 555, 556, 594, 596, 595, 597,
         650, 651, 652, 653, 657, 658, 659, 660, 719, 720, 765, 766,
         767, 768, 797, 799, 798, 800, 807, 808, 809, 818, 819, 820,
         825, 826, 827, 828, 831, 832, 956, 958, 957, 959, 964, 965,
         967, 968, 1490, 1494, 1504, 1515, 1802, 1803, 1805, 1806,
         1817, 1821, 1818, 1822 ];;

for k in ids do
  Print("exporting SmallGroup(128,", k, ")\n");
  DExport(SmallGroup(128, k),
          Concatenation("results/order128_pairs/g128_", String(k), ".txt"));
od;
Print("all ", Length(ids), " exports done\n");
QUIT;
