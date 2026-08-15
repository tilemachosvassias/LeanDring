# export64_pairs.g -- export species tables + marks for the seven surviving
# order-64 sieve pairs (results/order64_sieve_raw.log) for crossiso.py.
Read("gap/dring_sieve_standalone.g");
Read("gap/dring_export.g");
for id in [47, 48, 106, 107, 155, 157, 156, 158, 161, 162, 164, 165, 179, 181] do
  DExport(SmallGroup(64, id),
          Concatenation("results/order64_pairs/g64_", String(id), ".txt"));
  Print("exported ", id, "\n");
od;
QUIT;
