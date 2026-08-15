# Export multiplication tables and subgroup-class representatives for the
# exact Mackey structure-constant calculation on SmallGroup(128,1597/1598).
#
# Run from the repository root:
#   ~/gap-4.15.1/gap -q -b gap/export_group_128_1597_1598.g < /dev/null

Read("gap/export_group_for_deiml.g");;

ExportGroupForDeiml(128, 1597,
    "results/order128_pairs/g128_1597_group.json");
ExportGroupForDeiml(128, 1598,
    "results/order128_pairs/g128_1598_group.json");
QUIT;
