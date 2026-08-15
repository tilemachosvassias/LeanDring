# gap/ — GAP scripts for the order-`p⁴` and order-`5⁵` results

The computational scripts behind Parts I–II of the paper: species-table
generation, the subgroup/conjugacy/character censuses of the two order-`5⁵`
twins, the gauge and linkage experiments, and the sieve searches.

Nothing here is trusted. Under the development's trust model, GAP is an
**untrusted hint provider**: it supplies candidate data — presentations,
subgroup inventories, normalizer generators, conjugation matrices, alignment
tables, column permutations — and every item is re-derived and re-checked
inside Lean by a kernel `decide`. A wrong hint can only produce a failing
`decide`, never an unsound proof. These scripts are published so the
provenance of the data is inspectable, not because any theorem rests on them.

That the model earns its keep is on the record: GAP's matching artifact for
the `5⁵` pair reported a 28-point column permutation that, checked against the
certified data, fails on 104 of 108 objects — while the identity pairing
validates all 12,200 entries involved. Two further GAP data errors were caught
the same way. See Section 8 of the paper.

## Scripts the paper names

| script | what it does |
|---|---|
| `em06_brauer_pair.g` | verifies the Brauer-pair property for the order-`5⁵` twins (cited in §5 and listed as an ancillary file) |
| `species_p4_small.g` | generates species tables for the small order-`p⁴` models |

## Running them

```bash
gap -q -b gap/em06_brauer_pair.g          # from the repository root
GAP=/path/to/gap ./gap/hunt128_launch.sh  # the one driver script
```

Written for GAP 4.x with the standard character-table and small-groups
libraries. Paths inside the scripts are repository-relative, so run them from
the repository root; a few write into `results/`, which you may need to create.

## What is not here

The development archive `gap/legacy/preprint_archive/` of the private research
repository — 856 files, 854 MB of bulk species dumps from earlier rounds — is
deliberately excluded. It is superseded by the certified Lean data and far too
large to publish. The even-order computations live separately, in
[`../verification/`](../verification/).
