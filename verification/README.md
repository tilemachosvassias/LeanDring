# verification/ — external computations (GAP, Python, Sage)

Supporting computations for the even-order layer. These corroborate numbers
quoted in the paper and guided the Lean development; they are **not** part of
it.

Nothing here is Lean, nothing here is compiled by `lake build`, and no theorem
in `LeanDring/` depends on any of it. The mathematics is proved in Lean; this
directory is provenance, so that a reader can see where a census count or a
worked example came from and re-run it independently.

## Contents

| kind | count | what it is |
|---|---|---|
| `.g` | 718 | GAP scripts |
| `.txt` | 803 | captured output of those scripts |
| `.md` | 74 | commentary on individual experiments |
| `.py` | 65 | Python helpers |
| `.sage` | 8 | Sage helpers |
| `.c` | 7 | small C search programs |
| `.sh` | 3 | drivers |

Each script is paired with its recorded output (`foo.g` / `foo_out.txt`), so
the results can be inspected without a GAP installation and re-derived with
one.

`lib/` holds four vendored Python modules (`dring2`, `swaprigid`, `fullaut3`,
`latauto` — about 1300 lines, standard library only) that the Python helpers
here import. They were copied from the private research monorepo this
formalization was developed in, so that this directory is self-contained in the
published repository.

## Reproducing

The GAP scripts were run under GAP 4.x with the standard character-table and
small-groups libraries. They are independent of the Lean toolchain: no build
step, no ordering, and no dependency on the state of the library.

```bash
GAP=/path/to/gap ./v_task21_run_sweep.sh    # GAP defaults to `gap` on PATH
python3 v_task6_cfcheck.py                  # helpers resolve lib/ relatively
```

The `v_task21_*` maximal-subgroup sweep additionally needs the
[`ClassicalMaximals`](https://github.com/gap-packages/ClassicalMaximals) and
`recog` GAP packages. `recog` ships with GAP; `ClassicalMaximals` does not, so
if it is not installed as an ordinary package, point the scripts at a checkout:

```bash
gap -c 'CLASSICAL_MAXIMALS_PATH := "/path/to/ClassicalMaximals";;' v_task21_one.g
```

Paths are otherwise script-relative, so the scripts run from anywhere. The one exception
is the captured `*_out.txt` files: they are verbatim records of the original
runs and still contain the absolute paths of the machine that produced them
(mostly inside GAP's own stack traces). They are left exactly as emitted —
rewriting recorded output would defeat its purpose.
