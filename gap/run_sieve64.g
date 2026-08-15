# run_sieve64.g -- OPEN_PROBLEMS section 3: sieve all groups of order 64.
# Any D-collision pair here is AUTOMATICALLY a D=>B counterexample
# (ToM-minimality at 96, docs/references.md). Regression first, then sieve.
Read("gap/dring_sieve_standalone.g");
DSelfTest();
DSieve(64);
QUIT;
