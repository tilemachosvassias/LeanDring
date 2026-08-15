# run_sieve128.g -- open-problem N1: sieve over order-128 candidates
# overnight: sieve all 2328 groups of order 128. Regression first.
Read("gap/dring_sieve_standalone.g");
DSelfTest();
DSieve(128);
QUIT;
