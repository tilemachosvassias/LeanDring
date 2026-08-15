# O-viii-b: uniqueness test on the NON-merge-robust tier-1/2 kills
# (/tmp/oviii_b_perms.g from python/oviii_b.py).
#
# A tier-1/2 kill whose order-poset OP* does NOT differ is not certified by
# the fusion-invariant argument.  BUT if K is the UNIQUE self-centralizing
# normal C4xC4 in both split local groups M_i, then no sibling exists for
# fusion to move K to, so L(W)/conj is recovered EXACTLY (Lemma 5.24a(ii)
# applies) and the interval-profile kill is VALID after all.
#
# So: uniq_both here = extra kills recovered on top of the 28 OP*-robust ones.
# The rest (non-robust AND non-unique) are genuinely live for N0a.
Read("/tmp/oviii_b_perms.g");
C44 := AbelianGroup([4,4]);;
uniq_both := 0;; uniq_fail := 0;; i := 0;;
uniq_by_tier := [0,0];;  kills_by_tier := [0,0];;
for P in PAIRS do
  i := i + 1;
  kills_by_tier[P.tier] := kills_by_tier[P.tier] + 1;
  res := [];
  for Wg in [P.W1, P.W2] do
    M := Group(Concatenation([t1,t2], Wg));;
    cands := Filtered(NormalSubgroups(M),
      N -> Size(N) = 16 and IsAbelian(N)
           and IdGroup(N) = IdGroup(C44)
           and Centralizer(M, N) = N);;
    Add(res, Length(cands));
  od;
  if res = [1,1] then
    uniq_both := uniq_both + 1;
    uniq_by_tier[P.tier] := uniq_by_tier[P.tier] + 1;
  else
    uniq_fail := uniq_fail + 1;
  fi;
od;
Print("=====\n");
Print("non-robust tier-1/2 kills tested: ", Length(PAIRS), "\n");
Print("  tier-1 among them: ", kills_by_tier[1],
      "  tier-2: ", kills_by_tier[2], "\n");
Print("K UNIQUE self-cent normal C4xC4 in BOTH (kill VALID via exact recovery): ",
      uniq_both, "\n");
Print("  by tier: tier1=", uniq_by_tier[1], " tier2=", uniq_by_tier[2], "\n");
Print("uniqueness FAILS (genuinely LIVE for N0a): ", uniq_fail, "\n");
QUIT;
