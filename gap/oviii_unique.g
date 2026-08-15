# Audit 5.25 check: is K the UNIQUE self-centralizing normal subgroup
# isomorphic to C4 x C4 in each local group M_i? Uniqueness makes the
# Lemma 5.24a(ii) fusion argument rigorous under external isomorphisms.
Read("/tmp/oviii_perms.g");
C44 := AbelianGroup([4,4]);;
uniq_both := 0;; uniq_fail := 0;; i := 0;;
failing := [];;
for P in PAIRS do
  i := i + 1;
  res := [];
  for Wg in [P.W1, P.W2] do
    M := Group(Concatenation([t1,t2], Wg));;
    K := Subgroup(M, [t1,t2]);;
    cands := Filtered(NormalSubgroups(M),
      N -> Size(N) = 16 and IsAbelian(N)
           and IdGroup(N) = IdGroup(C44)
           and Centralizer(M, N) = N);;
    Add(res, Length(cands));
  od;
  if res = [1,1] then
    uniq_both := uniq_both + 1;
  else
    uniq_fail := uniq_fail + 1;
    Add(failing, [i, res]);
  fi;
od;
Print("pairs: ", Length(PAIRS), "\n");
Print("K unique self-centralizing normal C4xC4 in BOTH: ", uniq_both, "\n");
Print("uniqueness FAILS somewhere: ", uniq_fail, "\n");
Print("failing (pair index, counts): ", failing, "\n");
QUIT;
