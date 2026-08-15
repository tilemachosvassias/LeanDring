# O-viii-b: cross-tabulate the 113 interval-blind deep pairs
# (/tmp/oviii_perms.g from python/oviii_interval.py) by
#   iso     : M1 ~ M2  (iso => same ToM => tier-3 does NOT separate => 58-core)
#   uniqB   : K unique self-centralizing normal C4xC4 in BOTH local groups
# to report the uniqueness diagnostic intersected with the 58-core (the
# "sharpest rigorous handle" subset the 5.25 audit asked for).
Read("/tmp/oviii_perms.g");
C44 := AbelianGroup([4,4]);;
i := 0;; core := 0;; core_uniq := 0;; noncore_uniq := 0;; uniq := 0;;
for P in PAIRS do
  i := i + 1;
  M1 := Group(Concatenation([t1,t2], P.W1));;
  M2 := Group(Concatenation([t1,t2], P.W2));;
  isom := IsomorphismGroups(M1, M2) <> fail;;
  ub := true;
  for M in [M1, M2] do
    cands := Filtered(NormalSubgroups(M),
      Nsg -> Size(Nsg) = 16 and IsAbelian(Nsg)
             and IdGroup(Nsg) = IdGroup(C44)
             and Centralizer(M, Nsg) = Nsg);;
    if Length(cands) <> 1 then ub := false; fi;
  od;
  if ub then uniq := uniq + 1; fi;
  if isom then
    core := core + 1;
    if ub then core_uniq := core_uniq + 1; fi;
  else
    if ub then noncore_uniq := noncore_uniq + 1; fi;
  fi;
od;
Print("=====\n");
Print("interval-blind deep pairs: ", Length(PAIRS), "\n");
Print("58-core (M1~M2): ", core, "\n");
Print("K unique-of-kind in BOTH (total): ", uniq, "\n");
Print("  core AND unique  (sharpest rigorous handle): ", core_uniq, "\n");
Print("  core, NOT unique (finest data needed, fusion-blind): ", core - core_uniq, "\n");
Print("  non-core (tier-3 separates) AND unique: ", noncore_uniq, "\n");
QUIT;
