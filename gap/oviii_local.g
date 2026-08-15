# O-viii (docs/r2_abelian.md §5.24): local-group tests on the 113 deep-candidate
# Z4^2 collision pairs emitted by python/oviii_interval.py -> /tmp/oviii_perms.g.
# Everything is a permutation group on the 16 points of K = C4 x C4:
#   K = <t1,t2> (regular translations); M_i = <t1,t2, W_i-gens> = K : W_i.
# Per pair we test:
#   charK : is K characteristic in M_i (ForAll Aut(M_i) fix K)?  -- the Fitting
#           handle of Lemma 5.24a; if false the pair ESCAPES the handle.
#   iso   : is M1 ~ M2?  Isomorphic local groups share their table of marks, so
#           the normalizer node N_G(K) cannot separate the pair -- these survive
#           every coarse split-model invariant (the hard candidate core).
Read("/tmp/oviii_perms.g");
charboth := 0;; esc := 0;; iso := 0;; niso := 0;; i := 0;;
cross := [];;
for P in PAIRS do
  i := i + 1;
  M1 := Group(Concatenation([t1,t2], P.W1));;
  M2 := Group(Concatenation([t1,t2], P.W2));;
  K1 := Subgroup(M1, [t1,t2]);; K2 := Subgroup(M2, [t1,t2]);;
  c1 := ForAll(GeneratorsOfGroup(AutomorphismGroup(M1)), a -> Image(a,K1)=K1);;
  c2 := ForAll(GeneratorsOfGroup(AutomorphismGroup(M2)), a -> Image(a,K2)=K2);;
  isom := IsomorphismGroups(M1, M2) <> fail;;
  if c1 and c2 then charboth := charboth + 1; fi;
  if (not c1) or (not c2) then esc := esc + 1; fi;
  if isom then iso := iso + 1; else niso := niso + 1; fi;
  Add(cross, [c1 and c2, isom]);
  Print(i, " |M|=", Size(M1), " (W=", P.wsz, ",m=", P.m, ") charK=",c1,"/",c2,
        " M1~M2=", isom, "\n");
od;
Print("=====\n");
Print("deep candidates: ", Length(PAIRS), "\n");
Print("K characteristic in BOTH local groups: ", charboth, "\n");
Print("ESCAPE the Fitting handle (K non-char in >=1): ", esc, "\n");
Print("local groups M1 ~ M2 (coarse-blind core): ", iso, "\n");
Print("local groups M1 !~ M2 (normalizer-node separates): ", niso, "\n");
Print("cross-tab [charBoth, iso] counts:\n");
Print("  [T,T]=", Number(cross,x->x=[true,true]),
      "  [T,F]=", Number(cross,x->x=[true,false]),
      "  [F,T]=", Number(cross,x->x=[false,true]),
      "  [F,F]=", Number(cross,x->x=[false,false]), "\n");
