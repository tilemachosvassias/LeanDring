# Layered d=2 hunt for D-isomorphic 2-group pairs.
#
# Target: pairs G,H with D(G) ~= D(H) as rings (isomorphic monomial-
# representation rings), G not iso H -- a p=2 analogue of the 5^5 pair.
# The interesting collisions so far are non-metacyclic Frattini-corank-2
# groups ((32,13/14), (64,13/14)), so we restrict to d(G)=2 -- also the
# Theorem-R frontier and a feasibility win (small species tables).
#
# Cheapest filter first, finest last; every stage is a canonical D-iso
# invariant of the FULL ring D(G) (rk_Z D, cyclotomic species table):
#   A  d(G)=2 filter
#   B  DKey        (rk D, Galois multiset, odd-block sig, fused conductors)
#   C  Gram SNF    (TraceGramSNFD: SNF of the species trace form T^T T)
#   D  field bag   (etale factors of Q (x) D: {(deg,conductor,real?)} per species)
#   E  table of marks (B-level) check on the survivors
# A pair surviving A-D is a *candidate* (invariants are necessary, not
# sufficient) -- hand to the theory lane; do NOT call it a counterexample.
#
# Validated on order 64: catches (64,13/14) [DKey collide]; Gram SNF
# separates them.  On order 32 (with the d=2 filter) it flags (32,13/14),
# which survive DKey+GramSNF and are cut only by the field bag
# (Q(sqrt -2) vs Q(sqrt 2)) -- exactly the P1 separation.

Read("gap/dring_sieve_standalone.g");

# etale factor-field bag of Q (x) D(G): per full-D species, the field it
# generates, recorded by (degree, conductor, totally-real?).
FieldBagD := function(G)
  local cls, T, i, F, out;
  cls := SpeciesClassesD(G);
  T := SpeciesTableD(G, cls);
  out := [];
  for i in [1..Length(cls)] do
    F := Field(Rationals, T[i]);
    Add(out, [ DegreeOverPrimeField(F), Conductor(F),
               ForAll(T[i], x -> GaloisCyc(x, -1) = x) ]);
  od;
  return Collected(out);
end;;

HuntD2 := function(order, maxSubClasses)
  local ids, d2, i, G, nsc, keys, mem, k, p, j, b, snfk, snfm, snf, q,
        fbk, fbm, fb, r, survivors, pr, stage;
  ids := [1..NrSmallGroups(order)];
  d2 := [];
  for i in ids do                               # Stage A
    G := SmallGroup(order, i);
    if RankPGroup(G) <> 2 then continue; fi;
    nsc := Length(ConjugacyClassesSubgroups(G));
    if nsc > maxSubClasses then
      Print(order, "#", i, "  SKIP (", nsc, " subgroup classes > cap)\n");
      continue;
    fi;
    Add(d2, i);
  od;
  Print("== order ", order, ": ", Length(d2),
        " d=2 groups within cap ", maxSubClasses, " ==\n");

  keys := []; mem := [];                          # Stage B: DKey buckets
  for i in d2 do
    k := DKey(SmallGroup(order, i));
    p := Position(keys, k);
    if p = fail then Add(keys, k); Add(mem, [i]); else Add(mem[p], i); fi;
    Print("  #", i, " DKey done\n");
  od;

  survivors := [];
  for j in [1..Length(keys)] do
    b := mem[j];
    if Length(b) <= 1 then continue; fi;
    Print("\n[B] DKey collision: ", b, "\n");
    snfk := []; snfm := [];                        # Stage C: Gram SNF
    for i in b do
      snf := TraceGramSNFD(SmallGroup(order, i));
      p := Position(snfk, snf);
      if p = fail then Add(snfk, snf); Add(snfm, [i]); else Add(snfm[p], i); fi;
    od;
    for q in [1..Length(snfk)] do
      if Length(snfm[q]) <= 1 then
        Print("  [C] Gram SNF separates within ", b, " -> ", snfm[q], "\n");
        continue;
      fi;
      Print("  [C] survives Gram SNF: ", snfm[q], "\n");
      fbk := []; fbm := [];                         # Stage D: field bag
      for i in snfm[q] do
        fb := FieldBagD(SmallGroup(order, i));
        p := Position(fbk, fb);
        if p = fail then Add(fbk, fb); Add(fbm, [i]); else Add(fbm[p], i); fi;
      od;
      for r in [1..Length(fbk)] do
        if Length(fbm[r]) > 1 then
          Print("  [D] *** SURVIVES FIELD BAG: ", fbm[r], " ***\n");
          Add(survivors, fbm[r]);
        else
          Print("  [D] field bag separates ", snfm[q], " -> ", fbm[r], "\n");
        fi;
      od;
    od;
  od;

  Print("\n== SURVIVORS (candidate D-iso pairs, order ", order, "): ",
        survivors, " ==\n");
  for b in survivors do                            # Stage E: table of marks
    for pr in Combinations(b, 2) do
      if TomRowInvariantD(SmallGroup(order, pr[1]))
         <> TomRowInvariantD(SmallGroup(order, pr[2])) then
        Print("  ", pr, ": table-of-marks DIFFER -> B(G) not iso; a D-iso here",
              " would break D=>B  (HIGH-VALUE candidate)\n");
      else
        Print("  ", pr, ": table-of-marks agree (D-determines-G candidate;",
              " next: D_F linkage / arity tower)\n");
      fi;
    od;
  od;
  return survivors;
end;;
