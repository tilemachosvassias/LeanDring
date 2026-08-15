# dring_sieve_standalone.g
# ==========================================================================
# Self-contained GAP sieve for the D(G)-isomorphism problem.
# No external files needed.  Usage:
#
#   gap> Read("gap/lib/dring_sieve_standalone.g");
#   gap> DSelfTest();          # regression anchors from verified Python runs
#   gap> DSieve(32);           # all groups of order 32, cheap invariants
#   gap> DSieve(64);
#   gap> DCompare(SmallGroup(16,6), SmallGroup(16,5), true);  # seeded pair
#
# Sieve keys are ONLY invariants provably intrinsic to the ring D(G)
# (fibre orders / subgroup levels are NOT keys -- swap automorphisms
# scramble them):
#   I1 number of species classes
#   I2 multiset of Galois-orbit sizes
#   I3 per odd prime p: block partition (Satz 2.2.7 / Thm B5*),
#      each block recorded as (size, sorted Galois-orbit sizes inside)
#   I4 conductor multiset over fully fused species (Lemma A lines)
#   I5 (stage 2, collisions only) SNF of the regular trace Gram matrix
# Collisions with different table-of-marks row invariants are
# counterexample candidates for D => B.
# Reference semantics: dring2.py (verified through order 24).
# ==========================================================================

# ---------- basic helpers -------------------------------------------------

OpResidualD := function(H, p)
  return SubgroupNC(H, Filtered(Elements(H), x -> Order(x) mod p <> 0));
end;

PPrimePartD := function(g, p)
  local o, a, m, e;
  o := Order(g); a := 1; m := o;
  while m mod p = 0 do m := m / p; a := a * p; od;
  if m = 1 then return g ^ 0; fi;
  e := a * ((1 / a) mod m);          # e = 0 mod a, e = 1 mod m
  return g ^ e;
end;

# ---------- species classes ----------------------------------------------
# One record per G-class of pairs (H, hH'):
#   rec(H, Hp, nat, q (element of H/Hp), h (preimage), Hidx (subgroup class))

SpeciesClassesD := function(G)
  local cls, sc, i, C, H, Hp, nat, Q, N, act, orbs, o;
  cls := [];
  sc  := ConjugacyClassesSubgroups(G);
  for i in [1..Length(sc)] do
    H   := Representative(sc[i]);
    Hp  := DerivedSubgroup(H);
    nat := NaturalHomomorphismByNormalSubgroupNC(H, Hp);
    Q   := Image(nat);
    N   := Normalizer(G, H);
    act := function(q, n)
      return Image(nat, PreImagesRepresentative(nat, q) ^ n);
    end;
    orbs := OrbitsDomain(N, Elements(Q), act);
    for o in orbs do
      Add(cls, rec(H := H, Hp := Hp, nat := nat, q := o[1],
                   h := PreImagesRepresentative(nat, o[1]), Hidx := i));
    od;
  od;
  return cls;
end;

# ---------- I2: Galois orbit sizes (per species and multiset) -------------

GaloisDataD := function(G, cls)
  local N, un, per, i, done, j, orb, frontier, newf, a, c, tq, k, sizes;
  N  := Exponent(G);
  un := Filtered([1..N], a -> Gcd(a, N) = 1);
  per := List(cls, c -> 0);
  done := List(cls, c -> false);
  for i in [1..Length(cls)] do
    if done[i] then continue; fi;
    orb := [i]; done[i] := true; frontier := [i];
    while frontier <> [] do
      newf := [];
      for j in frontier do
        for a in un do
          tq := cls[j].q ^ a;
          # find the species class of (H, tq): same Hidx, N-orbit test
          for k in [1..Length(cls)] do
            if not done[k] and cls[k].Hidx = cls[j].Hidx then
              if ForAny(Elements(Normalizer(G, cls[k].H)),
                   n -> Image(cls[k].nat,
                        PreImagesRepresentative(cls[k].nat, tq) ^ n)
                        = cls[k].q) then
                done[k] := true; Add(orb, k); Add(newf, k);
              fi;
            fi;
          od;
        od;
      od;
      frontier := newf;
    od;
    for j in orb do per[j] := Length(orb); od;
  od;
  sizes := ShallowCopy(per); Sort(sizes);
  return rec(perspecies := per, multiset := sizes);
end;

# ---------- I3: odd-p blocks via Satz 2.2.7 root -------------------------

BlockRootD := function(G, H, h, p)
  local K, Kp, nat, Kbar, Hgens, Cfix, B, hp, x, cand;
  K   := OpResidualD(H, p);
  Kp  := DerivedSubgroup(K);
  nat := NaturalHomomorphismByNormalSubgroupNC(K, Kp);
  Kbar := Image(nat);
  Hgens := GeneratorsOfGroup(H);
  Cfix := Filtered(Elements(Kbar),
            y -> ForAll(Hgens,
                 u -> Image(nat, PreImagesRepresentative(nat, y) ^ u) = y));
  B := Image(nat, CommutatorSubgroup(K, H));
  hp := PPrimePartD(h, p);
  if not hp in K then Error("p'-part not in O^p(H)"); fi;
  x := Image(nat, hp);
  cand := Filtered(Cfix, c -> c ^ -1 * x in B);
  if Length(cand) <> 1 then Error("C (+) B decomposition failed"); fi;
  return rec(K := K, c := PreImagesRepresentative(nat, cand[1]));
end;

PairsConjD := function(G, r1, r2)
  local rc, k;
  if Size(r1.K) <> Size(r2.K) then return false; fi;
  rc := RepresentativeAction(G, r1.K, r2.K);
  if rc = fail then return false; fi;
  k := r1.c ^ rc;
  return ForAny(Elements(Normalizer(G, r2.K)),
           n -> (k ^ n) * r2.c ^ -1 in DerivedSubgroup(r2.K));
end;

OddBlockSigD := function(G, cls, gal)
  local sig, p, roots, part, placed, i, j, s;
  sig := [];
  for p in Filtered(Set(Factors(Size(G))), q -> q <> 2) do
    roots := List(cls, c -> BlockRootD(G, c.H, c.h, p));
    part := []; placed := [];
    for i in [1..Length(cls)] do
      if i in placed then continue; fi;
      Add(part, [i]); AddSet(placed, i);
      for j in [i+1..Length(cls)] do
        if not (j in placed) and PairsConjD(G, roots[i], roots[j]) then
          Add(part[Length(part)], j); AddSet(placed, j);
        fi;
      od;
    od;
    s := List(part, b -> [Length(b),
           SortedList(List(b, i -> gal.perspecies[i]))]);
    Sort(s);
    Add(sig, [p, s]);
  od;
  return sig;
end;

# ---------- I4: fully fused conductors (Lemma A) ---------------------------

FullyFusedConductorsD := function(G, cls, gal)
  local out, i, c, N, cnt, n;
  out := [];
  for i in [1..Length(cls)] do
    if gal.perspecies[i] <> 1 then continue; fi;   # fully fused = Gamma-fixed class
    c := cls[i];
    N := Normalizer(G, c.H);
    cnt := 0;
    for n in Elements(N) do
      if Image(c.nat, c.h ^ n) = c.q then cnt := cnt + 1; fi;
    od;
    if cnt mod Size(c.Hp) <> 0 then Error("conductor not integral"); fi;
    Add(out, cnt / Size(c.Hp));
  od;
  Sort(out);
  return out;
end;

# ---------- stage-1 key ----------------------------------------------------

DKey := function(G)
  local cls, gal;
  cls := SpeciesClassesD(G);
  gal := GaloisDataD(G, cls);
  return [ Length(cls), gal.multiset,
           OddBlockSigD(G, cls, gal),
           FullyFusedConductorsD(G, cls, gal) ];
end;

# ---------- stage 2: species table and regular trace Gram SNF -------------

LinearCharValuesD := function(K)
  # returns list of value-lists on Elements(K) for all linear characters
  local Kp, nat, A, elK, gens, ords, r, exps, tuples, t, chi, vals, x, e, i;
  Kp  := DerivedSubgroup(K);
  nat := NaturalHomomorphismByNormalSubgroupNC(K, Kp);
  A   := Image(nat);
  elK := Elements(K);
  if Size(A) = 1 then return [ List(elK, x -> 1) ]; fi;
  gens := IndependentGeneratorsOfAbelianGroup(A);
  ords := List(gens, Order);
  exps := List(elK, x -> IndependentGeneratorExponents(A, Image(nat, x)));
  tuples := Cartesian(List(ords, o -> [0..o-1]));
  vals := [];
  for t in tuples do
    chi := List(exps, e ->
             Product([1..Length(ords)], i -> E(ords[i]) ^ (t[i] * e[i])));
    Add(vals, chi);
  od;
  return vals;
end;

BasisClassesD := function(G)
  local out, sc, i, K, elK, chars, N, act, orbs, o;
  out := [];
  sc  := ConjugacyClassesSubgroups(G);
  for i in [1..Length(sc)] do
    K := Representative(sc[i]);
    elK := Elements(K);
    chars := LinearCharValuesD(K);
    N := Normalizer(G, K);
    act := function(vals, n)
      return List(elK, x -> vals[Position(elK, x ^ (n ^ -1))]);
    end;
    orbs := OrbitsDomain(N, chars, act);
    for o in orbs do
      Add(out, rec(K := K, elK := elK, vals := o[1]));
    od;
  od;
  return out;
end;

SpeciesTableD := function(G, cls)
  local basis, n, T, i, j, s, b, conjH, g, tot, elG, pos;
  basis := BasisClassesD(G);
  n := Length(cls);
  if Length(basis) <> n then
    Error("species/basis count mismatch: ", n, " vs ", Length(basis));
  fi;
  elG := Elements(G);
  T := [];
  for i in [1..n] do
    s := cls[i];
    conjH := List(elG, g -> s.H ^ g);
    T[i] := [];
    for j in [1..n] do
      b := basis[j];
      tot := 0;
      for g in [1..Length(elG)] do
        if IsSubset(b.K, conjH[g]) then
          pos := Position(b.elK, s.h ^ elG[g]);
          tot := tot + b.vals[pos];
        fi;
      od;
      tot := tot / Size(b.K);
      if not IsCycInt(tot) then Error("species value not integral"); fi;
      T[i][j] := tot;
    od;
  od;
  return T;
end;

TraceGramSNFD := function(G)
  local cls, T, n, Gram, i, j, k, v;
  cls := SpeciesClassesD(G);
  T := SpeciesTableD(G, cls);
  n := Length(cls);
  Gram := NullMat(n, n);
  for i in [1..n] do
    for j in [i..n] do
      # Hermitian form: the second factor must be conjugated, otherwise the
      # entries are non-real cyclotomics on non-abelian groups and the
      # integrality check below fails.
      v := Sum([1..n], k -> T[k][i] * ComplexConjugate(T[k][j]));
      if not IsInt(v) then Error("Gram entry not an integer: ", v); fi;
      Gram[i][j] := v; Gram[j][i] := v;
    od;
  od;
  return ElementaryDivisorsMat(Gram);
end;

# ---------- table of marks row invariant (sound for DIFFER verdicts) ------

TomRowInvariantD := function(G)
  local M;
  M := MatTom(TableOfMarks(G));
  return SortedList(List(M, SortedList));
end;

# ---------- pairwise comparison and the sieve ------------------------------

DCompare := function(G, H, deep)
  local k1, k2, s1, s2;
  k1 := DKey(G); k2 := DKey(H);
  if k1 <> k2 then
    Print("stage-1 invariants DIFFER: D(G) and D(H) are NOT isomorphic.\n");
    return false;
  fi;
  Print("stage-1 invariants agree.\n");
  if deep then
    s1 := TraceGramSNFD(G); s2 := TraceGramSNFD(H);
    if s1 <> s2 then
      Print("trace-form SNF DIFFERS: D(G) and D(H) are NOT isomorphic.\n");
      return false;
    fi;
    Print("trace-form SNF agrees.\n");
  fi;
  if TomRowInvariantD(G) <> TomRowInvariantD(H) then
    Print(">>> tables of marks DIFFER: D=>B COUNTEREXAMPLE CANDIDATE.\n");
    Print(">>> verify with the exact cross-group lattice search.\n");
  else
    Print("ToM row invariants agree (candidate for D-determines-G side).\n");
  fi;
  return true;
end;

DSieveOpt := function(order, maxSubClasses, useI5)
  local ids, keys, members, i, G, nsc, k, p, j, b,
        rkeys, rmem, snf, q, pr;
  ids := [1..NrSmallGroups(order)];
  keys := []; members := [];
  for i in ids do
    G := SmallGroup(order, i);
    nsc := Length(ConjugacyClassesSubgroups(G));
    if nsc > maxSubClasses then
      Print(order, "#", i, " skipped (", nsc, " subgroup classes)\n");
      continue;
    fi;
    k := DKey(G);
    p := Position(keys, k);
    if p = fail then
      Add(keys, k); Add(members, [i]);
    else
      Add(members[p], i);
    fi;
    Print(order, "#", i, " ok\n");
  od;
  for j in [1..Length(keys)] do
    b := members[j];
    if Length(b) > 1 then
      Print("\nSTAGE-1 COLLISION at order ", order, ": ", b, "\n");
      if useI5 then
        rkeys := []; rmem := [];
        for i in b do
          snf := TraceGramSNFD(SmallGroup(order, i));
          p := Position(rkeys, snf);
          if p = fail then
            Add(rkeys, snf); Add(rmem, [i]);
          else
            Add(rmem[p], i);
          fi;
        od;
        for q in [1..Length(rkeys)] do
          if Length(rmem[q]) > 1 then
            Print("  survives trace-SNF: ", rmem[q], "\n");
            for pr in Combinations(rmem[q], 2) do
              if TomRowInvariantD(SmallGroup(order, pr[1]))
                 <> TomRowInvariantD(SmallGroup(order, pr[2])) then
                Print("  >>> ", pr, ": ToM DIFFER -- ",
                      "D=>B COUNTEREXAMPLE CANDIDATE <<<\n");
              else
                Print("  ", pr, ": ToM invariants agree ",
                      "(D-determines-G candidate)\n");
              fi;
            od;
          fi;
        od;
      else
        for pr in Combinations(b, 2) do
          if TomRowInvariantD(SmallGroup(order, pr[1]))
             <> TomRowInvariantD(SmallGroup(order, pr[2])) then
            Print("  >>> ", pr, ": ToM DIFFER -- rerun with useI5 ",
                  "before celebrating <<<\n");
          fi;
        od;
      fi;
    fi;
  od;
  return rec(keys := keys, members := members);
end;

DSieve := function(order)
  return DSieveOpt(order, 400, true);
end;

# ---------- self test (anchors from verified dring2.py / fullaut3.py) -----

DSelfTest := function()
  local checks, c, G, cls, T;
  checks := [ [ [4,1],  7 ],    # C4
              [ [4,2], 11 ],    # V4
              [ [8,4], 16 ],    # Q8
              [ [8,3], 20 ],    # D4
              [ [8,1], 15 ],    # C8
              [ [6,1],  7 ],    # S3
              [ [24,3], 20 ] ]; # SL(2,3)
  for c in checks do
    G := SmallGroup(c[1][1], c[1][2]);
    cls := SpeciesClassesD(G);
    if Length(cls) <> c[2] then
      Error("species count mismatch for ", c[1], ": got ",
            Length(cls), " expected ", c[2]);
    fi;
    Print("SmallGroup", c[1], ": ", Length(cls), " species  OK\n");
  od;
  # table build + squareness + Gram integrality on two anchors
  for c in [[6,1],[4,1]] do
    G := SmallGroup(c[1], c[2]);
    cls := SpeciesClassesD(G);
    T := SpeciesTableD(G, cls);
    Print("SmallGroup", c, ": table ", Length(T), "x", Length(T[1]),
          "  Gram SNF ", TraceGramSNFD(G), "\n");
  od;
  # a key computation end-to-end on a mixed-order group
  Print("DKey(S3) = ", DKey(SmallGroup(6,1)), "\n");
  Print("Self test passed.\n");
end;

Print("dring_sieve_standalone.g loaded.\n");
Print("Run DSelfTest(); then e.g. DSieve(32); DSieve(64);\n");
