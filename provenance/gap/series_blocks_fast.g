# series_blocks_fast.g — diagonal-block fingerprints without cyclotomic
# arithmetic.
#
# Every entry of a diagonal block is a sum of n-th roots of unity, n = the
# exponent of H/H' (a power of p).  Instead of adding them in Q(zeta_n) we
# record the multiplicity vector m = (m_0, ..., m_{n-1}) of the exponents
# and then canonicalize it, which is exact:  for n = p^e the only relations
# among the zeta_n^k are  sum_{j<p} zeta^{k + j n/p} = 0,  one for each
# k mod n/p.  Subtracting, in each such class, the minimum multiplicity
# gives a normal form -- two multiplicity vectors have the same normal form
# iff they represent the same algebraic number.  So the fingerprint is exact
# and costs only integer arithmetic.
#
# Columns are ALL linear characters of H, not orbit representatives: an
# isomorphism of species tables matches character orbits, so it matches the
# all-character multisets too.  Agreement is evidence; disagreement is
# decisive.
#
# Usage (from the repository root):
#   gap -q -b < provenance/gap/series_blocks_fast.g

Read("provenance/gap/series_higher_primes_defs.g");

LOG := "results/series_blocks_fast.log";
Say := function(args...)
  local s;
  s := JoinStringsWithSeparator(List(args, String), "");
  AppendTo(LOG, s, "\n");
  Print(s, "\n");
end;

# normal form of a multiplicity vector of n-th roots of unity, n = p^e
CanonMult := function(m, n, p)
  local step, k, j, lo;
  step := n / p;
  m := ShallowCopy(m);
  for k in [1..step] do
    lo := m[k];
    for j in [1..p-1] do
      if m[k + j*step] < lo then lo := m[k + j*step]; fi;
    od;
    if lo > 0 then
      for j in [0..p-1] do
        m[k + j*step] := m[k + j*step] - lo;
      od;
    fi;
  od;
  return m;
end;

BlockFingerprints := function(G, p, tag)
  local ccs, out, ci, H, N, nat, Q, gens, ords, k, n, scal, elts, orb, o,
        reps, fix, tv, blk, r, x, W, w, q, cvec, c, m, i, dot, row, t, done;
  ccs := ConjugacyClassesSubgroups(G);
  out := [];
  t := Runtime(); done := 0;
  for ci in [1..Length(ccs)] do
    H   := Representative(ccs[ci]);
    N   := Normalizer(G, H);
    nat := NaturalHomomorphismByNormalSubgroup(H, DerivedSubgroup(H));
    Q   := Image(nat);
    gens := IndependentGeneratorsOfAbelianGroup(Q);
    ords := List(gens, Order);
    k    := Length(gens);
    if k = 0 then
      Add(out, [Size(H), 1, [[1]]]);   # trivial quotient: single entry |fix|
      continue;
    fi;
    n    := Lcm(ords);
    scal := List(ords, o -> n / o);    # zeta_n^{v_i * scal_i} = zeta_{o_i}^{v_i}
    elts := Elements(Q);
    orb  := OrbitsDomain(N, elts,
              {x, g} -> Image(nat, PreImagesRepresentative(nat, x)^g));
    reps := List(orb, o -> Representative(o));
    # q with q^-1 H q <= H, one per coset: representatives of N_G(H)/H
    tv   := RightTransversal(N, H);
    fix  := AsList(tv);
    # all characters as exponent vectors
    cvec := Cartesian(List(ords, o -> [0..o-1]));
    blk := [];
    for r in [1..Length(reps)] do
      # multiset of exponent vectors of the conjugates of a lift of reps[r]
      x := PreImagesRepresentative(nat, reps[r]);
      W := [];
      for q in fix do
        w := IndependentGeneratorExponents(Q, Image(nat, x^q));
        Add(W, List([1..k], i -> w[i] * scal[i]));
      od;
      row := [];
      for c in cvec do
        m := ListWithIdenticalEntries(n, 0);
        for w in W do
          dot := 0;
          for i in [1..k] do dot := dot + c[i] * w[i]; od;
          dot := dot mod n;
          m[dot + 1] := m[dot + 1] + 1;
        od;
        Add(row, CanonMult(m, n, p));
      od;
      Sort(row);
      Add(blk, row);
    od;
    Sort(blk);
    Add(out, [Size(H), Length(reps), blk]);
    done := done + 1;
    if done mod 50 = 0 then
      Say("  ", tag, ": ", done, "/", Length(ccs), " classes  [",
          Int((Runtime()-t)/1000), " s]");
    fi;
  od;
  Sort(out);
  return out;
end;

Run := function(p)
  local d, G1, G2, b1, b2, t, i;
  d := NonResidue(p);
  Say("\n======== p = ", p, ",  twist d = ", d, " ========");
  G1 := Gpq(p, 1); G2 := Gpq(p, d);
  Say("|G| = ", Size(G1), ",  classes = ",
      Length(ConjugacyClassesSubgroups(G1)));
  t := Runtime();
  b1 := BlockFingerprints(G1, p, "G(1)");
  Say("blocks of G(1) done [", Int((Runtime()-t)/1000), " s]");
  t := Runtime();
  b2 := BlockFingerprints(G2, p, "G(d)");
  Say("blocks of G(d) done [", Int((Runtime()-t)/1000), " s]");
  if b1 = b2 then
    Say(">>> p = ", p, ": diagonal blocks AGREE",
        "  (consistent with D(G1) = D(G2); evidence, not proof)");
  else
    i := First([1..Length(b1)], j -> b1[j] <> b2[j]);
    Say(">>> p = ", p, ": diagonal blocks DIFFER at index ", i,
        "  -- species tables NON-isomorphic, so NOT a counterexample");
    Say("    G(1) block: |H| = ", b1[i][1], ", rows = ", b1[i][2]);
    Say("    G(d) block: |H| = ", b2[i][1], ", rows = ", b2[i][2]);
  fi;
end;

Run(5);
Run(7);
Run(11);
QUIT;
