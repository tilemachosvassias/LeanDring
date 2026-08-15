# v_task14_sd.g
# PART A (v_task14, NOTES §4p): Lemma SD test.
#
# For every 2-group P of order 2^k, k = 3..6 (SmallGroups of orders 8,16,32,64)
# and every d: test s_d(P) <= GaussianBinomial(k,d,2), where s_d(P) = number of
# subgroups of order 2^d, counted via ConjugacyClassesSubgroups (sum over
# classes of that order of class length = |P|/|N_P(K)|).
# Also: strictness claim s_1(P) < 2^k - 1 for non-elementary-abelian P.
#
# Order-64 EL1 check (same pass, reusing ConjugacyClassesSubgroups): for each
# P of order 64 compute r(P) = number of fused (K,lambda) pairs (generic
# engine from v_task4_rationality.g: orbits of N_P(K) on LinearCharacters(K)),
# and check whether any non-elementary P attains r(P) = r(C2^6).

qBin := function(k, d)
  local i, num, den;
  if d < 0 or d > k then return 0; fi;
  if d = 0 or d = k then return 1; fi;
  num := 1; den := 1;
  for i in [0..d-1] do
    num := num * (2^(k-i) - 1);
    den := den * (2^(i+1) - 1);
  od;
  return num/den;
end;;

# Single pass over ConjugacyClassesSubgroups(G): builds s_d(G) counts AND
# r(G) = number of fused (K,lambda) pairs (fusion engine identical in
# substance to DRingInvariants in v_task4_rationality.g, minus the
# Galois-degree bookkeeping which EL1 does not need).
AnalyzeGroup := function(G)
  local classes, k, counts, r, cls, K, ord, d, N, contrib,
        gens, elts, m, perms, lins, chvals, seen, orbit, frontier,
        newfront, v, w, p, gv;
  classes := ConjugacyClassesSubgroups(G);
  k := LogInt(Size(G), 2);
  counts := List([0..k], x -> 0);
  r := 0;
  for cls in classes do
    K := Representative(cls);
    ord := Size(K);
    d := LogInt(ord, 2);
    N := Normalizer(G, K);
    contrib := Size(G) / Size(N);
    counts[d+1] := counts[d+1] + contrib;

    gens := GeneratorsOfGroup(N);
    elts := Elements(K);
    m := Length(elts);
    perms := List(gens, n -> List([1..m],
                    i -> Position(elts, n * elts[i] * n^-1)));
    lins := LinearCharacters(K);
    chvals := List(lins, chi -> List(elts, x -> x ^ chi));
    seen := Set([]);
    for v in chvals do
      if not v in seen then
        orbit := [ v ]; frontier := [ v ];
        while Length(frontier) > 0 do
          newfront := [];
          for w in frontier do
            for p in perms do
              gv := w{ p };
              if not gv in orbit then
                Add(orbit, gv); Add(newfront, gv);
              fi;
            od;
          od;
          frontier := newfront;
        od;
        UniteSet(seen, orbit);
        r := r + 1;
      fi;
    od;
  od;
  return rec(counts := counts, r := r, k := k);
end;;

# ---------------- sanity check ----------------
Print("=== SANITY CHECK ===\n");
Print("qBin(3,1) = ", qBin(3,1), "  (expected 7)\n");
res := AnalyzeGroup(SmallGroup(8,5));; # C2^3, elementary abelian
Print("SmallGroup(8,5) = C2^3: counts = ", res.counts,
      "  s_1 = ", res.counts[2], "  qBin(3,1) = ", qBin(3,1),
      "  (equality expected for elementary abelian): ",
      res.counts[2] = qBin(3,1), "\n");
Print("SmallGroup(8,5) r = ", res.r,
      "  vs r(C2^3) formula Sum_d qBin(3,d)*2^d = ",
      Sum([0..3], dd -> qBin(3,dd)*2^dd), "\n\n");

# ---------------- main sweep, orders 8,16,32,64 ----------------
rvals64 := [];;
elemAb64 := [];;

for order in [8, 16, 32, 64] do
  n := NrSmallGroups(order);
  Print("=== ORDER ", order, " (", n, " groups) ===\n");
  violTotal := 0;
  for i in [1..n] do
    G := SmallGroup(order, i);
    t0 := Runtime();;
    res := AnalyzeGroup(G);;
    elapsed := Runtime() - t0;
    if order = 64 and elapsed > 180000 then
      Print("*** SLOW-FLAG: SmallGroup(64,", i, ") took ", elapsed,
            " ms (exceeds 3-min threshold) ***\n");
    fi;
    if order = 64 and i mod 50 = 0 then
      Print("... progress: order 64, group ", i, " of ", n, " done\n");
    fi;
    k := res.k;
    isEA := IsElementaryAbelian(G);
    localViol := false;
    for d in [0..k] do
      qb := qBin(k, d);
      if res.counts[d+1] > qb then
        Print("*** VIOLATION SD: SmallGroup(", order, ",", i, ") d=", d,
              " s_d=", res.counts[d+1], " > qBin(", k, ",", d, ")=", qb,
              " ***\n");
        localViol := true;
      fi;
    od;
    if not isEA then
      qb1 := qBin(k, 1);
      if not res.counts[2] < qb1 then
        Print("*** VIOLATION STRICTNESS: SmallGroup(", order, ",", i,
              ") non-elementary but s_1=", res.counts[2],
              " not < ", qb1, " ***\n");
        localViol := true;
      fi;
    fi;
    if localViol then violTotal := violTotal + 1; fi;
    if order = 64 then
      rvals64[i] := res.r;
      elemAb64[i] := isEA;
    fi;
  od;
  Print("--- ORDER ", order, " SUMMARY: ", n - violTotal, " of ", n,
        " groups pass SD + strictness cleanly (violations: ", violTotal,
        ") ---\n\n");
od;

# ---------------- order-64 EL1 collision check ----------------
Print("=== ORDER 64 EL1 CHECK ===\n");
rC26formula := Sum([0..6], dd -> qBin(6, dd) * 2^dd);;
Print("r(C2^6) via formula Sum_d qBin(6,d)*2^d = ", rC26formula, "\n");

elemIdx := Filtered([1..Length(elemAb64)], i -> elemAb64[i]);;
Print("Elementary abelian group(s) of order 64 found at index/indices: ",
      elemIdx, "\n");
for i in elemIdx do
  Print("SmallGroup(64,", i, ") [elementary abelian]: r = ", rvals64[i],
        "  matches formula: ", rvals64[i] = rC26formula, "\n");
od;

hits := Filtered([1..Length(rvals64)],
                  i -> not elemAb64[i] and rvals64[i] = rC26formula);;
Print("Non-elementary-abelian groups of order 64 with r(P) = r(C2^6): ",
      hits, "\n");
Print("EL1 COLLISION AT ORDER 64: ", Length(hits) > 0, "\n");

Print("\nDONE\n");
QUIT;
