# match_3125.g -- close task 5a/5b from the independently regenerated
# labeled tables (provenance/gap/species/regen_3125.g output).
#
# Phase A: find + fully verify a permutation equivalence
#          TM68[i][j] = TM69[rho[i]][gamma[j]]  (proves D(68) ~= D(69)
#          independently of the archive), then check in KNOWN labels whether
#          gamma maps the [K,1] columns of 68 onto those of 69 and rho the
#          (H,1) rows onto (H,1) rows  (the Conjecture-N instance).
# Phase B: same matcher against archived T1/T2 — validates the preprint-era
#          generation semantically (F1 + version-ordering notwithstanding).
#
# Matching = signature refinement: sorted row/column multisets as base keys,
# refined by projections onto already-matched columns/rows; greedy
# individualization when refinement stalls (sound because every returned
# equivalence is verified at ALL n^2 entries — a bad greedy choice cannot
# produce a false positive, only a `fail`, which is then INCONCLUSIVE, not a
# non-isomorphism proof).
#
# Run:  ~/gap-4.15.1/gap -q -b provenance/gap/species/match_3125.g

SortedKey := function(v)
  local w; w := ShallowCopy(v); Sort(w); return w;
end;

BaseColKeys := function(T)
  local n, keys, c;
  n := Length(T);
  keys := [];
  for c in [1..n] do
    keys[c] := SortedKey(List([1..n], r -> T[r][c]));
  od;
  return keys;
end;

MatchTables := function(A, B)
  local n, rho, gamma, rowTaken, colTaken, mRows, mCols, progress, rounds,
        baseRA, baseRB, baseCA, baseCB, uA, uB, sA, sB, keys, key, a, b,
        i, j, r, c, nchoices, cand;
  n := Length(A);
  rho := ListWithIdenticalEntries(n, 0);
  gamma := ListWithIdenticalEntries(n, 0);
  rowTaken := BlistList([1..n], []);
  colTaken := BlistList([1..n], []);
  mRows := []; mCols := [];
  baseRA := List([1..n], r -> SortedKey(A[r]));
  baseRB := List([1..n], r -> SortedKey(B[r]));
  baseCA := BaseColKeys(A);
  baseCB := BaseColKeys(B);
  rounds := 0; nchoices := 0;
  repeat
    progress := false; rounds := rounds + 1;
    # ---- rows
    uA := Filtered([1..n], r -> rho[r] = 0);
    uB := Filtered([1..n], r -> not rowTaken[r]);
    sA := List(uA, r -> [baseRA[r], List(mCols, c -> A[r][c])]);
    sB := List(uB, r -> [baseRB[r], List(mCols, c -> B[r][gamma[c]])]);
    keys := Set(sA);
    for key in keys do
      a := Positions(sA, key); b := Positions(sB, key);
      if Length(a) = 1 and Length(b) = 1 then
        rho[uA[a[1]]] := uB[b[1]]; rowTaken[uB[b[1]]] := true;
        Add(mRows, uA[a[1]]); progress := true;
      elif Length(a) <> Length(b) then
        Print("  bucket size mismatch (rows) -> fail\n"); return fail;
      fi;
    od;
    # ---- columns
    uA := Filtered([1..n], c -> gamma[c] = 0);
    uB := Filtered([1..n], c -> not colTaken[c]);
    sA := List(uA, c -> [baseCA[c], List(mRows, r -> A[r][c])]);
    sB := List(uB, c -> [baseCB[c], List(mRows, r -> B[rho[r]][c])]);
    keys := Set(sA);
    for key in keys do
      a := Positions(sA, key); b := Positions(sB, key);
      if Length(a) = 1 and Length(b) = 1 then
        gamma[uA[a[1]]] := uB[b[1]]; colTaken[uB[b[1]]] := true;
        Add(mCols, uA[a[1]]); progress := true;
      elif Length(a) <> Length(b) then
        Print("  bucket size mismatch (cols) -> fail\n"); return fail;
      fi;
    od;
    # ---- greedy individualization when stalled but incomplete
    if not progress and 0 in rho then
      uA := Filtered([1..n], r -> rho[r] = 0);
      uB := Filtered([1..n], r -> not rowTaken[r]);
      i := uA[1];
      sA := [baseRA[i], List(mCols, c -> A[i][c])];
      cand := Filtered(uB, r ->
                [baseRB[r], List(mCols, c -> B[r][gamma[c]])] = sA);
      if Length(cand) = 0 then
        Print("  individualization dead end -> fail\n"); return fail;
      fi;
      rho[i] := cand[1]; rowTaken[cand[1]] := true; Add(mRows, i);
      nchoices := nchoices + 1; progress := true;
    fi;
  until not progress;
  if 0 in rho or 0 in gamma then
    Print("  incomplete matching -> fail\n"); return fail;
  fi;
  for i in [1..n] do
    for j in [1..n] do
      if A[i][j] <> B[rho[i]][gamma[j]] then
        Print("  full verification FAILED at [", i, ",", j, "]\n");
        return fail;
      fi;
    od;
  od;
  Print("  match VERIFIED at all ", n, "^2 entries (", rounds,
        " rounds, ", nchoices, " greedy choices)\n");
  return [rho, gamma];
end;

Read("results/n_test_3125/Tmine_68.g");;
Read("results/n_test_3125/Tmine_68_meta.g");;
Read("results/n_test_3125/Tmine_69.g");;
Read("results/n_test_3125/Tmine_69_meta.g");;

Print("== Phase A: TM68 ~ TM69 (independent D-isomorphism + N test)\n");
mA := MatchTables(TM68, TM69);;
if mA = fail then
  Print("PHASE A: INCONCLUSIVE (greedy matcher failed; needs backtracking)\n");
else
  starts68 := Filtered([1..Length(META68.colClass)],
      j -> j = 1 or META68.colClass[j] <> META68.colClass[j-1]);;
  starts69 := Filtered([1..Length(META69.colClass)],
      j -> j = 1 or META69.colClass[j] <> META69.colClass[j-1]);;
  triv68 := Filtered([1..Length(META68.fibreOrder)],
      i -> META68.fibreOrder[i] = 1);;
  triv69 := Filtered([1..Length(META69.fibreOrder)],
      i -> META69.fibreOrder[i] = 1);;
  Print("PHASE A: D(3125,68) ~= D(3125,69) CONFIRMED independently.\n");
  Print("  [K,1]-column alignment (eta(B) preserved): ",
        Set(mA[2]{starts68}) = Set(starts69),
        " (", Length(starts68), " columns)\n");
  Print("  (H,1)-row alignment: ",
        Set(mA[1]{triv68}) = Set(triv69),
        " (", Length(triv68), " rows)\n");
  PrintTo("results/n_test_3125/match_A_perms.g",
          "rhoA := ", mA[1], ";\ngammaA := ", mA[2], ";\n");
fi;

Print("== Phase B1: TM68 ~ archived T1\n");
Read("provenance/gap/legacy/preprint_archive/G3125_68");;
mB1 := MatchTables(TM68, T1);;
if mB1 = fail then
  Print("PHASE B1: TM68 !~ archived T1 or matcher stalled -- INVESTIGATE\n");
else
  Print("PHASE B1: archived T1 semantically CORRECT (matches regeneration)\n");
fi;
Unbind(T1);

Print("== Phase B2: TM69 ~ archived T2\n");
Read("provenance/gap/legacy/preprint_archive/G3125_69");;
mB2 := MatchTables(TM69, T2);;
if mB2 = fail then
  Print("PHASE B2: TM69 !~ archived T2 or matcher stalled -- INVESTIGATE\n");
else
  Print("PHASE B2: archived T2 semantically CORRECT (matches regeneration)\n");
fi;
Print("MATCH OVERALL DONE\n");
QUIT;
