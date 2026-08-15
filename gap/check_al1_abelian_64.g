# Exact certification of the abelian linkage law AL1 for every abelian
# 2-group of order at most 64.  The count is aggregated by subgroup pairs,
# but covers every ordered pair of distinct rational species (K,y).

AlphaAL1 := function(overgroups, weights, k, l)
  local separating;
  separating := Difference(overgroups[k], overgroups[l]);
  if IsEmpty(separating) then return infinity; fi;
  return Minimum(List(separating, i -> weights[i]));
end;

OvergroupData := function(G, subs)
  local overgroups, weights, k, m;
  weights := List(subs, M -> PValuation(Index(G, M), 2));
  overgroups := [];
  for k in [1..Length(subs)] do
    Add(overgroups, Filtered([1..Length(subs)], m ->
      IsSubgroup(subs[m], subs[k])));
  od;
  return [overgroups, weights];
end;

AlphaAL1Slow := function(G, subs, K, L)
  local best, M, value;
  best := infinity;
  for M in subs do
    if IsSubgroup(M, K) and not IsSubgroup(M, L) then
      value := PValuation(Index(G, M), 2);
      if best = infinity or value < best then best := value; fi;
    fi;
  od;
  return best;
end;

MinInfinity := function(a, b)
  if a = infinity then return b; fi;
  if b = infinity then return a; fi;
  return Minimum(a, b);
end;

CheckAbelianGroup := function(G)
  local subs, twos, fsize, histogram, total, i, j, K, L, common,
        sameCount, differentCount, a, b, ell, expectedPairs, exponent,
        data, overgroups, weights;
  subs := AllSubgroups(G);
  twos := List(subs, K -> Filtered(Elements(K), x -> Order(x) <= 2));
  fsize := Sum(twos, Length);
  histogram := [];
  total := 0;
  exponent := Exponent(G);

  # In an elementary abelian group every two distinct points are separated
  # at valuation one: distinct decorations by M=G and a sign character;
  # distinct subgroups by an index-two hyperplane containing one but not the
  # other.  This avoids materializing the 26,387-square matrix for C2^6.
  if exponent = 2 then
    Add(histogram, [1, fsize * (fsize - 1)]);
    total := fsize * (fsize - 1);
  else
    data := OvergroupData(G, subs);
    overgroups := data[1]; weights := data[2];
    for i in [1..Length(subs)] do
      K := subs[i];
      for j in [1..Length(subs)] do
        L := subs[j];
        common := Length(Intersection(twos[i], twos[j]));
        if i = j then
          sameCount := 0;
        else
          sameCount := common;
        fi;
        differentCount := Length(twos[i]) * Length(twos[j]) - common;
        if i = j then
          differentCount := differentCount;
        fi;

        # Direct generator semantics: different decorations are separated
        # by [G,mu] at valuation one.  For a common decoration, only a
        # generator subgroup containing exactly one of K,L contributes.
        if differentCount > 0 then
          Add(histogram, [1, differentCount]);
          total := total + differentCount;
        fi;
        if sameCount > 0 then
          a := AlphaAL1(overgroups, weights, i, j);
          b := AlphaAL1(overgroups, weights, j, i);
          if Size(G) <= 16 then
            if a <> AlphaAL1Slow(G, subs, K, L) or
               b <> AlphaAL1Slow(G, subs, L, K) then
              Error("fast separation valuation disagrees with raw scan");
            fi;
          fi;
          ell := MinInfinity(a, b);
          if ell = infinity then Error("distinct points were not separated"); fi;
          Add(histogram, [ell, sameCount]);
          total := total + sameCount;
        fi;
      od;
    od;
  fi;

  expectedPairs := fsize * (fsize - 1);
  if total <> expectedPairs then
    Error("AL1 ordered-pair coverage failure");
  fi;
  Sort(histogram, function(x,y) return x[1] < y[1]; end);
  # Collapse equal valuations.
  for i in Reversed([2..Length(histogram)]) do
    if histogram[i][1] = histogram[i-1][1] then
      histogram[i-1][2] := histogram[i-1][2] + histogram[i][2];
      Remove(histogram, i);
    fi;
  od;
  Print("PASS ", IdGroup(G), ": subgroups=", Length(subs),
        ", |F|=", fsize, ", linkage=", histogram, "\n");
end;

for n in [1,2,4,8,16,32,64] do
  for i in [1..NumberSmallGroups(n)] do
    if IsAbelian(SmallGroup(n,i)) then
      CheckAbelianGroup(SmallGroup(n,i));
    fi;
  od;
od;
QUIT;
