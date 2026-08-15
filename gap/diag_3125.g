# diag_3125.g -- diagnose the Phase B failure of match_3125.g: is the archived
# generation genuinely inequivalent to the independent regeneration (ordering-
# independent invariant test), and if so, where?
#
# Invariant: the MULTISET of sorted-row-multisets (and dito columns) is
# invariant under any row/column permutation. If it differs between TM and T,
# no permutation equivalence exists -- a genuine semantic discrepancy in the
# archived table (matcher stall ruled out).
#
# Run:  ~/gap-4.15.1/gap -q -b gap/diag_3125.g

SortedKey := function(v)
  local w; w := ShallowCopy(v); Sort(w); return w;
end;

RowKeyMultiset := function(T)
  return SortedList(List([1..Length(T)], i -> SortedKey(T[i])));
end;
ColKeyMultiset := function(T)
  local n; n := Length(T);
  return SortedList(List([1..n], c -> SortedKey(List([1..n], r -> T[r][c]))));
end;

Diag := function(name, TM, TA, meta)
  local rm, ra, cm, ca, i, ndiff, firstdiff, badrowsTM, badrowsTA, classes;
  rm := RowKeyMultiset(TM);; ra := RowKeyMultiset(TA);;
  if rm = ra then
    Print(name, ": row-key multisets EQUAL (matcher stall, not semantics)\n");
  else
    ndiff := Number([1..Length(rm)], i -> rm[i] <> ra[i]);
    Print(name, ": row-key multisets DIFFER (", ndiff,
          " of ", Length(rm), " sorted positions) -- archived table is NOT\n",
          "   a row/column permutation of the regenerated one: GENUINE\n",
          "   semantic discrepancy in the archived generation.\n");
    # which of MY rows have keys not present (with multiplicity) in TA?
    badrowsTM := [];
    ra := List([1..Length(TA)], i -> SortedKey(TA[i]));  # unsorted list
    for i in [1..Length(TM)] do
      firstdiff := Position(ra, SortedKey(TM[i]));
      if firstdiff = fail then Add(badrowsTM, i);
      else Unbind(ra[firstdiff]); ra := Compacted(ra); fi;
    od;
    classes := Set(meta.rowClass{badrowsTM});
    Print("   regenerated rows with no archived partner: ", Length(badrowsTM),
          "\n   their subgroup-class indices: ", classes,
          "\n   class sizes |H|: ", Set(meta.classSize{classes}), "\n");
  fi;
  cm := ColKeyMultiset(TM);; ca := ColKeyMultiset(TA);;
  if cm = ca then Print(name, ": column-key multisets EQUAL\n");
  else Print(name, ": column-key multisets DIFFER too\n"); fi;
end;

Read("results/n_test_3125/Tmine_68.g");;
Read("results/n_test_3125/Tmine_68_meta.g");;
Read("gap/legacy/preprint_archive/G3125_68");;
Diag("68", TM68, T1, META68);
Unbind(TM68); Unbind(T1);
Read("results/n_test_3125/Tmine_69.g");;
Read("results/n_test_3125/Tmine_69_meta.g");;
Read("gap/legacy/preprint_archive/G3125_69");;
Diag("69", TM69, T2, META69);
Print("DIAG DONE\n");
QUIT;
