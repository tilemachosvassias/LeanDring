# Collision resolver worker: for each DKey-collision bucket, compute the
# canonical D_F-linkage per group and sub-bucket.  Linkage separates => the
# groups are NOT D-iso (done).  Linkage collides => escalate (candidate).
# rk D cap: skip (flag) collisions whose species table is too large to build.
# Fine-grained flushed logging, same style as the DKey workers.

Read("gap/df_linkage.g");   # DFLinkage, DFL_v2, dring

# capped linkage: returns rec(rkD, bag) or rec(rkD, toolarge:=true)
CappedLinkage := function(i, cap)
  local G, cls, T, n, rows, TR, m, p, q, L, j;
  G := SmallGroup(128, i);
  cls := SpeciesClassesD(G); n := Length(cls);
  if n > cap then return rec(rkD := n, toolarge := true); fi;
  T := SpeciesTableD(G, cls);
  rows := Filtered([1..n], j -> ForAll(T[j], IsInt));
  TR := T{rows}; m := Length(rows); L := [];
  for p in [1..m] do for q in [p+1..m] do
    Add(L, DFL_v2(Gcd(List([1..n], j -> TR[p][j] - TR[q][j])))); od; od;
  return rec(rkD := n, bag := Collected(L));
end;;

ResolveWorker := function(colls, cap, wid, logf, resf)
  local t0, secs, nc, ci, c, res, lk, i, seen, keys, sub, ks, done, out;
  t0 := Runtime();
  secs := function() return String(Int((Runtime()-t0)/1000)); end;
  nc := Length(colls);
  AppendTo(logf, "[r", wid, "] START ", nc, " collisions\n");
  for ci in [1..nc] do
    c := colls[ci];
    AppendTo(logf, "[r", wid, "] ", secs(), "s BEGIN ", c, " (", ci, "/", nc, ") ...\n");
    lk := List(c, i -> CappedLinkage(i, cap));
    if ForAny(lk, x -> IsBound(x.toolarge)) then
      AppendTo(logf, "[r", wid, "] ", secs(), "s TOOLARGE ", c, " rkD=",
               List(lk, x -> x.rkD), "\n");
      out := OutputTextFile(resf, true); SetPrintFormattingStatus(out, false);
      WriteLine(out, Concatenation("TOOLARGE\t", String(c), "\t", String(List(lk,x->x.rkD))));
      CloseStream(out);
      continue;
    fi;
    # sub-bucket by linkage bag
    keys := []; sub := [];
    for i in [1..Length(c)] do
      ks := String(lk[i].bag);
      if ks in keys then Add(sub[Position(keys,ks)], c[i]);
      else Add(keys, ks); Add(sub, [c[i]]); fi;
    od;
    res := Filtered(sub, b -> Length(b) > 1);   # linkage-surviving sub-buckets
    out := OutputTextFile(resf, true); SetPrintFormattingStatus(out, false);
    if Length(res) = 0 then
      WriteLine(out, Concatenation("SEP\t", String(c), "\t", String(List(lk,x->x.rkD))));
      AppendTo(logf, "[r", wid, "] ", secs(), "s SEP ", c,
               " rkD=", List(lk,x->x.rkD), "\n");
    else
      WriteLine(out, Concatenation("CANDIDATE\t", String(res), "\t", String(List(lk,x->x.rkD))));
      AppendTo(logf, "[r", wid, "] ", secs(), "s *** CANDIDATE ", res, " ***\n");
    fi;
    CloseStream(out);
  od;
  AppendTo(logf, "[r", wid, "] COMPLETE in ", secs(), "s\n");
end;;
