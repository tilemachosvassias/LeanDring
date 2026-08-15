# DKey worker for the parallel order-128 hunt.  One GAP process per worker.
# Logging is per-group and guaranteed-flushed (AppendTo reopens each call), so
#   tail -f w_<id>.log
# always shows the exact group a worker is on, with live timing + ETA.
# Results stream to res_<id>.txt (one line "id \t DKeyString") as they finish,
# so partial progress survives a crash and the merge step can run any time.
#
# Uses only DKey (the D-invariant bucket key): cheap, seconds/group.  The
# expensive deep chain (Gram SNF / field bag / D_F-linkage) runs later, only on
# DKey collisions, in hunt128_merge.g.

Read("gap/hunt_blocks.g");   # DKey, tags, dring

# write "id \t DKeyString" as ONE physical line (no AppendTo line-wrapping),
# flushed, so counts/collision-detection are line-based and crash-safe.
WriteResult := function(resf, i, ks)
  local rs;
  rs := OutputTextFile(resf, true);        # append
  SetPrintFormattingStatus(rs, false);     # disable 80-col wrapping
  WriteLine(rs, Concatenation(String(i), "\t", ks));
  CloseStream(rs);                         # flush
end;;

DKeyWorker := function(order, idlist, wid, logf, resf)
  local total, t0, secs, idx, i, G, gp, cls, nsc, k, ks, tg, tprev, done, avg, eta;
  total := Length(idlist);
  t0 := Runtime();
  secs := function() return String(Int((Runtime() - t0) / 1000)); end;
  if total = 0 then
    AppendTo(logf, "[w", wid, "] EMPTY worklist\n"); return;
  fi;
  AppendTo(logf, "[w", wid, "] START ", total, " groups, ids ",
           idlist[1], "..", idlist[total], "\n");
  done := 0;
  for idx in [1..total] do
    i := idlist[idx];
    G := SmallGroup(order, i);
    gp := Size(DerivedSubgroup(G));
    # heartbeat BEFORE the expensive computation -> shows the live group
    AppendTo(logf, "[w", wid, "] ", secs(), "s  BEGIN #", i,
             " (", idx, "/", total, ") |G'|=", gp, " ...\n");
    tprev := Runtime();
    cls := SpeciesClassesD(G);
    nsc := Length(ConjugacyClassesSubgroups(G));
    k := DKey(G);
    ks := String(k);
    tg := Int((Runtime() - tprev) / 1000);
    done := done + 1;
    avg := (Runtime() - t0) / done;
    eta := Int(avg * (total - done) / 1000);
    WriteResult(resf, i, ks);
    AppendTo(logf, "[w", wid, "] ", secs(), "s  DONE  #", i,
             "  nsc=", nsc, " rkD=", Length(cls), " t=", tg, "s",
             "  [", done, "/", total, " ETA~", eta, "s]\n");
  od;
  AppendTo(logf, "[w", wid, "] COMPLETE ", total, " groups in ", secs(), "s\n");
end;;
