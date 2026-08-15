# Merge + resolve the parallel order-128 hunt.
#   gap ... -c 'RUNDIR:="/tmp/hunt128_run";; DEEPCAP:=8000;;' hunt128_merge.g
# (or set RUNDIR/DEEPCAP as globals before Read).  Reads every res_*.txt, buckets
# groups by their DKey string, reports DKey collisions, and on each collision
# runs the deep chain (Gram SNF + etale field bag + canonical D_F-linkage) when
# rk D <= DEEPCAP -- otherwise flags the pair as "deep-stage too large" for a
# targeted follow-up.  A survivor of the deep chain is a genuine D-iso candidate.

Read("gap/hunt_blocks.g");   # DeepKeyD, DKey, dring
if not IsBound(RUNDIR) then RUNDIR := "/tmp/hunt128_run"; fi;
if not IsBound(DEEPCAP) then DEEPCAP := 8000; fi;

# 1. read all results -> list of [id, DKeyString]
recs := [];;
for f in DirectoryContents(RUNDIR) do
  if Length(f) >= 4 and f{[1..4]} = "res_" then
    for line in SplitString(StringFile(Concatenation(RUNDIR,"/",f)), "\n") do
      if line <> "" then
        p := Position(line, '\t');
        Add(recs, [Int(line{[1..p-1]}), line{[p+1..Length(line)]}]);
      fi;
    od;
  fi;
od;;
Print("read ", Length(recs), " DKey results from ", RUNDIR, "\n");

# 2. bucket by DKey string
keys := [];; mem := [];;
for r in recs do
  p := Position(keys, r[2]);
  if p = fail then Add(keys, r[2]); Add(mem, [r[1]]); else Add(mem[p], r[1]); fi;
od;;
coll := Filtered(mem, b -> Length(b) > 1);;
Print("DKey buckets: ", Length(keys), " ; collisions: ", Length(coll), "\n");
for b in coll do Print("  DKey collision: ", b, "\n"); od;

# 3. deep-resolve each collision (Gram SNF + fields + D_F-linkage)
survivors := [];;
for b in coll do
  Print(">> resolving ", b, "\n");
  rk := List(b, i -> Length(SpeciesClassesD(SmallGroup(128,i))));
  Print("   rkD = ", rk, "\n");
  if Maximum(rk) > DEEPCAP then
    Print("   DEEP-STAGE TOO LARGE (rkD>", DEEPCAP, ") -- flagged for follow-up\n");
    Add(survivors, rec(ids := b, status := "deep-too-large", rkD := rk));
    continue;
  fi;
  dk := [];; dm := [];;
  for i in b do
    k := DeepKeyD(SmallGroup(128,i));
    p := Position(dk, k);
    if p = fail then Add(dk, k); Add(dm, [i]); else Add(dm[p], i); fi;
  od;
  for j in [1..Length(dk)] do
    if Length(dm[j]) > 1 then
      Print("   *** SURVIVES DEEP CHAIN (D-iso CANDIDATE): ", dm[j], " ***\n");
      Add(survivors, rec(ids := dm[j], status := "candidate"));
    else
      Print("   separated -> ", dm[j], "\n");
    fi;
  od;
od;;
Print("=== SUMMARY: ", Length(coll), " DKey-collision buckets; survivors/flags: ",
      survivors, " ===\n");
QUIT;
