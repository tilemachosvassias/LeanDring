#!/bin/bash
# Launch the parallel order-128 D-iso hunt (DKey stage).
#   usage: hunt128_launch.sh [N_WORKERS] [RUNDIR] [MAXG]
# N_WORKERS : number of parallel GAP workers (default 10)
# RUNDIR    : where logs/results/drivers live (default /tmp/hunt128_run)
# MAXG      : optional cap on #generic ids (for a quick test run; 0 = all)
#
# Target set = generic residual = order-128 groups with RankPGroup in {3,4,5}
# and |G'| >= 4 (non-abelian, non-extraspecial, non-generalized-extraspecial;
# d=2 already done, d=6/7 fully theory-covered).  Each worker DKeys its share
# and streams results; monitor with hunt128_status.sh, resolve with
# hunt128_merge.g.
set -u
N=${1:-10}
RUNDIR=${2:-/tmp/hunt128_run}
MAXG=${3:-0}
GAP="${GAP:-gap}"           # override: GAP=/path/to/gap
REPO="${REPO:-$(cd "$(dirname "$0")/.." && pwd)}"
mkdir -p "$RUNDIR"
echo "start: $(date)  N=$N  RUNDIR=$RUNDIR  MAXG=$MAXG" > "$RUNDIR/MANIFEST"

# 1. generate the sorted generic id list
cat > "$RUNDIR/prep.g" <<EOF
Read("$REPO/gap/hunt_blocks.g");
gen := Filtered([1..NrSmallGroups(128)], function(i) local G;
  G := SmallGroup(128,i);
  return RankPGroup(G) in [3,4,5] and Size(DerivedSubgroup(G)) >= 4; end);;
PrintTo("$RUNDIR/generic_ids.txt", JoinStringsWithSeparator(List(gen,String),"\n"));
Print("GENERIC ", Length(gen), "\n"); QUIT;
EOF
echo "generating generic id list ..."
"$GAP" -q --nointeract "$RUNDIR/prep.g" 2>&1 | grep GENERIC | tee -a "$RUNDIR/MANIFEST"

# 2. round-robin split (balances big/small groups across workers)
mapfile -t IDS < "$RUNDIR/generic_ids.txt"
if [ "$MAXG" -gt 0 ]; then IDS=("${IDS[@]:0:$MAXG}"); fi
for w in $(seq 1 "$N"); do : > "$RUNDIR/ids_$w.txt"; done
idx=0
for id in "${IDS[@]}"; do
  w=$(( idx % N + 1 )); echo "$id" >> "$RUNDIR/ids_$w.txt"; idx=$((idx+1))
done
echo "split ${#IDS[@]} groups across $N workers" | tee -a "$RUNDIR/MANIFEST"

# 3. per-worker driver + launch
for w in $(seq 1 "$N"); do
  cat > "$RUNDIR/drv_$w.g" <<EOF
Read("$REPO/gap/dkey_worker.g");
ids := List(Filtered(SplitString(StringFile("$RUNDIR/ids_$w.txt"),"\n"), s -> s <> ""), Int);;
DKeyWorker(128, ids, $w, "$RUNDIR/w_$w.log", "$RUNDIR/res_$w.txt");
QUIT;
EOF
  : > "$RUNDIR/w_$w.log"; : > "$RUNDIR/res_$w.txt"
  setsid bash -c "$GAP -q --nointeract $RUNDIR/drv_$w.g > $RUNDIR/gap_$w.out 2>&1" < /dev/null &
done
echo "launched $N workers.  monitor: bash $REPO/gap/hunt128_status.sh $RUNDIR"
