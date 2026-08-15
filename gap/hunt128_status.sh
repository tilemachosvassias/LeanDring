#!/bin/bash
# Live status of the parallel order-128 hunt.  usage: hunt128_status.sh [RUNDIR]
RUNDIR=${1:-/tmp/hunt128_run}
now=$(date '+%Y-%m-%d %H:%M:%S')
total=$(grep -c . "$RUNDIR/generic_ids.txt" 2>/dev/null)
done=$(cat "$RUNDIR"/res_*.txt 2>/dev/null | grep -c .)
echo "===== hunt128 @ $now ====="
pct=$([ "${total:-0}" -gt 0 ] && echo $(( 100 * ${done:-0} / total )) || echo 0)
# overall ETA ~ slowest worker's *latest* reported ETA
maxeta=$(for f in "$RUNDIR"/w_*.log; do
           [ -e "$f" ] && grep 'ETA~' "$f" | tail -1 | sed -n 's/.*ETA~\([0-9]*\)s.*/\1/p'
         done 2>/dev/null | sort -n | tail -1)
echo "overall: ${done:-0} / ${total:-?} groups DKey'd  (${pct}%)  ~ETA ${maxeta:-?}s"
echo "--- workers ---"
for f in "$RUNDIR"/w_*.log; do
  [ -e "$f" ] || continue
  w=$(basename "$f" .log)
  nd=$(grep -c ' DONE ' "$f")
  last=$(tail -1 "$f" | sed 's/^\[[^]]*\] *//')
  age=$(( $(date +%s) - $(stat -c %Y "$f") ))
  # "age" = seconds since this worker last wrote (rising age on a BEGIN line = long group)
  printf "  %-4s done=%-4s  (last write %ss ago)  %s\n" "$w" "$nd" "$age" "$last"
done
echo "--- collision candidates so far (ids sharing a DKey) ---"
cat "$RUNDIR"/res_*.txt 2>/dev/null | sort -t$'\t' -k2 | \
  awk -F'\t' '{grp[$2]=grp[$2]" "$1; cnt[$2]++}
              END{n=0; for(k in cnt) if(cnt[k]>1){print "  [" grp[k] " ]"; n++}
                  if(n==0) print "  (none yet)"}'
echo "--- completion ---"
comp=$(grep -l COMPLETE "$RUNDIR"/w_*.log 2>/dev/null | wc -l)
nw=$(ls "$RUNDIR"/w_*.log 2>/dev/null | wc -l)
echo "  $comp / $nw workers COMPLETE"
