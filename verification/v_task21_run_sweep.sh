#!/usr/bin/env bash
# Driver for v_task21_tbc.g: loops over the T-BC q-list, one GAP process per q,
# 10-minute wall-clock cap per q (per task instructions), serial (no parallel
# GAP processes), output captured per-q and concatenated into the master log.
set -u
cd "$(dirname "$0")"

GAP="${GAP:-gap}"   # override with: GAP=/path/to/gap ./this-script.sh
SCRIPT=v_task21_tbc.g
OUTDIR=v_task21_perq
MASTER=v_task21_out.txt

mkdir -p "$OUTDIR"
: > "$MASTER"

QLIST="3 5 7 9 11 13 17 19 23 25 27 29 31 37 41 49 81 121 125"

for q in $QLIST; do
    echo "### Starting q=$q at $(date -Is)" | tee -a "$MASTER"
    driver="$OUTDIR/drv_q${q}.g"
    out="$OUTDIR/q${q}_out.txt"
    printf 'Q := %s;;\n' "$q" > "$driver"
    cat "$SCRIPT" >> "$driver"
    timeout 600 "$GAP" -q -o 6g < "$driver" > "$out" 2>&1
    rc=$?
    if [ $rc -eq 124 ]; then
        echo "### q=$q TIMED OUT after 600s (partial output below)" | tee -a "$MASTER"
    elif [ $rc -ne 0 ]; then
        echo "### q=$q EXITED with code $rc" | tee -a "$MASTER"
    else
        echo "### q=$q completed OK" | tee -a "$MASTER"
    fi
    grep -v "^#I" "$out" >> "$MASTER"
    echo "" >> "$MASTER"
done

echo "### Sweep finished at $(date -Is)" | tee -a "$MASTER"
