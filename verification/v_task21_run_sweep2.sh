#!/usr/bin/env bash
# Driver v2: per-maximal-subgroup subprocess isolation. Each maximal M gets
# its own GAP process with a 60s wall-clock cap; recog occasionally hits a
# pathological internal method (unbounded orbit growth) that cannot be
# preempted from inside GAP, so external process-level timeout is the only
# reliable way to bound it without losing the rest of the sweep for that q.
set -u
cd "$(dirname "$0")"

GAP="${GAP:-gap}"   # override with: GAP=/path/to/gap ./this-script.sh
OUTDIR=v_task21_perq
MASTER=v_task21_out.txt
PERM_TIMEOUT=60

mkdir -p "$OUTDIR"
: > "$MASTER"

QLIST="3 5 7 9 11 13 17 19 23 25 27 29 31 37 41 49 81 121 125"

for q in $QLIST; do
    echo "### q=$q sizes pass at $(date -Is)" | tee -a "$MASTER"
    sizedrv="$OUTDIR/sizes_q${q}.g"
    sizeout="$OUTDIR/sizes_q${q}_out.txt"
    printf 'Q := %s;;\n' "$q" > "$sizedrv"
    cat v_task21_sizes.g >> "$sizedrv"
    timeout 120 "$GAP" -q -o 2g < "$sizedrv" > "$sizeout" 2>&1
    grep -v "^#I" "$sizeout" >> "$MASTER"

    scount=$(grep -c "^S_SIZE_" "$sizeout")
    ocount=$(grep -c "^O_SIZE_" "$sizeout")
    echo "### q=$q: S count=$scount  O count=$ocount" | tee -a "$MASTER"

    for type in S O; do
        if [ "$type" = "S" ]; then n=$scount; else n=$ocount; fi
        for idx in $(seq 1 "$n"); do
            onedrv="$OUTDIR/one_q${q}_${type}${idx}.g"
            oneout="$OUTDIR/one_q${q}_${type}${idx}_out.txt"
            printf 'Q := %s;; TYPESTR := "%s";; IDXV := %s;;\n' "$q" "$type" "$idx" > "$onedrv"
            cat v_task21_one.g >> "$onedrv"
            timeout $PERM_TIMEOUT "$GAP" -q -o 3g < "$onedrv" > "$oneout" 2>&1
            rc=$?
            line=$(grep "^RESULT " "$oneout")
            if [ -n "$line" ]; then
                echo "$line" >> "$MASTER"
            else
                sz=$(grep "^${type}_SIZE_${idx}:" "$sizeout" | awk '{print $2}')
                if [ $rc -eq 124 ]; then
                    echo "RESULT $type q=$q idx=$idx sizeM=$sz FAILED reason=EXTERNAL_TIMEOUT_${PERM_TIMEOUT}s" >> "$MASTER"
                else
                    echo "RESULT $type q=$q idx=$idx sizeM=$sz FAILED reason=CRASH_rc${rc}" >> "$MASTER"
                fi
            fi
        done
    done
    echo "### q=$q done at $(date -Is)" | tee -a "$MASTER"
    echo "" >> "$MASTER"
done

echo "### Sweep finished at $(date -Is)" | tee -a "$MASTER"
