#!/bin/bash
# Staged, memory-isolated build for low-RAM machines (16 GB: mandatory; 32 GB+:
# a plain `lake build` with ~4-way effective parallelism is fine, but never run
# unbounded parallel kernel-decide builds — see REPRODUCIBILITY.md §6).
# Strategy: build the kernel-heavy modules ONE AT A TIME (each lean process
# accumulates non-released decide memory), then a final full `lake build`
# (cheap: everything heavy is cached).
set -u
cd "$(dirname "$0")"

# JOBS: bounded-parallel mode for machines with more RAM. Each kernel-decide
# job peaks at ~2-8 GB, sometimes more — JOBS=2 has crashed a 32 GB machine.
# Default is therefore the staged serial build (JOBS=1); set JOBS=n explicitly
# to opt into parallelism if you know your machine can take it.
if [ -z "${JOBS:-}" ]; then
  JOBS=1
  echo "==> default staged serial build, JOBS=1 (override with JOBS=n $0)"
fi
if [ "$JOBS" -gt 1 ]; then
  # This Lake version (5.0.0 / Lean 4.32.0) has no --jobs flag; it sizes its
  # worker pool from the visible processor count. On Linux, restrict CPU
  # affinity so Lake sees exactly JOBS processors. (No parallel mode on macOS
  # -- the 16 GB Mac uses the staged serial build anyway.)
  if command -v taskset >/dev/null 2>&1; then
    echo "==> bounded-parallel mode: taskset -c 0-$((JOBS-1)) lake build  $(date +%H:%M:%S)"
    exec taskset -c 0-$((JOBS-1)) lake build
  else
    echo "==> JOBS=$JOBS requested but no taskset on this platform; falling back to staged serial build"
    JOBS=1
  fi
fi

# Serial mode: even a single `lake build <module>` invocation parallelizes
# internally (Lake sizes its worker pool from the visible processor count),
# so pin it to one CPU where taskset exists — that is what makes this build
# genuinely sequential and memory-safe.
if command -v taskset >/dev/null 2>&1; then
  LAKE="taskset -c 0 lake"
else
  LAKE="lake"
fi

# Progress: 410 lake-build invocations total (131 heavy + 278 staged + 1 final).
# Each prints a [n/378] line; grep '^==>' in the log to see how far along it is.
TOTAL=410
STEP=0
progress() {
  STEP=$((STEP + 1))
  echo "==> [$STEP/$TOTAL] $(date +%H:%M:%S) $1"
}

HEAVY="P5ConjR0 P5ConjR1 P5ConjR2 P5ConjR3 P5ConjR4 P5ConjTree P5ConjAux P5ConjBound P5ConjCount \
P5Conj2R0 P5Conj2R1 P5Conj2R2 P5Conj2R3 P5Conj2R4 P5Conj2Tree P5Conj2Aux P5Conj2Bound P5Conj2Count \
P5AllSubgroupsProofs P5AllSubgroupsProofs2 P5FrattiniCert P5FrattiniCert2 \
P5CharRows0 P5CharRows1 P5CharRows2 P5CharRows3 P5CharRows2a P5CharRows2b P5CharRows2c P5CharRows2d \
P5CharRows2e P5CharRows2f P5CharRows2g P5CharRows2h P5CharExp P5CharExp2 \
P5CharComplete P5CharComplete3a P5CharComplete3b P5CharComplete3c P5CharComplete3d P5CharComplete3e \
P5CharComplete3f P5CharComplete3g P5CharComplete3h \
P5CharComplete2_3a P5CharComplete2_3b P5CharComplete2_3c P5CharComplete2_3d P5CharComplete2_3e \
P5CharComplete2_3f P5CharComplete2_3g P5CharComplete2_3h \
P5SpeciesCosets P5SpeciesCosets2 \
P5SpeciesOrbitChunk0 P5SpeciesOrbitChunk1 P5SpeciesOrbitChunk2 P5SpeciesOrbitChunk3 P5SpeciesOrbitChunk4 \
P5SpeciesOrbitChunk5 P5SpeciesOrbitChunk6 P5SpeciesOrbitChunk7 P5SpeciesOrbitChunk8 P5SpeciesOrbitChunk9 \
P5SpeciesOrbitChunk10 P5SpeciesOrbitChunk11 \
P5SpeciesOrbitChunk0_2 P5SpeciesOrbitChunk1_2 P5SpeciesOrbitChunk2_2 P5SpeciesOrbitChunk3_2 \
P5SpeciesOrbitChunk4_2 P5SpeciesOrbitChunk5_2 P5SpeciesOrbitChunk6_2 P5SpeciesOrbitChunk7_2 \
P5SpeciesOrbitChunk8_2 P5SpeciesOrbitChunk9_2 P5SpeciesOrbitChunk10_2 P5SpeciesOrbitChunk11_2 \
P5NormChunk0 P5NormChunk1 P5NormChunk2 P5NormChunk3 P5NormChunk0_2 P5NormChunk1_2 P5NormChunk2_2 P5NormChunk3_2 \
P5EntryDataK1 P5EntryDataK2 P5EntryDataK3 P5EntryDataK4 P5EntryDataK5 P5EntryDataK6 P5EntryDataK7 \
P5EntryDataK8 P5EntryDataK9 P5EntryDataK10 P5EntryDataK11 P5EntryDataK12 \
P5EntryDataK13 P5EntryDataK14 P5EntryDataK15 P5EntryDataK16 P5EntryDataK17 P5EntryDataK18 \
P5EntryDataK19 P5EntryDataK20 P5EntryDataK21 P5EntryDataK22 P5EntryDataK23 P5EntryDataK24 \
P5EntryDataK25 P5EntryDataK26 P5EntryDataK27 P5EntryDataK28 P5EntryDataK29 P5EntryDataK30 \
P5EntryDataK31 P5EntryDataK32 P5EntryDataK33 P5EntryDataK34 P5EntryDataK35 P5EntryDataK36 \
P5EntryDataK37 P5EntryDataK38 P5EntryDataK39 P5EntryDataK40 P5EntryDataK41 P5EntryDataK42 \
P5EntryDataK43 P5EntryDataK44"
# Module names moved out of the old flat LeanDring/Basic/ layout (see
# ARCHITECTURE.md); mapping.tsv (old-path <TAB> new-path, one row per file)
# is the source of truth for the old-name -> new-module translation used
# below, so this script keeps working as long as mapping.tsv does.
# This file is operational, not historical: the build below cannot resolve
# the heavy module names without it.
MAPPING="scripts/mapping.tsv"
if [ ! -f "$MAPPING" ]; then
  echo "FAILED: $MAPPING not found — compile.sh cannot translate the heavy"
  echo "        module names without it (see ARCHITECTURE.md)."
  exit 1
fi

old_to_new_module() {
  # $1: bare old name (e.g. P5ConjR0) that used to live at
  # LeanDring/Basic/$1.lean under module LeanDring.Basic.$1
  awk -F'\t' -v old="LeanDring/Basic/$1.lean" '$1==old{print $2}' "$MAPPING" \
    | sed -e 's/\.lean$//' -e 's#/#.#g'
}

for m in $HEAVY; do
  newmod=$(old_to_new_module "$m")
  if [ -z "$newmod" ]; then echo "FAILED: $m (not found in mapping.tsv)"; exit 1; fi
  progress "$newmod"
  $LAKE build "$newmod" || { echo "FAILED: $m"; exit 1; }
done

# Stage 3-5 certificate layers (divergent chunks, tau, alignment, emptiness,
# assembly dispatch) — serial over the emitted families. The old glob over
# LeanDring/Basic/P5SpeciesDiv*.lean etc. now spans multiple directories
# (LeanDring/P5/Data/<Family>/C*.lean and, for a few small hand-written
# files, LeanDring/P5/Certificate/*.lean) with renamed chunk files, so the
# family membership is looked up from mapping.tsv by old-name prefix instead
# of re-globbing the new tree.
for prefix in P5SpeciesDiv P5SpeciesTau P5SpeciesAlign P5FixZero P5Match; do
  for old in $(awk -F'\t' -v p="LeanDring/Basic/$prefix" 'index($1, p) == 1 {print $1}' "$MAPPING" | sort); do
    newmod=$(awk -F'\t' -v o="$old" '$1==o{print $2}' "$MAPPING" | sed -e 's/\.lean$//' -e 's#/#.#g')
    progress "$newmod"
    $LAKE build "$newmod" || { echo "FAILED: $old"; exit 1; }
  done
done

progress "final full lake build"
$LAKE build
echo "==> compile.sh done ($TOTAL/$TOTAL) $(date +%H:%M:%S)"
