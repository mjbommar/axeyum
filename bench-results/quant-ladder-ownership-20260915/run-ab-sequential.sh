#!/usr/bin/env bash
# Run ADR-2103's interleaved A/B ONE DIVISION AT A TIME.
#
# WHY THIS EXISTS, and it is a real finding about the runner it wraps.
# ADR-2100's `launch-ab.sh` takes N division specs and launches them ALL at
# once: its loop is `for spec in "$@"` over divisions, inside which it loops
# hosts x cores. With nine divisions that is 9 x 4 = **36 concurrent `ab-run.sh`
# per host, pinned onto 4 core pairs** -- nine solves sharing each physical
# core. Measured on the first launch here: `pgrep -cf ab-run.sh` returned 129,
# 129 and 133 on s5/s6/s7 with one-minute load at ~30 on 16 CPUs.
#
# That does not merely make the run slow, it dismantles the property the whole
# design rests on. `ab-run.sh`'s header says both arms run "back to back on the
# SAME file on the SAME pinned physical core" so that ambient load "cancels in
# the DIFFERENCE rather than landing entirely on whichever arm ran second" --
# and at 9x oversubscription each 24 s solve gets about a ninth of a core, so
# nearly everything times out and both columns collapse toward `unknown`. A
# wash of `unknown` reads exactly like "no movement", which is how a
# measurement manufactures a null.
#
# One division at a time is 12 shards across three hosts -- one shard per pinned
# core pair, which is what ADR-2100's own prose describes ("12 shards across
# s5/s6/s7"). It costs about nine times the wall clock and it is the only
# version of this run that measures anything.
#
# Usage: run-ab-sequential.sh <binA> <binB> <outdir> <budget_s> <div> [...]
set -eu
HERE="$(cd "$(dirname "$0")" && pwd)"
AX_A="$1"; AX_B="$2"; OUTDIR="$3"; BUDGET="$4"; shift 4

for DIV in "$@"; do
  echo "=== $DIV: launching 12 shards ==="
  bash "$HERE/launch-ab.sh" "$AX_A" "$AX_B" "$OUTDIR" "$BUDGET" "$DIV"
  # Wait for THIS division's shards to finish before the next is launched.
  # Watching the artifact, not the process: a `pgrep` loop whose own command
  # line contains the pattern it greps for never exits.
  while :; do
    done_n=0
    for log in "$OUTDIR/$DIV".shard*.log; do
      [ -f "$log" ] || continue
      if grep -q "^AB-DONE" "$log" 2>/dev/null; then done_n=$((done_n + 1)); fi
    done
    total=$(ls "$OUTDIR/$DIV".shard*.log 2>/dev/null | wc -l)
    [ "$total" -gt 0 ] && [ "$done_n" -eq "$total" ] && break
    sleep 20
  done
  rows=$(cat "$OUTDIR/$DIV".shard*.tsv 2>/dev/null | grep -vc '^file' || true)
  echo "=== $DIV: DONE, $rows rows ==="
done
echo "AB-SEQUENTIAL-COMPLETE"
