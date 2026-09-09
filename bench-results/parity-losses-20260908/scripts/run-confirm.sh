#!/usr/bin/env bash
# Confirm pass: re-run only what pass 1 left `unsolved`, on pinned slots.
# See `unsolved-of.sh` for why the pass is one-sided.
#
# Usage: run-confirm.sh "<cores>:<DIV>[,<DIV>...]" ...
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
outdir="$here/.."
mkdir -p "$outdir/confirm" "$outdir/frames"
i=0
for spec in "$@"; do
  cores="${spec%%:*}"
  divs="${spec#*:}"
  (
    echo "confirm slot $i cores=$cores divs=$divs start $(date -Is) load=$(cut -d' ' -f1-3 /proc/loadavg)" \
      > "$outdir/frames/confirm-slot$i.frame"
    IFS=',' read -ra dl <<< "$divs"
    for d in "${dl[@]}"; do
      taskset -c "$cores" bash "$here/sweep.sh" "$outdir/pending/$d.txt" "$d" "$outdir/confirm/$d.tsv"
      echo "  $d done $(date -Is) load=$(cut -d' ' -f1-3 /proc/loadavg)" \
        >> "$outdir/frames/confirm-slot$i.frame"
    done
    echo "confirm slot $i end $(date -Is) load=$(cut -d' ' -f1-3 /proc/loadavg)" \
      >> "$outdir/frames/confirm-slot$i.frame"
  ) &
  i=$((i + 1))
done
wait
echo "confirm done $(date -Is)"
