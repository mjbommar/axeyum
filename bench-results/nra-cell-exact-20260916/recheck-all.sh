#!/usr/bin/env bash
# Three passes per arm on every mover, pinned and alternating, after the sweeps
# have released the cores.
#
# ONE binary behind TWO wrapper scripts, so `recheck-movers.sh`'s same-binary
# guard still means something: the wrappers differ, the binary does not.
#
# Usage: recheck-all.sh [wait-for-log]
set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
WAIT_LOG="${1:-}"
CORE=1

if [ -n "$WAIT_LOG" ]; then
  # Watch the ARTIFACT, not a process.
  for _ in $(seq 1 720); do
    if [ -f "$WAIT_LOG" ] && grep -q 'ab-sweep-heldout: complete' "$WAIT_LOG"; then break; fi
    sleep 15
  done
  if ! grep -q 'ab-sweep-heldout: complete' "$WAIT_LOG"; then
    echo "recheck-all: ABORT -- held-out sweep never finished; refusing to share cores" >&2
    exit 2
  fi
fi

for tag in qfnra qfnraheldout; do
  list="$HERE/movers-$tag-abs.txt"
  out="$HERE/recheck-$tag.tsv"
  if [ ! -s "$list" ]; then
    echo "recheck-all: $tag has no movers -- nothing to recheck" >&2
    continue
  fi
  rm -f "$out"
  "$HERE/recheck-movers.sh" "$list" "$out" "$CORE" \
    "$HERE/arm-a-sat-default.sh" "$HERE/arm-b-single-cell.sh" 24
done
echo "recheck-all: complete" >&2
