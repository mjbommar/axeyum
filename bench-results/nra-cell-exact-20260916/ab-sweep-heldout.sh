#!/usr/bin/env bash
# The HELD-OUT QF_NRA A/B: same arms, same protocol, same cores, fresh files.
#
# Waits for the pinned sweep to finish before starting, because the two share
# the four pinned cores and an interleaved A/B measures the DIFFERENCE between
# two arms on one core — which only survives contention if the contention is the
# same for both arms. Two sweeps on the same cores would break that for both.
#
# Usage: ab-sweep-heldout.sh /path/to/smtcomp_cli [wait-for-log]
set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
BIN="${1:?usage: ab-sweep-heldout.sh /path/to/smtcomp_cli [wait-for-log]}"
WAIT_LOG="${2:-}"
CORES=(1 9 3 11)
TAG=exact
DIV=qfnraheldout

if [ -n "$WAIT_LOG" ]; then
  # Watch the ARTIFACT, not a process: a `pgrep` loop whose own command line
  # contains the pattern never exits.
  for _ in $(seq 1 720); do
    if [ -f "$WAIT_LOG" ] && grep -q 'SWEEP_EXIT=' "$WAIT_LOG"; then break; fi
    sleep 15
  done
  if ! grep -q 'SWEEP_EXIT=' "$WAIT_LOG"; then
    echo "ab-sweep-heldout: ABORT -- pinned sweep never finished; refusing to share cores" >&2
    exit 2
  fi
fi

sha256sum "$BIN" > "$HERE/ab-$TAG-heldout-binary-sha256.txt"

pids=()
for i in 0 1 2 3; do
  "$HERE/ab-run.sh" \
    --list "$HERE/shard$i-$DIV.txt" \
    --out "$HERE/ab-$TAG-$DIV-shard$i.tsv" \
    --shard "$i" --core "${CORES[$i]}" \
    --binary "$BIN" --arm-b single-cell --budget-s 24 \
    > "$HERE/ab-$TAG-$DIV-shard$i.log" 2>&1 &
  pids+=($!)
done
rc=0
for p in "${pids[@]}"; do wait "$p" || rc=1; done
echo "ab-sweep-heldout: complete (rc=$rc)" >&2
