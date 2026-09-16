#!/usr/bin/env bash
# Launch ONE sweep, fully detached, refusing if one is already running for the
# same output directory (two concurrent writers to one ledger is a corrupt
# measurement, not a slow one).
set -u
cd ~/lra-model-replay-work || exit 2
LIST="$1"; OUT="$2"; CORES="$3"; BIN="$4"; ARM="$5"; shift 5
PIDFILE="$OUT.pid"
if [ -f "$PIDFILE" ] && kill -0 "$(cat "$PIDFILE")" 2>/dev/null; then
  echo "REFUSE: $OUT already running as pid $(cat "$PIDFILE")"
  exit 75
fi
setsid nohup bash run-sweep.sh "$LIST" "$OUT" "$CORES" "$BIN" "$ARM" "$@" \
  > "$OUT.log" 2>&1 < /dev/null &
echo $! > "$PIDFILE"
echo "launched $ARM pid $(cat "$PIDFILE") -> $OUT.log"
