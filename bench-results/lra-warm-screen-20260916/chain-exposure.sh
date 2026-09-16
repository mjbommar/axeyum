#!/usr/bin/env bash
# ADR-2132: start this shard's EXPOSURE queue the moment its `QF_LRA` shard is
# done, without a human in the loop.
#
# # Why chained rather than launched by hand
#
# The two `QF_LRA` shards finish at different times and neither finishes at a
# moment anyone is watching. A hand-launched exposure queue costs the gap
# between "the shard finished" and "somebody noticed", and on a queue that then
# runs for hours that gap is the difference between the five divisions being
# measured and being reported as DID NOT RUN -- which is what happened to four
# of them in [ADR-2125].
#
# # It waits on the ARTIFACT, never on a process name
#
# `ab3-run.sh` prints `AB3-DONE <tag> <n> rows` as its last act. That line is
# the condition. A `pgrep -f ab3-run` would match THIS script's own command
# line -- the loop would see itself and never exit -- which is a real incident
# in this repository's history rather than a hypothetical.
#
# The wait is BOUNDED. An unbounded `while true` on a shard that died would hold
# a core pair idle indefinitely and report nothing; at the deadline this says so
# and exits non-zero, which is a finding rather than a silence.
#
# Usage: chain-exposure.sh <shard 00|01> <cores> <bin> <ab-log> [max_wait_s]
set -u
SHARD="$1"; PIN="$2"; AX="$3"; ABLOG="$4"; MAXWAIT="${5:-21600}"

waited=0
while ! grep -q 'AB3-DONE' "$ABLOG" 2>/dev/null; do
  if [ "$waited" -ge "$MAXWAIT" ]; then
    echo "ABORT $SHARD: $ABLOG never printed AB3-DONE in ${MAXWAIT}s -- the QF_LRA shard did not finish, and the exposure queue is NOT started"
    exit 2
  fi
  sleep 60
  waited=$((waited + 60))
done

echo "CHAIN $SHARD: $ABLOG reported AB3-DONE after ${waited}s of waiting; starting the exposure queue $(date -Is)"
exec ./launch-exposure.sh "$SHARD" "$PIN" "$AX"
