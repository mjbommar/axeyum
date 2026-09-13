#!/usr/bin/env bash
# Launch ONE shard of one division on a named host and a named physical core.
#
# The finest-grained placement primitive, needed because a re-sharded division
# does not fit the "two shards, one host" shape: UFNIA was split five ways
# across two boxes so it would not be a 3.3 h long pole on its own.
#
# It refuses if the shard's output file already has rows, so a second launch
# cannot quietly replace a measured shard with one taken under different
# conditions.
#
# Usage: launch-shard.sh <host> <DIV> <shard> <cores>
#   e.g. launch-shard.sh s6 UFNIA s0 3,11
set -eu
H=/nas3/data/axeyum/harness/tier1-divisions
HOST="$1"; DIV="$2"; S="$3"; C="$4"

[ -f "$H/lists/$DIV.$S" ] || { echo "ABORT: $H/lists/$DIV.$S missing"; exit 2; }
if [ -s "$H/out/$DIV.$S.tsv" ]; then
  echo "ABORT: $H/out/$DIV.$S.tsv already has rows -- refusing to re-measure"
  exit 2
fi

ssh -o BatchMode=yes "$HOST" \
  "nohup \"$H/shard-run.sh\" \"$DIV.$S\" \"$H/lists/$DIV.$S\" \"$H/out/$DIV.$S.tsv\" $C \
   > $H/out/$DIV.$S.log 2>&1 & sleep 1; echo launched $DIV.$S on \$(hostname) core $C"
