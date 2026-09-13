#!/usr/bin/env bash
# Stage the harness onto the shared NAS path every board host reads, and split
# each pinned 200 into two modulo-interleaved shards.
#
# Shards are NR%2 through the pinned list, so each shard spans the whole
# division; the merged TSV is re-ordered back into the pinned list's order, so
# the artifact does not encode the shard split.
#
# FP's pinned list is `FP-fullspan.txt`, not `FP.txt` -- see mklist.py.  The
# harness tag is still `FP`; the mapping is here and nowhere else.
set -eu
LANE="$(cd "$(dirname "$0")" && pwd)"
H=/nas3/data/axeyum/harness/tier1-divisions

mkdir -p "$H/lists" "$H/out" "$H/census"
cp "$LANE/shard-run.sh" "$LANE/chain-run.sh" "$LANE/census-run.sh" \
   "$LANE/probe.sh" "$H/"
chmod +x "$H/shard-run.sh" "$H/chain-run.sh" "$H/census-run.sh" "$H/probe.sh"

stage_one() { # $1 tag  $2 list stem
  local src="$LANE/../parity-lists/$2.txt"
  [ -f "$src" ] || { echo "ABORT: $src missing"; exit 2; }
  awk 'NR%2==1' "$src" > "$H/lists/$1.s0"
  awk 'NR%2==0' "$src" > "$H/lists/$1.s1"
  local a b
  a=$(wc -l < "$H/lists/$1.s0"); b=$(wc -l < "$H/lists/$1.s1")
  [ $((a + b)) = 200 ] || { echo "ABORT: $1 shards are $a + $b"; exit 2; }
  echo "staged $1 from $2.txt: $a + $b"
}

stage_one AUFLIRA AUFLIRA
stage_one UFNIA   UFNIA
stage_one ABV     ABV
stage_one ALIA    ALIA
stage_one AUFNIRA AUFNIRA
stage_one AUFBV   AUFBV
stage_one FP      FP-fullspan
echo STAGE-OK
