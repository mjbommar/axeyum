#!/usr/bin/env bash
# ZERO-INST -- run one A/B phase across a FIXED shard configuration.
#
#   ab-launch.sh <phase> <list> <outdir> [budget_s]
#
# SHARD CONFIGURATION, HELD FIXED ACROSS ARMS AND PHASES:
#   s5 cores {1,3,5}   s6 cores {1,3,5}   = 6 pinned pairs, and never more.
# Both arms of a file run INSIDE one shard, back to back on one core, so a
# shard can never move one arm relative to the other.
#
# Files are assigned to shards ROUND-ROBIN by line index, not by contiguous
# block: these lists are PATH-SORTED, so a contiguous split puts a whole
# division on one core and confounds shard with subject.
set -eu
PHASE="$1"
LIST="$2"
OUTDIR="$3"
BUDGET="${4:-24}"
HERE="$(cd "$(dirname "$0")" && pwd)"
AX=/nas3/data/axeyum/harness/zero-inst/bin/smtcomp_cli-lever
SHARDS=("s5:1" "s5:3" "s5:5" "s6:1" "s6:3" "s6:5")
STAGE=/nas3/data/axeyum/harness/zero-inst/stage

mkdir -p "$OUTDIR" "$STAGE"
cp "$HERE"/ab-run*.sh "$STAGE/"
chmod +x "$STAGE"/*.sh

RUNNER=ab-run.sh
if [ "$PHASE" = noise ]; then
  RUNNER=ab-run-noise.sh
fi

n=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  s=$((n % ${#SHARDS[@]}))
  printf '%s\n' "$f" >> "$OUTDIR/shard$s.list"
  n=$((n + 1))
done < "$LIST"
echo "$PHASE: $n files over ${#SHARDS[@]} shards, budget=${BUDGET}s runner=$RUNNER"

i=0
for sh in "${SHARDS[@]}"; do
  host="${sh%%:*}"
  core="${sh##*:}"
  L="$OUTDIR/shard$i.list"
  if [ -f "$L" ]; then
    R="$STAGE/$PHASE.shard$i.list"
    cp "$L" "$R"
    rm -f "$STAGE/$PHASE.shard$i.tsv"
    ssh -o BatchMode=yes "$host" \
      "nohup setsid $STAGE/$RUNNER $R $STAGE/$PHASE.shard$i.tsv $core $AX $BUDGET \
         > $STAGE/$PHASE.shard$i.log 2>&1 < /dev/null &" >/dev/null 2>&1
    echo "  launched $PHASE shard$i on $host core $core ($(wc -l < "$L") files)"
  fi
  i=$((i + 1))
done
echo "$PHASE: all shards launched; results land in $STAGE/$PHASE.shard*.tsv"
