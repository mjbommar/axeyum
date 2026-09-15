#!/usr/bin/env bash
# Re-run every MOVED row 3x per arm, sharded one row per core so the whole mover
# set finishes in one row's worth of wall clock rather than in N.
#
# ADR-2100's `recheck-movers.sh` is reused UNCHANGED (it is the thing that
# classifies STABLE-GAIN / STABLE-LOSS / UNSTABLE, and rewriting a classifier
# between two comparisons is how two ADRs stop being comparable). This script
# only shards its input.
#
# WHY RE-CHECK AT ALL. A single interleaved pairing at 24 s carries a measured
# 1-1.5 % ambient flip rate on these boxes. ADR-1966 reported 25 raw movers and
# 22 after re-checking -- 11 of its 18 movers outside the treatment division
# VANISHED -- so the raw column would have overstated the effect by 11 files.
#
# Usage: launch-recheck.sh <movers.txt> <outdir> <binA> <binB> [budget_s]
set -eu
MOVERS="$1"; OUTDIR="$2"; AX_A="$3"; AX_B="$4"; BUDGET="${5:-24}"
REMOTE=/nas3/data/axeyum/harness/route-ownership/scripts
read -r -a HOSTS <<< "${AB_HOSTS:-s5 s6 s7}"
read -r -a CORES <<< "${AB_CORES:-1,9 3,11 5,13 6,14}"
SHARDS=$(( ${#HOSTS[@]} * ${#CORES[@]} ))

[ -s "$MOVERS" ] || { echo "ABORT: $MOVERS is empty -- a recheck of nothing is not a recheck"; exit 2; }
mkdir -p "$OUTDIR/lists"
rm -f "$OUTDIR"/lists/movers.*.txt
awk -v n="$SHARDS" -v out="$OUTDIR/lists" \
  '{ print > sprintf("%s/movers.%02d.txt", out, NR % n) }' "$MOVERS"

echo "movers: $(wc -l < "$MOVERS") across $SHARDS shards"
s=0
for h in "${HOSTS[@]}"; do
  for c in "${CORES[@]}"; do
    sl=$(printf '%s/lists/movers.%02d.txt' "$OUTDIR" "$s")
    so=$(printf '%s/recheck.%02d.tsv' "$OUTDIR" "$s")
    if [ -s "$so" ]; then echo "ABORT: $so already non-empty"; exit 2; fi
    if [ ! -f "$sl" ]; then s=$((s + 1)); continue; fi
    ssh -n -f -- "$h" "cd /tmp && nohup setsid bash $REMOTE/recheck-movers.sh \
          $sl $so '$c' $AX_A $AX_B $BUDGET \
          > $OUTDIR/recheck.$(printf %02d $s).log 2>&1 < /dev/null &"
    echo "LAUNCHED recheck shard $s on $h cores $c ($(wc -l < "$sl") rows)"
    s=$((s + 1))
  done
done
echo "RECHECK-LAUNCH-OK"
