#!/usr/bin/env bash
# Per-route timing of the three losing files under both arms, head binary.
set -u
BIN=$1; OUTDIR=$2; PIN=$3; shift 3
mkdir -p "$OUTDIR"
n=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  n=$((n+1))
  for arm in "$@"; do
    tag=$(echo "$arm" | tr " =" "__")
    t0=$EPOCHREALTIME
    env $arm AXEYUM_NIA_DEBUG=1 timeout 40 taskset -c "$PIN" bash -c "ulimit -v $((8*1024*1024)); exec \"\$0\" \"\$1\" --timeout-ms 24000 --trace" "$BIN" "$f" > "$OUTDIR/l$n-$tag.txt" 2>&1
    t1=$EPOCHREALTIME
    echo "l$n $arm wall_ms=$(python3 -c "print(int(($t1-$t0)*1000))") verdict=$(grep -m1 -oE "^(sat|unsat|unknown)$" "$OUTDIR/l$n-$tag.txt") $(basename "$f")"
  done
done < losers3.txt
echo TRACE-DONE
