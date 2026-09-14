#!/usr/bin/env bash
# NOISE FLOOR: the SAME arm against ITSELF, one whole division.
#
# Identical to ab-run.sh in every respect except that BOTH arms are the BASE
# configuration (`AXEYUM_MEMORY_LIMIT_MB` unset).  Any row that "moves" here
# moved for no reason at all, so this is the band below which an A/B delta
# means nothing.  The band is assumed NON-ZERO until measured (R5).
#
# Usage: nf-run.sh <tag> <list> <out.tsv> <cores> <bin> [budget_s]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; BIN="$5"; BUDGET="${6:-24}"
HEADROOM=16; VLIM=$((8 * 1024 * 1024))
[ -x "$BIN" ] || { echo "ABORT $TAG: $BIN missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT non-empty"; exit 2; }

run() {
  local t0 t1 raw v rc
  t0=$(date +%s%N)
  raw=$( ( ulimit -v $VLIM
           exec timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
             "$BIN" "$f" --timeout-ms $((BUDGET * 1000)) ) 2>/dev/null )
  rc=$?
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s\t%s\t%s' "${v:-none}" "$rc" "$(( (t1 - t0) / 1000000 ))"
}

printf 'file\tbase\tbase_rc\tbase_ms\tarm\tarm_rc\tarm_ms\tfirst\tstatus\n' > "$OUT"
n=0
while read -r f; do
  [ -z "$f" ] && continue
  n=$((n + 1))
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
  a=$(run); b=$(run)
  if [ $((n % 2)) -eq 1 ]; then first=base; else first=arm; fi
  printf '%s\t%s\t%s\t%s\t%s\n' "$f" "$a" "$b" "$first" "${st:-none}" >> "$OUT"
done < "$LIST"
echo "NF_COMPLETE $TAG rows=$(( $(wc -l < "$OUT") - 1 ))"
