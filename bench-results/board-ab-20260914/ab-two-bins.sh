#!/usr/bin/env bash
# Interleaved per-file A/B of TWO BINARIES (a commit comparison, not a lever).
#
# Normally this repo A/Bs one binary under two env values, because two builds can
# differ by more than the change under test. Here the QUESTION IS the commit
# difference, so two binaries is the correct instrument -- and the risk it
# usually carries (accidentally comparing two trees) is the thing being measured.
#
# Both arms run BACK TO BACK on the SAME file on the SAME pinned core, order
# alternating per file, so ambient load cancels in the DIFFERENCE.
#
# Usage: ab-two-bins.sh <tag> <list> <out.tsv> <cores> <binA> <binB> [budget_s]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; AXA="$5"; AXB="$6"; BUDGET="${7:-24}"
HEADROOM=16; VLIM=$((8 * 1024 * 1024))
[ -x "$AXA" ] || { echo "ABORT $TAG: $AXA missing"; exit 2; }
[ -x "$AXB" ] || { echo "ABORT $TAG: $AXB missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT non-empty"; exit 2; }

run() {  # $1 = binary
  local t0 t1 raw v
  t0=$(date +%s%N)
  raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
          "$1" "$f" 2>/dev/null)
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s\t%s' "${v:-none}" "$(( (t1 - t0) / 1000000 ))"
}

printf 'file\tA\tA_ms\tB\tB_ms\tfirst\tstatus\n' > "$OUT"
n=0
while read -r f; do
  [ -z "$f" ] && continue
  n=$((n + 1))
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
  if [ $((n % 2)) -eq 1 ]; then
    a=$(run "$AXA"); b=$(run "$AXB"); first=A
  else
    b=$(run "$AXB"); a=$(run "$AXA"); first=B
  fi
  printf '%s\t%s\t%s\t%s\t%s\n' "$f" "$a" "$b" "$first" "${st:-none}" >> "$OUT"
done < "$LIST"
echo "AB_TWO_BINS_COMPLETE $TAG rows=$(( $(wc -l < "$OUT") - 1 ))"
