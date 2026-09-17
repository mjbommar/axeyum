#!/usr/bin/env bash
# Interleaved per-file A/B of TWO BINARIES (a commit comparison, not a lever).
# Copied from bench-results/board-ab-20260914/ab-two-bins.sh with two changes:
#   * wall time is read from $EPOCHREALTIME, not `date +%s%N` -- s5's `date` is
#     uutils and its %N ignores the width (memory: s7-date-prints-nanoseconds);
#   * each arm's EXIT STATUS is recorded as its own column (ADR-2045 measured
#     `losses=0` by verdict and five new ABORTs underneath it).
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
HA=$(sha256sum "$AXA" | cut -d' ' -f1); HB=$(sha256sum "$AXB" | cut -d' ' -f1)
[ "$HA" = "$HB" ] && { echo "ABORT $TAG: both arms are the SAME binary"; exit 2; }

ms_now() { local t=$EPOCHREALTIME; echo $(( ${t%.*} * 1000 + 10#${t#*.} / 1000 )); }

run() {  # $1 = binary
  local t0 t1 raw rc v
  t0=$(ms_now)
  raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
          "$1" "$f" 2>/dev/null)
  rc=$?
  t1=$(ms_now)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s\t%s\t%s' "${v:-none}" "$(( t1 - t0 ))" "$rc"
}

printf 'file\tA\tA_ms\tA_rc\tB\tB_ms\tB_rc\tfirst\tstatus\n' > "$OUT"
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
