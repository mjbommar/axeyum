#!/usr/bin/env bash
# Where does the BUDGET go on the rows ADR-2045 attributes to the dense engine?
#
# ADR-2045 split its `Timeout/ResourceLimit` bucket on the engines' own counters
# and concluded "34 of 34 rows have cube_matrices=0 and cube_simplex_calls>0;
# Fourier-Motzkin never ran" -- which is correct, and establishes that the
# SIMPLEX ran rather than the elimination. It does not establish that the
# simplex spent the budget: a call counter says a thing happened, not that it
# dominated.  `--trace`'s `; lazy-smt` line carries the milliseconds:
#
#   cube_simplex_ms   the offline dense engine
#   skeleton_ms       the Boolean skeleton the lazy-SMT loop re-solves
#   theory_ms         the online theory propagation
#   cube_collect_ms   constraint collection
#   accounted_ms      their sum, against a 24 000 ms budget
#
# Captured raw, one line per file, so the attribution can be re-split without
# re-running.
#
# Usage: attrib-run.sh <tag> <list> <out.tsv> <logdir> <cores> <bin> [budget_s]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; LOGD="$4"; PIN="$5"; BIN="$6"; BUDGET="${7:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))

[ -x "$BIN" ] || { echo "ABORT $TAG: $BIN missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT non-empty"; exit 2; }
mkdir -p "$LOGD"

printf 'file\tkey\tverdict\trc\tms\tmaxrss_kb\tlazy\troute\n' > "$OUT"

while read -r f; do
  [ -z "$f" ] && continue
  key=$(printf '%s' "$f" | sha1sum | cut -c1-12)
  so="$LOGD/$key.out"; se="$LOGD/$key.err"
  t0=$(date +%s%N)
  ( ulimit -v "$VLIM"
    exec /usr/bin/time -f '%M' -o "$se.rss" \
      timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
      "$BIN" "$f" --timeout-ms $((BUDGET * 1000)) --trace
  ) > "$so" 2> "$se"
  rc=$?
  t1=$(date +%s%N)
  v=$(grep -m1 -oE '^(sat|unsat|unknown)$' "$so")
  rss=$(tail -1 "$se.rss" 2>/dev/null | grep -oE '^[0-9]+$')
  lz=$(grep -m1 '^; lazy-smt' "$so" 2>/dev/null | tr '\t' ' ')
  rt=$(grep -m1 '^; route ' "$so" 2>/dev/null | tr '\t' ' ')
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$f" "$key" "${v:-none}" "$rc" "$(( (t1 - t0) / 1000000 ))" "${rss:-na}" \
    "${lz:-none}" "${rt:-none}" >> "$OUT"
  gzip -f "$so" 2>/dev/null
  rm -f "$se" "$se.rss"
done < "$LIST"
echo "ATTRIB_COMPLETE $TAG rows=$(( $(wc -l < "$OUT") - 1 ))"
