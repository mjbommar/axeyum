#!/usr/bin/env bash
# SINGLE-ARM post-merge board run: what does merged `main` actually decide?
#
# This is deliberately NOT an A/B. A lane's A/B measures its BRANCH; this
# measures the tree that shipped. Same envelope as every board on this corpus:
# 24 s wall, 8 GiB `ulimit -v`, one pinned physical core, one file at a time.
#
# The shipped arm is the UNSET environment (ADR-1980 ships `Decline` ON), so the
# variable is explicitly stripped rather than merely not set -- a remote login
# shell that exports it would otherwise measure the historical arm silently.
#
# Usage: board-run.sh <tag> <list> <out.tsv> <cores> <bin> [budget_s]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; AX="$5"; BUDGET="${6:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT is non-empty; refusing to overwrite"; exit 2; }

printf 'file\tverdict\tms\trc\tstatus\n' > "$OUT"
while read -r f; do
  [ -z "$f" ] && continue
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
  t0=$(date +%s%N)
  raw=$(env -u AXEYUM_DATATYPE_NATIVE_REFUSAL timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$f" 2>/dev/null)
  rc=$?
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s\t%s\t%s\t%s\t%s\n' "$f" "${v:-none}" "$(( (t1 - t0) / 1000000 ))" "$rc" "${st:-none}" >> "$OUT"
done < "$LIST"
echo "BOARD_RUN_COMPLETE $TAG rows=$(( $(wc -l < "$OUT") - 1 ))"
