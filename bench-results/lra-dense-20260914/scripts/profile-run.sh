#!/usr/bin/env bash
# LRA-DENSE profile runner -- priority 1: where does the memory ACTUALLY go?
#
# ADR-2045 measured a 5.07 GiB median peak RSS over this division and named two
# allocations on the offline dense LRA route, but `/usr/bin/time -v` reports one
# number for the whole process and cannot say which structure holds it.
#
# `AXEYUM_LRADENSEPROBE=1` reports the resident set at four points on that route.
# The SHAPE (nvars, m, nnz, tableau_cells) and the resident set are both printed
# at `feasible_within-entry`, which is BEFORE the tableau is allocated -- so a
# row that dies IN that allocation has still reported everything needed to price
# it. That is why this runs at the board's own `ulimit -v 8G` rather than needing
# 24 GiB of headroom per shard.
#
# This script CAPTURES and does not summarise: the per-row probe log is kept
# (gzipped) so the profile can be re-split later without re-running, which is
# the discipline ADR-2045's own census runner was built on. `profile.py` does
# every derivation.
#
# Channels, because a verdict alone loses the abort bucket entirely:
#   verdict, process exit status (134 = abort, 124 = wall kill), wall ms,
#   peak RSS from /usr/bin/time, first non-probe stderr line.
#
# Usage: profile-run.sh <tag> <list> <out.tsv> <logdir> <cores> <bin> [budget_s] [vlim_kb]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; LOGD="$4"; PIN="$5"; BIN="$6"
BUDGET="${7:-24}"; VLIM="${8:-$((8 * 1024 * 1024))}"
HEADROOM=16

[ -x "$BIN" ] || { echo "ABORT $TAG: $BIN missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT non-empty"; exit 2; }
mkdir -p "$LOGD"

printf 'file\tkey\tverdict\trc\tms\tmaxrss_kb\tstderr1\n' > "$OUT"

while read -r f; do
  [ -z "$f" ] && continue
  key=$(printf '%s' "$f" | sha1sum | cut -c1-12)
  so="$LOGD/$key.out"; se="$LOGD/$key.err"
  t0=$(date +%s%N)
  ( ulimit -v "$VLIM"
    export AXEYUM_LRADENSEPROBE=1
    exec /usr/bin/time -f '%M' -o "$se.rss" \
      timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
      "$BIN" "$f" --timeout-ms $((BUDGET * 1000))
  ) > "$so" 2> "$se"
  rc=$?
  t1=$(date +%s%N)
  v=$(grep -m1 -oE '^(sat|unsat|unknown)$' "$so")
  rss=$(tail -1 "$se.rss" 2>/dev/null | grep -oE '^[0-9]+$')
  e=$(grep -v LRADENSEPROBE "$se" 2>/dev/null | grep -m1 -v '^[[:space:]]*$' | tr '\t' ' ' | cut -c1-160)
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$f" "$key" "${v:-none}" "$rc" "$(( (t1 - t0) / 1000000 ))" "${rss:-na}" "${e:-none}" >> "$OUT"
  gzip -f "$se" 2>/dev/null
done < "$LIST"
echo "PROFILE_COMPLETE $TAG rows=$(( $(wc -l < "$OUT") - 1 ))"
