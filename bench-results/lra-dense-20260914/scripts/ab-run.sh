#!/usr/bin/env bash
# LRA-DENSE interleaved A/B.
#
# POLARITY, stated here so it cannot be inferred from a result:
#   A  = base       -- BOTH levers UNSET.  This is what ships today.
#   A2 = base again -- the IDENTICAL configuration to A.  Its row-level
#                      disagreement with A is the NOISE FLOOR, measured in this
#                      same run against the same neighbours rather than borrowed
#                      from another pass taken at another time.
#   B  = AXEYUM_LRA_SPARSE_ROWS=1                       (drop the round trip)
#   C  = AXEYUM_LRA_CELL_CAP=1                          (consult MAX_TABLEAU_CELLS)
#   D  = both                                           (what would ship)
#
# ONE BINARY, FIVE ENVIRONMENT VALUES. Never two builds: two builds cannot be
# interleaved on the same core against the same file, which is how this
# repository's benchmark noise gets mistaken for an effect.
#
# The five arms run BACK TO BACK on the same file on the same pinned core, and
# the starting arm ROTATES with the file index, so no arm is systematically
# first (first place is worth real milliseconds on a cold page cache).
#
# Channels per arm, because a verdict count MISSES a loss -- ADR-2045's arm was
# `losses=0` by verdict and created five new process aborts:
#   verdict, PROCESS EXIT STATUS (134 abort / 124 wall kill), wall ms, peak RSS.
#
# Usage: ab-run.sh <tag> <list> <out.tsv> <logdir> <cores> <bin> [budget_s]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; LOGD="$4"; PIN="$5"; BIN="$6"; BUDGET="${7:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))   # 8 GiB, identical to the board run

[ -x "$BIN" ] || { echo "ABORT $TAG: $BIN missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT non-empty"; exit 2; }
mkdir -p "$LOGD"

# One run under one arm. Echoes: verdict \t exit \t wall_ms \t maxrss_kb
run() {   # $1 = arm letter, $2 = stdout path, $3 = stderr path
  local arm="$1" so="$2" se="$3" t0 t1 rc v rss sp cap
  sp=; cap=
  case "$arm" in
    A|A2) ;;
    B)  sp=1 ;;
    C)  cap=1 ;;
    D)  sp=1; cap=1 ;;
  esac
  t0=$(date +%s%N)
  ( ulimit -v $VLIM
    [ -n "$sp" ]  && export AXEYUM_LRA_SPARSE_ROWS=1
    [ -n "$cap" ] && export AXEYUM_LRA_CELL_CAP=1
    exec /usr/bin/time -f '%M' -o "$se.rss" \
      timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
      "$BIN" "$f" --timeout-ms $((BUDGET * 1000))
  ) > "$so" 2> "$se"
  rc=$?
  t1=$(date +%s%N)
  v=$(grep -m1 -oE '^(sat|unsat|unknown)$' "$so")
  rss=$(tail -1 "$se.rss" 2>/dev/null | grep -oE '^[0-9]+$')
  printf '%s\t%s\t%s\t%s' "${v:-none}" "$rc" "$(( (t1 - t0) / 1000000 ))" "${rss:-na}"
}

printf 'file\tA\tA_rc\tA_ms\tA_rss\tA2\tA2_rc\tA2_ms\tA2_rss\tB\tB_rc\tB_ms\tB_rss\tC\tC_rc\tC_ms\tC_rss\tD\tD_rc\tD_ms\tD_rss\tfirst\tstatus\n' > "$OUT"

ORDER=("A A2 B C D" "A2 B C D A" "B C D A A2" "C D A A2 B" "D A A2 B C")
n=0
while read -r f; do
  [ -z "$f" ] && continue
  key=$(printf '%s' "$f" | sha1sum | cut -c1-12)
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
  seq=${ORDER[$((n % 5))]}
  first=${seq%% *}
  declare -A R=()
  for arm in $seq; do
    R[$arm]=$(run "$arm" "$LOGD/$key.$arm.out" "$LOGD/$key.$arm.err")
    rm -f "$LOGD/$key.$arm.err" "$LOGD/$key.$arm.err.rss" "$LOGD/$key.$arm.out"
  done
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$f" "${R[A]}" "${R[A2]}" "${R[B]}" "${R[C]}" "${R[D]}" "$first" "${st:-none}" >> "$OUT"
  n=$((n + 1))
done < "$LIST"
echo "AB_COMPLETE $TAG rows=$(( $(wc -l < "$OUT") - 1 ))"
