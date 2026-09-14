#!/usr/bin/env bash
# QFLRA-GAP census runner.
#
# Purpose: re-derive the QF_LRA population ON THE CURRENT TREE and capture
# EVERY cause channel, so the census can be re-split later WITHOUT re-running.
#
# Four cause channels exist and only the first is a "give-up string":
#   1. `; give-up kind=... detail=...` on stdout  (solver/ingest/watchdog)
#   2. the VERDICT line itself                    (sat/unsat/unknown)
#   3. the PROCESS EXIT STATUS                    (134 = abort, 124 = wall kill)
#   4. STDERR                                     (allocation failure prints ONLY here)
# Channel 4 is how the board's 40 `none` rows die and it emits no `; give-up`
# line at all -- so a census built on channel 1 alone would silently lose them.
#
# Two arms per file, back to back on the same pinned core, order alternating:
#   T = --trace    (the census instrument)
#   P = plain      (the competition-identical run; the population of record)
# This measures whether --trace perturbs the population rather than assuming it
# does not, and gives the trace overhead for free.
#
# Usage: census-run.sh <tag> <list> <out.tsv> <logdir> <cores> <bin> [budget_s]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; LOGD="$4"; PIN="$5"; BIN="$6"; BUDGET="${7:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))   # 8 GiB, identical to the board run

[ -x "$BIN" ] || { echo "ABORT $TAG: $BIN missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT non-empty"; exit 2; }
mkdir -p "$LOGD"

# One run. Echoes: verdict \t exit \t wall_ms \t maxrss_kb
# Raw stdout and stderr are left in $so / $se for the caller to mine.
run() {   # $1 = extra flag ("" or "--trace"), $2 = stdout path, $3 = stderr path
  local extra="$1" so="$2" se="$3" t0 t1 rc v rss
  t0=$(date +%s%N)
  ( ulimit -v $VLIM
    exec /usr/bin/time -f '%M' -o "$se.rss" \
      timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
      "$BIN" "$f" --timeout-ms $((BUDGET * 1000)) $extra
  ) > "$so" 2> "$se"
  rc=$?
  t1=$(date +%s%N)
  v=$(grep -m1 -oE '^(sat|unsat|unknown)$' "$so")
  rss=$(tail -1 "$se.rss" 2>/dev/null | grep -oE '^[0-9]+$')
  printf '%s\t%s\t%s\t%s' "${v:-none}" "$rc" "$(( (t1 - t0) / 1000000 ))" "${rss:-na}"
}

printf 'file\tT\tT_rc\tT_ms\tT_rss\tP\tP_rc\tP_ms\tP_rss\tfirst\tstatus\tgiveup\tstderr1\n' > "$OUT"
n=0
while read -r f; do
  [ -z "$f" ] && continue
  n=$((n + 1))
  key=$(printf '%s' "$f" | sha1sum | cut -c1-12)
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
  if [ $((n % 2)) -eq 1 ]; then
    t=$(run "--trace" "$LOGD/$key.T.out" "$LOGD/$key.T.err")
    p=$(run ""        "$LOGD/$key.P.out" "$LOGD/$key.P.err")
    first=T
  else
    p=$(run ""        "$LOGD/$key.P.out" "$LOGD/$key.P.err")
    t=$(run "--trace" "$LOGD/$key.T.out" "$LOGD/$key.T.err")
    first=P
  fi
  # Channel 1: every `; give-up` line from the trace arm, joined -- NOT just the
  # first. A run that gives up more than once must not be collapsed to one label.
  g=$(grep -h '^; give-up' "$LOGD/$key.T.out" 2>/dev/null \
        | tr '\t' ' ' | paste -sd '~' -)
  # Channel 4: first non-empty stderr line of the PLAIN arm.
  e=$(grep -m1 -v '^[[:space:]]*$' "$LOGD/$key.P.err" 2>/dev/null | tr '\t' ' ' | cut -c1-200)
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$f" "$t" "$p" "$first" "${st:-none}" "${g:-none}" "${e:-none}" >> "$OUT"
done < "$LIST"
echo "CENSUS_COMPLETE $TAG rows=$(( $(wc -l < "$OUT") - 1 ))"
