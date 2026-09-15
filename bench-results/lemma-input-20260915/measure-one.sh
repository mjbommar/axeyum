#!/usr/bin/env bash
# LEMMA-INPUT -- run ONE row under the ATTRIBUTION binary (R2) and print the
# LAST `; li-stats` reading plus the verdict, the exit status and peak RSS.
#
# The instrument reports once a second on stderr because the rows under study
# are killed by the watchdog: a report emitted at return would never exist.
# A row that finishes in under a second therefore prints NO li-stats line, and
# that is written as `NOREAD`, never as zero (R3).
set -u
F="$1"; BUDGET="${2:-24}"; PIN="${3:-0}"
CORPUS="${LI_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
AX="${LI_AX:-/data0/axeyum/lemma-input-target-measure/release/examples/smtcomp_cli}"
OUT=$(mktemp -t "li-measure-XXXXXX")
trap 'rm -f "$OUT"' EXIT

/usr/bin/time -f 'li-maxrss %M' -o "$OUT.rss" \
  taskset -c "$PIN" timeout $((BUDGET + 120)) \
  "$AX" "$CORPUS/$F" --timeout-ms $((BUDGET * 1000)) > "$OUT" 2>"$OUT.err"
status=$?

verdict=$(grep -m1 -E '^(sat|unsat|unknown)$' "$OUT" || true)
[ -n "$verdict" ] || verdict=NOVERDICT
stats=$(grep '^; li-stats ' "$OUT.err" | tail -1 || true)
[ -n "$stats" ] || stats="; li-stats NOREAD"
rss=$(awk '/li-maxrss/{print $2}' "$OUT.rss" 2>/dev/null || echo NA)
printf '%s\t%s\t%s\t%s\t%s\n' "$F" "$verdict" "$status" "$rss" "${stats#; li-stats }"
rm -f "$OUT.err" "$OUT.rss"
