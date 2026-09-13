#!/usr/bin/env bash
# Live probe: run the lane binary on one file of each division, with the EXACT
# flags and envelope the census will use, and require a verdict-shaped line and
# a route trail from each.
#
# A missing binary and a hard division produce the identical empty TSV.  A
# previous board recorded a reference absent on one host and 800 files scoring a
# silent 0/200 that read exactly like a result.
set -u
BIN="${1:-/nas3/data/axeyum/harness/ufnia-uflia/bin/smtcomp_cli-base}"
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/
HERE="$(cd "$(dirname "$0")" && pwd)"
ok=0
for div in UFNIA UFLIA; do
  f="$(head -1 "$HERE/../parity-lists/$div.txt")"
  out=$(AXEYUM_QTRACE=1 timeout 40 taskset -c "${2:-1,9}" \
          bash -c "ulimit -v 8388608; exec \"\$0\" \"\$1\" --trace --timeout-ms 24000" \
          "$BIN" "$f" 2>&1)
  v=$(printf '%s\n' "$out" | grep -m1 -oE '^(sat|unsat|unknown)$')
  r=$(printf '%s\n' "$out" | grep -c 'route decided_by=')
  echo "PROBE $div verdict=${v:-NONE} route_lines=$r file=${f#"$CORPUS"}"
  [ -n "$v" ] && [ "$r" -ge 1 ] && ok=$((ok + 1))
done
[ "$ok" -eq 2 ] && { echo "PROBE-OK"; exit 0; }
echo "PROBE-FAILED $ok of 2"
exit 1
