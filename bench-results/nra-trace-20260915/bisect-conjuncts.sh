#!/usr/bin/env bash
# Bisect one benchmark by conjunct count: which conjunct takes the query out of
# the exact decider's reach (ADR-2110, lane NRA-TRACE).
#
# For N = 1..K, emit the first N conjuncts and report the verdict and the route
# that decided or held the budget. The prefix is a WEAKER query, so an `unsat`
# on it transfers to the whole file and a `sat` on it does not -- the column is
# labelled accordingly and no conclusion is drawn from a prefix `sat`.
#
# Usage: bisect-conjuncts.sh --file F --bin PATH --outdir DIR [--budget-ms 20000]
set -u

FILE=""; BIN=""; OUT=""; BUDGET_MS=20000
HERE="$(cd -- "$(dirname -- "$0")" && pwd)"

while [ $# -gt 0 ]; do
  case "$1" in
    --file) FILE="$2"; shift 2 ;;
    --bin) BIN="$2"; shift 2 ;;
    --outdir) OUT="$2"; shift 2 ;;
    --budget-ms) BUDGET_MS="$2"; shift 2 ;;
    *) echo "bisect-conjuncts: unknown argument $1" >&2; exit 2 ;;
  esac
done
for required in FILE BIN OUT; do
  if [ -z "${!required}" ]; then
    echo "bisect-conjuncts: --${required,,} is required" >&2; exit 2
  fi
done
mkdir -p "$OUT" || exit 2

total="$(python3 "$HERE/flatten-conjuncts.py" "$FILE" "$OUT/all.smt2" \
         | awk '{print $1}')"
if [ -z "$total" ]; then
  echo "bisect-conjuncts: flatten produced no conjunct count" >&2; exit 2
fi

printf 'n\tverdict\tdecided_by\tbound_by\tms\n'
n=1
while [ "$n" -le "$total" ]; do
  python3 "$HERE/flatten-conjuncts.py" "$FILE" "$OUT/n$n.smt2" --first "$n" \
    > /dev/null
  log="$OUT/n$n.log"
  t0=$(date +%s%N)
  timeout $(( BUDGET_MS / 1000 + 16 )) "$BIN" "$OUT/n$n.smt2" \
    --timeout-ms "$BUDGET_MS" --trace > "$log" 2>&1
  t1=$(date +%s%N)
  v="$(grep -m1 -oE '^(sat|unsat|unknown)$' "$log" || true)"
  dec="$(grep -m1 -oE 'decided_by=[^ ]+' "$log" | cut -d= -f2 || true)"
  bnd="$(grep -m1 -oE 'bound_by=[^ ]+' "$log" | cut -d= -f2 || true)"
  printf '%s\t%s\t%s\t%s\t%s\n' \
    "$n" "${v:-none}" "${dec:-none}" "${bnd:-none}" "$(( (t1 - t0) / 1000000 ))"
  n=$(( n + 1 ))
done
