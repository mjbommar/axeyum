#!/usr/bin/env bash
# QF-WALL -- our verdict on the MINIMAL unsat subset, for the rows the first
# run did not reach, plus the route trail on the two rows whose abstraction
# cannot be built (f07, f10). For those the trail is the only mechanism-level
# instrument available, and it is reported as such.
set -u
W="$(cd "$(dirname "$0")" && pwd)"
AX=/nas3/data/axeyum/harness/qf-wall/bin/smtcomp_cli-qfwall
PIN="${2:-8}"
for id in $1; do
  c="$W/core/$id.core.smt2"; [ -r "$c" ] || { echo "$id NO-CORE"; continue; }
  o=$(env AXEYUM_DECLARED_NAME_WINS=on AXEYUM_DISTINCT_LINEAR=on AXEYUM_TRACE=1 \
      timeout 140 taskset -c "$PIN" "$AX" "$c" --timeout-ms 24000 2>&1)
  v=$(printf '%s\n' "$o" | grep -m1 -oE '^(sat|unsat|unknown)$' || echo NONE)
  printf '%-4s core n=%-4s verdict=%s\n' "$id" "$(grep -c '^(assert' "$c")" "$v"
  printf '%s' "$o" | grep -oE '\{"route":"[^"]*","outcome":"[^"]*"(,"reason":"[^"]*")?(,"detail":"[^"]{0,150})?' \
    | sed 's/,"elapsed_ns.*//' | sort -u | sed 's/^/      /'
done
echo DONE
