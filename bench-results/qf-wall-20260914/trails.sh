#!/usr/bin/env bash
# QF-WALL -- the route trail per row, on the QUANTIFIER-FREE skeleton.
# Reports the detected fragment and the DISTINCT decline reasons, deduplicated,
# because the ladder repeats itself once per string_bound widening and the raw
# trail is four identical passes.
set -u
W="$(cd "$(dirname "$0")" && pwd)"
AX=/nas3/data/axeyum/harness/qf-wall/bin/smtcomp_cli-qfwall
PIN="${1:-6}"
out="$W/trails.txt"; : > "$out"
for i in $(seq -w 1 13); do
  id="f$i"; f="$W/skel/$id.smt2"
  [ -r "$f" ] || continue
  o=$(env AXEYUM_TRACE=1 timeout 120 taskset -c "$PIN" "$AX" "$f" --timeout-ms 24000 2>&1)
  v=$(printf '%s\n' "$o" | grep -m1 -oE '^(sat|unsat|unknown)$' || echo NONE)
  frag=$(printf '%s' "$o" | grep -oE '"detail":"fragment [^"]*"' | head -1 | cut -d'"' -f4)
  att=$(printf '%s' "$o" | grep -oE 'attempts=[0-9]+' | head -1)
  {
    printf '===== %s  verdict=%s  %s  %s\n' "$id" "$v" "${frag:-no-fragment-line}" "${att:-no-attempts}"
    printf '%s' "$o" | grep -oE '\{"route":"[^"]*","outcome":"[^"]*"(,"reason":"[^"]*")?(,"kind":"[^"]*")?(,"detail":"[^"]*")?' \
      | sed 's/,"elapsed_ns.*//' | sort -u
  } >> "$out"
done
echo "DONE $out"
