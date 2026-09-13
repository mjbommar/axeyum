#!/usr/bin/env bash
# How often does each guard this lane added actually FIRE?
#
# ADR-1927 wrote a fourth guard, measured it firing 0 times over 800 corpus
# files, and DELETED it: "a guard with no reachable trigger is the un-failable
# checker this repository keeps deleting". This script is that measurement, so
# the same standard can be applied here rather than assumed.
#
# It reads the ROUTE TRAIL, not the give-up line: a guard that fires records a
# `declined` entry with `reason":"unsupported"` under its route name, and that
# entry exists whether or not the query is eventually decided. Counting
# give-ups instead would only see the guards on files that still fail.
#
# Usage: guard-firing.sh <fix-bin> <outdir> <core0> <division>...
set -u
AX="$1"; OUT="$2"; CORE0="$3"; shift 3
HERE="$(cd "$(dirname "$0")" && pwd)"
LISTS="$HERE/../parity-lists"
BUDGET="${BUDGET:-3}"
HEADROOM="${HEADROOM:-4}"
VLIM=$((8 * 1024 * 1024))
mkdir -p "$OUT"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

i=0
for d in "$@"; do
  core=$((CORE0 + i)); i=$((i + 1))
  (
    : > "$OUT/$d.trails"
    while read -r f; do
      [ -n "$f" ] || continue
      timeout $((BUDGET + HEADROOM)) taskset -c "$core" \
        bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
        "$AX" "$f" 2>/dev/null | grep -m1 'route-trail' >> "$OUT/$d.trails"
    done < "$LISTS/$d.txt"
    echo "TRAILS-DONE $d $(wc -l < "$OUT/$d.trails")"
  ) > "$OUT/$d.log" 2>&1 &
done
wait
echo "GUARD-FIRING-DONE $*"
