#!/usr/bin/env bash
# Are the control and exposure divisions' zeros zeros over a LIVE division, or
# over 200 instant declines?
#
# A zero from a division the change cannot reach is not evidence, and a control
# whose rows all decline in milliseconds proves nothing about drift. So:
#
#   EXPOSURE (QF_UFLRA) must SHARE the changed code. Shown by running its rows
#   under AXEYUM_LRADENSEPROBE=1 and counting entries into the offline route
#   `lra::simplex_fallback` -- the function this lane rewrote. A nonzero count
#   is the proof; a zero would mean the exposure division was never exposed.
#
#   CONTROL (QF_S) must be a live division bound by a DIFFERENT route. Shown by
#   naming the route its undecided rows bind on (from `; route bound_by=`) and
#   by the offline LRA route NOT executing there.
#
# Usage: nonvacuity.sh <list> <label> <bin> [n]
set -u
LIST="$1"; LABEL="$2"; BIN="$3"; N="${4:-12}"
B=8000
VLIM=$((8 * 1024 * 1024))

echo "== $LABEL: first $N rows =="
entries=0; rows=0; declare -A BOUND=()
while read -r f; do
  rows=$((rows + 1))
  [ "$rows" -gt "$N" ] && break
  so=$(mktemp); se=$(mktemp)
  ( ulimit -v $VLIM
    env AXEYUM_LRADENSEPROBE=1 timeout 40 "$BIN" "$f" --timeout-ms $B --trace
  ) > "$so" 2> "$se"
  e=$(grep -c 'site=simplex-fallback-entry' "$se")
  entries=$((entries + e))
  b=$(grep -m1 '^; route ' "$so" | grep -oE 'bound_by=[^ ]+' | cut -d= -f2)
  v=$(grep -m1 -oE '^(sat|unsat|unknown)$' "$so")
  ms=$(grep -m1 '^; route ' "$so" | grep -oE 'total_ms=[0-9]+' | cut -d= -f2)
  BOUND["${b:-none}"]=$(( ${BOUND["${b:-none}"]:-0} + 1 ))
  printf '  %-7s %-9s offline-entries=%-4s total_ms=%-6s %s\n' \
    "${v:-none}" "${b:-none}" "$e" "${ms:-na}" "$(basename "$f" | cut -c1-44)"
  rm -f "$so" "$se"
done < "$LIST"

echo "  ---"
echo "  TOTAL entries into lra::simplex_fallback (the changed code): $entries"
echo -n "  routes the rows bound on: "
for k in "${!BOUND[@]}"; do printf '%s=%s ' "$k" "${BOUND[$k]}"; done
echo
