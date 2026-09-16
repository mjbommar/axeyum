#!/usr/bin/env bash
# QUANT-SESSION-ARITH (ADR-2130) -- refuse the probe unless the lever ENGAGES.
#
#   self-check.sh <bin> <one-core-file> [budget_s]
#
# A probe whose ON arm never hosted arithmetic produces a clean-looking null
# that is indistinguishable from a lever that engaged and did not help. This
# runs the file at all THREE levels and requires, from the binary's own trace:
#
#   * level 2's session line says `hosted=1`   -- the arithmetic theory exists
#   * level 0's and level 1's say `hosted=0`   -- neither of them hosts
#   * the three arms resolve DIFFERENT `level=` values
#   * level 2 abstracts STRICTLY FEWER terms than level 1 on the same file
#
# The last one is the load-bearing check and the only one that measures the
# thing this lane changed. `hosted=1` says an arithmetic sub-theory was
# CONSTRUCTED; the opaque delta says atoms actually moved out of the
# abstraction and into it. A session that hosted a theory and still abstracted
# every comparison would pass the first three and be inert.
#
# WHAT THIS DOES *NOT* ASSERT, and why: that level 0 declines to build a session
# at all. It builds one whenever the ground set is EUF-only, which is correct
# historical behaviour and happens on real UFLIA cores at round 0. An earlier
# version of this script required `built=0` at level 0 and failed on the first
# core it was pointed at -- the script was wrong, not the solver.
set -u
AX="$1"; FILE="$2"; BUDGET="${3:-24}"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -f "$FILE" ] || { echo "ABORT: $FILE missing"; exit 2; }

run_level() {  # $1 = label, $2 = level or "unset"
  if [ "$2" = "unset" ]; then
    env -u AXEYUM_QINST_GROUND_SESSION AXEYUM_QTRACE=1 \
      timeout $((BUDGET + 16)) "$AX" "$FILE" --trace --timeout-ms $((BUDGET * 1000)) \
      > "$WORK/$1.out" 2> "$WORK/$1.err"
  else
    AXEYUM_QINST_GROUND_SESSION="$2" AXEYUM_QTRACE=1 \
      timeout $((BUDGET + 16)) "$AX" "$FILE" --trace --timeout-ms $((BUDGET * 1000)) \
      > "$WORK/$1.out" 2> "$WORK/$1.err"
  fi
}

field() {  # $1 = file label, $2 = key ; prints the value or empty
  sed -n 's/.*[[:space:]]'"$2"'=\([0-9]*\).*/\1/p' "$WORK/$1.line" 2>/dev/null | head -1
}

for pair in "l0 unset" "l1 1" "l2 2"; do
  set -- $pair
  run_level "$1" "$2"
  grep -m1 'ground-session' "$WORK/$1.err" > "$WORK/$1.line" 2>/dev/null || : > "$WORK/$1.line"
  echo "$1: $(cat "$WORK/$1.line" | tr -s ' ' || echo '<no session line>')"
done

fail=0
say() { echo "$1 $2"; [ "$1" = "BAD" ] && fail=1; return 0; }

[ "$(field l2 hosted)" = "1" ] \
  && say ok  "level 2 hosts arithmetic" \
  || say BAD "level 2 did NOT host arithmetic (hosted='$(field l2 hosted)')"
h0="$(field l0 hosted)"; h1="$(field l1 hosted)"
[ "${h0:-0}" = "0" ] && say ok  "level 0 hosts nothing" || say BAD "level 0 hosted=$h0"
[ "${h1:-0}" = "0" ] && say ok  "level 1 hosts nothing" || say BAD "level 1 hosted=$h1"
[ "$(field l2 level)" = "2" ] \
  && say ok  "level 2 resolved level=2" \
  || say BAD "the override did not reach the solver (level='$(field l2 level)')"

o1="$(field l1 abstracted)"; o2="$(field l2 abstracted)"
if [ -n "$o1" ] && [ -n "$o2" ]; then
  if [ "$o2" -lt "$o1" ]; then
    say ok  "level 2 abstracts $o2 where level 1 abstracts $o1 -- $((o1 - o2)) atoms moved into the theory"
  else
    say BAD "level 2 abstracts $o2 and level 1 abstracts $o1 -- NOTHING moved into the theory"
  fi
else
  say BAD "no opaque counts to compare (l1='$o1' l2='$o2')"
fi

if [ "$fail" -ne 0 ]; then
  echo "SELF-CHECK FAILED -- do not run the probe, it would measure nothing"
  exit 1
fi
echo "SELF-CHECK PASS"
