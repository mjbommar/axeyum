#!/usr/bin/env bash
# WHY does adding a cap CREATE process aborts?
#
# The A/B's exit-status channel found arm C (AXEYUM_LRA_CELL_CAP=1) turning 18
# rows that terminate cleanly in the base into rc=134 aborts, and losing one row
# that was `sat`. A cap is supposed to convert an abort INTO a decline, so this
# is the opposite of the intended direction and the mechanism has to be named
# rather than inferred.
#
# Two hypotheses, and the counts below separate them:
#
#   H1  "the freed BUDGET is spent worse".  The dense tableau was a time sink;
#       declining it hands the query ~24 s it did not have, and the route that
#       then runs allocates more than the tableau the cap refused.
#       Signature: entries into the offline route stay ~the same, the give-up
#       changes from a clock/watchdog reason to an allocation failure.
#
#   H2  "the LOOP runs away".  Each lazy-SMT round used to cost seconds in the
#       tableau; now each costs microseconds, so the cube loop spins orders of
#       magnitude more rounds and the blocking clauses / cores it accumulates
#       are what exhausts memory.
#       Signature: entries into the offline route explode between the arms.
#
# Usage: cap-abort-probe.sh <file> <bin>
set -u
F="$1"; BIN="$2"
VLIM=$((8 * 1024 * 1024))
B=24000
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT

probe() {  # $1 = label, rest = env assignments
  local label="$1"; shift
  ( ulimit -v $VLIM
    env "$@" AXEYUM_LRADENSEPROBE=1 timeout 60 "$BIN" "$F" --timeout-ms $B --trace
  ) > "$T/$label.out" 2> "$T/$label.err"
  local rc=$?
  echo "== $label =="
  echo "   exit          : $rc"
  echo "   verdict       : $(grep -m1 -oE '^(sat|unsat|unknown)$' "$T/$label.out" || echo none)"
  echo "   give-up       : $(grep -m1 '^; give-up' "$T/$label.out" | cut -c1-140)"
  echo "   stderr        : $(grep -v LRADENSEPROBE "$T/$label.err" | grep -m1 -v '^[[:space:]]*$' | cut -c1-110)"
  echo "   offline-route entries : $(grep -c 'site=simplex-fallback-entry' "$T/$label.err")"
  echo "   tableaux BUILT        : $(grep -c 'site=tableau-built' "$T/$label.err")"
  echo "   cap declines          : $(grep -c 'site=cell-cap-declined' "$T/$label.err")"
  echo "   lazy-smt      : $(grep -m1 '^; lazy-smt' "$T/$label.out" \
      | tr ' ' '\n' | grep -E '^(lra_rounds|blocking_clauses|blocking_literals|cube_simplex_ms|skeleton_ms)=' | tr '\n' ' ')"
}

probe base AXEYUM_UNUSED=0
probe cap  AXEYUM_LRA_CELL_CAP=1
