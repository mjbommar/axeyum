#!/usr/bin/env bash
# QUANT-SESSION-ARITH (ADR-2130) -- the z3 differential fuzzes.
#
#   gates-z3.sh <logfile>
#
# These are the ONLY checks that compare our verdicts against an independent
# solver, and they compile to ZERO tests without `--features z3` -- the same
# silent-inertness trap the corpus sweep has. The summary prints each suite's
# TEST COUNT, and a zero count is reported as a failure of the gate rather than
# as a pass, because "running 0 tests ... ok" is what an inert gate prints.
set -u
LOG="${1:-/tmp/qsa-gates-z3.log}"
cd "$(dirname "$0")/../.." || exit 2
: > "$LOG"

for suite in qf_uflra_differential_fuzz qf_lia_differential_fuzz qf_lra_differential_fuzz; do
  echo "=== STEP $suite ===" >> "$LOG"
  scripts/cargo-serialized.sh test -p axeyum-solver --features z3 --test "$suite" >> "$LOG" 2>&1
  echo "=== RC $suite = $? ===" >> "$LOG"
done
echo "ALL-STEPS-DONE" >> "$LOG"

echo
echo "== SUMMARY (a ZERO test count is an INERT gate, not a pass) =="
awk '
  /^=== STEP /    { label=$3 }
  /^test result:/ { counts[label] = counts[label] $0 " " }
  /^=== RC /      { rc[$3]=$5; order[++n]=$3 }
  END {
    for (i=1; i<=n; i++) {
      l=order[i]
      c = counts[l] ? counts[l] : "(NO test-result line -- suite did not run)"
      printf "%-34s rc=%-3s %s\n", l, rc[l], c
    }
  }
' "$LOG"
