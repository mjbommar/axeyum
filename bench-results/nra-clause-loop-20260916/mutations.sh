#!/usr/bin/env bash
# Run the two ADR-2131 mutation suites.
#
# `killed N` is the only outcome that supports a coverage claim. SURVIVED is a
# real finding (the guard is not load-bearing); DID NOT BUILD, DID NOT RUN, NOT
# APPLIED and AMBIGUOUS ANCHOR are not results at all, and the harness prints
# them apart for exactly that reason.
set -u
cd "$(dirname "$0")/../.." || exit 2
LOG="${1:?usage: mutations.sh <log-path>}"

python3 -P scripts/tests/mutation_controls.py \
  nra-clause-loop-certified-unsat nra-clause-loop-certificate > "$LOG" 2>&1
rc=$?
echo "MUTATIONS rc=$rc"
grep -E 'killed|SURVIVED|DID NOT|NOT APPLIED|AMBIGUOUS|INCONSISTENT' "$LOG" | tail -20
echo "MUTATIONS_DONE"
exit "$rc"
