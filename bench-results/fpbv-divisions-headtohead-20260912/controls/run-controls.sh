#!/usr/bin/env bash
# The two checkers in this directory must be able to FAIL.  This runs each
# against a fixture that contains exactly the finding it exists to report, and
# fails if the finding does not appear.
#
# `board-fixture.tsv` carries three rows:
#   a  we say unsat, :status/z3/cvc5 all say sat   -> 3 disagreements, one row
#   b  everyone agrees sat                          -> must produce NOTHING
#   c  we are wrapper-killed, z3 decides            -> 1 winnable, 1 kill, 1 rc134
# Row b is the inverted-control half: a checker that flagged it too would be
# reporting agreement as disagreement and its zero would mean nothing.
#
# `census-fixture.tsv` carries four rows:
#   a  attempts=9 == ladder, unknown  -> the ONLY rankable row
#   b  attempts=3  < ladder           -> UNCLASSIFIED, must not be ranked
#   c  no route trail at all          -> its own row, not an absence
#   d  attempts=9, decided            -> excluded, not a blocker
#   e  attempts=6, kind=Error         -> UNCLASSIFIED for ranking, but the
#                                        internal error message is REPORTED
#                                        anyway, with its repro path
set -u
cd "$(dirname "$0")"
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
fail=0

cp ../summarize.py "$T"/
for d in QF_ABVFP QF_BVFP QF_UFBV; do cp board-fixture.tsv "$T/$d.tsv"; done
b=$(cd "$T" && python3 summarize.py)

grep -q "DISAGREEMENTS: 3" <<<"$b" \
  || { echo "FAIL: the disagreement check did not fire on the injected row"; fail=1; }
grep -q "a/y.smt2" <<<"$b" \
  && { echo "FAIL: the agreeing row was reported (inverted control)"; fail=1; }
grep -q "winnable (we unknown, a reference decides): 1" <<<"$b" \
  || { echo "FAIL: the winnable set was miscounted"; fail=1; }
grep -q "'ax': 1" <<<"$b" \
  || { echo "FAIL: the wrapper-killed count did not surface"; fail=1; }

mkdir -p "$T/census"
cp ../census-summarize.py "$T"/
cp census-fixture.tsv "$T/census/QF_ABVFP.tsv"
c=$(cd "$T" && python3 census-summarize.py)

grep -q "CLASSIFIED 1   UNCLASSIFIED 2   no-route 1   decided-on-recheck 1" <<<"$c" \
  || { echo "FAIL: the ADR-1936 partition is wrong"; fail=1; }
grep -q "TERMINAL INTERNAL ERROR: 1" <<<"$c" \
  || { echo "FAIL: the internal-error row was not reported"; fail=1; }
grep -A3 "TERMINAL INTERNAL ERROR" <<<"$c" | grep -q "repro: e.smt2" \
  || { echo "FAIL: the internal-error row was reported without a repro path"; fail=1; }
ranked() { sed -n '/classified give-up reasons/,/^   -- /p' <<<"$c" | grep '^      '; }
ranked | grep -q "array projection" \
  && { echo "FAIL: an internal-error row was RANKED as a capability blocker"; fail=1; }
grep -q "1  Incomplete: bit-blast too big" <<<"$c" \
  || { echo "FAIL: the rankable row was not ranked"; fail=1; }
ranked | grep -q "Watchdog" \
  && { echo "FAIL: an UNCLASSIFIED row was ranked by its give-up reason"; fail=1; }
grep -q "census DID NOT RUN" <<<"$c" \
  || { echo "FAIL: a missing census renders the same as an empty one"; fail=1; }

[ "$fail" = 0 ] && echo "CONTROLS-OK: both checkers fired on the finding and stayed silent otherwise"
exit "$fail"
