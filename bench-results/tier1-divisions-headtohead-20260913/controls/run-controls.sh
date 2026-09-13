#!/usr/bin/env bash
# The three checkers in this lane must be able to FAIL.  This runs each against
# a fixture containing exactly the finding it exists to report, and fails if the
# finding does not appear -- and, in the other direction, fails if a row that
# should produce NOTHING is reported.  A checker that flags everything has a
# zero worth as little as one that flags nothing.
#
# `board-fixture.tsv` (3 rows, 2 decided = 66.7 %):
#   a  we say unsat, :status/z3/cvc5 all say sat   -> 3 disagreements, one row
#   b  everyone agrees sat                          -> must produce NOTHING
#   c  we are wrapper-killed, z3 decides            -> 1 winnable, 1 kill, 1 rc134
#   66.7 % is outside every division's probe interval -> REFUTED.
#
# `board-fixture-lowrate.tsv` (10 rows, 2 decided = 20.0 %):
#   exactly UFNIA's probe rate, inside its interval -> CONFIRMED, and every row
#   agrees so it is a second inverted control on the disagreement check.
#
# `census-fixture.tsv`:
#   a  attempts=9, kind=Error, PARSE refusal -> RANKED (this lane's split)
#   b  attempts=3, open segment              -> UNCLASSIFIED, never ranked
#   c  no route trail at all                 -> its own row, not an absence
#   d  attempts=9, decided                   -> excluded, not a blocker
#   e  attempts=6, kind=Error, NOT parse     -> internal error: listed with a
#                                               repro, NEVER ranked
#   f  attempts=6, no open segment           -> ADR-1941: ran to the end of its
#                                               OWN shorter ladder, so RANKED
#   g  ROUND reason, total_ms=3              -> ms_left 23,997, clock NOT binding
#   h  CLOCK reason, total_ms=24,051         -> ms_left -51, clock-bound
#   g and h are the ADR-1950 pair: both say "budget", opposite findings.
set -u
cd "$(dirname "$0")"
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
fail=0

# ---------------------------------------------------------------- board
cp ../summarize.py "$T"/
for d in AUFLIRA ABV ALIA AUFNIRA AUFBV FP; do cp board-fixture.tsv "$T/$d.tsv"; done
cp board-fixture-lowrate.tsv "$T/UFNIA.tsv"
b=$(cd "$T" && python3 summarize.py)

grep -q "DISAGREEMENTS: 3" <<<"$b" \
  || { echo "FAIL: the disagreement check did not fire on the injected row"; fail=1; }
grep -q "a/y.smt2" <<<"$b" \
  && { echo "FAIL: the agreeing row was reported (inverted control)"; fail=1; }
grep -q "winnable (we unknown, a reference decides): 1" <<<"$b" \
  || { echo "FAIL: the winnable set was miscounted"; fail=1; }
grep -q "'ax': 1" <<<"$b" \
  || { echo "FAIL: the wrapper-killed count did not surface"; fail=1; }

# ADR-1950 has nothing to say about a board, but this lane's PURPOSE is the
# probe verdict, so it gets the same treatment: it must be able to say both
# words, and must say them from the arithmetic rather than from a literal.
grep -q "ALIA .*REFUTED (board HIGHER)" <<<"$b" \
  || { echo "FAIL: a board far outside the probe interval was not REFUTED"; fail=1; }
grep -q "UFNIA .*CONFIRMED" <<<"$b" \
  || { echo "FAIL: a board AT the probe rate was not CONFIRMED"; fail=1; }
# ALIA's probe was 0 of 24.  A normal-approximation interval at k=0 is the
# single point 0.0, which would make EVERY possible board refute it -- a
# verdict manufactured by the wrong interval rather than measured.  The Wilson
# upper bound must be a real number above zero.
grep -qE "ALIA .*CI +0\.0% *- *1[0-9]\.[0-9]%" <<<"$b" \
  || { echo "FAIL: the k=0 interval is degenerate; every board would 'refute' it"; fail=1; }
grep -q "== FP: board DID NOT RUN" <<<"$b" \
  && { echo "FAIL: FP fixture was not picked up (test is not testing FP)"; fail=1; }

# ---------------------------------------------------------------- census
mkdir -p "$T/census" "$T/winnable"
cp ../census-summarize.py ../census-crossdiv.py "$T"/
cp census-fixture.tsv "$T/census/AUFLIRA.tsv"
printf '/c/AUFLIRA/a.smt2\n/c/AUFLIRA/b.smt2\n/c/AUFLIRA/c.smt2\n/c/AUFLIRA/d.smt2\n/c/AUFLIRA/e.smt2\n/c/AUFLIRA/f.smt2\n/c/AUFLIRA/g.smt2\n/c/AUFLIRA/h.smt2\n' \
  > "$T/winnable/AUFLIRA.txt"
c=$(cd "$T" && python3 census-summarize.py)

grep -q "CLASSIFIED 4   UNCLASSIFIED 1   no-route 1   decided-on-recheck 1   internal-error 1" <<<"$c" \
  || { echo "FAIL: the ADR-1936/1941 partition is wrong"; fail=1; }
grep -q "would call 3 rows UNCLASSIFIED; 1 of them actually carry an open segment" <<<"$c" \
  || { echo "FAIL: the two ADR-1941 readings were not both published"; fail=1; }

ranked() { sed -n '/classified give-up reasons/,/^   -- UNCLASSIFIED/p' <<<"$c"; }
ranked | grep -q "ran to the end of a shorter ladder" \
  || { echo "FAIL: a row with a SHORT ladder and no open segment was not ranked"; fail=1; }
ranked | grep -q "nested array element sort is unsupported" \
  || { echo "FAIL: a front-door PARSE refusal was not ranked as a capability gap"; fail=1; }
ranked | grep -q "array projection" \
  && { echo "FAIL: an internal-error row was RANKED as a capability blocker"; fail=1; }
ranked | grep -q "Watchdog" \
  && { echo "FAIL: an UNCLASSIFIED row was ranked by its give-up reason"; fail=1; }
grep -q "TERMINAL INTERNAL ERROR: 1" <<<"$c" \
  || { echo "FAIL: the internal-error row was not reported"; fail=1; }
grep -A3 "TERMINAL INTERNAL ERROR" <<<"$c" | grep -q "repro: e.smt2" \
  || { echo "FAIL: the internal-error row was reported without a repro path"; fail=1; }
grep -q "census DID NOT RUN" <<<"$c" \
  || { echo "FAIL: a missing census renders the same as an empty one"; fail=1; }

# ADR-1950: rows g and h both say "budget exhausted"; they are opposite
# findings and the ms_left line is what tells them apart.  If either note goes
# missing, or both rows get the SAME note, the census has merged them.
ranked | grep -q "round budget" \
  || { echo "FAIL: the ROUND row was not ranked"; fail=1; }
ranked | grep -A1 "round budget" | grep -q "ms_left min 23997 med 23997 max 23997  \[clock NOT binding\]" \
  || { echo "FAIL: ADR-1950 -- a ROUND row was not shown with its unspent budget"; fail=1; }
ranked | grep -A1 "time budget exhausted after e-matching" | grep -q "\[clock-bound\]" \
  || { echo "FAIL: ADR-1950 -- a CLOCK row was not shown as clock-bound"; fail=1; }

# ---------------------------------------------------------------- cross-division
x=$(cd "$T" && python3 census-crossdiv.py)
grep -q "nested array element sort refused (PARSE)" <<<"$x" \
  || { echo "FAIL: the crossdiv table lost the nested-array family"; fail=1; }
grep -qE "^AUFLIRA +8 +1 +12%" <<<"$x" \
  || { echo "FAIL: the nested-array SHARE table is wrong (1 of 8 winnable = 12%)"; fail=1; }
grep -q "'PARSE': 1" <<<"$x" \
  || { echo "FAIL: PARSE did not appear as its own kind"; fail=1; }
grep -q "'INTERNAL': 1" <<<"$x" \
  || { echo "FAIL: an internal error was not separated from the capability kinds"; fail=1; }
grep -q "census DID NOT RUN for" <<<"$x" \
  || { echo "FAIL: six missing censuses rendered as six empty ones"; fail=1; }
# The OTHER bucket must be printed IN FULL.  A catch-all that silently absorbs
# a family leaves a total that looks stable and is wrong.
grep -q "OTHER bucket, in full" <<<"$x" \
  || { echo "FAIL: the OTHER bucket is not printed"; fail=1; }

[ "$fail" = 0 ] && echo "CONTROLS-OK: all three checkers fired on the finding and stayed silent otherwise"
exit "$fail"
