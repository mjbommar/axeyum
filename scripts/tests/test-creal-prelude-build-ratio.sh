#!/usr/bin/env bash
# Controls for `scripts/check-creal-prelude-build-ratio.sh`.
#
# Every case drives the gate through canned harness transcripts and a private
# pin file, so the whole suite costs milliseconds and NEVER runs a prelude
# build. That is deliberate twice over: a control suite nobody can afford to run
# does not get run, and mutating the tracked pin file to test a guard would
# break every other lane reading it.
#
# Each case names the ONE guard it exists to kill. Mutation-verified: with that
# guard removed, exactly this case dies and the others stay green.
# `--self-table` prints the guard/case mapping so a future reader can re-run the
# verification.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"

# Overridable so the mutation verification below can point the whole suite at a
# COPY with one guard removed. Never mutate the tracked file in a shared
# checkout: other lanes read it while your mutant is on disk.
GATE="${AXEYUM_RATIO_GATE_UNDER_TEST:-scripts/check-creal-prelude-build-ratio.sh}"

if [ "${1:-}" = "--self-table" ]; then
  cat <<'TABLE'
Measured 2026-08-28 by deleting each guard from a COPY of the gate and running
this suite against it. `killed` is how many cases died.

guard in the gate                             killed  cases
--------------------------------------------  ------  --------------------------------
G1  `1 passed` count check                          3  under_budget_is_green,
                                                       over_budget_is_red,
                                                       vacuous_zero_test_run_is_rejected
G2  `finished in Xs` must parse                     1  unparsable_transcript_is_rejected
G3  reference >= 1.0 s                              1  tiny_reference_is_rejected
G4  ratio > budget  =>  RED                         2  under_budget_is_green,
                                                       over_budget_is_red
G6  exactly one pinned row                          1  two_pinned_rows_is_rejected
G7  budget must be a positive number                1  non_numeric_budget_is_rejected

G1 kills three, and that is the coupling working rather than a weak suite: the
gate's own self-demonstration feeds a zero-test transcript through the SAME
`extract_seconds`, so removing the count check makes the self-check fire and
every green path dies with it. G4 kills two because a positive and a negative
case share one comparison, which is what a matched pair is for.

G5 (the self-demonstration itself) is not separately killable by a black-box
case: deleting it leaves a gate that still reports the right verdict, which is
exactly the class of defect it exists to catch and exactly why it cannot be
tested from outside. It is verified by INVERSION instead --
`self_check_fires_when_comparison_is_broken` neuters `verdict` in a COPY of the
gate and requires the self-check to notice.

Re-run the verification: for each row, `sed` the guard out of a copy, set
AXEYUM_RATIO_GATE_UNDER_TEST to it, and run this suite.
TABLE
  exit 0
fi

TMP="$(mktemp -d "${TMPDIR:-/tmp}/creal-ratio-controls.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT

PASS=0
FAIL=0

ok()   { PASS=$((PASS + 1)); printf 'ok   %s\n' "$1"; }
bad()  { FAIL=$((FAIL + 1)); printf 'FAIL %s -- %s\n' "$1" "$2"; }

transcript() {  # $1 = out file, $2 = passed-count line fragment, $3 = seconds
  cat >"$1" <<EOF

running 1 test
test $2 ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 936 filtered out; finished in $3s

EOF
}

pin() {  # $1 = out file, $2 = budget
  {
    echo "# private pin for the control suite"
    printf 'subject\treference\tbudget_ratio\n'
    printf 'creal::creal_tests::creal_prelude_builds\trat_prelude::rat_prelude_tests::rat_prelude_builds\t%s\n' "$2"
  } >"$1"
}

SUB="$TMP/sub.txt"
REF="$TMP/ref.txt"
PIN="$TMP/pin.tsv"

run_gate() {
  AXEYUM_CREAL_RATIO_PIN_FILE="$PIN" \
  AXEYUM_CREAL_RATIO_FAKE_SUBJECT="$SUB" \
  AXEYUM_CREAL_RATIO_FAKE_REFERENCE="$REF" \
    bash "${1:-$GATE}" --check >"$TMP/out" 2>&1
  echo $?
}

# --- the POSITIVE control ---------------------------------------------------
# Without this, every guard below could be satisfied by a gate that always
# fails, which is not a gate either.
transcript "$SUB" "creal::creal_tests::creal_prelude_builds" "105.51"
transcript "$REF" "rat_prelude::rat_prelude_tests::rat_prelude_builds" "5.22"
pin "$PIN" 21
STATUS="$(run_gate)"
if [ "$STATUS" = "0" ] && /usr/bin/grep -q 'GREEN -- 20.21' "$TMP/out"; then
  ok "under_budget_is_green (positive control: 105.51/5.22 = 20.21 <= 21)"
else
  bad "under_budget_is_green" "status=$STATUS out=$(cat "$TMP/out")"
fi

# --- G4: the budget comparison actually bites -------------------------------
# The real measured pair at 77b71bf10 was 12.60/4.85 = 2.60 and at HEAD
# 105.51/5.22 = 20.21. This drives the HEAD pair against a baseline-era pin.
pin "$PIN" 3
STATUS="$(run_gate)"
if [ "$STATUS" != "0" ] && /usr/bin/grep -q 'RED -- 20.21 > 3' "$TMP/out"; then
  ok "over_budget_is_red (G4)"
else
  bad "over_budget_is_red (G4)" "status=$STATUS out=$(cat "$TMP/out")"
fi

# --- G1: the vacuity guard --------------------------------------------------
# `--exact` on a renamed test matches nothing, prints `0 passed ... ok`, and
# exits 0. A gate that times that reports a fast, green, meaningless number.
pin "$PIN" 21
cat >"$SUB" <<'EOF'

running 0 tests

test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 937 filtered out; finished in 0.00s

EOF
STATUS="$(run_gate)"
if [ "$STATUS" != "0" ] && /usr/bin/grep -q 'did not run exactly one passing test' "$TMP/out"; then
  ok "vacuous_zero_test_run_is_rejected (G1)"
else
  bad "vacuous_zero_test_run_is_rejected (G1)" "status=$STATUS out=$(cat "$TMP/out")"
fi

# --- G2: an unparsable transcript is not silently a zero --------------------
cat >"$SUB" <<'EOF'

running 1 test
test creal::creal_tests::creal_prelude_builds ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 936 filtered out
EOF
STATUS="$(run_gate)"
if [ "$STATUS" != "0" ] && /usr/bin/grep -q "no parsable 'finished in Xs' line" "$TMP/out"; then
  ok "unparsable_transcript_is_rejected (G2)"
else
  bad "unparsable_transcript_is_rejected (G2)" "status=$STATUS out=$(cat "$TMP/out")"
fi

# --- G3: a degenerate reference makes the ratio meaningless -----------------
transcript "$SUB" "creal::creal_tests::creal_prelude_builds" "105.51"
transcript "$REF" "rat_prelude::rat_prelude_tests::rat_prelude_builds" "0.01"
STATUS="$(run_gate)"
if [ "$STATUS" != "0" ] && /usr/bin/grep -q 'the ratio would be noise' "$TMP/out"; then
  ok "tiny_reference_is_rejected (G3)"
else
  bad "tiny_reference_is_rejected (G3)" "status=$STATUS out=$(cat "$TMP/out")"
fi
transcript "$REF" "rat_prelude::rat_prelude_tests::rat_prelude_builds" "5.22"

# --- G6: the pin file must say exactly one thing ----------------------------
{
  printf 'subject\treference\tbudget_ratio\n'
  printf 'a\tb\t21\n'
  printf 'c\td\t7\n'
} >"$PIN"
STATUS="$(run_gate)"
if [ "$STATUS" != "0" ] && /usr/bin/grep -q 'expected exactly one pinned row' "$TMP/out"; then
  ok "two_pinned_rows_is_rejected (G6)"
else
  bad "two_pinned_rows_is_rejected (G6)" "status=$STATUS out=$(cat "$TMP/out")"
fi

# --- G7: a budget that is not a number would compare as 0 in awk ------------
pin "$PIN" "twenty-one"
STATUS="$(run_gate)"
if [ "$STATUS" != "0" ] && /usr/bin/grep -q 'is not a positive number' "$TMP/out"; then
  ok "non_numeric_budget_is_rejected (G7)"
else
  bad "non_numeric_budget_is_rejected (G7)" "status=$STATUS out=$(cat "$TMP/out")"
fi

# --- G5, by inversion: the self-demonstration catches a dead comparison -----
# Deleting G5 leaves a gate that still gives the right answer, so no black-box
# case can kill it. What CAN be shown is that it does its job: neuter `verdict`
# in a COPY (never the tracked file -- other lanes read it), and require the
# self-check to notice.
pin "$PIN" 21
BROKEN="$TMP/broken-gate.sh"
/usr/bin/sed -E 's/^    echo RED$/    echo GREEN/' "$GATE" >"$BROKEN"
if ! /usr/bin/grep -qc 'echo RED' "$BROKEN" >/dev/null 2>&1; then :; fi
STATUS="$(run_gate "$BROKEN")"
if [ "$STATUS" != "0" ] && /usr/bin/grep -q 'SELF-CHECK FAILED' "$TMP/out"; then
  ok "self_check_fires_when_comparison_is_broken (G5, by inversion)"
else
  bad "self_check_fires_when_comparison_is_broken (G5, by inversion)" "status=$STATUS out=$(cat "$TMP/out")"
fi

# --- --measure prints a row you can paste, and rounds UP --------------------
pin "$PIN" 21
AXEYUM_CREAL_RATIO_PIN_FILE="$PIN" \
AXEYUM_CREAL_RATIO_FAKE_SUBJECT="$SUB" \
AXEYUM_CREAL_RATIO_FAKE_REFERENCE="$REF" \
  bash "$GATE" --measure >"$TMP/out" 2>&1
if /usr/bin/grep -qP '\t21$' "$TMP/out" 2>/dev/null \
   || /usr/bin/grep -q "$(printf 'rat_prelude_builds\t21')" "$TMP/out"; then
  ok "measure_rounds_up (20.21 -> 21)"
else
  bad "measure_rounds_up" "out=$(cat "$TMP/out")"
fi

printf '\n%d passed, %d failed\n' "$PASS" "$FAIL"
[ "$FAIL" -eq 0 ]
