#!/usr/bin/env bash
# Controls for the config-registry staleness ratchet (ADR-2085).
#
# A ratchet over an accepted backlog is one edit away from being a suppression
# list, and the difference is not visible by reading it: both look like a file
# full of exemptions. The difference is whether the gate still FAILS. So each
# control below mutates one thing and requires a specific exit status.
#
# Every mutation goes to a COPY under the scratch dir via `--accepted`; nothing
# here writes a mutated file into the worktree, because a mutant on disk in a
# shared checkout is in every other lane's build.
#
#   0  all controls behaved
#   1  a control did not fire -- the ratchet has stopped being one
set -uo pipefail

cd "$(dirname "$0")/../.." || exit 1
GATE=scripts/check-config-registry-staleness.py
ACCEPTED=artifacts/config-registry-accepted-staleness.tsv
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
fail=0

# Exit status is read from `$?` of the command itself, never through a pipe:
# `cmd | tail` reports tail's status, which is this repository's most-banned
# shell idiom and has hidden this very gate before.
run_gate() {
  python3 "$GATE" --accepted "$1" >"$TMP/out.txt" 2>&1
  echo $?
}

expect() {
  local label="$1" want="$2" got="$3"
  if [ "$got" = "$want" ]; then
    echo "  ok    $label (exit $got)"
  else
    echo "  FAIL  $label: expected exit $want, got $got" >&2
    sed -n '1,12p' "$TMP/out.txt" >&2
    fail=1
  fi
}

echo "config-registry ratchet controls:"

# 0. NEGATIVE CONTROL. The unmutated ledger must pass, or every control below
#    is measuring a tree that was already broken.
expect "unmutated ledger passes" 0 "$(run_gate "$ACCEPTED")"

# 1. A stale row that is NOT accepted must fail. This is the direction that
#    catches a measurement newly gone stale.
grep -v 'ABV_ONLINE_LADDER_RESERVE_SHARE.*dispatch_abv_online' "$ACCEPTED" \
  >"$TMP/deleted.tsv"
expect "deleting one accepted row fails" 1 "$(run_gate "$TMP/deleted.tsv")"

# 2. An accepted row that is NO LONGER stale must also fail. Without this the
#    ledger silently accumulates lines describing nothing, and its length stops
#    being the backlog. `MAX_GROUND_TERMS`/`GroundBudget` is used because it is
#    a dependency this gate is currently green on.
cp "$ACCEPTED" "$TMP/rotted.tsv"
printf 'crates/axeyum-solver/src/qinst_egraph.rs::MAX_GROUND_TERMS\tcrates/axeyum-solver/src/qinst_egraph.rs::GroundBudget\tnot stale; the ratchet must reject this line\n' \
  >>"$TMP/rotted.tsv"
expect "a no-longer-stale accepted row fails" 1 "$(run_gate "$TMP/rotted.tsv")"

# 3. A row without a written reason is rejected outright. A bare identifier is
#    an exemption nobody argued for, which is the thing this file must not
#    become.
cp "$ACCEPTED" "$TMP/mute.tsv"
printf 'crates/axeyum-solver/src/x.rs::Y\tcrates/axeyum-solver/src/x.rs::Z\t\n' \
  >>"$TMP/mute.tsv"
expect "a row with an empty reason is rejected" 2 "$(run_gate "$TMP/mute.tsv")"

# 4. The enumeration rewrite must still agree with the git pickaxe it replaced.
python3 "$GATE" --self-test >"$TMP/selftest.txt" 2>&1
st=$?
expect "--self-test agrees with the pickaxe" 0 "$st"
# ...and it must have COMPARED something. "0 disagreements" over 0 pairs is what
# a control that never ran also prints.
if ! grep -qE 'over [1-9][0-9]* compared' "$TMP/selftest.txt"; then
  echo "  FAIL  --self-test compared an empty population" >&2
  fail=1
else
  echo "  ok    $(grep -o 'over [0-9]* compared rests_on pair(s)' "$TMP/selftest.txt")"
fi

if [ "$fail" -eq 0 ]; then
  echo "config-registry ratchet controls: all fired as specified"
else
  echo "config-registry ratchet controls: FAILED" >&2
fi
exit "$fail"
