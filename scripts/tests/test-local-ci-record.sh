#!/usr/bin/env bash
# Controls for `scripts/local-ci.sh --record`: the run recorder must be able to
# say a step FAILED, and — the point of the whole thing — that a step which
# exited 0 ran ZERO TESTS.
#
# Why a harness rather than reading the code: the first version was wrong in a
# way that reading it did not reveal. `tee -a a b` appends to BOTH files, so the
# per-step slice accumulated every earlier step and each step inherited the
# previous one's count. Counts came out 5, 5, 9, 9 where the answer is
# 5, 0, 9, -1 — and the consequence is not cosmetic: a vacuous step reads the
# last real step's total, so the zero-test rule CANNOT FIRE. The guard was
# unreachable, which is exactly the failure it exists to catch.
#
# The functions are extracted from the real script by `sed`, so this tests the
# shipped code rather than a copy of it. If `count_tests` or `run` is renamed or
# reshaped, the extraction yields nothing and the harness fails loudly.
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 2

SCRIPT=scripts/local-ci.sh
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
fail=0

extract() {
  { echo "LOG=$WORK/log"; echo "STEP_SLICE=$WORK/step"; echo "STEPS_JSON="; echo "SECONDS=0"
    sed -n '/^count_tests()/,/^}/p' "$SCRIPT"
    sed -n '/^run() {/,/^}/p' "$SCRIPT"
  } > "$WORK/harness.sh"
  # An empty extraction would make every case below pass vacuously.
  if ! grep -q 'count_tests()' "$WORK/harness.sh" || ! grep -q '^run() {' "$WORK/harness.sh"; then
    echo "FAIL: could not extract count_tests/run from $SCRIPT — the harness is testing nothing"
    exit 1
  fi
}

# --- 1. count_tests, against real cargo/nextest output shapes ---------------
counts() {
  extract
  cat >> "$WORK/harness.sh" <<'EOF'
bad=0
chk() { got=$(count_tests "$2"); if [ "$got" = "$3" ]; then echo "ok   count:$1 -> $got"; else echo "FAIL count:$1 -> $got (want $3)"; bad=1; fi; }
EOF
  printf 'test result: ok. 47 passed; 0 failed; 0 ignored\ntest result: ok. 3 passed; 0 failed\n' > "$WORK/libtest"
  printf 'Summary [   12.345s] 968 tests run: 968 passed, 2 skipped\n' > "$WORK/nextest"
  printf 'running 0 tests\n\ntest result: ok. 0 passed; 0 failed; 0 ignored\n' > "$WORK/zero"
  printf 'Checking axeyum-ir v0.1.0\n    Finished dev profile\n' > "$WORK/nocount"
  cat >> "$WORK/harness.sh" <<EOF
chk libtest-summed $WORK/libtest 50
chk nextest        $WORK/nextest 968
chk zero-tests     $WORK/zero 0
chk no-count       $WORK/nocount -1
exit \$bad
EOF
  bash "$WORK/harness.sh" || fail=1
}

# --- 2. run(): the verdicts, including the vacuous one ----------------------
verdicts() {
  extract
  cat >> "$WORK/harness.sh" <<'EOF'
bad=0
fake_zero()    { printf 'running 0 tests\n\ntest result: ok. 0 passed; 0 failed\n'; return 0; }
fake_pass()    { printf 'test result: ok. 5 passed; 0 failed\n'; return 0; }
fake_fail()    { printf 'test result: FAILED. 4 passed; 1 failed\n'; return 101; }
fake_nocount() { echo "Finished"; return 0; }
for spec in fake_pass:0 fake_zero:90 fake_fail:101 fake_nocount:0; do
  cmd=${spec%:*}; want=${spec#*:}
  run "$cmd" >/dev/null 2>&1; got=$?
  if [ "$got" = "$want" ]; then echo "ok   verdict:$cmd -> $got"
  else echo "FAIL verdict:$cmd -> $got (want $want)"; bad=1; fi
done
# The recorded counts must be PER STEP, not cumulative — the bug this file
# exists for. 5, 0, 4, -1 in order.
echo "[$STEPS_JSON]" | python3 -c '
import json, sys
got = [s["tests"] for s in json.load(sys.stdin)]
want = [5, 0, 4, -1]
print(("ok   " if got == want else "FAIL ") + f"per-step counts {got} (want {want})")
sys.exit(0 if got == want else 1)
' || bad=1
exit $bad
EOF
  bash "$WORK/harness.sh" || fail=1
}

counts
verdicts
if [ "$fail" = 0 ]; then echo "LOCAL_CI_RECORD_CONTROLS|ok"; else echo "LOCAL_CI_RECORD_CONTROLS|FAILED" >&2; fi
exit "$fail"
