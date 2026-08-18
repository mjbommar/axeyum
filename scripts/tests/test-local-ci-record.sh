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
    sed -n '/^claims_tests()/,/^}/p' "$SCRIPT"
    sed -n '/^run() {/,/^}/p' "$SCRIPT"
  } > "$WORK/harness.sh"
  # An empty extraction would make every case below pass vacuously. `run` calls
  # `claims_tests`, and an UNEXTRACTED helper does not error loudly -- bash
  # returns 127 and the guarded branch is simply skipped, so the control goes
  # green over a rule it never reached. Name each one.
  for fn in 'count_tests()' 'claims_tests()' '^run() {'; do
    if ! grep -q "$fn" "$WORK/harness.sh"; then
      echo "FAIL: could not extract ${fn} from $SCRIPT — the harness is testing nothing"
      exit 1
    fi
  done
}

# --- 1. count_tests, against real cargo/nextest output shapes ---------------
counts() {
  extract
  cat >> "$WORK/harness.sh" <<'EOF'
bad=0
chk() { got=$(count_tests "$2"); if [ "$got" = "$3" ]; then echo "ok   count:$1 -> $got"; else echo "FAIL count:$1 -> $got (want $3)"; bad=1; fi; }
EOF
  # EVERY nextest fixture below is a line CAPTURED from the tool, not typed from
  # its documentation. The previous one was typed, and so was flush-left --
  # nextest indents its Summary by five spaces. The pattern was anchored at `^`,
  # never matched, and the first completed run of the gate (a6ee37c6a) recorded
  # `tests: -1` for the step that ran 7511 tests, leaving the zero-test rule
  # unable to fire on the workspace sweep. A fixture the real tool would never
  # emit is not a control; it is a second copy of the bug.
  printf 'test result: ok. 47 passed; 0 failed; 0 ignored\ntest result: ok. 3 passed; 0 failed\n' > "$WORK/libtest"
  printf '     Summary [   0.107s] 31 tests run: 31 passed, 0 skipped\n' > "$WORK/nextest"
  # ...and the shape nextest prints when the run FAILED, which is not the same
  # line: it carries a "(85 slow)" parenthetical and a "4 failed" clause. This
  # exact line is from the run log behind artifacts/local-ci-runs/a6ee37c6a-s4.json.
  printf '     Summary [6384.534s] 7511 tests run: 7507 passed (85 slow), 4 failed, 32 skipped\n' > "$WORK/nextest-failed"
  # The vacuous shape, also captured: a nextest run that selected nothing.
  printf '    Starting 0 tests across 1 binary (31 tests skipped)\n     Summary [   0.000s] 0 tests run: 0 passed, 31 skipped\n' > "$WORK/nextest-zero"
  printf 'running 0 tests\n\ntest result: ok. 0 passed; 0 failed; 0 ignored\n' > "$WORK/zero"
  printf 'Checking axeyum-ir v0.1.0\n    Finished dev profile\n' > "$WORK/nocount"
  cat >> "$WORK/harness.sh" <<EOF
chk libtest-summed $WORK/libtest 50
chk nextest        $WORK/nextest 31
chk nextest-failed $WORK/nextest-failed 7511
chk nextest-zero   $WORK/nextest-zero 0
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
# A step that CLAIMS to run tests, exits 0, and prints a count this script
# cannot parse. `pass, tests=-1` there means "green, and we do not know whether
# it ran anything" -- the exact statement the recorder exists to make
# impossible, and precisely what the anchored-`^` bug produced for 7511 tests.
# 89 = unreadable, distinct from 90 = vacuous.
unparseable_stub() { echo "Summary in some future format"; return 0; }
# ...while a step that does NOT claim to run tests stays allowed to be silent,
# or `cargo fmt`/`clippy`/`check` would all become failures.
quiet_stub() { echo "Finished"; return 0; }
# The last two carry FLAGS, because `claims_tests` inspects the whole argument
# vector: a stub invoked as a bare word could never exercise it, and a control
# that cannot reach the code it names is the failure mode this file exists for.
specs=("fake_pass:0" "fake_zero:90" "fake_fail:101" "fake_nocount:0" \
       "unparseable_stub test --workspace:89" "quiet_stub --all --check:0")
for spec in "${specs[@]}"; do
  cmd=${spec%:*}; want=${spec#*:}
  # Unquoted on purpose -- word splitting is what hands `run` a real argv.
  # shellcheck disable=SC2086
  run $cmd >/dev/null 2>&1; got=$?
  if [ "$got" = "$want" ]; then echo "ok   verdict:$cmd -> $got"
  else echo "FAIL verdict:$cmd -> $got (want $want)"; bad=1; fi
done
# The recorded counts must be PER STEP, not cumulative — the bug this file
# exists for. 5, 0, 4, -1, -1, -1 in order.
echo "[$STEPS_JSON]" | python3 -c '
import json, sys
got = [s["tests"] for s in json.load(sys.stdin)]
want = [5, 0, 4, -1, -1, -1]
print(("ok   " if got == want else "FAIL ") + f"per-step counts {got} (want {want})")
sys.exit(0 if got == want else 1)
' || bad=1
exit $bad
EOF
  bash "$WORK/harness.sh" || fail=1
}

# --- 3. worktree isolation: the gate must measure the COMMIT, not the tree ----
#
# This script gates a shared checkout that always has some other lane's
# uncommitted work in it. Before 2026-08-18 it ran against that tree, so a
# sibling lane's half-finished edit could red the authoritative gate for a SHA
# that is perfectly fine -- and the record would name that SHA. The property
# under test is exactly one thing: what `prepare_worktree` hands back must equal
# the COMMIT, with the dirty worktree's content nowhere in it.
#
# Extracted from the real script by sed, like the blocks above, so a rename or a
# reshape of the functions fails here loudly instead of testing a stale copy.
worktree() {
  local wsrc="$WORK/src" got want
  if ! grep -q '^prepare_worktree() {' "$SCRIPT" || ! grep -q '^local_ci_gate_root() {' "$SCRIPT"; then
    echo "FAIL: could not find prepare_worktree/local_ci_gate_root in $SCRIPT — testing nothing"
    fail=1; return
  fi
  { sed -n '/^local_ci_gate_root() {/,/^}/p' "$SCRIPT"
    sed -n '/^prepare_worktree() {/,/^}/p' "$SCRIPT"
  } > "$WORK/wt-harness.sh"

  rm -rf "$wsrc"; mkdir -p "$wsrc"
  ( cd "$wsrc" \
    && git init -q . \
    && git config user.email t@t && git config user.name t \
    && git config commit.gpgsign false \
    && printf 'COMMITTED\n' > f.txt \
    && git add f.txt && git -c core.hooksPath=/dev/null commit -qm c1 ) >/dev/null 2>&1 \
    || { echo "FAIL: could not build the throwaway repo"; fail=1; return; }
  # A sibling lane's uncommitted work, of both kinds that have actually bitten:
  # a modified tracked file, and an untracked file cargo/fmt would still see.
  printf 'ANOTHER LANE WIP\n' > "$wsrc/f.txt"
  printf 'ANOTHER LANE WIP\n' > "$wsrc/g.txt"

  # The worktree is REUSED across runs (that is what keeps the cargo cache warm),
  # so the second call is the one that matters: leftovers from a crashed or
  # interrupted previous gate -- a stray untracked file, a modified tracked file
  # -- must not survive into the next run's measurement. Calling it once would
  # test a freshly-created tree, where `--force` and `clean -xdf` are both
  # no-ops and the assertions below hold vacuously.
  cat >> "$WORK/wt-harness.sh" <<EOF
set -uo pipefail
export AXEYUM_LOCAL_CI_WORKTREE_ROOT="$WORK/gateroot"
sha=\$(git -C "$wsrc" rev-parse HEAD)
wt=\$(prepare_worktree "$wsrc" "\$sha") || { echo "prepare_worktree failed (1st)"; exit 1; }
printf 'LEFTOVER STRAY\n' > "\$wt/g.txt"
printf 'LEFTOVER EDIT\n'  > "\$wt/f.txt"
wt=\$(prepare_worktree "$wsrc" "\$sha") || { echo "prepare_worktree failed (2nd)"; exit 1; }
printf 'CONTENT %s\n' "\$(cat "\$wt/f.txt")"
printf 'STRAY %s\n' "\$( [ -e "\$wt/g.txt" ] && echo present || echo absent)"
printf 'HEAD %s\n' "\$(git -C "\$wt" rev-parse HEAD)"
printf 'SRCDIRTY %s\n' "\$(git -C "$wsrc" status --porcelain | wc -l)"
EOF
  got=$(bash "$WORK/wt-harness.sh" 2>&1)
  want_sha=$(git -C "$wsrc" rev-parse HEAD)
  chkline() {
    if printf '%s\n' "$got" | grep -qxF "$1"; then echo "ok   worktree:$2"
    else echo "FAIL worktree:$2 — got: $(printf '%s\n' "$got" | tr '\n' '|')"; fail=1; fi
  }
  # The gate sees the commit...
  chkline "CONTENT COMMITTED" "tracked file is the COMMITTED content, not a leftover edit"
  # ...and does not see the untracked file either (`clean -xdf`).
  chkline "STRAY absent"      "a leftover untracked file does not survive into the next run"
  chkline "HEAD $want_sha"    "gate worktree is detached at the requested SHA"
  # ...and the sibling lane's WIP is still there afterwards. A gate that
  # "isolated" by stashing or checking out would read 0 here, and that is the
  # one failure mode this whole change must never introduce.
  chkline "SRCDIRTY 2"        "sibling lane's uncommitted work is untouched"
}

counts
verdicts
worktree
if [ "$fail" = 0 ]; then echo "LOCAL_CI_RECORD_CONTROLS|ok"; else echo "LOCAL_CI_RECORD_CONTROLS|FAILED" >&2; fi
exit "$fail"
