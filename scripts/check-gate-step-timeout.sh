#!/usr/bin/env bash
# Prove that the aggregate gate's per-step time caps ACTUALLY FIRE (ADR-0623).
#
# # Why this exists
#
# `scripts/check.sh` had zero timeout-guarded steps until 2026-08-30, and one
# hung step hung the whole gate forever -- a live run was reaped after nine
# hours, 0% CPU at every level, log stopped mid `=== facts-replay ===`.
#
# The fix is a per-step `timeout`. The reason this PROBE exists rather than just
# the fix is the second finding, which is worse: **`scripts/check-fast.sh` had a
# per-step cap all along and it did not bind.**
#
#     trap '' TERM; sleep 25
#     timeout 2      ./that.sh   ->  exit 124 after 25s
#     timeout -k 1 2 ./that.sh   ->  exit 137 after  3s
#
# `timeout N` sends SIGTERM at the deadline and then waits FOREVER. The status
# it returns is 124 either way, so a caller testing for 124 gets a
# correct-looking "timed out" verdict after an arbitrarily long wait. A run of
# `check-fast.sh` was found stuck 23 minutes on a step with a 3-second budget.
#
# So: a cap nobody has watched bite is a cap you do not have. This is the same
# lesson `scripts/cargo-serialized.sh --self-check` encodes -- `MemoryMax`
# without `MemorySwapMax` is a ceiling that never fires, so the wrapper
# over-allocates through its own construction and fails if the job survives.
# This does that for time: it runs a TERM-IGNORING step under the real gate's
# real cap and fails if the step outlives it.
#
# # What it does NOT do
#
# It never runs the real 401-step gate. Every case builds a COPY of
# `scripts/check.sh` with the step list stripped and synthetic steps injected --
# the mechanism `scripts/tests/test-gate-scope-controls.sh` already uses for the
# step floor. So the code under test is the real `step()` function and the real
# `step_cap_for`, exercised against steps this script controls.
#
# Usage:
#   scripts/check-gate-step-timeout.sh            # all cases
#   scripts/check-gate-step-timeout.sh --self-check  # only the TERM-ignoring probe
set -uo pipefail
cd "$(dirname "$0")/.."

repo="$PWD"
work="$(mktemp -d "${TMPDIR:-/tmp}/gate-step-timeout.XXXXXX")"
trap 'rm -rf "$work"' EXIT

pass=0
fail=0

note_pass() { echo "  ok   $1"; pass=$((pass + 1)); }
note_fail() { echo "  FAIL $1" >&2; fail=$((fail + 1)); }

# ---------------------------------------------------------------------------
# Build a synthetic gate: the real scripts/check.sh with every `step` line
# removed and our own injected in their place, plus a floor low enough that the
# floor guard is not what fails.
#
# `sed '/^step /d'` and the marker replacement are lifted from
# `scripts/tests/test-gate-scope-controls.sh` control 6 deliberately -- two
# copies of this trick is one too many, but diverging from the shape that is
# already proven to work here would be worse.
# ---------------------------------------------------------------------------
make_gate() {
  local dir="$1"; shift          # where to build it
  local steps="$1"; shift        # literal `step ...` lines to inject
  mkdir -p "$dir/scripts"
  sed '/^step /d' "$repo/scripts/check.sh" > "$dir/scripts/check.sh"
  STEPS="$steps" python3 - "$dir/scripts/check.sh" <<'PY'
import os, sys
path = sys.argv[1]
text = open(path).read()
text = text.replace("STEP_FLOOR=80", "STEP_FLOOR=1")
anchor = 'if [ "$list_only" = "1" ]; then\n  echo "check: $ran steps" >&2'
assert anchor in text, "check.sh's list-mode tail moved; this probe cannot inject steps"
text = text.replace(anchor, os.environ["STEPS"] + "\n" + anchor)
open(path, "w").write(text)
PY
}

# A child that IGNORES SIGTERM. This is the whole point: `timeout` without
# `--kill-after` cannot stop it, and cannot be shown not to.
cat > "$work/ignores-term.sh" <<'EOF'
#!/usr/bin/env bash
trap '' TERM
sleep 120
EOF
chmod +x "$work/ignores-term.sh"

# A child that exits 124 IMMEDIATELY. 124 is `timeout`'s own status, so a naive
# classifier reads this as "timed out" -- and a step that exits 124 in no time
# has FAILED. This is what forces the elapsed-time conjunct.
cat > "$work/exits-124.sh" <<'EOF'
#!/usr/bin/env bash
exit 124
EOF
chmod +x "$work/exits-124.sh"

run_gate() {  # run_gate <dir> <env assignments...> ; sets REPLY_OUT / REPLY_ST / REPLY_EL
  local dir="$1"; shift
  local t0=$SECONDS
  REPLY_OUT="$(env AXEYUM_CHECK_NO_SLOT=1 "$@" bash "$dir/scripts/check.sh" 2>&1)"
  REPLY_ST=$?
  REPLY_EL=$(( SECONDS - t0 ))
}

echo "=== case 1: check.sh caps a step that simply hangs ==="
make_gate "$work/hang" "step hangs sleep 120"
run_gate "$work/hang" AXEYUM_CHECK_STEP_CAP=2 AXEYUM_CHECK_STEP_KILL_GRACE=1
if [ "$REPLY_EL" -le 20 ]; then
  note_pass "a 120s step under a 2s cap returned in ${REPLY_EL}s"
else
  note_fail "a 120s step under a 2s cap took ${REPLY_EL}s -- the cap did not bind"
fi
case "$REPLY_OUT" in
  *"TIMED OUT"*) note_pass "it is reported as TIMED OUT" ;;
  *) note_fail "no TIMED OUT in the output" ;;
esac

echo "=== case 2 (THE SELF-CHECK): check.sh caps a step that IGNORES SIGTERM ==="
# Without `--kill-after` this case runs for 120s and still exits 124, so the
# classification looks right while the bound is fiction. This is the ONLY case
# that distinguishes a real cap from a decorative one.
#
# AND IT TESTS THE ORPHAN REAPER FOR FREE, which is why the elapsed assertion is
# on the CAPTURE rather than on the gate's own reported time. `run_gate` reads
# the gate through a command substitution, and a command substitution returns
# only when every descendant has closed the write end of that pipe. So a
# surviving grandchild -- the thing that held cargo's build lock for nine hours
# -- keeps this case blocked even though the gate itself already exited.
#
# That is not a hypothetical about this fixture: with `timeout` alone the gate
# reported `status=137` at 3s and the capture still took the sleeper's full
# lifetime, because SIG_IGN for TERM is inherited across exec and `timeout`
# signals the child it monitors rather than the tree beneath it.
make_gate "$work/ignore" "step ignores-term $work/ignores-term.sh"
run_gate "$work/ignore" AXEYUM_CHECK_STEP_CAP=2 AXEYUM_CHECK_STEP_KILL_GRACE=1
if [ "$REPLY_EL" -le 20 ]; then
  note_pass "a TERM-ignoring step under a 2s cap returned in ${REPLY_EL}s"
else
  note_fail "a TERM-ignoring step under a 2s cap took ${REPLY_EL}s -- SIGTERM was sent and then waited on forever; the cap needs --kill-after"
fi
case "$REPLY_OUT" in
  *"TIMED OUT"*) note_pass "the TERM-ignoring step is reported as TIMED OUT" ;;
  *) note_fail "the TERM-ignoring step was not reported as TIMED OUT" ;;
esac

if [ "${1:-}" = "--self-check" ]; then
  echo
  echo "GATE_STEP_TIMEOUT|self-check|pass=${pass}|fail=${fail}"
  [ "$fail" -eq 0 ] || exit 1
  exit 0
fi

echo "=== case 3: a TIMED OUT step is never a pass ==="
make_gate "$work/green" "step hangs sleep 120"
run_gate "$work/green" AXEYUM_CHECK_STEP_CAP=2 AXEYUM_CHECK_STEP_KILL_GRACE=1
if [ "$REPLY_ST" -ne 0 ]; then
  note_pass "the gate exits non-zero (${REPLY_ST}) when a step timed out"
else
  note_fail "the gate exited 0 with a timed-out step -- green by going blind"
fi
case "$REPLY_OUT" in
  *"all "*" gates passed"*) note_fail "it printed the all-passed banner anyway" ;;
  *) note_pass "the all-passed banner is absent" ;;
esac
case "$REPLY_OUT" in
  *"UNCHECKED"*) note_pass "the summary says UNCHECKED as loudly as check-fast does" ;;
  *) note_fail "the summary never says UNCHECKED" ;;
esac

echo "=== case 4: a step that exits 124 FAST is FAILED, not TIMED OUT ==="
# 124 is timeout's own status but it is also an ordinary exit code. Without the
# elapsed-time conjunct, a broken step could be reclassified out of `failed`
# and into the softer bucket just by choosing its exit code.
make_gate "$work/fast124" "step quick-124 $work/exits-124.sh"
run_gate "$work/fast124" AXEYUM_CHECK_STEP_CAP=60 AXEYUM_CHECK_STEP_KILL_GRACE=1
case "$REPLY_OUT" in
  *"quick-124: FAILED"*) note_pass "a fast exit-124 step is FAILED" ;;
  *) note_fail "a fast exit-124 step was not reported as FAILED" ;;
esac
case "$REPLY_OUT" in
  *"TIMED OUT"*) note_fail "a fast exit-124 step was misread as a timeout" ;;
  *) note_pass "it was not misread as a timeout" ;;
esac

echo "=== case 5: a SLOW step that FINISHES is not misclassified ==="
# The failure this guards against is the one that makes a cap worse than no
# cap: spurious timeouts on healthy steps teach readers to ignore the gate.
make_gate "$work/slow" "step slow-but-ok sleep 3"
run_gate "$work/slow" AXEYUM_CHECK_STEP_CAP=60 AXEYUM_CHECK_STEP_KILL_GRACE=1
if [ "$REPLY_ST" -eq 0 ]; then
  note_pass "a 3s step under a 60s cap passes"
else
  note_fail "a 3s step under a 60s cap did not pass (exit ${REPLY_ST})"
fi
case "$REPLY_OUT" in
  *"slow-but-ok: ok"*) note_pass "it is reported ok, with its elapsed time" ;;
  *) note_fail "the slow-but-finishing step was not reported ok" ;;
esac

echo "=== case 6: check-fast.sh's cap binds against a TERM-ignoring step ==="
# check-fast.sh takes its step list from AXEYUM_CHECK_FAST_LIST_CMD, so this
# needs no synthetic gate -- feed it a fixture directly.
printf 'ignores-term\t%s\n' "$work/ignores-term.sh" > "$work/fast-steps.tsv"
t0=$SECONDS
fast_out="$(AXEYUM_CHECK_FAST_LIST_CMD="cat $work/fast-steps.tsv" \
  AXEYUM_CHECK_FAST_KILL_GRACE=1 \
  bash "$repo/scripts/check-fast.sh" --budget 2 2>&1)"
fast_el=$(( SECONDS - t0 ))
if [ "$fast_el" -le 20 ]; then
  note_pass "check-fast capped a TERM-ignoring step in ${fast_el}s"
else
  note_fail "check-fast took ${fast_el}s on a 2s budget -- its cap has no --kill-after"
fi
case "$fast_out" in
  *"deferred=1"*) note_pass "check-fast reports it DEFERRED, not ok" ;;
  *) note_fail "check-fast did not defer the capped step" ;;
esac

echo "=== case 7: check.sh REFUSES to run when \`timeout\` is absent ==="
# Running uncapped is the state this whole change rescued the gate from, so the
# absence of the tool must be loud rather than a silent fallback.
make_gate "$work/notimeout" "step trivial true"
mkdir -p "$work/emptybin"
nt_out="$(env AXEYUM_CHECK_NO_SLOT=1 PATH="$work/emptybin" \
  /bin/bash "$work/notimeout/scripts/check.sh" 2>&1)"
nt_st=$?
if [ "$nt_st" -eq 2 ]; then
  note_pass "it exits 2 (distinct from a step failure) with no \`timeout\` on PATH"
else
  note_fail "with no \`timeout\` on PATH it exited ${nt_st}, not 2"
fi
case "$nt_out" in
  *"no per-step cap"*) note_pass "and it says why" ;;
  *) note_fail "it refused without explaining itself" ;;
esac

echo
echo "GATE_STEP_TIMEOUT|cases=7|pass=${pass}|fail=${fail}"
if [ "$fail" -ne 0 ]; then
  echo "check-gate-step-timeout: FAILED -- the gate's per-step cap is not doing what it claims" >&2
  exit 1
fi
