#!/usr/bin/env bash
# Controls for `scripts/check-local-ci-freshness.sh`: run the REAL script
# end-to-end (not an extracted copy) against a disposable throwaway repo, one
# scenario at a time, and assert both the exit code and that the printed
# reason names the right thing. Black-box on purpose: the script's job is to
# turn a JSON record file plus `HEAD`'s git history into a verdict, and both
# of those are cheap to fabricate, so there is no need to sed-extract
# functions the way `test-local-ci-record.sh` does for a script that must stay
# rooted at the real repo.
#
# `AXEYUM_LOCAL_CI_FRESHNESS_REPO` and `AXEYUM_LOCAL_CI_RECORDS` are the hooks
# that make this possible: point the SAME shipped script at a throwaway repo
# and a throwaway record dir instead of this checkout.
#
# Per CLAUDE.md: "a checker that cannot fail is worse than no checker."  Every
# case below is a case the checker must REJECT, plus exactly one it must
# ACCEPT. A case that always passed here would not be a control.
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 2

SCRIPT="$PWD/scripts/check-local-ci-freshness.sh"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
fail=0

REPO="$WORK/repo"
mkdir -p "$REPO"
(
  cd "$REPO" && git init -q . \
    && git config user.email t@t && git config user.name t \
    && git config commit.gpgsign false \
    && echo one > f.txt && git add f.txt \
    && git -c core.hooksPath=/dev/null commit -qm c1 \
    && echo two >> f.txt && git add f.txt \
    && git -c core.hooksPath=/dev/null commit -qm c2
) >/dev/null 2>&1 || { echo "FAIL: could not build the throwaway repo"; exit 1; }

HEAD_SHA="$(git -C "$REPO" rev-parse --short HEAD)"
NOW="$(date -u +%FT%TZ)"
OLD="$(date -u -d '100 hours ago' +%FT%TZ)"

RECORDS="$WORK/records"

run_checker() {
  AXEYUM_LOCAL_CI_FRESHNESS_REPO="$REPO" AXEYUM_LOCAL_CI_RECORDS="$RECORDS" \
    bash "$SCRIPT" "$@"
}

# case NAME WANT_RC WANT_SUBSTRING -- writes $2's record body (or none), runs,
# asserts exit code and that the named substring appears in the output.
case_() {
  local name="$1" want_rc="$2" want_grep="$3" out
  out="$(run_checker 2>&1)"; local got_rc=$?
  if [ "$got_rc" != "$want_rc" ]; then
    echo "FAIL case:$name rc=$got_rc (want $want_rc) — output: $(printf '%s' "$out" | tr '\n' '|')"
    fail=1; return
  fi
  if [ -n "$want_grep" ] && ! printf '%s' "$out" | grep -qF "$want_grep"; then
    echo "FAIL case:$name rc ok but missing '$want_grep' — output: $(printf '%s' "$out" | tr '\n' '|')"
    fail=1; return
  fi
  echo "ok   case:$name -> rc=$got_rc"
}

record() {
  # record <verdict> <finished_utc> <steps_json>
  rm -rf "$RECORDS"; mkdir -p "$RECORDS"
  cat > "$RECORDS/${HEAD_SHA}-x.json" <<EOF
{"sha":"${HEAD_SHA}","host":"x","finished_utc":"${2}","moment":0,"verdict":"${1}","rc":0,"steps":${3}}
EOF
}

# --- 1. no record at all: MUST reject, not merely report ---------------------
rm -rf "$RECORDS"; mkdir -p "$RECORDS"
case_ no-record 1 "NO_RECORD"

# --- 2. stale: fresh git ancestry, old finished_utc ---------------------------
record PASS "$OLD" '[{"cmd":"cargo fmt --all --check","status":0,"tests":-1,"seconds":1,"verdict":"pass"}]'
case_ stale 1 "STALE"

# --- 3/4/5: a bad step must red it EVEN WHEN the record's own top-level
#        `verdict` field lies and says PASS. This is the dangerous direction
#        -- local-ci.sh itself can never honestly emit PASS alongside a bad
#        step (`run`'s nonzero return always flows into `rc`), so top=PASS
#        here only happens from a corrupted/hand-edited record -- and it is
#        also the only fixture shape that actually isolates each per-step
#        guard from guard G6 (top-level verdict). A top=FAIL fixture would
#        let G6 alone drive `fail=1` and mask a deleted per-step guard, which
#        is exactly what a first draft of this suite got wrong: G6 quietly
#        did G5's job and mutating G5 killed nothing. -----------------------
record PASS "$NOW" '[{"cmd":"cargo nextest run --profile local","status":100,"tests":10,"seconds":5,"verdict":"fail"}]'
case_ fail-step 1 "STEP FAILED: \`cargo nextest run --profile local\`"

record PASS "$NOW" '[{"cmd":"cargo test -p foo","status":0,"tests":0,"seconds":5,"verdict":"vacuous"}]'
case_ vacuous-step 1 "STEP VACUOUS: \`cargo test -p foo\`"

record PASS "$NOW" '[{"cmd":"cargo nextest run --profile local","status":0,"tests":-1,"seconds":5,"verdict":"unreadable"}]'
case_ unreadable-step 1 "STEP UNREADABLE: \`cargo nextest run --profile local\`"

# --- 6. a record naming a sha NOT reachable from HEAD must be inapplicable,
#        not "old" -- built on a divergent branch so the sha resolves but is
#        not an ancestor. -----------------------------------------------------
(
  cd "$REPO" && git checkout -q -b sidebranch HEAD~1 \
    && echo divergent > g.txt && git add g.txt \
    && git -c core.hooksPath=/dev/null commit -qm side1
) >/dev/null 2>&1
SIDE_SHA="$(git -C "$REPO" rev-parse --short sidebranch)"
git -C "$REPO" checkout -q - >/dev/null 2>&1
rm -rf "$RECORDS"; mkdir -p "$RECORDS"
cat > "$RECORDS/${SIDE_SHA}-x.json" <<EOF
{"sha":"${SIDE_SHA}","host":"x","finished_utc":"${NOW}","moment":0,"verdict":"PASS","rc":0,"steps":[{"cmd":"cargo fmt --all --check","status":0,"tests":-1,"seconds":1,"verdict":"pass"}]}
EOF
case_ non-ancestor 1 "NO_APPLICABLE_RECORD"

# --- 7. top-level verdict lying about its own steps must red it too ----------
record FAIL "$NOW" '[{"cmd":"cargo fmt --all --check","status":0,"tests":-1,"seconds":1,"verdict":"pass"}]'
case_ inconsistent-record 1 "INCONSISTENT RECORD"

# --- 8. the one case that must be accepted: fresh, ancestor, all-pass --------
record PASS "$NOW" '[{"cmd":"cargo fmt --all --check","status":0,"tests":-1,"seconds":1,"verdict":"pass"},{"cmd":"cargo nextest run --profile local","status":0,"tests":7511,"seconds":6000,"verdict":"pass"}]'
case_ clean-pass 0 "local-ci-freshness: PASS"

# --- 8b. COVERAGE: a record that predates a step local-ci.sh now runs --------
# Freshness is not coverage. This is the case that was live on 2026-08-19: the
# frontier ratchet moved into `local-ci.sh` and the gate went on printing PASS
# over a record written before it existed. Without this case the coverage guard
# is unreachable — deleting it killed ZERO controls when it was added.
FAKE_CI="$WORK/fake-local-ci.sh"
cat > "$FAKE_CI" <<'FAKE'
run cargo fmt --all --check || rc=$?
run cargo nextest run --profile local || rc=$?
run cargo test --new-step-added-later || rc=$?
FAKE
record PASS "$NOW" '[{"cmd":"cargo fmt --all --check","status":0,"tests":-1,"seconds":1,"verdict":"pass"},{"cmd":"cargo nextest run --profile local","status":0,"tests":7511,"seconds":6000,"verdict":"pass"}]'
out="$(AXEYUM_LOCAL_CI_FRESHNESS_REPO="$REPO" AXEYUM_LOCAL_CI_RECORDS="$RECORDS" \
      AXEYUM_LOCAL_CI="$FAKE_CI" bash "$SCRIPT" 2>&1)"; rc=$?
if [ "$rc" = 1 ] && printf '%s' "$out" | grep -qF "UNCOVERED STEP: \`cargo test --new-step-added-later\`"; then
  echo "ok   case:uncovered-step -> rc=1"
else
  echo "FAIL case:uncovered-step rc=$rc — output: $(printf '%s' "$out" | tr '\n' '|')"
  fail=1
fi

# ...and the same record against a script whose steps it DOES cover must pass,
# or the case above proves only that the gate can reject, not that it discriminates.
cat > "$FAKE_CI" <<'FAKE'
run cargo fmt --all --check || rc=$?
run cargo nextest run --profile local || rc=$?
FAKE
out="$(AXEYUM_LOCAL_CI_FRESHNESS_REPO="$REPO" AXEYUM_LOCAL_CI_RECORDS="$RECORDS" \
      AXEYUM_LOCAL_CI="$FAKE_CI" bash "$SCRIPT" 2>&1)"; rc=$?
if [ "$rc" = 0 ]; then echo "ok   case:covered-step -> rc=0"
else echo "FAIL case:covered-step rc=$rc — output: $(printf '%s' "$out" | tr '\n' '|')"; fail=1; fi

# --- 9. --report-only must ALWAYS exit 0 even though the underlying verdict
#        is FAIL, and the FAIL text must still print. This exercises a
#        DIFFERENT piece of logic than cases 2-7 (the final
#        `[ "$REPORT_ONLY" = 1 ] && exit 0` override, not any one guard), so
#        the fixture deliberately trips TWO independent guards at once
#        (stale AND a failed step). That makes this control robust to any
#        SINGLE guard's own fail=1 being deleted -- the other guard still
#        drives global `fail=1` and the reasons print -- so this case dies
#        only if the report-only override itself is broken, never as a
#        side effect of mutating cases 2-7's own guards. Sharing a
#        single-cause fixture with another case would mean one mutation
#        could kill two controls, the "shared check" failure mode CLAUDE.md
#        warns about. ---------------------------------------------------
record FAIL "$OLD" '[{"cmd":"cargo nextest run --profile local","status":100,"tests":10,"seconds":5,"verdict":"fail"}]'
out="$(AXEYUM_LOCAL_CI_FRESHNESS_REPO="$REPO" AXEYUM_LOCAL_CI_RECORDS="$RECORDS" bash "$SCRIPT" --report-only 2>&1)"
rc=$?
if [ "$rc" = 0 ] && printf '%s' "$out" | grep -qF "local-ci-freshness: FAIL"; then
  echo "ok   case:report-only-still-diagnoses -> rc=0, reason printed"
else
  echo "FAIL case:report-only-still-diagnoses rc=$rc — output: $(printf '%s' "$out" | tr '\n' '|')"
  fail=1
fi

if [ "$fail" = 0 ]; then echo "LOCAL_CI_FRESHNESS_CONTROLS|ok"; else echo "LOCAL_CI_FRESHNESS_CONTROLS|FAILED" >&2; fi
exit "$fail"
