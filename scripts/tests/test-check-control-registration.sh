#!/usr/bin/env bash
# Controls for `scripts/check-control-registration.sh` -- the gate that decides
# whether this repository's controls are RUN by anything.
#
# It had no control suite of its own until 2026-08-27, which is the joke this
# file exists to stop being: the gate whose entire subject is "a check nobody
# invokes cannot fail" was itself unverified. Its python half then pinned an
# unexplained floor of 188 unnamed suites, and the redesign that removed the
# floor added seven guards -- none of which anything would have noticed losing.
#
# METHOD: copy the REAL gate and the REAL runner into a disposable skeleton
# repository and drive them there. Copying rather than sed-extracting because
# the gate is black-box by construction -- it reads the filesystem and four
# caller files, all of which are cheap to fabricate.
#
# Per CLAUDE.md: "a checker that cannot fail is worse than no checker." Every
# case below is one the gate must REJECT, plus a healthy tree it must ACCEPT.
# A case that passed in both worlds would not be a control.
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 2

GATE="$PWD/scripts/check-control-registration.sh"
RUNNER="$PWD/scripts/run-python-controls.py"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
fail=0
cases=0

# Build a healthy skeleton at $1.
#
# The corpus floors are real and deliberately not env-overridable, so the
# skeleton has to be big enough to clear them: >= 5 `.sh` controls, >= 50 `.py`
# suites for the gate, and >= 200 discovered `.py` suites for the runner's own
# floor. They are empty files -- nothing here EXECUTES a suite, `--list` only
# partitions names.
build() {
  local root="$1"
  rm -rf "$root"
  mkdir -p "$root/scripts/tests" "$root/.github/workflows" "$root/hooks" "$root/artifacts/facts"
  cp "$GATE" "$root/scripts/check-control-registration.sh"
  cp "$RUNNER" "$root/scripts/run-python-controls.py"

  local i
  for i in $(seq 1 210); do
    printf 'import unittest\n' > "$root/scripts/tests/test_gen_$i.py"
  done
  for i in $(seq 1 6); do
    printf '#!/usr/bin/env bash\nexit 0\n' > "$root/scripts/tests/test-sh-$i.sh"
  done

  # G2: a hyphenated `.py` reachable ONLY via a fact's checker_command -- not
  # named in scripts/check.sh, the justfile, hooks/pre-push, or
  # .github/workflows. This is the property check-fact-evidence-replay.sh
  # actually establishes for 3 of the 4 real scripts G2 was written against.
  printf 'import sys\nsys.exit(0)\n' > "$root/scripts/tests/check-reachable-numerics.py"
  printf '{"checker_command": "python3 scripts/tests/check-reachable-numerics.py"}\n' \
    > "$root/artifacts/facts/fake-fact.json"

  # Callers. Every `.sh` control is named; two `.py` suites are named by hand,
  # one in each invocation form, so the "both forms count" path is exercised;
  # the runner is named, which is guard G1.
  {
    echo '#!/usr/bin/env bash'
    echo 'scripts/run-python-controls.py'
    echo 'python3 -m unittest scripts.tests.test_gen_1'
    echo 'python3 scripts/tests/test_gen_2.py'
    for i in $(seq 1 6); do echo "scripts/tests/test-sh-$i.sh"; done
  } > "$root/scripts/check.sh"
  printf 'check:\n\techo hi\n' > "$root/justfile"
  printf '#!/usr/bin/env bash\nexit 0\n' > "$root/hooks/pre-push"
  printf 'name: x\n' > "$root/.github/workflows/x.yml"

  # Three exclusions, so the ceiling has room to move in BOTH directions.
  {
    printf '# skeleton opt-out list\n'
    printf 'test_gen_200\tdeliberately excluded, case (a)\n'
    printf 'test_gen_201\tdeliberately excluded, case (b)\n'
    printf 'test_gen_202\tdeliberately excluded, case (c)\n'
  } > "$root/scripts/control-optout.tsv"
}

# case_ NAME WANT_RC WANT_SUBSTRING -- runs the gate in $WORK/repo.
case_() {
  local name="$1" want_rc="$2" want="$3" out got
  cases=$((cases + 1))
  out="$(AXEYUM_CONTROL_OPTOUT_CEILING="${CEIL:-3}" bash "$WORK/repo/scripts/check-control-registration.sh" 2>&1)"
  got=$?
  if [ "$got" != "$want_rc" ]; then
    echo "FAIL case:$name rc=$got (want $want_rc) -- $(printf '%s' "$out" | tr '\n' '|')"
    fail=1
    return
  fi
  # `grep -cF` and a tested count, never `grep -q`: under `set -o pipefail` a
  # `-q` consumer SIGPIPEs the producer and 141 reads as "not found".
  if [ -n "$want" ]; then
    local hits
    hits=$(printf '%s' "$out" | grep -cF "$want")
    if [ "${hits:-0}" -eq 0 ]; then
      echo "FAIL case:$name rc ok but missing '$want' -- $(printf '%s' "$out" | tr '\n' '|')"
      fail=1
      return
    fi
  fi
  echo "ok   case:$name"
}

# --- 1. the POSITIVE control. A healthy skeleton must pass, or every REJECT
#        below proves nothing (they could all be failing for the same unrelated
#        reason).
build "$WORK/repo"
case_ healthy 0 "py_orphans=0"

# ...and it must actually have partitioned something. A gate reporting 0/0/0
# would satisfy the line above.
out="$(AXEYUM_CONTROL_OPTOUT_CEILING=3 bash "$WORK/repo/scripts/check-control-registration.sh" 2>&1)"
cases=$((cases + 1))
if [ "$(printf '%s' "$out" | grep -cF 'py_catchall=205')" -eq 0 ]; then
  echo "FAIL case:healthy-partition -- expected py_catchall=205 (210 - 2 named - 3 excluded): $(printf '%s' "$out" | tr '\n' '|')"
  fail=1
else
  echo "ok   case:healthy-partition"
fi

# --- 2. G1: the catch-all runner invoked by nobody. This is the whole scheme
#        going inert, and it is the one failure that makes every other number
#        the gate prints a statement about work that never happens.
build "$WORK/repo"
grep -vF 'scripts/run-python-controls.py' "$WORK/repo/scripts/check.sh" > "$WORK/tmp" \
  && mv "$WORK/tmp" "$WORK/repo/scripts/check.sh"
case_ runner-not-invoked 1 "is invoked by no caller"

# --- 3. G1 again: a COMMENT is not a caller. The original gate shipped with
#        this hole -- a `# Control: ...` line satisfied a plain grep -F.
build "$WORK/repo"
sed -i 's|^scripts/run-python-controls.py$|# scripts/run-python-controls.py|' "$WORK/repo/scripts/check.sh"
case_ runner-named-only-in-a-comment 1 "is invoked by no caller"

# --- 4. G2: a hyphenated `.py` control invoked by NOTHING -- not a caller, not
#        a fact's checker_command. Confirmed by probe 2026-08-30 that the old
#        "not an importable module" half of this guard's reasoning was false
#        (see check-control-registration.sh's header); reachability, not the
#        hyphen itself, is what this now tests.
build "$WORK/repo"
printf 'import unittest\n' > "$WORK/repo/scripts/tests/test-hyphen-probe.py"
case_ hyphenated-py 1 "invoked by NOTHING"

# --- 4b. G2 POSITIVE: a hyphenated `.py` cited ONLY by a fact's
#         checker_command (build()'s check-reachable-numerics.py, named in
#         artifacts/facts/fake-fact.json and nowhere else) must NOT be
#         rejected. This is the real-world shape: 3 of the 4 scripts G2 was
#         written against are reachable this way and by nothing else.
build "$WORK/repo"
out="$(AXEYUM_CONTROL_OPTOUT_CEILING=3 bash "$WORK/repo/scripts/check-control-registration.sh" 2>&1)"
got=$?
cases=$((cases + 1))
if [ "$got" -ne 0 ] || [ "$(printf '%s' "$out" | grep -cF 'check-reachable-numerics.py')" -ne 0 ]; then
  echo "FAIL case:hyphen-py-reachable-via-fact rc=$got -- $(printf '%s' "$out" | tr '\n' '|')"
  fail=1
else
  echo "ok   case:hyphen-py-reachable-via-fact"
fi

# --- 4c. G2 MUTATION CHECK: remove the ONE fact reference that makes 4b pass
#         and confirm the gate now rejects the same file. This is what proves
#         4b is testing the fact-reachability path and not passing by
#         accident (e.g. an empty-corpus vacuity in the new facts_text glob).
build "$WORK/repo"
rm -f "$WORK/repo/artifacts/facts/fake-fact.json"
case_ hyphen-py-fact-reference-removed 1 "check-reachable-numerics.py"

# --- 5. G3: an opt-out entry naming a file that no longer exists. An allowlist
#        that only ever grows is where dead entries hide.
build "$WORK/repo"
printf 'test_gen_does_not_exist\tstale entry\n' >> "$WORK/repo/scripts/control-optout.tsv"
CEIL=4 case_ optout-stale 1 "does not exist"

# --- 6. G4: an exclusion with no reason is the anonymous numeric floor again.
build "$WORK/repo"
printf 'test_gen_203\t\n' >> "$WORK/repo/scripts/control-optout.tsv"
CEIL=4 case_ optout-no-reason 1 "has no reason"

# --- 7. G4b: no TAB at all.
build "$WORK/repo"
printf 'test_gen_203\n' >> "$WORK/repo/scripts/control-optout.tsv"
CEIL=4 case_ optout-no-tab 1 "no TAB"

# --- 8. G5: opted out AND named by a caller. One of the two is a lie about
#        whether the suite runs, and the gate must not pick a winner silently.
build "$WORK/repo"
echo 'python3 -m unittest scripts.tests.test_gen_200' >> "$WORK/repo/scripts/check.sh"
case_ optout-and-named 1 "cannot be both excluded and run"

# --- 9. G6: the ratchet, upward. Adding an exclusion must be deliberate.
build "$WORK/repo"
printf 'test_gen_204\tanother exclusion\n' >> "$WORK/repo/scripts/control-optout.tsv"
case_ optout-rose 1 "opt-outs ROSE"

# --- 10. G6: the ratchet, downward. Removing one is a RESULT and must be
#         recorded, not absorbed -- the failure the old 188 floor never had.
build "$WORK/repo"
grep -vF 'test_gen_202' "$WORK/repo/scripts/control-optout.tsv" > "$WORK/tmp" \
  && mv "$WORK/tmp" "$WORK/repo/scripts/control-optout.tsv"
case_ optout-fell 1 "opt-outs FELL"

# --- 11. G7: the gate's partition and the runner's must agree. Two independent
#         implementations; a silent divergence means the set that RUNS is not
#         the set the gate believes it audited.
build "$WORK/repo"
sed -i 's|TESTS.glob("test_\*.py")|TESTS.glob("test_gen_1*.py")|' "$WORK/repo/scripts/run-python-controls.py"
case_ partition-disagreement 1 "differs from what"

# --- 12. the `.sh` half still works: an unregistered shell control is an
#         orphan. This is the original guard and must survive the rewrite.
build "$WORK/repo"
printf '#!/usr/bin/env bash\nexit 0\n' > "$WORK/repo/scripts/tests/test-unregistered.sh"
case_ sh-orphan 1 "is run by nothing"

# --- 13. an empty corpus must be LOUD, not green. A ratchet over nothing
#         passes for the wrong reason, which is this file's whole subject.
build "$WORK/repo"
rm -f "$WORK/repo/scripts/tests"/*.sh
case_ empty-sh-corpus 1 "found only 0 control script"

# --- 14. a missing opt-out file is not "no exclusions"; it is a broken gate.
build "$WORK/repo"
rm -f "$WORK/repo/scripts/control-optout.tsv"
case_ optout-missing 1 "is missing"

echo "test-check-control-registration: $cases case(s)"
if [ "$cases" -lt 17 ]; then
  echo "FAIL: only $cases case(s) ran; this suite must not shrink silently" >&2
  exit 1
fi
[ "$fail" -eq 0 ] || exit 1
echo "test-check-control-registration: all $cases case(s) passed"
