#!/usr/bin/env bash
# Mutation harness for scripts/tests/test-gate-admission-controls.sh.
#
# The technique's blind spot is documented in CLAUDE.md -- it measures the
# guards you HAVE, never the ones you are missing -- so this is not evidence
# that the control suite is complete. It is evidence that no guard in it is
# decorative, which is the failure mode a scheduling change invites: "it went
# faster" is not an exit status, and a check that cannot fail is worse than none.
#
# Mutates a COPY under $TMPDIR, never the checkout: CLAUDE.md records a lane
# whose in-place `sed` made a sibling's build fail with errors that named the
# mutant's value, and cost that lane a re-run from a snapshot.
#
# Usage: scripts/tests/mutate-gate-admission.sh
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 2

SRC="$PWD"
W="$(mktemp -d "${TMPDIR:-/tmp}/axeyum-mutate-admission-XXXXXX")"
trap 'rm -rf "$W"' EXIT

echo "=== mutation controls: gate admission ==="
echo "workspace: $W"
echo

run_case() {
  local name="$1" file="$2" pattern="$3" want="$4"
  rm -rf "$W/t"
  mkdir -p "$W/t"
  # Only the four files the suite reads; a full copy would take minutes.
  mkdir -p "$W/t/scripts/tests" "$W/t/hooks"
  cp "$SRC/scripts/cargo-serialized.sh" "$W/t/scripts/"
  cp "$SRC/scripts/check.sh" "$W/t/scripts/"
  cp "$SRC/hooks/pre-push" "$W/t/hooks/"
  cp "$SRC/scripts/tests/test-gate-admission-controls.sh" "$W/t/scripts/tests/"
  chmod +x "$W/t/scripts/"*.sh "$W/t/scripts/tests/"*.sh "$W/t/hooks/pre-push"
  # THE MUTANT NEVER TOUCHES THE CHECKOUT. Everything runs from `$W/t`, a
  # four-file scratch copy, because CLAUDE.md records a lane whose in-place
  # `sed` made a sibling's build fail with errors naming the mutant's value --
  # and these particular files are worse than a Rust constant: `hooks/pre-push`
  # and `scripts/check.sh` are SHELL, read fresh on every invocation, so any
  # lane running a gate during the window executes the mutant directly.
  #
  # This is also why the control suite takes no `git` query: binding it to a
  # real repository would force the mutants back into the checkout.
  cp "$SRC/$file" "$W/orig"
  sed -i "$pattern" "$W/t/$file"
  if cmp -s "$W/orig" "$W/t/$file"; then
    echo "  !! $name: MUTATION DID NOT APPLY (pattern matched nothing) — inconclusive"
    return 1
  fi
  local out status
  out="$(cd "$W/t" && ./scripts/tests/test-gate-admission-controls.sh 2>&1)"
  status=$?
  local dead
  dead="$(printf '%s\n' "$out" | grep -c '^  FAIL')"
  if [ "$status" = "0" ]; then
    echo "  !! $name: SURVIVED — the guard is decorative"
    return 1
  fi
  if [ "$dead" != "$want" ]; then
    echo "  !! $name: killed $dead cases, expected exactly $want"
    printf '%s\n' "$out" | grep '^  FAIL' | sed 's/^/       /'
    return 1
  fi
  echo "  ok  $name: killed exactly $want"
  printf '%s\n' "$out" | grep '^  FAIL' | sed 's/^/       /'
  return 0
}

bad=0

# BASELINE FIRST. A mutant that "kills" a case proves nothing if the unmutated
# scratch copy already fails it -- that is the shape of the stale-bytecode trap
# CLAUDE.md documents for Python loops, arriving here as a scratch tree that is
# simply incomplete. So the four-file copy must go GREEN before any mutation is
# believed, and this harness refuses to report otherwise.
rm -rf "$W/t"; mkdir -p "$W/t/scripts/tests" "$W/t/hooks"
cp "$SRC/scripts/cargo-serialized.sh" "$SRC/scripts/check.sh" "$W/t/scripts/"
cp "$SRC/hooks/pre-push" "$W/t/hooks/"
cp "$SRC/scripts/tests/test-gate-admission-controls.sh" "$W/t/scripts/tests/"
chmod +x "$W/t/scripts/"*.sh "$W/t/scripts/tests/"*.sh "$W/t/hooks/pre-push"
if (cd "$W/t" && ./scripts/tests/test-gate-admission-controls.sh >/dev/null 2>&1); then
  echo "  ok  baseline: the unmutated scratch copy passes all cases"
else
  echo "  !! baseline: the UNMUTATED copy already fails — every kill below is"
  echo "     an artifact of the scratch tree, not of a guard. Refusing to report."
  exit 1
fi
echo

# nice/ionice removed -> lane work stops yielding to the battery. Two assertions
# fire (the default and the "not actually controllable" pair), which is one
# guard: they are the two halves that make each other evidence.
run_case "nice block removed" scripts/cargo-serialized.sh \
  '/^  run=(nice -n "\$NICE" "\${run\[@\]}")$/d' 2 || bad=1

# The re-entrancy check neutered -> a wrapped script calling a wrapped script
# blocks until AXEYUM_CARGO_WAIT. The positive control (75) must SURVIVE, which
# is what proves the first half measures re-entrancy and not luck.
#
# The CONDITION is falsified rather than the `exec` deleted. Deleting it leaves
# an `if` with an empty body, so the script stops parsing and all twelve cases
# die -- which reports the guard as strong for the wrong reason and would hide a
# genuinely decorative one. A mutation that breaks the subject measures nothing.
run_case "re-entrancy check neutered" scripts/cargo-serialized.sh \
  's/"\${AXEYUM_CARGO_SLOT_HELD:-0}" = "1"/"mutant" = "no"/' 1 || bad=1

# --batch memory scope suppression removed -> the aggregate gate becomes
# SIGKILL-able at a threshold no step of it exceeds.
#
# Targeted at the `:` arm, not at `if [ "$BATCH" = "1" ]`: that condition
# appears TWICE (it also selects the command vector), so mutating the text
# disabled `--batch` entirely and killed five cases. Replacing the arm's body
# with the scope it exempts is the faithful "we forgot the exemption" mutant.
run_case "--batch scope suppression removed" scripts/cargo-serialized.sh \
  's|^  : # a supervisor, not a cargo job.*|  run=(systemd-run --user --scope -q -p "MemoryMax=$MEM" -p "MemorySwapMax=$SWAP" "${run[@]}")|' 1 || bad=1

# The slice renamed back to the DASHED form -- the version that was correctly
# applied (cpu.weight really was 10) and completely ineffective, because systemd
# reads `-` as hierarchy and the sibling of the session scope became
# `axeyum.slice` at the default weight. This is the mutant that a naive
# "cpu.weight == 10" assertion would survive, which is why the suite asserts the
# cgroup LEVEL. Two halves of one guard: the name and the level.
run_case "slice renamed to the dashed (wrong-level) form" scripts/cargo-serialized.sh \
  's/axeyumlane/axeyum-lane/g' 2 || bad=1

# Cargo.lock dropped from the pre-push filter -> a dependency bump skips the
# whole battery, which is how it behaved until 2026-08-27.
run_case "Cargo.lock dropped from pre-push filter" hooks/pre-push \
  "s/ 'Cargo.lock' | head -1/ | head -1/" 1 || bad=1

# check.sh's slot re-exec removed -> the largest consumer on the box is outside
# the semaphore again, which was the whole diagnosis.
run_case "check.sh slot re-exec removed" scripts/check.sh \
  '/exec scripts\/cargo-serialized.sh --batch scripts\/check.sh/d' 1 || bad=1

echo
if [ "$bad" = "0" ]; then
  echo "mutation controls: ok — every guard is killed by exactly its own case"
else
  echo "mutation controls: FAILED"
fi
exit "$bad"
