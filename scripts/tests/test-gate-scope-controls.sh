#!/usr/bin/env bash
# Negative controls for the gate-scope fixes: each one must FAIL without the fix.
#
# A control that passes while testing nothing is the trap this repository has
# already stepped in (one lane found six of seven guards removable with every
# test still green). So each control here is built the same way:
#
#   1. show the OLD gate exits 0 on a broken tree   (the hole is real)
#   2. show the NEW gate exits non-zero on it       (the hole is closed)
#   3. show the new gate with its guard DELETED exits 0 again
#      (the guard is load-bearing, not decoration)
#
# Step 3 is the one that matters: it is a mutation test on our own gate.
#
# Runs in a throwaway workspace under ${TMPDIR:-/tmp}/axeyum-gate-control.$$;
# nothing here touches the repository it is run from except reading two scripts.
#
# Usage: scripts/tests/test-gate-scope-controls.sh
set -uo pipefail

repo="$(cd "$(dirname "$0")/../.." && pwd)"
work="$(mktemp -d "${TMPDIR:-/tmp}/axeyum-gate-control.XXXXXX")" || exit 2
trap 'rm -rf "$work"' EXIT

pass=0
fail=0
check() { # check <description> <expected-exit> <actual-exit>
  if [ "$2" -eq "$3" ]; then
    echo "  ok   $1 (exit $3)"
    pass=$((pass + 1))
  else
    echo "  FAIL $1 (expected exit $2, got $3)" >&2
    fail=$((fail + 1))
  fi
}

# ---------------------------------------------------------------------------
# The fixture: a one-crate workspace laid out like axeyum (crates/<name>), with
# an example and a unit test, plus copies of the two scripts under test so they
# resolve this workspace as their root.
# ---------------------------------------------------------------------------
mkdir -p "$work/crates/demo/src" "$work/crates/demo/examples" "$work/scripts"
cp "$repo/scripts/check-source-freshness.sh" "$repo/scripts/check-clippy-complete.sh" \
   "$repo/scripts/check-workspace-tests.sh" "$work/scripts/"
chmod +x "$work/scripts/"*.sh

cat > "$work/Cargo.toml" <<'EOF'
[workspace]
members = ["crates/demo"]
resolver = "3"
EOF
cat > "$work/crates/demo/Cargo.toml" <<'EOF'
[package]
name = "demo"
version = "0.0.0"
edition = "2021"
EOF

clean_lib() {
  cat > "$work/crates/demo/src/lib.rs" <<'EOF'
pub fn answer() -> usize {
    1
}

#[cfg(test)]
mod tests {
    #[test]
    fn answer_is_one() {
        assert_eq!(super::answer(), 1);
    }
}
EOF
}
clean_example() {
  cat > "$work/crates/demo/examples/probe.rs" <<'EOF'
fn main() {
    println!("{}", value());
}

fn value() -> usize {
    7
}
EOF
}
# `needless_return` is warn-by-default in clippy, so `-D warnings` must reject it.
warning_example() {
  cat > "$work/crates/demo/examples/probe.rs" <<'EOF'
fn main() {
    println!("{}", value());
}

fn value() -> usize {
    return 7;
}
EOF
}
# The library now contradicts its own unit test, so the test MUST fail.
broken_lib() {
  cat > "$work/crates/demo/src/lib.rs" <<'EOF'
pub fn answer() -> usize {
    99
}

#[cfg(test)]
mod tests {
    #[test]
    fn answer_is_one() {
        assert_eq!(super::answer(), 1);
    }
}
EOF
}

# The mtime every stale file gets. `git archive | tar -x` stamps files with the
# COMMIT time, which is how this happens in real life; an explicit old date makes
# the control deterministic.
STALE='2020-01-01 00:00:00'

cd "$work" || exit 2
export CARGO_TARGET_DIR="$work/target"

echo "=== control 1: clippy over a stale-mtime warning ==="
clean_lib; clean_example
cargo clippy --workspace --all-targets --all-features -- -D warnings >/dev/null 2>&1
check "baseline: bare clippy is green on a clean tree" 0 $?

# Record the clean tree as examined, so the new gate has a manifest to compare
# against (this is what a passing gate run leaves behind).
./scripts/check-clippy-complete.sh >/dev/null 2>&1
check "baseline: new clippy gate is green on a clean tree" 0 $?

warning_example
touch -d "$STALE" crates/demo/examples/probe.rs
cargo clippy --workspace --all-targets --all-features -- -D warnings >/dev/null 2>&1
check "THE HOLE: bare clippy exits 0 over a warning it never compiled" 0 $?

out="$(./scripts/check-clippy-complete.sh 2>&1)"
check "FIXED: check-clippy-complete rejects it" 101 $?
case "$out" in
  *needless_return*) echo "  ok   the diagnostic is reported, not swallowed"; pass=$((pass + 1)) ;;
  *) echo "  FAIL the gate failed without naming needless_return" >&2; fail=$((fail + 1)) ;;
esac
case "$out" in
  *"linted "*" of "*" workspace targets"*) echo "  ok   the gate reports its scope"; pass=$((pass + 1)) ;;
  *) echo "  FAIL the gate did not report how many targets it linted" >&2; fail=$((fail + 1)) ;;
esac

echo "=== control 2: the guard is load-bearing (mutation) ==="
# Delete exactly one line — the freshness step — and nothing else. If the gate
# still fails after this, the control above was not testing the guard.
sed '/check-source-freshness.sh" --gate clippy --touch/d' \
  scripts/check-clippy-complete.sh > scripts/clippy-guard-deleted.sh
chmod +x scripts/clippy-guard-deleted.sh
if ! cmp -s scripts/check-clippy-complete.sh scripts/clippy-guard-deleted.sh; then
  echo "  ok   the mutation removed a line"
  pass=$((pass + 1))
else
  echo "  FAIL the mutation removed nothing — the sed pattern no longer matches" >&2
  fail=$((fail + 1))
fi
# Reset to a GREEN, CACHED state first. A failed compilation is not cached, so
# after control 1 cargo would recompile the example on any subsequent run and the
# mutation would look harmless — the hole needs a successful artifact to replay.
clean_example
cargo clippy --workspace --all-targets --all-features -- -D warnings >/dev/null 2>&1
check "reset: clean tree compiled and cached" 0 $?
warning_example
touch -d "$STALE" crates/demo/examples/probe.rs
./scripts/clippy-guard-deleted.sh >/dev/null 2>&1
check "guard deleted: the gate goes green over the same warning" 0 $?

echo "=== control 3: cargo test over stale-mtime source ==="
clean_lib; clean_example
cargo test --workspace >/dev/null 2>&1
check "baseline: cargo test is green" 0 $?

out="$(./scripts/check-workspace-tests.sh 2>&1)"
check "baseline: check-workspace-tests is green" 0 $?
case "$out" in
  *"ran 1 tests across"*) echo "  ok   the test gate reports its count"; pass=$((pass + 1)) ;;
  *) echo "  FAIL the test gate did not report a test count" >&2; fail=$((fail + 1)) ;;
esac

broken_lib
touch -d "$STALE" crates/demo/src/lib.rs
cargo test --workspace >/dev/null 2>&1
check "THE HOLE: cargo test PASSES a test that must fail" 0 $?

./scripts/check-workspace-tests.sh >/dev/null 2>&1
check "FIXED: check-workspace-tests fails on the same tree" 101 $?

# ---------------------------------------------------------------------------
# Controls 4 and 5 run against the REPOSITORY, not the fixture: they are about
# the aggregate gate's own scope, which only exists there. Both are read-only.
# ---------------------------------------------------------------------------
echo "=== control 4: the aggregate gate cannot silently lose steps ==="
listed="$(AXEYUM_CHECK_LIST=1 "$repo/scripts/check.sh" 2>/dev/null | wc -l)"
floor="$(grep -E '^STEP_FLOOR=[0-9]+$' "$repo/scripts/check.sh" | cut -d= -f2)"
if [ -n "$floor" ] && [ "$listed" -ge "$floor" ] && [ "$listed" -gt 0 ]; then
  echo "  ok   check.sh lists $listed steps against its floor of $floor"
  pass=$((pass + 1))
else
  echo "  FAIL check.sh lists $listed steps, floor '$floor'" >&2
  fail=$((fail + 1))
fi
# The mutation: delete one step and require the floor to notice. Done on a COPY
# so the repository is untouched.
sed '0,/^step /{/^step /d}' "$repo/scripts/check.sh" > "$work/check-one-step-less.sh"
mutated="$(AXEYUM_CHECK_LIST=1 bash "$work/check-one-step-less.sh" 2>/dev/null | wc -l)"
if [ "$mutated" -eq $((listed - 1)) ]; then
  echo "  ok   the mutation removed exactly one step ($mutated vs $listed)"
  pass=$((pass + 1))
else
  echo "  FAIL the mutation changed the step count from $listed to $mutated" >&2
  fail=$((fail + 1))
fi

echo "=== control 6: the step floor fails a gate that lost steps ==="
# Take check.sh, delete every step, add two trivial ones, and set the floor above
# them: a run with nothing failing must still exit non-zero.
mkdir -p "$work/floor/scripts"
sed '/^step /d' "$repo/scripts/check.sh" > "$work/floor/scripts/check.sh"
python3 - "$work/floor/scripts/check.sh" <<'PY'
import sys
path = sys.argv[1]
text = open(path).read()
text = text.replace("STEP_FLOOR=80", "STEP_FLOOR=5")
text = text.replace(
    'if [ "$list_only" = "1" ]; then\n  echo "check: $ran steps" >&2',
    'step ok-one true\nstep ok-two true\n\nif [ "$list_only" = "1" ]; then\n  echo "check: $ran steps" >&2',
)
open(path, "w").write(text)
PY
out="$(bash "$work/floor/scripts/check.sh" 2>&1)"
check "two steps against a floor of five fails despite nothing failing" 1 $?
case "$out" in
  *"below the committed floor"*) echo "  ok   the floor says why"; pass=$((pass + 1)) ;;
  *) echo "  FAIL the floor failed without explaining itself" >&2; fail=$((fail + 1)) ;;
esac

echo "=== control 5: new just-vs-check.sh divergence is rejected ==="
if command -v just >/dev/null 2>&1; then
  # Drop one accepted difference: the gate must then report it as unrecorded.
  grep -v '^#' "$repo/scripts/check-aggregate-scope.expected" | grep -v '^[[:space:]]*$' \
    | tail -n +2 > "$work/expected-minus-one"
  "$repo/scripts/check-aggregate-scope.sh" --expected "$work/expected-minus-one" >/dev/null 2>&1
  check "a difference missing from the expectation file fails the gate" 1 $?
  "$repo/scripts/check-aggregate-scope.sh" >/dev/null 2>&1
  check "the committed expectation file passes" 0 $?
else
  echo "  skip \`just\` is not installed — the divergence gate cannot be controlled here"
fi

echo
echo "gate-scope controls: $pass passed, $fail failed"
[ "$fail" -eq 0 ] || exit 1
