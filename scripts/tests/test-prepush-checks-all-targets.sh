#!/usr/bin/env bash
# The pre-push compile gate must see `examples/` and `tests/`, not just libs.
#
# On 2026-08-20 a new `Evidence` variant broke the exhaustive `match` in two
# `axeyum-bench` examples. `hooks/pre-push` ran `cargo check --workspace`, which
# does not build example or test targets, so it passed and printed
# "pushed SHA compiles" — over a workspace that did not. The break reached
# `main`.
#
# This is a static control, deliberately. Actually compiling a broken fixture
# workspace would cost minutes per run and would test cargo rather than the
# hook. What went wrong was one missing flag in one command, and that is a
# property of the file.
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 2

HOOK=hooks/pre-push
fail=0

# The compile step, whatever it is called, must carry --all-targets.
line=$(grep -nE '^\s*step_seconds "cargo check[^"]*"' "$HOOK" | head -1)
if [ -z "$line" ]; then
  echo "FAIL: no 'cargo check' step found in $HOOK -- did it move? This control" >&2
  echo "      pins a step that must exist; a silently renamed step is a hole." >&2
  exit 1
fi

# The actual invocation is on the continuation line after the label.
invocation=$(grep -A1 -E '^\s*step_seconds "cargo check[^"]*"' "$HOOK" | tr '\n' ' ')
case "$invocation" in
  *"cargo check --workspace --all-targets"*)
    echo "  ok   the compile step builds all targets" ;;
  *)
    echo "FAIL: the pre-push compile step does not pass --all-targets, so" >&2
    echo "      examples/ and tests/ are never compiled and the hook's" >&2
    echo "      'pushed SHA compiles' line is false for half the tree." >&2
    echo "      found: $invocation" >&2
    fail=1 ;;
esac

# ...and the label must say so, because the label is what a reader believes.
case "$line" in
  *"--all-targets"*) echo "  ok   the step's label names what it checks" ;;
  *) echo "FAIL: the step is labelled '$line' but checks more/less than that;" >&2
     echo "      a label that understates the step is how the hole survived." >&2
     fail=1 ;;
esac

[ "$fail" = 0 ] && echo "prepush all-targets: ok"
exit "$fail"
