#!/usr/bin/env bash
# Run the ENTIRE `dispatch/reason:` block from `hooks/pre-push`, not just the
# suites this lane's change happens to name.
#
# WHY THIS EXISTS: the ADR-2065 regression reached a push because the pre-merge
# list was clippy, fmt, the two builds, cargo doc, the lib sweep, and "the suites
# a change names". `flat_real_element_array_row_decides` is in none of those --
# it is a synthetic fixture in a suite this change never mentioned. The suite
# list is READ OUT OF THE HOOK rather than retyped, so it cannot drift from what
# the hook actually runs.
#
# TWO BUGS THIS SCRIPT HAD ON ITS FIRST RUN, both of which made it lie:
#   1. `case "$line" in *"0 passed"*)` matched "1**0 passed**" and "2**0
#      passed**", so it flagged three GREEN suites as inert. The emptiness test
#      has to anchor on the whole field, not a substring of a number.
#   2. Eleven suites reported "NO RESULT LINE" and the real cause was `/` at
#      100% -- `No space left on device` while writing a fingerprint. A missing
#      result line is not evidence about a suite; it is evidence the run did not
#      happen, and the two must not print the same way.
# Both are why the build failure is now surfaced verbatim instead of collapsed.
set -u
cd "${1:-$(git rev-parse --show-toplevel)}" || exit 2
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$PWD/target}"

SUITES=$(python3 - <<'PY'
import re
src = open("hooks/pre-push").read()
m = re.search(r"for suite in (unknown_reason_coverage.*?); do", src, re.S)
assert m, "the dispatch/reason suite list moved -- find it rather than guessing"
print(" ".join(m.group(1).replace("\\\n", " ").split()))
PY
)
echo "suites read from hooks/pre-push: $(echo "$SUITES" | wc -w)"
echo

rc=0
for suite in $SUITES; do
  out=$(scripts/cargo-serialized.sh test -p axeyum-solver --features full \
          --test "$suite" -- --test-threads=4 2>&1)
  line=$(printf '%s\n' "$out" | grep -E "^test result" | tail -1)
  if [ -z "$line" ]; then
    printf '%-42s %s\n' "$suite" "DID NOT RUN"
    printf '%s\n' "$out" | grep -E "^error|No space left" | head -2 | sed 's/^/      /'
    rc=1
    continue
  fi
  # Anchor on the whole count field: `0 passed` is only zero when the digit
  # before it is a word boundary.
  passed=$(printf '%s\n' "$line" | grep -oE "ok\. [0-9]+ passed" | grep -oE "[0-9]+")
  printf '%-42s %s\n' "$suite" "$line"
  case "$line" in *"result: ok"*) : ;; *) rc=1 ;; esac
  if [ "${passed:-0}" -eq 0 ]; then
    echo "      ^^ ZERO TESTS -- an inert suite is not a passing one"
    rc=1
  fi
done
echo
[ "$rc" -eq 0 ] && echo "ALL dispatch/reason SUITES GREEN" || echo "AT LEAST ONE SUITE RED, INERT, OR DID NOT RUN"
exit "$rc"
