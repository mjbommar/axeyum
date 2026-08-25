#!/usr/bin/env bash
# Controls for `hooks/commit-msg`'s lane stamp.
#
# The property under test is NOT "the text `Agent:` is in the message" -- the
# defect this suite exists for produced exactly that and was still broken. It is
# that `git log --format='%(trailers:key=Agent,valueonly)'` RETURNS THE LANE,
# because that is the query CLAUDE.md prescribes and the one every attribution
# check runs. A stamp git does not parse is an unattributed commit that looks
# attributed.
set -uo pipefail

HOOK="$(cd "$(dirname "$0")/../.." && pwd)/hooks/commit-msg"
[ -x "$HOOK" ] || { echo "FAIL: $HOOK is not executable"; exit 1; }

TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
pass=0; fail=0

# Assert the hook's output PARSES as a trailer with the expected value.
check_parses() {
    local name="$1" agent="$2" file="$TMP/msg"
    printf '%s' "$3" > "$file"
    if ! AXEYUM_AGENT="$agent" "$HOOK" "$file" >/dev/null 2>&1; then
        echo "FAIL $name: hook exited nonzero"; fail=$((fail+1)); return
    fi
    local got
    got=$(git interpret-trailers --parse < "$file" | grep '^Agent:' | sed 's/^Agent:[[:space:]]*//')
    if [ "$got" = "$agent" ]; then
        echo "ok   $name"; pass=$((pass+1))
    else
        echo "FAIL $name: parsed trailer is '$got', want '$agent'"; fail=$((fail+1))
    fi
}

check_refuses() {
    local name="$1" file="$TMP/msg"
    printf '%s' "$2" > "$file"
    if env -u AXEYUM_AGENT "$HOOK" "$file" >/dev/null 2>&1; then
        echo "FAIL $name: hook accepted an unidentified commit"; fail=$((fail+1))
    else
        echo "ok   $name"; pass=$((pass+1))
    fi
}

check_unchanged() {
    local name="$1" file="$TMP/msg"
    printf '%s' "$2" > "$file"
    local before; before=$(cat "$file")
    AXEYUM_AGENT=other "$HOOK" "$file" >/dev/null 2>&1
    if [ "$(cat "$file")" = "$before" ]; then
        echo "ok   $name"; pass=$((pass+1))
    else
        echo "FAIL $name: hook modified a message it should have left alone"; fail=$((fail+1))
    fi
}

# --- the two shapes that were BROKEN, 2026-08-25 -------------------------
# A body whose last line is prose beginning `ways: ` -- indistinguishable from
# a trailer to a regex, so no blank line was inserted and the stamp joined the
# preceding paragraph.
check_parses "prose line that looks like a trailer" "lane-a" \
'subject line

body text
ways: the true value is accepted, the false claim is refused.
'
# A subject-only message whose subject begins `fixup: ` -- same misreading, and
# a two-line message has no trailer block at all.
check_parses "subject-only message with a colon" "lane-b" \
'fixup: clippy doc-lazy-continuation
'

# --- shapes that already worked, kept so a fix cannot regress them --------
check_parses "ordinary body" "lane-c" \
'subject

an ordinary body paragraph.
'
check_parses "existing trailer block" "lane-d" \
'subject

body

Co-Authored-By: Someone <s@example.com>
'
check_parses "body ending in a blank line" "lane-e" \
'subject

body

'

# --- the guards, each verified to FIRE ------------------------------------
check_refuses "no lane identity is refused" \
'subject

body
'
check_unchanged "an already-stamped message is left alone" \
'subject

body

Agent: original-lane
'
check_unchanged "a merge message is not stamped" \
'Merge branch '"'"'x'"'"' into y
'

echo
echo "commit-msg trailer controls: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
