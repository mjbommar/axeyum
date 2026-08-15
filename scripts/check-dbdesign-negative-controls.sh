#!/usr/bin/env bash
# Measure that the database-design checkers FAIL when the claim is false.
#
# WHY THIS EXISTS. An audit of this ledger on 2026-08-15 found 40 of 162
# checker runs exiting 0 on *completion alone*: they ran a tool, the tool
# finished, and the fact was recorded as checked. `nat_theorem_inventory --
# this_theorem_does_not_exist` prints "0 theorems" and exits 0. A checker with
# that shape is not evidence of anything, and adding another one would be
# adding a fact that looks established and is not.
#
# So every settled database-design fact cites this script alongside its own
# checker. Each file in artifacts/instances/dbdesign/negative-controls/ pins
# exactly one FALSE answer -- a dependency that is not implied, a candidate-key
# list with one key missing, a lossy split declared lossless, a query
# containment that does not hold -- and this script requires a NON-ZERO exit
# for every one of them. It also requires:
#
#   * that the count of controls is at least the expected minimum, so a
#     deleted or renamed fixture is a failure rather than a silently smaller
#     sweep;
#   * that an instance pinning NO expectation is refused (the "the check never
#     ran" control);
#   * that `--expect-checks` with the wrong number fails on an instance whose
#     every claim is true, so the count itself is load-bearing;
#   * that the positive instances still pass, because a checker that rejects
#     everything would sail through all of the above.
#
# Usage: scripts/check-dbdesign-negative-controls.sh
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

CONTROLS="artifacts/instances/dbdesign/negative-controls"
MIN_CONTROLS=13

SCHEMA_BIN=(cargo run --release -q -p axeyum-bench --example db_design_certify --)
QUERY_BIN=(cargo run --release -q -p axeyum-bench --example cq_containment_certify --)

fails=0
ran=0

# A control passes when the checker REJECTS it.
expect_rejected() {
    local label="$1"; shift
    ran=$((ran + 1))
    if "$@" >/dev/null 2>&1; then
        printf 'ACCEPTED  %s -- the checker did NOT catch a false claim\n' "$label"
        fails=$((fails + 1))
    else
        printf 'rejected  %s (exit %d)\n' "$label" "$?"
    fi
}

expect_accepted() {
    local label="$1"; shift
    ran=$((ran + 1))
    if "$@" >/dev/null 2>&1; then
        printf 'accepted  %s\n' "$label"
    else
        printf 'REJECTED  %s -- a TRUE instance was refused; the checker rejects everything\n' "$label"
        fails=$((fails + 1))
    fi
}

echo "== negative controls: every one of these must be refused =="
controls=0
for file in "$CONTROLS"/*.dbd; do
    [ -e "$file" ] || continue
    controls=$((controls + 1))
    expect_rejected "$(basename "$file")" "${SCHEMA_BIN[@]}" "$file"
done
for file in "$CONTROLS"/*.cq; do
    [ -e "$file" ] || continue
    controls=$((controls + 1))
    expect_rejected "$(basename "$file")" "${QUERY_BIN[@]}" "$file"
done

echo "== the count itself must be load-bearing =="
expect_rejected "addresses-zip.dbd --expect-checks 99" \
    "${SCHEMA_BIN[@]}" artifacts/instances/dbdesign/addresses-zip.dbd --expect-checks 99
expect_rejected "view-reuse.cq --expect-checks 99" \
    "${QUERY_BIN[@]}" artifacts/instances/dbdesign/view-reuse.cq --expect-checks 99
expect_rejected "a schema question run through the containment checker" \
    "${QUERY_BIN[@]}" artifacts/instances/dbdesign/addresses-zip.dbd
expect_rejected "a containment question run through the schema checker" \
    "${SCHEMA_BIN[@]}" artifacts/instances/dbdesign/view-reuse.cq

echo "== a formal statement that is not valid must be refused =="
expect_rejected "wrong-formal.smt2 through --verify-formal" \
    "${SCHEMA_BIN[@]}" artifacts/instances/dbdesign/orders-schema.dbd \
    --verify-formal "$CONTROLS/wrong-formal.smt2"
expect_rejected "--verify-formal on a file that asserts nothing" \
    "${SCHEMA_BIN[@]}" artifacts/instances/dbdesign/orders-schema.dbd \
    --verify-formal artifacts/instances/dbdesign/orders-schema.dbd

echo "== and the true instances must still be accepted =="
expect_accepted "addresses-zip.dbd --expect-checks 11" \
    "${SCHEMA_BIN[@]}" artifacts/instances/dbdesign/addresses-zip.dbd --expect-checks 11
expect_accepted "orders-schema.dbd --expect-checks 11 --verify-formal orders-fd-claims.smt2" \
    "${SCHEMA_BIN[@]}" artifacts/instances/dbdesign/orders-schema.dbd --expect-checks 11 \
    --verify-formal artifacts/instances/dbdesign/orders-fd-claims.smt2
expect_accepted "view-reuse.cq --expect-checks 6" \
    "${QUERY_BIN[@]}" artifacts/instances/dbdesign/view-reuse.cq --expect-checks 6

if [ "$controls" -lt "$MIN_CONTROLS" ]; then
    printf '\nFAIL: found %d negative controls, expected at least %d. A shrinking\n' \
        "$controls" "$MIN_CONTROLS"
    printf 'sweep is a weaker gate wearing the same name.\n'
    exit 1
fi

printf '\n%d control(s) in %s; %d assertion(s) run, %d failure(s)\n' \
    "$controls" "$CONTROLS" "$ran" "$fails"
if [ "$fails" -ne 0 ]; then
    echo "FAIL: the database-design checkers do not fail closed."
    exit 1
fi
echo "VERIFIED: every false claim is refused and every true one is accepted."
