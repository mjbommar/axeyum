#!/usr/bin/env bash
#
# The SOS certificate checker must FAIL on false certificates.
#
# WHY THIS EXISTS. A checker is only worth what it rejects. The 2026-08-15 audit
# of this repository's fact ledger found 40 of 162 checker runs exiting zero on
# *completion alone*: `nat_theorem_inventory -- this_theorem_does_not_exist`
# prints "0 theorems" and exits 0, and that was the shape of a real fact's
# checker. Every fact in the `sos` family cites this script, so no SOS fact can
# be closed by `scripts/close-fact.py` -- which executes every checker_command
# and refuses the flip on a non-zero exit -- without these controls passing.
#
# Three classes of assertion, and all three are load-bearing:
#
#   expect_rejected  a committed FALSE certificate must exit non-zero. Twenty-one
#                    fixtures, each one surgical edit away from an honest
#                    artifact, produced by scripts/gen-sos-negative-controls.py.
#   expect_accepted  the honest artifacts must still be ACCEPTED. Without this
#                    half the suite is passed by a checker that rejects
#                    everything, which is the classic way a negative-control
#                    suite becomes decorative.
#   flag assertions  the --expect-* flags must themselves bite. A flag that is
#                    silently ignored is an assertion that never ran, and the
#                    facts that cite this binary pin their obligation counts
#                    through exactly those flags.
#
# Cost: measured 5.1 s warm on this box (load 1.3), 36 assertions over 21
# fixtures. The suite was itself probed: dropping a COPY of an honest artifact
# into the fixture directory makes it report `ACCEPTED ... the checker did NOT
# catch a false claim` and exit 1, so the gate fails closed rather than passing
# on a fixture that stopped being false.

set -euo pipefail
cd "$(dirname "$0")/.."

if [ -z "${TMPDIR:-}" ] && [ -d /data0/axeyum/scratch ]; then
    export TMPDIR=/data0/axeyum/scratch
fi

CONTROLS="artifacts/instances/sos/negative-controls"
HONEST="artifacts/sos-certificates"
MIN_CONTROLS=21

BIN=(cargo run --release -q -p axeyum-cas --example sos_certify --)

ran=0
fails=0

expect_rejected() {
    local label="$1"
    shift
    ran=$((ran + 1))
    if "$@" >/dev/null 2>&1; then
        printf 'ACCEPTED  %s  -- the checker did NOT catch a false claim\n' "$label"
        fails=$((fails + 1))
    fi
}

expect_accepted() {
    local label="$1"
    shift
    ran=$((ran + 1))
    if ! "$@" >/dev/null 2>&1; then
        printf 'REJECTED  %s  -- a TRUE certificate was refused; the checker rejects everything\n' "$label"
        fails=$((fails + 1))
    fi
}

# Build once so the per-assertion cost is the check, not the compiler.
cargo build --release -q -p axeyum-cas --example sos_certify

# --- (a) every committed false certificate is rejected ----------------------
controls=0
for fixture in "$CONTROLS"/*.json; do
    [ -e "$fixture" ] || continue
    controls=$((controls + 1))
    expect_rejected "tampered $(basename "$fixture")" "${BIN[@]}" "$fixture"
done

if [ "$controls" -lt "$MIN_CONTROLS" ]; then
    printf 'only %d negative control(s) found, expected at least %d -- a shrinking sweep is a weaker gate wearing the same name\n' \
        "$controls" "$MIN_CONTROLS"
    exit 1
fi

# --- (b) the --expect-* flags bite ------------------------------------------
expect_rejected "obligation count is load-bearing (lyapunov)" \
    "${BIN[@]}" "$HONEST/damped-rotation-lyapunov.json" --expect-checks 99
expect_rejected "obligation count is load-bearing (barrier)" \
    "${BIN[@]}" "$HONEST/energy-barrier-reachability.json" --expect-checks 99
expect_rejected "obligation count is load-bearing (psd-not-sos)" \
    "${BIN[@]}" "$HONEST/motzkin-psd-not-sos.json" --expect-checks 99
expect_rejected "kind assertion is load-bearing" \
    "${BIN[@]}" "$HONEST/damped-rotation-lyapunov.json" --expect-kind barrier
expect_rejected "id assertion is load-bearing" \
    "${BIN[@]}" "$HONEST/damped-rotation-lyapunov.json" --expect-id motzkin-psd-not-sos
expect_rejected "decay rate assertion is load-bearing" \
    "${BIN[@]}" "$HONEST/damped-rotation-lyapunov.json" --expect-rate 1/25
expect_rejected "a rate demanded of a certificate that reports none" \
    "${BIN[@]}" "$HONEST/energy-barrier-reachability.json" --expect-rate 1/26
expect_rejected "an unknown flag is an assertion that never ran" \
    "${BIN[@]}" "$HONEST/damped-rotation-lyapunov.json" --no-such-flag
expect_rejected "no artifact at all" "${BIN[@]}"
expect_rejected "a path that does not exist" "${BIN[@]}" "$CONTROLS/absent.json"

# --- (c) the honest artifacts are still accepted ----------------------------
expect_accepted "damped-rotation-lyapunov" \
    "${BIN[@]}" "$HONEST/damped-rotation-lyapunov.json" \
    --expect-kind lyapunov --expect-id damped-rotation-lyapunov \
    --expect-checks 8 --expect-rate 1/26
expect_accepted "energy-barrier-reachability" \
    "${BIN[@]}" "$HONEST/energy-barrier-reachability.json" \
    --expect-kind barrier --expect-id energy-barrier-reachability --expect-checks 6
expect_accepted "motzkin-psd-not-sos" \
    "${BIN[@]}" "$HONEST/motzkin-psd-not-sos.json" \
    --expect-kind psd-not-sos --expect-id motzkin-psd-not-sos --expect-checks 5

# --- (d) the fixtures are reproducible from their generator -----------------
ran=$((ran + 1))
if ! python3 scripts/gen-sos-negative-controls.py --check >/dev/null 2>&1; then
    printf 'DRIFT     the committed fixtures no longer match scripts/gen-sos-negative-controls.py\n'
    fails=$((fails + 1))
fi

# --- (e) the honest artifacts still match the corpus they were emitted from --
ran=$((ran + 1))
if ! cargo run --release -q -p axeyum-cas --example emit_sos_certificates -- --check >/dev/null 2>&1; then
    printf 'DRIFT     artifacts/sos-certificates/ no longer matches axeyum_cas::sos::corpus\n'
    fails=$((fails + 1))
fi

printf '%d negative control fixture(s), %d assertion(s) run, %d failure(s)\n' \
    "$controls" "$ran" "$fails"
[ "$fails" -eq 0 ] || exit 1
