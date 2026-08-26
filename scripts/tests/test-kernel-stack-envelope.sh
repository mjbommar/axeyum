#!/usr/bin/env bash
# Controls for `scripts/check-kernel-stack-envelope.sh`.
#
# A ratchet nobody has watched go red is not a ratchet. Each case here drives
# the checker with a deliberately wrong pin file (via `AXEYUM_STACK_PIN_FILE`,
# so no tracked file is mutated and no other lane's build is disturbed) and
# asserts the checker distinguishes it from a pass.
#
# The four failure modes, and why each needs its own case:
#
#  1. A prelude outgrew its budget      -> exit 1, message names the stack.
#     This is the one the gate exists for.
#  2. A budget so large it proves nothing -> WARN, exit 0. A pinned 1 TiB would
#     pass forever while measuring nothing; without this the "observed failure"
#     requirement could be deleted and every case would still be green.
#  3. No rows matched the profile        -> exit 1, "ran nothing". An empty
#     ledger and a passing one are the same observation otherwise.
#  4. The probe rejected its own arguments -> exit 2, NOT read as "needs more
#     stack". A typo in a prelude name must not masquerade as a measurement.
#
# Release profile throughout: same code path, ~30x cheaper than debug.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"

CHECK="scripts/check-kernel-stack-envelope.sh"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

failures=0

# $1 case name, $2 expected exit, $3 a string the output must contain
run_case() {
  local name="$1" want="$2" needle="$3" pin="$4"
  local out status=0
  out=$(AXEYUM_STACK_PIN_FILE="$pin" "$CHECK" --check --profile release 2>&1) || status=$?
  if [ "$status" -ne "$want" ]; then
    echo "FAIL [$name]: expected exit $want, got $status" >&2
    printf '%s\n' "$out" | sed 's/^/    /' >&2
    failures=$(( failures + 1 ))
    return
  fi
  if [ "$(printf '%s' "$out" | /usr/bin/grep -c -- "$needle")" -eq 0 ]; then
    echo "FAIL [$name]: exit $status was right but the output never said '$needle'" >&2
    printf '%s\n' "$out" | sed 's/^/    /' >&2
    failures=$(( failures + 1 ))
    return
  fi
  echo "ok   [$name]"
}

# --- 0. control: the committed pins pass, so a later failure is the mutation
#        and not a broken harness.
run_case "committed pins pass" 0 "within budget" "artifacts/kernel-stack-envelope.tsv"

# --- 1. a prelude outgrew its budget. 4096 bytes is below every measured
#        requirement, so this stands in for growth without needing a new
#        declaration.
printf 'release\tcpoint\t4096\n' > "$TMP/too-small.tsv"
run_case "budget below requirement is RED" 1 "no longer builds on its pinned" "$TMP/too-small.tsv"

# --- 2. a budget that cannot fail. 256 MiB is ~256x cpoint's release
#        requirement, so three halvings still succeed and the run has proved
#        nothing.
printf 'release\tcpoint\t268435456\n' > "$TMP/too-big.tsv"
run_case "budget that cannot fail WARNs" 0 "more than 8x the requirement" "$TMP/too-big.tsv"

# --- 3. nothing matched the profile.
printf 'debug\tcpoint\t33554432\n' > "$TMP/wrong-profile.tsv"
run_case "no matching rows is RED" 1 "ran nothing" "$TMP/wrong-profile.tsv"

# --- 4. the probe rejected its own arguments. Exit 2, distinct from both a
#        pass and a stack failure.
printf 'release\tnot-a-prelude\t1048576\n' > "$TMP/bad-name.tsv"
run_case "probe usage error is exit 2" 2 "NOT a stack result" "$TMP/bad-name.tsv"

# --- 5. a missing pin file is RED, not an empty pass.
run_case "missing pin file is RED" 1 "is missing" "$TMP/does-not-exist.tsv"

if [ "$failures" -gt 0 ]; then
  echo "$failures control(s) failed" >&2
  exit 1
fi
echo "all controls passed"
