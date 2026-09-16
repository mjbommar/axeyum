#!/usr/bin/env bash
# The ADR-2131 pre-merge gate battery, in one place so the list is a FILE rather
# than something retyped per run.
#
# The order is deliberate: cheapest first, so a failure costs the least. fmt and
# the default-feature check take seconds and have each refused a push here after
# the whole battery had already been spent.
#
# Each step writes its own log and its exit status is recorded; the summary at
# the end prints PASS/FAIL per step with the test COUNT, because a
# feature-gated suite that compiles to nothing prints "running 0 tests ... ok"
# and exits 0.
set -u
cd "$(dirname "$0")/../.." || exit 2
LOGS="${1:?usage: gates.sh <log-dir>}"
mkdir -p "$LOGS" || exit 2

declare -a NAMES=() RCS=()

run() {  # $1 label, rest: command
  local label="$1"; shift
  local log="$LOGS/${label}.log"
  echo "=== $label ===" >&2
  "$@" > "$log" 2>&1
  local rc=$?
  NAMES+=("$label"); RCS+=("$rc")
  echo "--- $label rc=$rc" >&2
}

run fmt cargo fmt --all --check
run check-default scripts/cargo-serialized.sh check --workspace --all-targets
run lib-sweep scripts/cargo-serialized.sh test -p axeyum-solver --lib --features full
run fixtures scripts/cargo-serialized.sh test -p axeyum-solver --features full \
  --test nra_clause_cert_2131

echo
echo "== gates =="
i=0
fail=0
while [ "$i" -lt "${#NAMES[@]}" ]; do
  n="${NAMES[$i]}"; rc="${RCS[$i]}"
  # The test COUNT, not just the status: a suite that ran zero tests exits 0.
  count=$(grep -E "^test result" "$LOGS/$n.log" 2>/dev/null | tail -1)
  if [ "$rc" -eq 0 ]; then s=PASS; else s=FAIL; fail=1; fi
  printf '%-16s %-4s rc=%-3s %s\n' "$n" "$s" "$rc" "${count:-<no test result line>}"
  i=$((i + 1))
done
[ "$fail" -eq 0 ] && echo "GATES_ALL_PASS" || echo "GATES_FAILED"
exit "$fail"
