#!/usr/bin/env bash
# Mutation table for scripts/credit-transaction.py (L0 phase S6).
#
# CLAUDE.md's standing rule: "when you touch a checker, delete one guard and
# require that EXACTLY ONE test dies." This script deletes nine guards, one
# at a time, in a SCRATCH COPY (never the shared checkout -- see CLAUDE.md's
# "mutation testing in the shared worktree breaks other lanes' builds"), and
# requires each mutation to kill exactly one CANARY test from a fixed,
# disjoint set of nine -- one canary per guard.
#
# Why a curated canary set rather than the whole suite: several tests in
# scripts/tests/test-credit-transaction.py are deliberately BROAD (the
# aggregate "all four fixtures reject" check, the subprocess-level CLI exit
# code checks) and exercise more than one guard by design. Running mutation
# verification against those would make every staleness-guard deletion kill
# two or three tests at once, which is a real property of the integration
# tests but tells you nothing about whether the nine guards are separately
# load-bearing. The nine canaries below were written narrow specifically so
# this table means something; the broader tests still run in the normal
# suite and still need to pass on the unmutated tree (checked at the end).
#
# `__pycache__` is cleared before every run: Python's bytecode cache keys on
# (mtime-in-whole-seconds, size), mutations are equal-size by construction,
# and a hand loop that skips this reports the PREVIOUS mutant's result
# (CLAUDE.md, "stale .pyc in mutation loops").
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SCRATCH="$(mktemp -d "${TMPDIR:-/tmp}/credit-txn-mutation-XXXXXX")"
trap 'rm -rf "$SCRATCH"' EXIT

mkdir -p "$SCRATCH/scripts/tests"
cp "$REPO_ROOT/scripts/credit-transaction.py" "$SCRATCH/scripts/credit-transaction.py"
cp "$REPO_ROOT/scripts/check-credit-transaction.py" "$SCRATCH/scripts/check-credit-transaction.py"
cp "$REPO_ROOT/scripts/tests/test-credit-transaction.py" "$SCRATCH/scripts/tests/test-credit-transaction.py"

ENGINE="$SCRATCH/scripts/credit-transaction.py"
TESTFILE="$SCRATCH/scripts/tests/test-credit-transaction.py"

# All nine canaries, run together for every mutation (and once unmutated as
# a baseline). Each is written to isolate exactly one guard.
CANARIES=(
  "FreshReadTests.test_commit_uses_fresh_disk_journal_not_cached_object"
  "StalenessFixtureTests.test_stale_receipt_raises_only_stale_receipt_error"
  "StalenessFixtureTests.test_stale_source_raises_only_stale_source_error"
  "StalenessFixtureTests.test_stale_graph_raises_only_stale_graph_error"
  "StalenessFixtureTests.test_stale_checker_raises_only_stale_checker_error"
  "GuardBehaviorTests.test_commit_rejects_a_non_prepared_transaction"
  "GuardBehaviorTests.test_apply_rejects_an_uncommitted_transaction"
  "GuardBehaviorTests.test_apply_refuses_corrupted_staged_content"
  "IdempotenceTests.test_replay_is_idempotent"
)

clear_pycache() {
  find "$SCRATCH" -name '__pycache__' -exec rm -rf {} + 2>/dev/null || true
}

# Runs the nine canaries against the (possibly mutated) scratch copy and
# prints one PASS/FAIL line per canary. Returns the list of FAILED canary
# names, one per line, on stdout via a marker prefix.
run_canaries() {
  clear_pycache
  python3 "$TESTFILE" -v "${CANARIES[@]}" > "$SCRATCH/run.log" 2>&1 || true
  return 0
}

# Determine, from a -v run log, which of the nine canaries failed/errored.
failed_canaries_from_log() {
  local log="$1"
  local name
  for name in "${CANARIES[@]}"; do
    # unittest -v prints: "<method> (<module>.<Class>...) ... ok|FAIL|ERROR"
    local method="${name##*.}"
    local line
    line="$(grep -E "^${method} \(" "$log" || true)"
    if [ -z "$line" ]; then
      echo "MISSING:${name}"
    elif [ "$(echo "$line" | grep -cE '\.\.\. (FAIL|ERROR)$')" -gt 0 ]; then
      echo "$name"
    fi
  done
}

echo "=== baseline (unmutated) ==="
run_canaries
baseline_failed="$(failed_canaries_from_log "$SCRATCH/run.log")"
if [ -n "$baseline_failed" ]; then
  echo "FATAL: baseline has failing canaries before any mutation:" >&2
  echo "$baseline_failed" >&2
  cat "$SCRATCH/run.log" >&2
  exit 1
fi
echo "baseline: all ${#CANARIES[@]} canaries pass"
echo

declare -a MUTATION_NAMES
declare -a MUTATION_OLD
declare -a MUTATION_NEW
declare -a MUTATION_EXPECT

add_mutation() {
  MUTATION_NAMES+=("$1")
  MUTATION_OLD+=("$2")
  MUTATION_NEW+=("$3")
  MUTATION_EXPECT+=("$4")
}

add_mutation "fresh-read (commit uses cached journal)" \
  '    journal = _load_journal_fresh(txn_dir)  # GUARD: fresh-read, not cached' \
  '    journal = _LAST_STAGED_JOURNAL[str(txn_dir)]  # MUTATED: fresh-read guard removed' \
  "FreshReadTests.test_commit_uses_fresh_disk_journal_not_cached_object"

add_mutation "stale-receipt check removed" \
  '    _check_receipt_fresh(journal, root)  # GUARD: stale receipt' \
  '    pass  # MUTATED: stale-receipt guard removed' \
  "StalenessFixtureTests.test_stale_receipt_raises_only_stale_receipt_error"

add_mutation "stale-source check removed" \
  '    _check_source_fresh(journal, root)  # GUARD: stale source' \
  '    pass  # MUTATED: stale-source guard removed' \
  "StalenessFixtureTests.test_stale_source_raises_only_stale_source_error"

add_mutation "stale-graph check removed" \
  '    _check_graph_fresh(journal, root)  # GUARD: stale graph' \
  '    pass  # MUTATED: stale-graph guard removed' \
  "StalenessFixtureTests.test_stale_graph_raises_only_stale_graph_error"

add_mutation "stale-checker check removed" \
  '    _check_checker_fresh(journal)  # GUARD: stale checker' \
  '    pass  # MUTATED: stale-checker guard removed' \
  "StalenessFixtureTests.test_stale_checker_raises_only_stale_checker_error"

add_mutation "commit status precondition removed" \
  '    if journal.status != "prepared":' \
  '    if False:  # MUTATED: commit status precondition removed' \
  "GuardBehaviorTests.test_commit_rejects_a_non_prepared_transaction"

add_mutation "apply status precondition removed" \
  '    if journal.status not in ("committed", "applied"):' \
  '    if False:  # MUTATED: apply status precondition removed' \
  "GuardBehaviorTests.test_apply_rejects_an_uncommitted_transaction"

add_mutation "corrupt-staging integrity check removed" \
  '    _verify_staged_integrity(txn_dir, pending)  # GUARD: corrupt staging' \
  '    pass  # MUTATED: corrupt-staging guard removed' \
  "GuardBehaviorTests.test_apply_refuses_corrupted_staged_content"

add_mutation "idempotent-replay short-circuit removed" \
  '    if registry.get(fact_id) == receipt_sha:  # GUARD: idempotent replay' \
  '    if False:  # MUTATED: idempotent-replay guard removed' \
  "IdempotenceTests.test_replay_is_idempotent"

fail=0
n="${#MUTATION_NAMES[@]}"
for ((i = 0; i < n; i++)); do
  name="${MUTATION_NAMES[$i]}"
  old="${MUTATION_OLD[$i]}"
  new="${MUTATION_NEW[$i]}"
  expect="${MUTATION_EXPECT[$i]}"

  cp "$REPO_ROOT/scripts/credit-transaction.py" "$ENGINE"
  count_before="$(grep -Fc -- "$old" "$ENGINE" || true)"
  if [ "$count_before" -ne 1 ]; then
    echo "FATAL: mutation anchor for '$name' matched $count_before times (need exactly 1)" >&2
    exit 1
  fi
  python3 - "$ENGINE" "$old" "$new" <<'PYEOF'
import sys
path, old, new = sys.argv[1], sys.argv[2], sys.argv[3]
text = open(path).read()
assert text.count(old) == 1, (path, old)
open(path, "w").write(text.replace(old, new, 1))
PYEOF

  run_canaries
  failed="$(failed_canaries_from_log "$SCRATCH/run.log")"
  failed_count=0
  [ -n "$failed" ] && failed_count="$(echo "$failed" | grep -c . || true)"

  if [ "$failed_count" -eq 1 ] && [ "$failed" = "$expect" ]; then
    echo "OK   $name -> killed exactly: $expect"
  else
    fail=1
    echo "FAIL $name -> expected exactly [$expect], got:" >&2
    if [ -z "$failed" ]; then
      echo "  (nothing died -- guard is unreachable/decorative)" >&2
    else
      printf '  %s\n' "$failed" >&2
    fi
  fi

  # restore for the next iteration
  cp "$REPO_ROOT/scripts/credit-transaction.py" "$ENGINE"
done

echo
if [ "$fail" -ne 0 ]; then
  echo "MUTATION TABLE: FAILED -- see above" >&2
  exit 1
fi
echo "MUTATION TABLE: all ${n} guards each killed exactly their own canary"
